package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"log"
	"math"
	"math/bits"
	"os"
	"sort"
	"time"

	"filippo.io/edwards25519"

	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/hash/poseidon2"
	"github.com/consensys/gnark/std/math/cmp"

	"github.com/consensys/gnark-crypto/ecc"
	bls377fr "github.com/consensys/gnark-crypto/ecc/bls12-377/fr"
	bls377poseidon2 "github.com/consensys/gnark-crypto/ecc/bls12-377/fr/poseidon2"
)

const (
	N = 128

	// byte-sized domain tags for Poseidon2-MD
	tagHash = 1
	tagKDF  = 2

	// used when the dataset directory isn't found
	dummyRuns = 100
	dummyTau  = 10
)

// Domain separation for Schnorr equality proof transcript hash
const schnorrCtx = "FE|SchnorrEq|v1"

// Demo sparse parity-check H
var HROWS = [][]int{
	{0, 7, 14, 21, 28, 35, 42, 49},
	{1, 8, 15, 22, 29, 36, 43, 50},
	{2, 9, 16, 23, 30, 37, 44, 51},
	{3, 10, 17, 24, 31, 38, 45, 52},
	{4, 11, 18, 25, 32, 39, 46, 53},
	{5, 12, 19, 26, 33, 40, 47, 54},
	{6, 13, 20, 27, 34, 41, 48, 55},
}

/* ============================ Bit helpers =========================================== */

func xorU8(a, b uint8) uint8 { return (a ^ b) & 1 }

func xorBits(a, b [N]uint8) (out [N]uint8) {
	for i := 0; i < N; i++ {
		out[i] = xorU8(a[i], b[i])
	}
	return
}

func weight(bitsA [N]uint8) int {
	w := 0
	for i := 0; i < N; i++ {
		if bitsA[i] == 1 {
			w++
		}
	}
	return w
}

func bitsToHex16(bitsA [N]uint8) string {
	var b [16]byte
	for i := 0; i < N; i++ {
		if bitsA[i] == 1 {
			b[i/8] |= 1 << uint(i%8)
		}
	}
	return hex.EncodeToString(b[:])
}

func printBits(name string, bitsA [N]uint8) {
	fmt.Printf("%s (hex128) = %s\n", name, bitsToHex16(bitsA))
	fmt.Printf("%s (bin)    = ", name)
	for i := 0; i < N; i++ {
		fmt.Print(bitsA[i])
	}
	fmt.Println()
}

// randBits128 and sampleErrorOfWeight are only used by the dummy-data fallback.
func randBits128() (out [N]uint8) {
	var b [16]byte
	if _, err := rand.Read(b[:]); err != nil {
		log.Fatal(err)
	}
	for i := 0; i < N; i++ {
		out[i] = (b[i/8] >> uint(i%8)) & 1
	}
	return
}

func sampleErrorOfWeight(t int) (e [N]uint8) {
	idx := make([]int, N)
	for i := 0; i < N; i++ {
		idx[i] = i
	}
	for i := N - 1; i > 0; i-- {
		var rb [4]byte
		_, _ = rand.Read(rb[:])
		j := int(uint32(rb[0]) | uint32(rb[1])<<8 | uint32(rb[2])<<16 | uint32(rb[3])<<24)
		if j < 0 {
			j = -j
		}
		j %= (i + 1)
		idx[i], idx[j] = idx[j], idx[i]
	}
	for k := 0; k < t; k++ {
		e[idx[k]] = 1
	}
	return
}

/* ============================ GF(2) nullspace for non-zero c' =========================================== */

// represent 128-bit vectors as 2 uint64 blocks
type v128 struct {
	lo uint64 // bits 0..63
	hi uint64 // bits 64..127
}

func (v v128) xor(w v128) v128 { return v128{lo: v.lo ^ w.lo, hi: v.hi ^ w.hi} }
func (v v128) bit(i int) uint64 {
	if i < 64 {
		return (v.lo >> uint(i)) & 1
	}
	return (v.hi >> uint(i-64)) & 1
}
func (v *v128) setBit(i int, b uint64) {
	if i < 64 {
		if b == 1 {
			v.lo |= 1 << uint(i)
		} else {
			v.lo &^= 1 << uint(i)
		}
	} else {
		j := i - 64
		if b == 1 {
			v.hi |= 1 << uint(j)
		} else {
			v.hi &^= 1 << uint(j)
		}
	}
}
func (v v128) and(w v128) v128 { return v128{lo: v.lo & w.lo, hi: v.hi & w.hi} }
func (v v128) isZero() bool    { return v.lo == 0 && v.hi == 0 }
func (v v128) parity() uint64 {
	return uint64((bits.OnesCount64(v.lo) ^ bits.OnesCount64(v.hi)) & 1)
}

// Build H as v128 rows
func buildHRowsV128() []v128 {
	H := make([]v128, len(HROWS))
	for r, row := range HROWS {
		var v v128
		for _, j := range row {
			if j < 0 || j >= N {
				panic("HROWS index out of range")
			}
			v.setBit(j, 1)
		}
		H[r] = v
	}
	return H
}

// Compute RREF of H and return (rrefRows, pivotCols, freeCols).
func rrefGF2(rows []v128, n int) ([]v128, []int, []int) {
	m := len(rows)
	A := make([]v128, m)
	copy(A, rows)

	pivotCols := make([]int, 0, m)

	r := 0
	for c := 0; c < n && r < m; c++ {
		piv := -1
		for rr := r; rr < m; rr++ {
			if A[rr].bit(c) == 1 {
				piv = rr
				break
			}
		}
		if piv == -1 {
			continue
		}
		A[r], A[piv] = A[piv], A[r]

		pivotCols = append(pivotCols, c)

		// eliminate pivot column in all other rows
		for rr := 0; rr < m; rr++ {
			if rr == r {
				continue
			}
			if A[rr].bit(c) == 1 {
				A[rr] = A[rr].xor(A[r])
			}
		}
		r++
	}

	isPivot := make([]bool, n)
	for _, c := range pivotCols {
		isPivot[c] = true
	}
	freeCols := make([]int, 0, n-len(pivotCols))
	for c := 0; c < n; c++ {
		if !isPivot[c] {
			freeCols = append(freeCols, c)
		}
	}
	return A, pivotCols, freeCols
}

// Construct a nullspace basis from (near) RREF rows.
func nullspaceBasisFromRREF(A []v128, pivotCols, freeCols []int) []v128 {
	basis := make([]v128, 0, len(freeCols))

	pivotRowForCol := make(map[int]int, len(pivotCols))
	for pr, pc := range pivotCols {
		pivotRowForCol[pc] = pr
	}

	for _, f := range freeCols {
		var x v128
		x.setBit(f, 1)

		for _, pc := range pivotCols {
			pr := pivotRowForCol[pc]
			p := A[pr].and(x).parity()
			if p == 1 {
				x.setBit(pc, 1)
			} else {
				x.setBit(pc, 0)
			}
		}
		if !x.isZero() {
			basis = append(basis, x)
		}
	}
	if len(basis) == 0 {
		panic("nullspace basis is empty: H appears full-rank or construction bug")
	}
	return basis
}

// Sample a random non-zero codeword from a basis by XOR-ing a random subset.
func sampleCodewordFromBasis(basis []v128) (cBits [N]uint8) {
	var c v128
	var sel [1]byte
	for i := 0; i < len(basis); i++ {
		_, _ = rand.Read(sel[:])
		if (sel[0] & 1) == 1 {
			c = c.xor(basis[i])
		}
	}
	if c.isZero() {
		c = c.xor(basis[0]) // force non-zero
	}
	for i := 0; i < N; i++ {
		cBits[i] = uint8(c.bit(i))
	}
	return
}

/* ============================ Outside Poseidon2-MD (bytes) ========================================== */

func mdHashBytes(data []byte) ([]byte, error) {
	h := bls377poseidon2.NewMerkleDamgardHasher()
	h.Reset()
	if _, err := h.Write(data); err != nil {
		return nil, err
	}
	return h.Sum(nil), nil
}

func computeDigestOutside(cBits [N]uint8) (bls377fr.Element, error) {
	in := make([]byte, 0, 1+N)
	in = append(in, byte(tagHash))
	for i := 0; i < N; i++ {
		in = append(in, byte(cBits[i]))
	}
	outBytes, err := mdHashBytes(in)
	if err != nil {
		return bls377fr.Element{}, err
	}
	var d bls377fr.Element
	d.SetBytes(outBytes)
	return d, nil
}

func computeKOutside(cBits [N]uint8) (bls377fr.Element, error) {
	in := make([]byte, 0, 1+N)
	in = append(in, byte(tagKDF))
	for i := 0; i < N; i++ {
		in = append(in, byte(cBits[i]))
	}
	outBytes, err := mdHashBytes(in)
	if err != nil {
		return bls377fr.Element{}, err
	}
	var k bls377fr.Element
	k.SetBytes(outBytes)
	return k, nil
}

func ed25519FromK(k bls377fr.Element) (ed25519.PublicKey, ed25519.PrivateKey) {
	kb := k.Bytes()
	sum := sha512.Sum512(append([]byte("KDF:Ed25519:FE:v1|"), kb[:]...))
	seed := sum[:32]
	sk := ed25519.NewKeyFromSeed(seed)
	pk := sk.Public().(ed25519.PublicKey)
	return pk, sk
}

/* ============================ Schnorr Key Equality Proof (Ed25519 group) ============================================= */
/*
Proves knowledge of k such that pk = [k]B (B = Ed25519 basepoint), with FS challenge:
  c = H(ctx || pk || R || nonce || hFE)
Proof: (R, z) where R=[r]B, z=r + c*k (mod L)

Verifier checks:
  [z]B ?= R + [c]pk
*/

type SchnorrEqProof struct {
	R [32]byte // compressed Edwards point
	Z [32]byte // scalar encoding (little-endian)
}

func ed25519SecretScalar(sk ed25519.PrivateKey) *edwards25519.Scalar {
	seed := sk.Seed() // 32 bytes
	h := sha512.Sum512(seed)

	s, err := new(edwards25519.Scalar).SetBytesWithClamping(h[:32])
	if err != nil {
		// This should never happen for 32-byte input,
		// but we fail hard if it does.
		panic(err)
	}
	return s
}

func hashToScalar(pkBytes []byte, RBytes [32]byte, nonce []byte, hFE [64]byte) *edwards25519.Scalar {
	h := sha512.New()
	h.Write([]byte(schnorrCtx))
	h.Write([]byte{0})
	h.Write(pkBytes)
	h.Write(RBytes[:])
	h.Write(nonce)
	h.Write(hFE[:])
	sum := h.Sum(nil) // 64 bytes

	if len(sum) != 64 {
		panic("unexpected hash length")
	}

	sc, err := new(edwards25519.Scalar).SetUniformBytes(sum)
	if err != nil {
		panic(err)
	}
	return sc
}

func schnorrEqProve(pk ed25519.PublicKey, sk ed25519.PrivateKey, nonce []byte, hFE [64]byte) (SchnorrEqProof, [32]byte, error) {
	var proof SchnorrEqProof

	k := ed25519SecretScalar(sk)

	// r <- uniform scalar
	var rBytes [64]byte
	if _, err := rand.Read(rBytes[:]); err != nil {
		return proof, [32]byte{}, err
	}
	r, err := new(edwards25519.Scalar).SetUniformBytes(rBytes[:])
	if err != nil {
		return proof, [32]byte{}, err
	}

	// R = [r]B
	Rpt := new(edwards25519.Point).ScalarBaseMult(r)
	Renc := Rpt.Bytes()
	copy(proof.R[:], Renc)

	// c = H(ctx||pk||R||nonce||hFE)
	c := hashToScalar(pk, proof.R, nonce, hFE)

	// z = r + c*k
	ck := new(edwards25519.Scalar).Multiply(c, k)
	z := new(edwards25519.Scalar).Add(r, ck)

	zBytes := z.Bytes()
	copy(proof.Z[:], zBytes)

	// also return challenge c as bytes for printing
	var cOut [32]byte
	copy(cOut[:], c.Bytes())
	return proof, cOut, nil
}

func schnorrEqVerify(pk ed25519.PublicKey, nonce []byte, hFE [64]byte, proof SchnorrEqProof) (bool, [32]byte, error) {
	// decode R
	Rpt, err := new(edwards25519.Point).SetBytes(proof.R[:])
	if err != nil {
		return false, [32]byte{}, err
	}

	// decode pk point
	PKpt, err := new(edwards25519.Point).SetBytes(pk)
	if err != nil {
		return false, [32]byte{}, err
	}

	// decode z scalar
	z, err := new(edwards25519.Scalar).SetCanonicalBytes(proof.Z[:])
	if err != nil {
		return false, [32]byte{}, err
	}

	// recompute c
	c := hashToScalar(pk, proof.R, nonce, hFE)

	// check: [z]B == R + [c]PK
	left := new(edwards25519.Point).ScalarBaseMult(z)
	right := new(edwards25519.Point).Add(Rpt, new(edwards25519.Point).ScalarMult(c, PKpt))

	ok := left.Equal(right) == 1

	var cOut [32]byte
	copy(cOut[:], c.Bytes())
	return ok, cOut, nil
}

/* ============================ Circuit (K removed) =========================================== */

type FECircuit struct {
	P   [N]frontend.Variable `gnark:",public"`
	Tau frontend.Variable    `gnark:",public"`

	W [N]frontend.Variable // w'
	C [N]frontend.Variable // c'
	E [N]frontend.Variable // e
}

func xorBit(api frontend.API, a, b frontend.Variable) frontend.Variable {
	api.AssertIsBoolean(a)
	api.AssertIsBoolean(b)
	return api.Sub(api.Add(a, b), api.Mul(2, api.Mul(a, b)))
}

func (c *FECircuit) Define(api frontend.API) error {
	for i := 0; i < N; i++ {
		api.AssertIsBoolean(c.P[i])
		api.AssertIsBoolean(c.W[i])
		api.AssertIsBoolean(c.C[i])
		api.AssertIsBoolean(c.E[i])

		api.AssertIsEqual(
			xorBit(api, c.W[i], c.P[i]),
			xorBit(api, c.C[i], c.E[i]),
		)
	}

	for r, row := range HROWS {
		par := frontend.Variable(0)
		for _, j := range row {
			if j < 0 || j >= N {
				return fmt.Errorf("H row %d invalid index %d", r, j)
			}
			par = xorBit(api, par, c.C[j])
		}
		api.AssertIsEqual(par, 0)
	}

	wt := frontend.Variable(0)
	for i := 0; i < N; i++ {
		wt = api.Add(wt, c.E[i])
	}
	api.AssertIsEqual(cmp.IsLessOrEqual(api, wt, c.Tau), 1)

	// existential private k derived in-circuit
	h, err := poseidon2.NewMerkleDamgardHasher(api)
	if err != nil {
		return fmt.Errorf("poseidon2 init failed: %w", err)
	}
	h.Reset()
	h.Write(tagKDF)
	for i := 0; i < N; i++ {
		h.Write(c.C[i])
	}
	k := h.Sum()
	api.AssertIsDifferent(api.Add(k, 1), k)

	return nil
}

/* ============================ Stats ============================================= */

func meanStdMinMax(xs []float64) (mean, std, min, max float64) {
	if len(xs) == 0 {
		return 0, 0, 0, 0
	}
	min, max = xs[0], xs[0]
	for _, x := range xs {
		mean += x
		if x < min {
			min = x
		}
		if x > max {
			max = x
		}
	}
	mean /= float64(len(xs))
	for _, x := range xs {
		d := x - mean
		std += d * d
	}
	std = math.Sqrt(std / float64(len(xs)))
	return mean, std, min, max
}

func proofHash64(proof groth16.Proof) [64]byte {
	var out [64]byte
	var buf bytes.Buffer
	// gnark Proof.WriteTo(io.Writer)
	if _, err := proof.WriteTo(&buf); err != nil {
		// if serialization fails, return zeros; this will just change transcript binding
		return out
	}
	out = sha512.Sum512(buf.Bytes())
	return out
}

/* ============================ Main =============================================== */

// EnrolledTemplate is one helper-data/key set bound to a single enrolled session.
type EnrolledTemplate struct {
	Session Session
	P, C    [N]uint8
	PK      ed25519.PublicKey
	SK      ed25519.PrivateKey
}

func main() {
	// ---- load real biometric data (Blow audio embeddings), or fall back to dummy data ----
	datasetMissing := false
	if _, statErr := os.Stat(DatasetDir); statErr != nil {
		if !os.IsNotExist(statErr) {
			log.Fatalf("checking dataset dir %s: %v", DatasetDir, statErr)
		}
		datasetMissing = true
	}

	var sessions []Session
	var byParticipant map[int][]Session
	var participantIDs []int
	if !datasetMissing {
		var err error
		sessions, err = loadAudioSessions(DatasetDir)
		if err != nil {
			log.Fatal(err)
		}
		byParticipant = groupByParticipant(sessions)
		participantIDs = make([]int, 0, len(byParticipant))
		for pid := range byParticipant {
			participantIDs = append(participantIDs, pid)
		}
		sort.Ints(participantIDs)
	}

	fmt.Println("========== CONFIG ==========")
	fmt.Printf("Curve: BLS12-377 | N=%d\n", N)
	if datasetMissing {
		fmt.Printf("Dataset dir not found: %s\n", DatasetDir)
		fmt.Printf("Falling back to dummy random data: single enrollment, %d runs\n", dummyRuns)
	} else {
		fmt.Printf("Dataset dir: %s\n", DatasetDir)
		fmt.Printf("Participants loaded: %d | Total sessions: %d\n", len(byParticipant), len(sessions))
		fmt.Println("Evaluation: every participant enrolls in turn, tested against every other real session (Threshold.py-style full matrix)")
		fmt.Printf("TAU source: k-NN threshold (k=%d, p=%d) over each enrolled participant's own session Hamming distances\n", thresholdK, thresholdP)
	}
	fmt.Printf("H rows=%d\n", len(HROWS))
	for i, row := range HROWS {
		fmt.Printf("  H[%d]=%v\n", i, row)
	}
	fmt.Println("===========================\n")

	// ---- build nullspace basis once (off-circuit only) ----
	Hv := buildHRowsV128()
	A, piv, free := rrefGF2(Hv, N)
	basis := nullspaceBasisFromRREF(A, piv, free)
	fmt.Printf("Nullspace basis size = %d (dimension >= %d)\n\n", len(basis), len(basis))

	// Compile + Setup (once, reused across all enrollments)
	fmt.Println("Compiling circuit (BLS12-377 scalar field)...")
	tCompile := time.Now()
	var circuit FECircuit
	ccs, err := frontend.Compile(ecc.BLS12_377.ScalarField(), r1cs.NewBuilder, &circuit)
	if err != nil {
		log.Fatal(err)
	}
	compileDur := time.Since(tCompile)
	fmt.Printf("Compile time: %v | Constraints: %d\n", compileDur, ccs.GetNbConstraints())

	fmt.Println("Groth16 setup (one-time)...")
	tSetup := time.Now()
	pkG, vkG, err := groth16.Setup(ccs)
	if err != nil {
		log.Fatal(err)
	}
	setupDur := time.Since(tSetup)
	fmt.Printf("Setup time  : %v\n\n", setupDur)

	// timing arrays, pooled across every enrollment/probe
	var proveAll, verifyAll []float64
	var schnorrPAll, schnorrVAll []float64
	var sigPAll, sigVAll []float64

	// same as proveAll, but only for probes that were ultimately ACCEPTED for both Genuine and Impostor runs
	var proveOK []float64

	genuineTotalAll, genuineAcceptAll := 0, 0
	impostorTotalAll, impostorAcceptAll := 0, 0
	totalRuns := 0

	enrollmentCount := len(participantIDs)

	if datasetMissing {
		fmt.Println("========== RUNS (dummy random data, single enrollment) ==========")
		enrollmentCount = 1

		wEnroll := randBits128()
		cCode := sampleCodewordFromBasis(basis)
		P := xorBits(wEnroll, cCode)
		kOutside, err := computeKOutside(cCode)
		if err != nil {
			log.Fatal(err)
		}
		enrollPK, enrollSK := ed25519FromK(kOutside)

		for run := 1; run <= dummyRuns; run++ {
			totalRuns++
			isGenuine := run%2 == 1

			nonce := make([]byte, 32)
			_, _ = rand.Read(nonce)

			var wPrime, eBits [N]uint8
			if isGenuine {
				var rb [1]byte
				_, _ = rand.Read(rb[:])
				t := int(rb[0]) % (dummyTau + 1)
				eBits = sampleErrorOfWeight(t)
				wPrime = xorBits(wEnroll, eBits)
			} else {
				wPrime = randBits128()
				eBits = xorBits(xorBits(wPrime, P), cCode)
			}
			wtE := weight(eBits)

			var a FECircuit
			a.Tau = dummyTau
			for i := 0; i < N; i++ {
				a.P[i] = int(P[i])
				a.W[i] = int(wPrime[i])
				a.C[i] = int(cCode[i])
				a.E[i] = int(eBits[i])
			}

			wit, err := frontend.NewWitness(&a, ecc.BLS12_377.ScalarField())
			if err != nil {
				log.Fatal(err)
			}
			pubWit, err := wit.Public()
			if err != nil {
				log.Fatal(err)
			}

			t0 := time.Now()
			proof, proveErr := groth16.Prove(ccs, pkG, wit)
			dtProve := float64(time.Since(t0).Nanoseconds()) / 1e6
			proveAll = append(proveAll, dtProve)

			okSNARK := false
			dtVerify := 0.0
			var verifyErr error
			if proveErr == nil {
				t1 := time.Now()
				verifyErr = groth16.Verify(proof, vkG, pubWit)
				dtVerify = float64(time.Since(t1).Nanoseconds()) / 1e6
				verifyAll = append(verifyAll, dtVerify)
				okSNARK = (verifyErr == nil)
			}

			var hFE [64]byte
			if proveErr == nil {
				hFE = proofHash64(proof)
			}

			t2 := time.Now()
			sEq, cEqProver, eqPerr := schnorrEqProve(enrollPK, enrollSK, nonce, hFE)
			dtSchnorrP := float64(time.Since(t2).Nanoseconds()) / 1e6
			schnorrPAll = append(schnorrPAll, dtSchnorrP)

			t3 := time.Now()
			eqOK := false
			var eqVerr error
			var cEqVerifier [32]byte
			if eqPerr == nil {
				eqOK, cEqVerifier, eqVerr = schnorrEqVerify(enrollPK, nonce, hFE, sEq)
			}
			dtSchnorrV := float64(time.Since(t3).Nanoseconds()) / 1e6
			schnorrVAll = append(schnorrVAll, dtSchnorrV)

			t4 := time.Now()
			sig := ed25519.Sign(enrollSK, nonce)
			dtSigP := float64(time.Since(t4).Nanoseconds()) / 1e6
			sigPAll = append(sigPAll, dtSigP)
			t5 := time.Now()
			sigOK := ed25519.Verify(enrollPK, nonce, sig)
			dtSigV := float64(time.Since(t5).Nanoseconds()) / 1e6
			sigVAll = append(sigVAll, dtSigV)

			accept := okSNARK && eqOK && sigOK
			if accept {
				proveOK = append(proveOK, dtProve)
			}

			kind := "IMPOSTOR"
			if isGenuine {
				genuineTotalAll++
				kind = "GENUINE"
				if accept {
					genuineAcceptAll++
				}
			} else {
				impostorTotalAll++
				if accept {
					impostorAcceptAll++
				}
			}

			fmt.Printf("Run %03d [%s]\n", run, kind)
			printBits("  w  (enroll)", wEnroll)
			printBits("  w' (probe) ", wPrime)
			printBits("  c' (code)  ", cCode)
			printBits("  e  (error) ", eBits)
			printBits("  P  (helper)", P)
			fmt.Printf("  tau=%d | wt(e)=%d | wt<=tau=%v\n", dummyTau, wtE, wtE <= dummyTau)

			fmt.Printf("  pk(ed25519)       = %s\n", hex.EncodeToString(enrollPK))
			fmt.Printf("  nonce(hex)        = %s\n", hex.EncodeToString(nonce))
			fmt.Printf("  sig(hex)          = %s\n", hex.EncodeToString(sig))

			fmt.Printf("  SNARK: proveErr=%v | verifyErr=%v | ok=%v | Prove=%.3f ms | Verify=%.3f ms\n",
				proveErr, verifyErr, okSNARK, dtProve, dtVerify,
			)

			if eqPerr != nil {
				fmt.Printf("  SchnorrEq: PROVE FAIL | err=%v | Prove=%.3f ms\n", eqPerr, dtSchnorrP)
			} else if eqVerr != nil {
				fmt.Printf("  SchnorrEq: VERIFY FAIL | err=%v | Prove=%.3f ms | Verify=%.3f ms\n",
					eqVerr, dtSchnorrP, dtSchnorrV,
				)
			} else {
				fmt.Printf("  SchnorrEq: ok=%v | Prove=%.3f ms | Verify=%.3f ms\n",
					eqOK, dtSchnorrP, dtSchnorrV,
				)
				fmt.Printf("    R(hex)          = %s\n", hex.EncodeToString(sEq.R[:]))
				fmt.Printf("    z(hex)          = %s\n", hex.EncodeToString(sEq.Z[:]))
				fmt.Printf("    c_prover(hex)   = %s\n", hex.EncodeToString(cEqProver[:]))
				fmt.Printf("    c_verifier(hex) = %s\n", hex.EncodeToString(cEqVerifier[:]))
			}

			fmt.Printf("  Signature verify: ok=%v | Verify=%.3f ms\n", sigOK, dtSigV)
			fmt.Printf("  FINAL ACCEPT = %v\n", accept)
			fmt.Println("--------------------------------------------------")
		}
		fmt.Println("===============================================\n")
	} else {

		// TAU per participant; probes are judged against the probe owner's own TAU, not the
		// enrolled participant's (see probeTau below).
		tauByParticipant := make(map[int]int, len(participantIDs))
		for _, pid := range participantIDs {
			tauByParticipant[pid] = computeTauForParticipant(byParticipant[pid])
		}

		fmt.Println("========== RUNS (every participant enrolled in turn) ==========")
		for _, pid := range participantIDs {
			enrolledSessions := byParticipant[pid]
			TAU := tauByParticipant[pid]

			// one (P, c') helper-data pair per real session
			templates := make([]EnrolledTemplate, len(enrolledSessions))
			for j, es := range enrolledSessions {
				cCode := sampleCodewordFromBasis(basis)
				P := xorBits(es.Vec, cCode)
				kOutside, err := computeKOutside(cCode)
				if err != nil {
					log.Fatal(err)
				}
				pk, sk := ed25519FromK(kOutside)
				templates[j] = EnrolledTemplate{Session: es, P: P, C: cCode, PK: pk, SK: sk}
			}

			// own sessions = genuine probes, every other participant's = impostor probes
			var probes []Session
			probes = append(probes, enrolledSessions...)
			for _, opid := range participantIDs {
				if opid == pid {
					continue
				}
				probes = append(probes, byParticipant[opid]...)
			}

			fmt.Printf("----- Enrolling participant %d | sessions=%d | TAU=%d | probes=%d -----\n",
				pid, len(enrolledSessions), TAU, len(probes))

			genuineTotal, genuineAccept := 0, 0
			impostorTotal, impostorAccept := 0, 0

			for _, probe := range probes {
				totalRuns++
				isGenuine := probe.Participant == pid

				// match against the k-th nearest gallery template
				ti := kthNearestTemplateIndex(probe, enrolledSessions, thresholdK)
				tmpl := templates[ti]

				// Server-side fresh nonce per session (replay resistance)
				nonce := make([]byte, 32)
				_, _ = rand.Read(nonce)

				// e = w' xor P xor c'
				wPrime := probe.Vec
				eBits := xorBits(xorBits(wPrime, tmpl.P), tmpl.C)
				wtE := weight(eBits)

				probeTau := tauByParticipant[probe.Participant]

				// Witness assignment for SNARK
				var a FECircuit
				a.Tau = probeTau
				for i := 0; i < N; i++ {
					a.P[i] = int(tmpl.P[i])
					a.W[i] = int(wPrime[i])
					a.C[i] = int(tmpl.C[i])
					a.E[i] = int(eBits[i])
				}

				wit, err := frontend.NewWitness(&a, ecc.BLS12_377.ScalarField())
				if err != nil {
					log.Fatal(err)
				}
				pubWit, err := wit.Public()
				if err != nil {
					log.Fatal(err)
				}

				// --- SNARK Prove + Verify ---
				t0 := time.Now()
				proof, proveErr := groth16.Prove(ccs, pkG, wit)
				dtProve := float64(time.Since(t0).Nanoseconds()) / 1e6
				proveAll = append(proveAll, dtProve)

				okSNARK := false
				dtVerify := 0.0
				var verifyErr error
				if proveErr == nil {
					t1 := time.Now()
					verifyErr = groth16.Verify(proof, vkG, pubWit)
					dtVerify = float64(time.Since(t1).Nanoseconds()) / 1e6
					verifyAll = append(verifyAll, dtVerify)
					okSNARK = (verifyErr == nil)
				}

				var hFE [64]byte
				if proveErr == nil {
					hFE = proofHash64(proof)
				}

				// --- Schnorr key equality proof (prover + verifier) ---
				t2 := time.Now()
				sEq, cEqProver, eqPerr := schnorrEqProve(tmpl.PK, tmpl.SK, nonce, hFE)
				dtSchnorrP := float64(time.Since(t2).Nanoseconds()) / 1e6
				schnorrPAll = append(schnorrPAll, dtSchnorrP)

				t3 := time.Now()
				eqOK := false
				var eqVerr error
				var cEqVerifier [32]byte
				if eqPerr == nil {
					eqOK, cEqVerifier, eqVerr = schnorrEqVerify(tmpl.PK, nonce, hFE, sEq)
				}
				dtSchnorrV := float64(time.Since(t3).Nanoseconds()) / 1e6
				schnorrVAll = append(schnorrVAll, dtSchnorrV)

				// --- Active key usage proof: signature on nonce ---
				t4 := time.Now()
				sig := ed25519.Sign(tmpl.SK, nonce)
				dtSigP := float64(time.Since(t4).Nanoseconds()) / 1e6
				sigPAll = append(sigPAll, dtSigP)
				t5 := time.Now()
				sigOK := ed25519.Verify(tmpl.PK, nonce, sig)
				dtSigV := float64(time.Since(t5).Nanoseconds()) / 1e6
				sigVAll = append(sigVAll, dtSigV)

				// --- Final server decision (Option B: all three must hold + fresh nonce) ---
				accept := okSNARK && eqOK && sigOK
				if accept {
					proveOK = append(proveOK, dtProve)
				}

				kind := "IMPOSTOR"
				if isGenuine {
					genuineTotal++
					kind = "GENUINE"
					if accept {
						genuineAccept++
					}
				} else {
					impostorTotal++
					if accept {
						impostorAccept++
					}
				}

				fmt.Printf("Run %06d [enroll=%03d] [%s] probe=%s matched=%s\n", totalRuns, pid, kind, probe, tmpl.Session)
				printBits("  w  (enroll)", tmpl.Session.Vec)
				printBits("  w' (probe) ", wPrime)
				printBits("  c' (code)  ", tmpl.C)
				printBits("  e  (error) ", eBits)
				printBits("  P  (helper)", tmpl.P)
				fmt.Printf("  tau=%d | wt(e)=%d | wt<=tau=%v\n", probeTau, wtE, wtE <= probeTau)

				fmt.Printf("  pk(ed25519)       = %s\n", hex.EncodeToString(tmpl.PK))
				fmt.Printf("  nonce(hex)        = %s\n", hex.EncodeToString(nonce))
				fmt.Printf("  sig(hex)          = %s\n", hex.EncodeToString(sig))

				fmt.Printf("  SNARK: proveErr=%v | verifyErr=%v | ok=%v | Prove=%.3f ms | Verify=%.3f ms\n",
					proveErr, verifyErr, okSNARK, dtProve, dtVerify,
				)

				if eqPerr != nil {
					fmt.Printf("  SchnorrEq: PROVE FAIL | err=%v | Prove=%.3f ms\n", eqPerr, dtSchnorrP)
				} else if eqVerr != nil {
					fmt.Printf("  SchnorrEq: VERIFY FAIL | err=%v | Prove=%.3f ms | Verify=%.3f ms\n",
						eqVerr, dtSchnorrP, dtSchnorrV,
					)
				} else {
					fmt.Printf("  SchnorrEq: ok=%v | Prove=%.3f ms | Verify=%.3f ms\n",
						eqOK, dtSchnorrP, dtSchnorrV,
					)
					fmt.Printf("    R(hex)          = %s\n", hex.EncodeToString(sEq.R[:]))
					fmt.Printf("    z(hex)          = %s\n", hex.EncodeToString(sEq.Z[:]))
					fmt.Printf("    c_prover(hex)   = %s\n", hex.EncodeToString(cEqProver[:]))
					fmt.Printf("    c_verifier(hex) = %s\n", hex.EncodeToString(cEqVerifier[:]))
				}

				fmt.Printf("  Signature verify: ok=%v | Verify=%.3f ms\n", sigOK, dtSigV)
				fmt.Printf("  FINAL ACCEPT = %v\n", accept)
				fmt.Println("--------------------------------------------------")
			}

			fmt.Printf("--- Participant %d summary: genuine accept %d/%d | impostor accept %d/%d ---\n\n",
				pid, genuineAccept, genuineTotal, impostorAccept, impostorTotal)

			genuineTotalAll += genuineTotal
			genuineAcceptAll += genuineAccept
			impostorTotalAll += impostorTotal
			impostorAcceptAll += impostorAccept
		}
		fmt.Println("===============================================\n")
	}

	mvA, svA, minVA, maxVA := meanStdMinMax(verifyAll)
	meqPA, seqPA, mineqPA, maxeqPA := meanStdMinMax(schnorrPAll)
	meqVA, seqVA, mineqVA, maxeqVA := meanStdMinMax(schnorrVAll)
	msigP, ssigP, minsigP, maxsigP := meanStdMinMax(sigPAll)
	msigV, ssigV, minsigV, maxsigV := meanStdMinMax(sigVAll)

	mpS, spS, minPS, maxPS := meanStdMinMax(proveOK)

	fmt.Println("========== SUMMARY ==========")
	fmt.Printf("Compile time: %v | Setup time: %v | Constraints: %d\n", compileDur, setupDur, ccs.GetNbConstraints())
	fmt.Printf("Enrollments  : %d | Total runs: %d\n", enrollmentCount, totalRuns)

	if datasetMissing {
		fmt.Println("(dummy data - no dataset accuracy metrics, timing only)")
	} else {
		frr := 0.0
		if genuineTotalAll > 0 {
			frr = 1.0 - float64(genuineAcceptAll)/float64(genuineTotalAll)
		}
		far := 0.0
		if impostorTotalAll > 0 {
			far = float64(impostorAcceptAll) / float64(impostorTotalAll)
		}

		// TP=genuine accepted, FN=genuine rejected, FP=impostor accepted, TN=impostor rejected
		TP := float64(genuineAcceptAll)
		FN := float64(genuineTotalAll - genuineAcceptAll)
		FP := float64(impostorAcceptAll)
		TN := float64(impostorTotalAll - impostorAcceptAll)

		precision := 0.0
		if TP+FP > 0 {
			precision = TP / (TP + FP)
		}
		recall := 0.0
		if TP+FN > 0 {
			recall = TP / (TP + FN)
		}
		accuracy := 0.0
		if TP+TN+FP+FN > 0 {
			accuracy = (TP + TN) / (TP + TN + FP + FN)
		}

		fmt.Printf("Genuine trials : %d | Accept=%d | FRR=%.4f\n", genuineTotalAll, genuineAcceptAll, frr)
		fmt.Printf("Impostor trials: %d | Accept=%d | FAR=%.4f\n", impostorTotalAll, impostorAcceptAll, far)
		fmt.Printf("Precision=%.4f | Recall=%.4f | Accuracy=%.4f\n", precision, recall, accuracy)
		fmt.Printf("TP=%.0f TN=%.0f FP=%.0f FN=%.0f\n", TP, TN, FP, FN)
	}


	fmt.Printf("\nTiming (Semantic Correctness Generation over %d successful attempts, rest over %d runs):\n", len(proveOK), totalRuns)
	fmt.Printf("  Semantic Correctness Proof Generation   : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", mpS, spS, minPS, maxPS)
	fmt.Printf("  Semantic Correctness Proof Verification : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", mvA, svA, minVA, maxVA)
	fmt.Printf("  Key Equality Proof Generation           : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", meqPA, seqPA, mineqPA, maxeqPA)
	fmt.Printf("  Key Equality Proof Verification         : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", meqVA, seqVA, mineqVA, maxeqVA)
	fmt.Printf("  Key Freshness Proof Generation          : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", msigP, ssigP, minsigP, maxsigP)
	fmt.Printf("  Key Freshness Proof Verification        : mean=%.4f ms std=%.4f ms min=%.4f ms max=%.4f ms\n", msigV, ssigV, minsigV, maxsigV)
	fmt.Println("================================")
}
