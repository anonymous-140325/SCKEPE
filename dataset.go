package main

import (
	"bufio"
	"crypto/rand"
	"fmt"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

const DatasetDir = "Blow_Biometric_Binarize_Data"

// k-th nearest neighbor / p-th largest parameters
const (
	thresholdK = 1
	thresholdP = 1
)

// Session holds one participant's binarized 128-bit audio embedding for one session.
type Session struct {
	Participant int
	SessionNum  int
	Posture     string // "sit" or "stand"
	Path        string
	Vec         [N]uint8
}

func (s Session) String() string {
	return fmt.Sprintf("Participant %d / session %d (%s)", s.Participant, s.SessionNum, s.Posture)
}

var (
	participantDirRe = regexp.MustCompile(`^Participant (\d+)$`)
	sessionFileRe    = regexp.MustCompile(`^session_(\d+)_(sit|stand)_audio\.csv$`)
)

// loadAudioSessions walks root/"Participant N"/session_X_<sit|stand>_audio.csv and parses
// each file's 128 lines of 0/1 into a binary embedding vector.
func loadAudioSessions(root string) ([]Session, error) {
	participantDirs, err := os.ReadDir(root)
	if err != nil {
		return nil, fmt.Errorf("reading dataset dir %s: %w", root, err)
	}

	var sessions []Session
	for _, pd := range participantDirs {
		if !pd.IsDir() {
			continue
		}
		m := participantDirRe.FindStringSubmatch(pd.Name())
		if m == nil {
			continue
		}
		participant, _ := strconv.Atoi(m[1])

		dir := filepath.Join(root, pd.Name())
		files, err := os.ReadDir(dir)
		if err != nil {
			return nil, fmt.Errorf("reading %s: %w", dir, err)
		}
		for _, f := range files {
			if f.IsDir() {
				continue
			}
			fm := sessionFileRe.FindStringSubmatch(f.Name())
			if fm == nil {
				continue
			}
			sessionNum, _ := strconv.Atoi(fm[1])
			posture := fm[2]
			path := filepath.Join(dir, f.Name())

			vec, err := readBitVectorCSV(path)
			if err != nil {
				return nil, err
			}
			sessions = append(sessions, Session{
				Participant: participant,
				SessionNum:  sessionNum,
				Posture:     posture,
				Path:        path,
				Vec:         vec,
			})
		}
	}
	if len(sessions) == 0 {
		return nil, fmt.Errorf("no *_audio.csv session files found under %s", root)
	}

	sort.Slice(sessions, func(i, j int) bool {
		if sessions[i].Participant != sessions[j].Participant {
			return sessions[i].Participant < sessions[j].Participant
		}
		if sessions[i].SessionNum != sessions[j].SessionNum {
			return sessions[i].SessionNum < sessions[j].SessionNum
		}
		return sessions[i].Posture < sessions[j].Posture
	})
	return sessions, nil
}

// readBitVectorCSV reads a one-value-per-line CSV of exactly N zeros/ones.
func readBitVectorCSV(path string) (v [N]uint8, err error) {
	f, err := os.Open(path)
	if err != nil {
		return v, err
	}
	defer f.Close()

	scanner := bufio.NewScanner(f)
	i := 0
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		if i >= N {
			return v, fmt.Errorf("%s: more than %d values", path, N)
		}
		val, convErr := strconv.Atoi(line)
		if convErr != nil || (val != 0 && val != 1) {
			return v, fmt.Errorf("%s: expected 0/1, got %q", path, line)
		}
		v[i] = uint8(val)
		i++
	}
	if err := scanner.Err(); err != nil {
		return v, err
	}
	if i != N {
		return v, fmt.Errorf("%s: found %d values, expected %d", path, i, N)
	}
	return v, nil
}

func groupByParticipant(sessions []Session) map[int][]Session {
	m := make(map[int][]Session)
	for _, s := range sessions {
		m[s.Participant] = append(m[s.Participant], s)
	}
	return m
}

func hammingDistance(a, b [N]uint8) int {
	d := 0
	for i := 0; i < N; i++ {
		if a[i] != b[i] {
			d++
		}
	}
	return d
}

// determineThreshold returns the p-th largest of each row's k-th smallest value.
func determineThreshold(matrix [][]int, k, p int) int {
	candidates := make([]int, len(matrix))
	for i, row := range matrix {
		sorted := append([]int(nil), row...)
		sort.Ints(sorted)
		candidates[i] = sorted[k]
	}
	sort.Sort(sort.Reverse(sort.IntSlice(candidates)))
	return candidates[p]
}

// computeTauForParticipant derives TAU from a participant's own session Hamming distances
// (self excluded via +Inf on the diagonal).
func computeTauForParticipant(sessions []Session) int {
	n := len(sessions)
	matrix := make([][]int, n)
	for i := range matrix {
		matrix[i] = make([]int, n)
		for j := range matrix[i] {
			if i == j {
				matrix[i][j] = math.MaxInt
				continue
			}
			matrix[i][j] = hammingDistance(sessions[i].Vec, sessions[j].Vec)
		}
	}
	return determineThreshold(matrix, thresholdK, thresholdP)
}

// kthNearestTemplateIndex returns the index of the candidate whose Hamming distance to probe
// is k-th smallest (self excluded via +Inf).
func kthNearestTemplateIndex(probe Session, candidates []Session, k int) int {
	type pair struct {
		idx int
		d   int
	}
	pairs := make([]pair, len(candidates))
	for idx, s := range candidates {
		d := hammingDistance(probe.Vec, s.Vec)
		if s.Path == probe.Path {
			d = math.MaxInt
		}
		pairs[idx] = pair{idx, d}
	}
	sort.Slice(pairs, func(i, j int) bool { return pairs[i].d < pairs[j].d })
	if k >= len(pairs) {
		k = len(pairs) - 1
	}
	return pairs[k].idx
}

// shuffleSessions returns a random permutation of sessions using crypto/rand.
func shuffleSessions(sessions []Session) []Session {
	out := make([]Session, len(sessions))
	copy(out, sessions)
	for i := len(out) - 1; i > 0; i-- {
		jBig, err := rand.Int(rand.Reader, big.NewInt(int64(i+1)))
		if err != nil {
			continue
		}
		j := int(jBig.Int64())
		out[i], out[j] = out[j], out[i]
	}
	return out
}
