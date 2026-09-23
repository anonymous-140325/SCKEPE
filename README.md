# Setup (Linux)

Install a stable version of `go`, e.g., 1.24.11

## Configuration

### Create directory
- Download the code from this repository
- Go to the directory: `cd SCKEPE`
  
### Initialize module
- `go mod init SCKEPE`

### Add dependencies
- `go get github.com/consensys/gnark@v0.14.0`
- `go get github.com/consensys/gnark-crypto@v0.19.2`
- `go get github.com/liyue201/gnark-circomlib@latest`
- `go get github.com/iden3/go-iden3-crypto@latest`
- `go mod tidy`

The above steps create `go.mod` and `go.sum` configuration files in the project directory. 

### Data dependency

This code reads real enrollment/probe data from the BlowLive audio-embedding dataset at
`Blow_Biometric_Binarize_Data` (i.e. it expects that dataset folder to live directly inside
`SCKEPE/`, alongside `main.go`/`dataset.go`). It contains 128-bit binarized, anonymized audio
data for each participant's 10 sessions.

Every participant enrolls in turn (with their full 10-session set as a template gallery), and
every real session in the dataset is tested as a probe against every enrollment. TAU is derived
per participant from their own session-to-session Hamming distances (k-NN threshold), and a
probe is judged against its own owner's TAU, not the enrolled participant's. The k and p values
used for this can be changed in `dataset.go`.

## Run

- `go run .`

Prints a per-run line for each authentication attempt, a per-participant genuine/impostor
summary, and a final aggregate report (FRR, FAR, Precision, Recall, Accuracy, plus proof/verify
timing stats).


# Setup (Phone)

It is also possible to simulate the runtime performance of SCKEPE on a mobile device. While this can be achieved in various ways, a straightforward approach is to execute the code on an Android device via the Android shell using ADB. For example, to run the code on a Samsung Galaxy S24 Ultra from a Linux host using ADB, follow the steps below.

### ADB and phone setup

- Install adb on Linux using package manager, e.g., `sudo apt install android-tools-adb`.
- Verify its installation on terminal by typing `adb`.
- From the phone's setting, set "Developer options" ON, and allow "USB debugging".
- Connect the phone to the computer through cable.
- Verify the phone in terminal using `adb devices`. If the phone is found, you will see a device under list of devices.

### Go code cross-compilation (Linux → Android ARM64)
Compile the `go` code to arm64 as follows:
- On terminal, go to the "main.go" folder.
- Run `GOOS=android GOARCH=arm64 go build -o main`.
-  The aboe command will generate an executable file named "main".

### Execute code

- Push the executable file to the phone using adb: `adb push main /data/local/tmp`.
- Open the phone shell using adb: `adb shell`.
- Go to the executable file directory: `cd /data/local/tmp`.
- Set execution permissions: `chmod +x main`.
- Run the executable file: `./main`.
