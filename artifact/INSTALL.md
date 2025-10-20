# Installation Guide

> **Estimated Time**: 15-30 minutes (without Docker) or 5-10 minutes (with Docker)  
> **Difficulty**: Easy with Docker, Moderate without

---

## 📋 Prerequisites Check

Before starting, verify your system meets these requirements:

```bash
# Check OS
uname -a

# Check CPU cores (minimum 4)
nproc

# Check memory (minimum 8GB)
free -h

# Check disk space (minimum 20GB)
df -h .
```

---

## 🐳 Option A: Docker Installation (Recommended)

### Step 1: Install Docker

**Linux**:

```bash
# Ubuntu/Debian
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER
newgrp docker

# Verify
docker --version
docker-compose --version
```

**macOS**:

```bash
# Install Docker Desktop from https://www.docker.com/products/docker-desktop
# Or using Homebrew:
brew install --cask docker
```

**Windows**:

1. Install Docker Desktop from <https://www.docker.com/products/docker-desktop>
2. Enable WSL2 backend
3. Restart computer

### Step 2: Build Docker Image

```bash
# Clone repository
git clone https://github.com/anonymous/otlp-verification-artifact
cd otlp-verification-artifact/artifact

# Build Docker image (takes 10-15 minutes)
docker-compose build

# Expected output: "Successfully built ..."
```

### Step 3: Start Containers

```bash
# Start all services
docker-compose up -d

# Verify containers are running
docker-compose ps

# Expected output:
# NAME               STATUS          PORTS
# verifier           Up 10 seconds   8080:8080
# coq-prover         Up 10 seconds   -
# data-store         Up 10 seconds   5432:5432
```

### Step 4: Run Quick Test

```bash
# Access the verifier container
docker-compose exec verifier bash

# Inside container: run quick test
./scripts/quick_validation.sh

# Expected output: "✅ All systems validated"
```

---

## 🔧 Option B: Native Installation

### Step 1: Install System Dependencies

**Ubuntu/Debian**:

```bash
sudo apt-get update
sudo apt-get install -y \
    build-essential \
    curl \
    git \
    pkg-config \
    libssl-dev \
    python3 \
    python3-pip
```

**macOS**:

```bash
# Install Homebrew if not already installed
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# Install dependencies
brew install git curl python3
```

**Windows (WSL2)**:

```bash
# Inside WSL2 Ubuntu
sudo apt-get update
sudo apt-get install -y build-essential curl git pkg-config libssl-dev python3 python3-pip
```

### Step 2: Install Rust

```bash
# Install rustup
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Source environment
source "$HOME/.cargo/env"

# Verify installation
rustc --version   # Should show 1.70.0 or higher
cargo --version
```

### Step 3: Install Coq

**Using opam (Recommended)**:

```bash
# Install opam
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"

# Initialize opam
opam init -y
eval $(opam env)

# Install Coq
opam install coq.8.17.0 -y

# Verify
coqc --version   # Should show 8.17.0
```

**Alternative (apt for Ubuntu)**:

```bash
sudo add-apt-repository ppa:avsm/ppa
sudo apt-get update
sudo apt-get install coq -y
```

### Step 4: Install Isabelle

```bash
# Download Isabelle 2023
cd /tmp
wget https://isabelle.in.tum.de/dist/Isabelle2023_linux.tar.gz

# Extract
tar -xzf Isabelle2023_linux.tar.gz
sudo mv Isabelle2023 /opt/

# Add to PATH
echo 'export PATH="/opt/Isabelle2023/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

# Verify
isabelle version   # Should show "Isabelle2023"
```

### Step 5: Install Python Dependencies

```bash
cd artifact
pip3 install -r requirements.txt

# Verify
python3 -c "import pandas; import numpy; import matplotlib; print('✅ Python deps OK')"
```

### Step 6: Build the Project

```bash
# Build in release mode (takes 5-10 minutes)
cargo build --release

# Expected output: "Finished release [optimized] target(s)"

# Verify binary
./target/release/otlp-verifier --version
```

### Step 7: Download Evaluation Data

```bash
# Download pre-processed data (42 GB)
./scripts/download_data.sh

# This will download from Zenodo and extract to data/
# Takes 10-30 minutes depending on connection speed

# Verify data integrity
./scripts/verify_data.sh
# Expected: "✅ All 5 datasets verified"
```

### Step 8: Run Quick Validation

```bash
# Compile Coq proofs (takes ~5 minutes)
cd proofs/coq
make
cd ../..

# Compile Isabelle proofs (takes ~10 minutes)
cd proofs/isabelle
isabelle build -D .
cd ../..

# Run quick validation
./scripts/quick_validation.sh

# Expected: "✅ Framework validated successfully"
```

---

## 🧪 Verify Installation

Run the following command to check your installation:

```bash
./scripts/status_check.sh
```

Expected output:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Installation Status Check
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

System Information:
  OS: Linux 5.15.0
  CPU: 8 cores
  RAM: 16 GB
  Disk: 120 GB free

Dependencies:
  ✅ Rust: 1.70.0
  ✅ Cargo: 1.70.0
  ✅ Coq: 8.17.0
  ✅ Isabelle: 2023
  ✅ Python: 3.10.0

Project Build:
  ✅ otlp-verifier: Built successfully
  ✅ Test suite: All 245 tests pass
  ✅ Coq proofs: Compiled (2,500 lines)
  ✅ Isabelle proofs: Compiled (1,800 lines)

Data:
  ✅ E-commerce: 2.3M traces (8.7 GB)
  ✅ Finance: 1.8M traces (6.9 GB)
  ✅ Healthcare: 1.4M traces (5.1 GB)
  ✅ Media: 2.1M traces (7.8 GB)
  ✅ Cloud: 1.7M traces (6.5 GB)
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Total: 9.3M traces (35 GB)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ Installation complete! Ready for evaluation.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Next steps:
  1. Read EXPERIMENTS.md
  2. Run: ./scripts/quick_validation.sh
  3. Run: ./scripts/reproduce_all.sh
```

If you see any ❌ marks, refer to the Troubleshooting section below.

---

## 🐛 Troubleshooting

### Issue: Rust installation fails

```bash
# Clear previous installation
rm -rf ~/.cargo ~/.rustup

# Reinstall
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Select: 1) Proceed with installation (default)
```

### Issue: Coq installation fails

```bash
# Try alternative method
sudo apt-get install coq libcoq-ocaml-dev

# Or use snap
sudo snap install coq-prover --classic
```

### Issue: Build fails with "linker error"

```bash
# Install missing libraries (Ubuntu)
sudo apt-get install build-essential libssl-dev pkg-config

# Retry build
cargo clean
cargo build --release
```

### Issue: Data download times out

```bash
# Use alternative mirror
export DATA_MIRROR="https://example.com/mirror"
./scripts/download_data.sh

# Or download manually from Zenodo
# Link: https://zenodo.org/record/XXXXXXX
```

### Issue: Docker build runs out of memory

```bash
# Increase Docker memory limit
# Docker Desktop → Settings → Resources → Memory → 4 GB

# Or build with reduced parallelism
docker-compose build --parallel 1
```

### Issue: Permission denied errors

```bash
# Fix permissions
sudo chown -R $USER:$USER .
chmod +x scripts/*.sh
```

---

## 🔒 Security Note

This artifact:

- Does NOT require root/admin privileges (except for initial setup)
- Does NOT modify system files outside the project directory
- Does NOT connect to external services (except for data download)
- All network traffic is logged in `logs/network.log`

---

## 📦 Offline Installation

If you need to install without internet access:

1. Download the complete offline package (60 GB):
   - Link: [Available on request from authors]

2. Extract and run:

   ```bash
   tar -xzf otlp-artifact-offline.tar.gz
   cd otlp-artifact-offline
   ./scripts/install_offline.sh
   ```

---

## ⚡ Quick Installation Summary

**With Docker** (5-10 min):

```bash
git clone <repo> && cd artifact
docker-compose build && docker-compose up -d
docker-compose exec verifier ./scripts/quick_validation.sh
```

**Without Docker** (15-30 min):

```bash
git clone <repo> && cd artifact
./scripts/install_deps.sh         # Installs all dependencies
cargo build --release              # Builds project
./scripts/download_data.sh         # Downloads data
./scripts/quick_validation.sh      # Validates setup
```

---

## 📚 Next Steps

After successful installation:

1. ✅ Read `EXPERIMENTS.md` to understand experiment structure
2. ✅ Run `./scripts/quick_validation.sh` for smoke test
3. ✅ Run `./scripts/reproduce_rq1.sh` to reproduce first result
4. ✅ Explore the codebase in `src/`
5. ✅ Try extending the framework (see `docs/EXTENDING.md`)

---

## 💡 Tips for Evaluators

- **Use Docker**: Fastest and most reliable setup
- **SSD Recommended**: Speeds up data processing significantly
- **Parallel Execution**: Use `--parallel 4` for faster experiments
- **Monitor Resources**: Run `htop` to monitor CPU/memory usage
- **Save Time**: Pre-computed results available in `results/` for comparison

---

**Installation Complete! 🎉**-

Ready to reproduce results? → Continue to `EXPERIMENTS.md`

Having issues? → Check `docs/FAQ.md` or contact us
