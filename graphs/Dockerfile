# syntax=docker/dockerfile:1

# This Dockerfile creates an environment that can generate the graphs in our paper.
# Steps:
#
#  1. Install Docker (make sure the "Buildx" plugin is installed as well)
#     https://docs.docker.com/build/architecture/#buildx
#     https://docs.docker.com/engine/reference/commandline/buildx/
#
#  2. Build Docker image. From the etch4/ directory, run:
#     docker build -t etch-bench -f graphs/Dockerfile .
#
#  3. Run benchmarks. Run:
#     docker run --rm -v '.:/mnt' -e HOME=/mnt -w /mnt -u $(id -u):$(id -g) etch-bench bash graphs/run.sh
#
#  4. Generate graphs. Run:
#     docker run --rm -v '.:/mnt' -e HOME=/mnt -w /mnt -u $(id -u):$(id -g) etch-bench python3 graphs/graph.py

FROM python:3.11-bullseye

# Install clang and other apt dependencies
COPY <<EOF /etc/apt/sources.list.d/llvm.list
deb https://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-15 main
deb-src https://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-15 main
EOF
RUN wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -

RUN apt-get update && apt-get install -y \
    clang-15 \
    lld-15 \
    bc \
    && rm -rf /var/lib/apt/lists/*
# Bring unsuffixed 'clang' etc. into the PATH. (Otherwise only 'clang-15' is available.)
ENV PATH="/usr/lib/llvm-15/bin:$PATH"

# Install elan
ENV ELAN_HOME=/usr/local
RUN mkdir -p /tmp/elan && \
    wget -O /tmp/elan/elan.tar.gz https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz && \
    echo 'dad23772f43f2727f28dedbdc3ce8d646a9373692ec4d7e7e3ea0bb683339c3c /tmp/elan/elan.tar.gz' | sha256sum -c && \
    cd /tmp/elan && \
    tar -xf elan.tar.gz && \
    chmod +x elan-init && \
    ./elan-init -y --no-modify-path --default-toolchain none && \
    rm -rf /tmp/elan

# Install correct Lean version
RUN --mount=type=bind,target=/mnt \
    cd /mnt && lean --version

# Install Python packages
RUN --mount=type=bind,target=/mnt \
    pip install -r /mnt/graphs/requirements.txt
