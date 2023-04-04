# syntax=docker/dockerfile:1

FROM python:3.11-bullseye

# Install clang
COPY <<EOF /etc/apt/sources.list.d/llvm.list
deb https://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-15 main
deb-src https://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-15 main
EOF
RUN wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -

RUN apt-get update && apt-get install -y \
    clang-15 \
    lld-15 \
    && rm -rf /var/lib/apt/lists/*
# Bring unsuffixed 'clang' etc. into the PATH. (Otherwise only 'clang-15' is available.)
ENV PATH="/usr/lib/llvm-15/bin:$PATH"

# Install elan
RUN mkdir -p /tmp/elan && \
    wget -O /tmp/elan/elan.tar.gz https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz && \
    echo 'dad23772f43f2727f28dedbdc3ce8d646a9373692ec4d7e7e3ea0bb683339c3c /tmp/elan/elan.tar.gz' | sha256sum -c && \
    cd /tmp/elan && \
    tar -xf elan.tar.gz && \
    chmod +x elan-init && \
    ELAN_HOME=/usr/local ./elan-init -y --no-modify-path --default-toolchain none && \
    rm -rf /tmp/elan

# Install Python packages
RUN --mount=type=bind,target=/mnt \
    pip install -r /mnt/graphs/requirements.txt
