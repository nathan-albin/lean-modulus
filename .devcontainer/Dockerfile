FROM mcr.microsoft.com/devcontainers/base:trixie

# Switch to Codespace user
USER vscode
WORKDIR /home/vscode

# Set the SHELL to a login shell to ensure ~/.profile (modified by elan) is sourced
SHELL ["/bin/bash", "-lc"]

# Install Lean and Elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- --default-toolchain stable -y

# Add to PATH for the vscode user
ENV PATH="/home/vscode/.elan/bin:${PATH}"