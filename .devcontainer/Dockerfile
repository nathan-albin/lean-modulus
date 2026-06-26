FROM mcr.microsoft.com/devcontainers/base:trixie

# System dependencies for leanblueprint (pygraphviz needs the graphviz headers
# and a compiler; plasTeX/leanblueprint itself just needs Python + pipx).
RUN apt-get update && apt-get install -y --no-install-recommends \
        python3 \
        python3-pip \
        pipx \
        graphviz \
        libgraphviz-dev \
        pkg-config \
        build-essential \
    && rm -rf /var/lib/apt/lists/*

# Switch to Codespace user
USER vscode
WORKDIR /home/vscode

# Set the SHELL to a login shell to ensure ~/.profile (modified by elan) is sourced
SHELL ["/bin/bash", "-lc"]

# Install Lean and Elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- --default-toolchain stable -y

# Add elan and pipx-installed tools to PATH for the vscode user
ENV PATH="/home/vscode/.elan/bin:/home/vscode/.local/bin:${PATH}"

# Install leanblueprint (builds the web/PDF blueprint and checks that Lean
# declarations named in the blueprint actually exist). --include-deps is
# required so that plastex (a dependency, not the package itself) also gets
# linked onto PATH -- without it, `leanblueprint web`/`checkdecls` fail with
# "plastex: not found".
RUN pipx install leanblueprint --include-deps