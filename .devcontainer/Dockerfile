FROM mcr.microsoft.com/devcontainers/base:trixie

# System dependencies for leanblueprint (pygraphviz needs the graphviz headers
# and a compiler; plasTeX/leanblueprint itself just needs Python + pipx).
# texlive-binaries + texlive-base provide `kpsewhich`, which plasTeX's `\input`
# shells out to in order to resolve every \input{...} (including our own
# macros/common.tex and macros/web.tex). Without it, `\input` silently fails
# ("File not found", swallowed as a warning, not an error) and every
# \newtheorem-defined environment (theorem, definition, ...) falls back to an
# unrecognized-macro stub -- which crashes `leanblueprint web`/`checkdecls`
# with "TypeError: unhashable type: ..." as soon as the blueprint actually
# uses one. This does NOT yet cover `leanblueprint pdf` (needs xelatex, i.e.
# a much larger texlive install) -- only the web build / checkdecls path.
RUN apt-get update && apt-get install -y --no-install-recommends \
        python3 \
        python3-pip \
        pipx \
        graphviz \
        libgraphviz-dev \
        pkg-config \
        build-essential \
        texlive-binaries \
        texlive-base \
    && rm -rf /var/lib/apt/lists/*

# Ruby for the home_page/ Jekyll site (the GitHub Pages homepage), so it can be
# previewed locally instead of waiting on CI. ruby-full pulls in a usable
# gem/irb toolchain; the -dev headers cover native gems (e.g. nokogiri) on
# platforms where github-pages's pinned version has no prebuilt binary.
RUN apt-get update && apt-get install -y --no-install-recommends \
        ruby-full \
        zlib1g-dev \
        libxml2-dev \
        libxslt1-dev \
        libssl-dev \
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

# Redirect gem installs to a directory owned by vscode (the apt-installed Ruby's
# default GEM_HOME is root-owned) and install Bundler, which home_page/Gemfile.lock
# needs to pin and install the exact `github-pages` gem version GitHub Pages builds with.
ENV GEM_HOME="/home/vscode/gems"
ENV PATH="/home/vscode/gems/bin:${PATH}"
RUN gem install bundler