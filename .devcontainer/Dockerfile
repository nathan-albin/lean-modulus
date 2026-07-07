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
# uses one.
#
# texlive-xetex + texlive-latex-extra + texlive-fonts-recommended + latexmk
# give `leanblueprint pdf` a real xelatex (the engine blueprint/src/print.tex
# requires) instead of just plasTeX's lenient web build, so a typo'd macro
# (undefined control sequence, missing \label, etc.) that plasTeX silently
# swallows still gets caught locally instead of only surfacing 20 minutes
# into CI's "Compile blueprint" job.
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
        texlive-xetex \
        texlive-latex-extra \
        texlive-fonts-recommended \
        latexmk \
    && rm -rf /var/lib/apt/lists/*

# Ruby for the home_page/ Jekyll site (the GitHub Pages homepage), so it can be
# previewed locally instead of waiting on CI. This is the *exact* prebuilt
# Ruby that CI's `ruby/setup-ruby` step downloads -- not apt's `ruby-full`,
# which on Debian trixie is Ruby 3.3. That mismatch isn't cosmetic: resolving
# home_page/Gemfile.lock on Ruby 3.3 silently picks Bundler/gem versions
# (Bundler itself, activesupport, connection_pool, nokogiri, ...) whose
# *minimum* required Ruby is 3.2 -- newer than CI's pinned Ruby 3.1 -- so a
# lockfile that installs fine locally then fails in CI with "requires ruby
# version >= 3.2.0, which is incompatible with the current version, 3.1.7".
# Installed at the same path CI uses (/opt/hostedtoolcache/Ruby/3.1.7/x64)
# because the prebuilt gem/bundle wrapper scripts hardcode that path in their
# shebang line and won't run from anywhere else. The -dev headers are a
# fallback for native gems (e.g. nokogiri) on platforms with no precompiled
# binary, where bundler falls back to compiling from source. libyaml-dev is
# different: it's not a gem fallback but a runtime dependency of the prebuilt
# Ruby's own bundled psych (YAML) extension -- without it, `require 'psych'`
# fails with a libyaml-0.so.2 LoadError before bundler can even parse the
# Gemfile.lock, so trixie's base image (which lacks libyaml) breaks every
# `bundle` invocation.
RUN apt-get update && apt-get install -y --no-install-recommends \
        zlib1g-dev \
        libxml2-dev \
        libxslt1-dev \
        libssl-dev \
        libyaml-dev \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /opt/hostedtoolcache/Ruby/3.1.7 \
    && curl -sL https://github.com/ruby/ruby-builder/releases/download/toolcache/ruby-3.1.7-ubuntu-24.04.tar.gz \
       | tar -xz -C /opt/hostedtoolcache/Ruby/3.1.7 \
    && chown -R vscode:vscode /opt/hostedtoolcache
ENV PATH="/opt/hostedtoolcache/Ruby/3.1.7/x64/bin:${PATH}"
ENV LD_LIBRARY_PATH="/opt/hostedtoolcache/Ruby/3.1.7/x64/lib"

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

# Redirect gem installs to a directory owned by vscode (the prebuilt Ruby's
# own gem dir is root-owned). No separate Bundler install needed: the
# prebuilt Ruby above already ships the same Bundler version pinned in
# home_page/Gemfile.lock's BUNDLED WITH.
ENV GEM_HOME="/home/vscode/gems"
ENV PATH="/home/vscode/gems/bin:${PATH}"