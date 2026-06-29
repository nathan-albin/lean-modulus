# Contributing

This is primarily a personal formalization project, but contributions are welcome,
especially on open `sorry`s and TODOs tracked as
[issues](https://github.com/nathan-albin/lean-modulus/issues).

## Setup

Open the repo in the included [devcontainer](.devcontainer) (VS Code "Reopen in Container," or
GitHub Codespaces) — it installs Lean/elan, fetches the Mathlib cache, and installs
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) and a Ruby/Jekyll toolchain for
previewing the [blueprint](#previewing-the-blueprint-and-homepage) and the homepage.

## Workflow

1. Pick an issue, ideally one labeled `good first issue`. If none fit, open the
   [dependency graph](https://nathan-albin.com/lean-modulus/blueprint/dep_graph_document.html) (or
   build it locally, see [below](#previewing-the-blueprint-and-homepage)) and look for a node with
   a blue border and fill: that means every result it `\uses` already has `\lean` + `\leanok`, so
   it's unblocked and ready to formalize next. A plain/uncolored node means something it depends on
   isn't formalized yet — pick one of those dependencies instead.
2. Check the [blueprint](blueprint) for the statement you're formalizing and how it depends on
   other results.
3. Match the paper's definition/theorem numbering in docstrings (see existing files under
   `LeanModulus/Papers/` for the convention).
4. Open a PR. CI runs `lake build` and rebuilds the blueprint.

If you've added a new Lean file, make sure it is included by `LeanModulus.lean`. The following bash command can help check for missing imports. An empty result means all files are included. Run it from the repo root.
```bash
comm -3 \
  <(find LeanModulus -name "*.lean" | sed 's#^LeanModulus/##; s#\.lean$##; s#/#.#g; s/^/LeanModulus./' | sort) \
  <(grep -oP '^import \S+' LeanModulus.lean | sed 's/^import //' | sort)
```

## Previewing the blueprint and homepage

Both are normally only built by CI, but you can check changes locally before pushing.

**Blueprint** (after editing anything under `blueprint/src/`):
```bash
leanblueprint web      # regenerates blueprint/web/ from the .tex sources
leanblueprint serve    # serves it at http://localhost:8000
```
`leanblueprint web` goes through plasTeX, not a real TeX engine, so it tolerates LaTeX errors (e.g.
a typo'd macro) that will still break CI, which also compiles a PDF with `latexmk`/`xelatex`. Run
that too before pushing — the devcontainer installs the same engine CI uses:
```bash
leanblueprint pdf      # compiles blueprint/print/print.pdf with xelatex
```

**Homepage** (`home_page/`, the Jekyll site deployed to the project's GitHub Pages URL). Run from
the repo root:
```bash
(cd home_page && bundle exec jekyll serve)   # serves it at http://localhost:4000
```
The homepage embeds the dependency graph, which only resolves locally if a built copy of the
blueprint exists under `home_page/blueprint/` (CI assembles this automatically when deploying; a
symlink won't work, since Jekyll skips symlinked directories). To preview that part too, also run
from the repo root, before starting `jekyll serve`:
```bash
leanblueprint web
cp -r blueprint/web home_page/blueprint
```
