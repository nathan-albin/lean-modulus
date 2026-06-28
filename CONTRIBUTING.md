# Contributing

This is primarily a personal formalization project, but contributions are welcome,
especially on open `sorry`s and TODOs tracked as
[issues](https://github.com/nathan-albin/lean-modulus/issues).

## Setup

Open the repo in the included [devcontainer](.devcontainer) (VS Code "Reopen in Container," or
GitHub Codespaces) — it installs Lean/elan, fetches the Mathlib cache, and installs
[leanblueprint](https://github.com/PatrickMassot/leanblueprint).

## Workflow

1. Pick an issue, ideally one labeled `good first issue`.
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
