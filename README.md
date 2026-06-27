# lean-modulus

Formalizations, in [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/),
of results from my research on graphs, networks, and the modulus of families of objects.

This is a working project. results are added incrementally, and the
[blueprint](#blueprint) tracks what's genuinely proved versus proved with `sorry`.

## Papers

| Paper | Status | Lean source |
|---|---|---|
| [Fairest Edge Usage and Minimum Expected Overlap for Random Spanning Trees](https://doi.org/10.1016/j.disc.2020.112282) (Albin, Clemens, Hoare, Poggi-Corradini, Sit, Tymochko, 2021) | 🚧 just started | [`LeanModulus/Papers/FairestEdgeUsage`](LeanModulus/Papers/FairestEdgeUsage) |

More papers will be added here as they're formalized.

## Repository layout

```
LeanModulus/
  Papers/
    FairestEdgeUsage/   -- one folder per paper, files roughly track paper section numbers
  Common/                -- shared definitions/lemmas reused across papers (multigraphs, etc.)
blueprint/                -- LaTeX source mapping paper statements to Lean declarations
docs/                     -- design notes: encoding choices, deviations from the paper, open TODOs
```

Each paper's Lean files cite the definition/theorem numbers they formalize, so you can read the
Lean code side-by-side with the paper. See [`docs/`](docs) for translation notes — places where the
Lean formalization had to make a choice the paper didn't have to (e.g. how multigraphs are encoded).

## Building

This project uses [Lake](https://github.com/leanprover/lake) and depends on
[Mathlib](https://github.com/leanprover-community/mathlib4). With [elan](https://github.com/leanprover/elan)
installed:

```bash
lake exe cache get   # fetch prebuilt Mathlib .olean files (much faster than building from source)
lake build
```

A [devcontainer](.devcontainer) is included and does this automatically. Open the repo in VS Code
and choose "Reopen in Container," or use GitHub Codespaces.

## Blueprint

This project uses [leanblueprint](https://github.com/PatrickMassot/leanblueprint) to maintain a
human-readable correspondence between the paper's statements and the Lean formalization, with a
dependency graph and a live count of completed vs. `sorry`-proved results. It is
browsable at [https://nathan-albin.com/lean-modulus/](https://nathan-albin.com/lean-modulus/).

## Why formalize this

I'm moving toward including Lean theorem proving in my courses and my research
workflow. Formalizing results from my recent papers is a way for me to practice
writing Lean proofs for real mathematical content rather than textbook
exercises. It also gives me a chance to explore the various AI tools for Lean,
and to see how well they can help with real research-level mathematics.

## License

[MIT](LICENSE)
