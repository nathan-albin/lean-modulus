# lean-modulus

This repo contains [Lean
4](https://lean-lang.org/)/[Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of some of my research on graphs, networks, and the modulus of
families of objects. A brief introduction to modulus and some associated code
can be found in my
[discrete-modulus](https://github.com/nathan-albin/discrete-modulus) repo.

You can also find a more complete coverage of the theory in my book with Pietro
Poggi-Corradini:

> Albin, N., & Poggi-Corradini, P. (2025). *Mathematics of Networks: Modulus
> Theory and Convex Optimization (1st ed.)*. Chapman and Hall/CRC.
> [https://doi.org/10.1201/9781003024866](https://doi.org/10.1201/9781003024866)

This is a working project. Results and the upcoming plan are tracked in the
[blueprint](#blueprint), tracks what's defined, stated, and proved.

## Papers

| Paper | Status | Lean source |
|---|---|---|
| [Fairest Edge Usage and Minimum Expected Overlap for Random Spanning Trees](https://doi.org/10.1016/j.disc.2020.112282) (Albin, Clemens, Hoare, Poggi-Corradini, Sit, Tymochko, 2021) | 🚧 just started | [`LeanModulus/Papers/FairestEdgeUsage`](LeanModulus/Papers/FairestEdgeUsage) |

More papers will be added here as they're formalized.

## Shared infrastructure

Building toward the goals of the papers, the following shared infrastructure is
formalized in the `Common` folder:

- **Multigraphs** — forests, spanning trees, connected components
  ([`Multigraph.lean`](LeanModulus/Common/Multigraph.lean))
- **Graphic matroid** — forests as the independent sets of the cycle matroid
  ([`GraphicMatroid.lean`](LeanModulus/Common/GraphicMatroid.lean))
- **Modulus / families of objects** — densities, admissible sets, Fulkerson duals
  ([`FamilyOfObjects.lean`](LeanModulus/Common/FamilyOfObjects.lean),
  [`ToReal.lean`](LeanModulus/Common/ToReal.lean))
- **Convex analysis for duality** — extreme points, Krein-Milman-adjacent lemmas
  ([`ExtremePoints.lean`](LeanModulus/Common/ExtremePoints.lean))
- **`SimpleGraph` connectivity facts** ([`SimpleGraph.lean`](LeanModulus/Common/SimpleGraph.lean))

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
