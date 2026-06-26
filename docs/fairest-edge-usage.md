# Fairest Edge Usage and Minimum Expected Overlap for Random Spanning Trees

## Generalizing spanning trees to matroids

The paper is written in the language of spanning trees of a multigraph (see the
paragraph preceding Section 1.1, which fixes $G = (V, E)$ as a finite, connected multigraph).
However, the paper's main results are really matroid facts, so the plan is to prove the results in
the matroid setting and then specialize to the spanning tree case.

Mathlib already proves the relevant facts at full matroid generality (e.g.
`Matroid.IsBase.encard_eq_eRank`, in `Mathlib.Combinatorics.Matroid.Rank.ENat`: all bases of a
matroid have the same cardinality), but it has no graphic/cycle matroid construction connecting
"spanning trees of a graph" to "bases of a matroid." That connection will be built here, so that
the matroid facts can be extracted as spanning tree facts.

- `LeanModulus/Common/Multigraph.lean` — the multigraph structure itself, plus the pure
  graph-theoretic notions (`IsForest`, `IsSpanningTree`) the matroid is built from.
- `LeanModulus/Common/GraphicMatroid.lean` (planned) — constructs the `Matroid` instance
  whose independent sets are forests, via `IndepMatroid.ofFinite`, and proves the bridge
  theorem connecting matroid bases back to spanning trees.

This means that much of the underlying scaffolding can live in `Common/` rather than under
`Papers/FairestEdgeUsage/`.  If it works as expected, it serves as a plausible
candidate to upstream to Mathlib later, since no graphic matroid exists there yet.

Blueprint entries for this paper are written in the paper's own language
(spanning trees, not matroids). In this sense, the matroid layer is a proof
strategy, not paper content. The paper versions of proofs are given as
corollaries derived from the matroid theorem, and these are what are linked in
the blueprint.
