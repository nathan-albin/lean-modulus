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

## The Fulkerson dual of the bases is (almost) not needed

The paper states (eq. (1.13), citing Chopra [6]) that the Fulkerson dual family
$\hat\Gamma_G$ of spanning trees is exactly the set of (weighted)
feasible-partition vectors $\tfrac{1}{k_P-1}\mathbb 1_{E_P}$. In matroid
language this is: the extreme points of $\mathrm{Adm}(\mathcal B(M))$ are
exactly $\tfrac{1}{r(E)-r(E-X)}\mathbb 1_X$ for $X$ ranging over complements of
flats satisfying a connectivity condition. This is a real theorem; the important
part is showing that the feasible partitions exhaust the extreme points. But,
unless I've missed something, the way the paper actually *uses* feasible
partitions (Lemma 4.7 through Theorem 4.10, and the later reuses in Section 5.4
and Theorem 6.3) shows that only one direction is really needed:

> **The elementary blocking inequality**: every spanning tree (basis) uses at
> least $k_P - 1$ edges of $E_P$ (Lemma 4.7's computation, eq. (4.9)). This is a
> direct submodularity fact about the matroid rank function. For this, we don't
> need Fulkerson duality, extreme points, or a full characterization of
> $\hat\Gamma_G$.

The *full* characterization (eq. 1.13) is invoked exactly once in the whole
paper: inside the converse direction of Theorem 4.11's proof (page 14, "Recall
from (1.13)..."), to show $\eta_{\mathrm{hom}} \in \mathrm{Adm}(\hat\Gamma_G)$.
Theorem 4.11 itself is not cited again anywhere later. Later, Theorem 6.3, via
eq. (4.12) only needs Theorem 4.11's *forward* direction, whose proof again only
needs the elementary inequality, not (1.13).

**Consequence for the Lean plan:** we won't build the full extreme-point
characterization of $\hat\Gamma_M$ (Fulkerson dual of matroid bases) as a
prerequisite for this paper. Instead, we'll provethe elementary blocking
inequality directly (a self-contained submodularity argument), which unlocks
Lemmas 4.7–4.10 and the Section 6.1 regular-graph results. Defer the full
characterization unless Theorem 4.11's converse specifically becomes a
formalization target.

**If the full characterization is needed later:** Truong & Poggi-Corradini,
"Modulus for bases of matroids" (arXiv:2404.05650, Discrete Math. 348(5), 2025)
prove the general matroid statement as their **Theorem 6.2** ($\hat{\mathcal B}
= \Theta$). Their Lemmas 6.3, 6.8, 6.11 that can be ported directly to Lean.
