# Common (shared modulus infrastructure)

Notes on deviations between the published papers' setups and the `Common`
chapter of the blueprint/Lean formalization, which is shared across papers.

## Family of objects: dropping the index set

Most of the modulus papers define a family of objects as a pair $(\Gamma,
\mathcal N)$: $\Gamma$ is a set of ``objects'' (e.g. spanning trees, feasible
partitions), and $\mathcal N \in \mathbb R_{\ge0}^{\Gamma\times E}$ a usage
matrix, with each $\gamma\in\Gamma$ then identified with its row $\mathcal
N(\gamma,\cdot)$. This redundancy is replaced in the blueprint by defining a
family of objects as a single set $\Gamma \subseteq \mathbb R_{\ge0}^E$ of usage
vectors. The rows of $\Gamma$ *are* the objects, and there is no need to have a
separate matrix $\mathcal N$. This also makes the transition to the Fulkerson
dual family $\widehat\Gamma$ much more natural.

The one thing this loses is the ability to give two distinct objects the same
usage vector. Since objects are not vectors, they inherit vector equivalence.
This doesn't seem to be a loss based on current papers, but if a future paper needs to
distinguish objects with identical usage vectors, we'll need to address this.

## Modulus duality: general $p$ deferred in favor of $p = 2$

`thm:modulus-extremal-unique` and `thm:modulus-fulkerson-duality` are stated for
general $1 < p < \infty$ but marked `\notready` in the blueprint. Mathlib
currently has no Fenchel-conjugate or convex-duality infrastructure to build the
general proof on, and the FEU paper currently under development only needs the
$p=2$ case. Rather than build general Fenchel-Rockafellar or Lagrangian duality,
Chapter~\ref{chap:feu} proves $p = 2$ duality directly using the connection
between the two-norm and the inner product, which avoids the conjugate-function
machinery and exploits the fact that usage vectors in $\Gamma$ are nonnegative.

If a future paper needs general $p$, these deferred theorems are the natural
place to pick that work back up. One possible direction for this is to follow up
on the stalled [mathlib4 PR #6058](https://github.com/leanprover-community/mathlib4/pull/6058).

