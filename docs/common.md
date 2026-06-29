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
