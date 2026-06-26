-- Shared graph-theoretic infrastructure reused across papers (e.g. multigraphs,
-- usage matrices) that isn't already in Mathlib. Mathlib's `SimpleGraph` doesn't
-- allow parallel edges or loops, so multigraphs need their own structure.
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-- A multigraph on vertex type `V` with edge type `E`: edges are first-class
objects (so parallel edges are distinct elements of `E`), each mapped to its
unordered pair of endpoints. A loop is an edge `e` with `endpoints e` a
diagonal element of `Sym2 V`. -/
structure Multigraph (V E : Type*) where
  endpoints : E → Sym2 V

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The simple graph obtained from a set of edges by forgetting multiplicities,
loops, and edge identities, remembering only which pairs of vertices are
joined by some edge in `F`. -/
def toSimpleGraph (F : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.endpoints '' F)

/-- A set of edges `F` is a forest if it has no loops, no two edges of `F`
share the same endpoints (parallel edges would form a 2-cycle), and the
underlying simple graph on `F` is acyclic. -/
def IsForest (F : Set E) : Prop :=
  (∀ e ∈ F, ¬ (G.endpoints e).IsDiag) ∧
  Set.InjOn G.endpoints F ∧
  (G.toSimpleGraph F).IsAcyclic

/-- A set of edges `T` is a spanning tree if it is a forest whose underlying
simple graph is connected, i.e. it touches and joins every vertex of `V`. -/
def IsSpanningTree (T : Set E) : Prop :=
  G.IsForest T ∧ (G.toSimpleGraph T).Connected

theorem IsForest.subset {F F' : Set E} (hF : G.IsForest F) (h : F' ⊆ F) :
    G.IsForest F' := by
  obtain ⟨hloop, hinj, hacyc⟩ := hF
  refine ⟨fun e he => hloop e (h he), hinj.mono h, ?_⟩
  exact hacyc.anti (SimpleGraph.fromEdgeSet_mono (Set.image_mono h))

end Multigraph
