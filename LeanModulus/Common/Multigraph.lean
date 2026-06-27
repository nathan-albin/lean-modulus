-- Shared graph-theoretic infrastructure reused across papers (e.g. multigraphs,
-- usage matrices) that isn't already in Mathlib. Mathlib's `SimpleGraph` doesn't
-- allow parallel edges or loops, so multigraphs need their own structure.
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

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

/-- The number of connected components of the simple graph on edge set `F` that meet
the vertex set `S`. Counted as the number of distinct `ConnectedComponent`s hit by `S`,
so a vertex of `S` untouched by any edge of `F` contributes its own singleton
component. -/
noncomputable def numComponents (F : Set E) (S : Set V) : ℕ :=
  ((G.toSimpleGraph F).connectedComponentMk '' S).ncard

/-- A nonempty, finite vertex set always splits into at least one component. -/
theorem numComponents_pos {F : Set E} {S : Set V} (hS : S.Finite) (hSne : S.Nonempty) :
    0 < G.numComponents F S :=
  (Set.ncard_pos (hS.image _)).2 (hSne.image _)

/-- Rank–nullity for forests: a finite forest's edge count equals the number of
vertices it touches (or any finite vertex set `S` containing them) minus the number of
components those vertices fall into. This is the key counting fact behind the
augmentation property of the cycle matroid (`GraphicMatroid`): it lets us compare the
edge counts of two forests component-by-component. -/
theorem IsForest.ncard_add_numComponents {F : Set E} (hF : G.IsForest F) (hFfin : F.Finite)
    {S : Set V} (hS : S.Finite) (hFS : (G.toSimpleGraph F).support ⊆ S) :
    F.ncard + G.numComponents F S = S.ncard := by
  sorry

/-- A finite forest restricted to a finite vertex set `S` has strictly fewer edges than
`S` has vertices, as long as `S` is nonempty. The forest need not touch all of `S`, nor
be connected; this is the inequality used for the "smaller" side of the augmentation
argument, while `IsForest.ncard_add_numComponents` gives the exact count needed for the
"larger" (already-spanning) side. -/
theorem IsForest.ncard_lt_of_nonempty {F : Set E} (hF : G.IsForest F) (hFfin : F.Finite)
    {S : Set V} (hS : S.Finite) (hSne : S.Nonempty) (hFS : (G.toSimpleGraph F).support ⊆ S) :
    F.ncard < S.ncard := by
  have h := IsForest.ncard_add_numComponents G hF hFfin hS hFS
  have hpos := G.numComponents_pos (F := F) hS hSne
  omega

end Multigraph
