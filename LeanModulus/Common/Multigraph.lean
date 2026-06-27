-- Shared graph-theoretic infrastructure reused across papers (e.g. multigraphs,
-- usage matrices) that isn't already in Mathlib. Mathlib's `SimpleGraph` doesn't
-- allow parallel edges or loops, so multigraphs need their own structure.
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import LeanModulus.Common.SimpleGraph

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
      have main : ∀ (F : Set E), F.Finite → (G.IsForest F) → ((G.toSimpleGraph F).support ⊆ S)
        → F.ncard + G.numComponents F S = S.ncard := by
        intro F hFfin
        induction F, hFfin using Set.Finite.induction_on with
        | empty =>
          intro hF hFS
          simp only [Set.ncard_empty, zero_add]
          rw [Multigraph.numComponents]
          rw [Multigraph.toSimpleGraph, Set.image_empty, SimpleGraph.fromEdgeSet_empty]
          have hinj : Function.Injective (⊥ : SimpleGraph V).connectedComponentMk := by
            rw [Function.Injective]
            intro u v h
            rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_bot] at h
            exact h
          exact Set.ncard_image_of_injective S hinj
        | insert ha hs ih =>
          rename_i a s
          intro hF hFS
          have hFs : G.IsForest s := IsForest.subset G hF (Set.subset_insert a s)
          have hle : (G.toSimpleGraph s) ≤ (G.toSimpleGraph (insert a s)) := by
            rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph]
            apply SimpleGraph.fromEdgeSet_mono
            apply Set.image_mono
            exact Set.subset_insert a s
          have hssub : (G.toSimpleGraph s).support ⊆ (G.toSimpleGraph (insert a s)).support := by
            rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph]
            apply SimpleGraph.support_mono
            apply SimpleGraph.fromEdgeSet_mono
            apply Set.image_mono
            exact Set.subset_insert a s
          have hssup : (G.toSimpleGraph s).support ⊆ S := by
            apply Set.Subset.trans hssub
            exact hFS
          have hih := ih hFs hssup
          have hadd : (G.numComponents s S) = G.numComponents (insert a s) S + 1 := by
            obtain ⟨u, v, huv⟩ := Sym2.exists.mp ⟨G.endpoints a, rfl⟩
            have hne : u ≠ v := by
              have hloop : ¬ (G.endpoints a).IsDiag := by
                obtain ⟨hloop, _, _⟩ := hF
                exact hloop a (Set.mem_insert a s)
              rw [huv] at hloop
              exact Ne.intro hloop
            have hadj : (G.toSimpleGraph (insert a s)).Adj u v := by
              rw [Multigraph.toSimpleGraph]
              rw [SimpleGraph.fromEdgeSet_adj]
              refine ⟨?_, hne⟩
              rw [← huv]
              exact Set.mem_image_of_mem G.endpoints (Set.mem_insert a s)
            have huS : u ∈ S := hFS ⟨v,hadj⟩
            have hvS : v ∈ S := hFS ⟨u,hadj.symm⟩
            have hcomp : (G.toSimpleGraph s).connectedComponentMk u ≠ (G.toSimpleGraph s).connectedComponentMk v := by
              have hbridge : (G.toSimpleGraph (insert a s)).IsBridge s(u, v) :=
                SimpleGraph.isAcyclic_iff_forall_isBridge.mp hF.2.2 ((SimpleGraph.mem_edgeSet _).mpr hadj)
              rw [SimpleGraph.isBridge_iff] at hbridge
              have hdel : (G.toSimpleGraph (insert a s)).deleteEdges {s(u, v)} = G.toSimpleGraph s := by
                rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph]
                rw [SimpleGraph.deleteEdges_fromEdgeSet]
                congr
                rw [← huv]
                rw [Set.image_insert_eq]
                have hnotmem : G.endpoints a ∉ G.endpoints '' s := by
                  rintro ⟨b, hbs, hba⟩
                  have hba' : b = a := hF.2.1 (Set.mem_insert_of_mem a hbs) (Set.mem_insert a s) hba
                  rw [hba'] at hbs
                  contradiction
                exact Set.insert_sdiff_self_of_notMem hnotmem
              rw [hdel] at hbridge
              rw [Ne, SimpleGraph.ConnectedComponent.eq]
              exact hbridge
            have hresp : ∀ v w (p : (G.toSimpleGraph s).Walk v w), p.IsPath →
                (G.toSimpleGraph (insert a s)).connectedComponentMk v =
                  (G.toSimpleGraph (insert a s)).connectedComponentMk w := by
              intro v w p _
              exact SimpleGraph.ConnectedComponent.sound (p.reachable.mono' hle)
            set ψ : (G.toSimpleGraph s).ConnectedComponent →
                (G.toSimpleGraph (insert a s)).ConnectedComponent :=
              SimpleGraph.ConnectedComponent.lift
                (G.toSimpleGraph (insert a s)).connectedComponentMk hresp
            have hψ : ∀ x, ψ ((G.toSimpleGraph s).connectedComponentMk x) =
                (G.toSimpleGraph (insert a s)).connectedComponentMk x := by
              intro x
              simp [ψ, SimpleGraph.ConnectedComponent.lift_mk]
            sorry
          rw [Set.ncard_insert_of_notMem ha hs]
          omega
      exact main F hFfin hF hFS

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
