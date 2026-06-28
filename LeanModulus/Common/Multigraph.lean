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

/-- If `F` is a finite set of edges, then the support of the simple graph on `F` is finite. -/
theorem toSimpleGraph_support_finite {F : Set E} (hF : F.Finite) :
    (G.toSimpleGraph F).support.Finite := by
  have hfin : (⋃ z ∈ G.endpoints '' F, {x | x ∈ z}).Finite := by
    apply Set.Finite.biUnion (hF.image G.endpoints)
    intro z _
    induction z using Sym2.ind with
    | _ a b =>
      exact Set.Finite.subset (Set.finite_insert.mpr (Set.finite_singleton b))
        (fun x hx => Sym2.mem_iff.mp hx)
  apply hfin.subset
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hadj⟩ := hv
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨hmem, _⟩ := hadj
  exact Set.mem_biUnion hmem (Sym2.mem_mk_left v w)

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

/-- If `F` is a forest and `F'` is a subset of `F`, then `F'` is also a forest. -/
theorem IsForest.subset {F F' : Set E} (hF : G.IsForest F) (h : F' ⊆ F) :
    G.IsForest F' := by
  obtain ⟨hloop, hinj, hacyc⟩ := hF
  refine ⟨fun e he => hloop e (h he), hinj.mono h, ?_⟩
  exact hacyc.anti (SimpleGraph.fromEdgeSet_mono (Set.image_mono h))

/-- If `F` is a forest and `e={u,v}` is an edge not in `F` with the property
that `u` and `v` are not reachable in the graph induced by `F`, then `F ∪ {e}` is also a forest. -/
theorem IsForest.insert_of_not_reachable {F : Set E} (hF : G.IsForest F) {e : E} {u v : V}
    (heF : e ∉ F) (huv : G.endpoints e = s(u, v)) (hne : u ≠ v)
    (hreach : ¬ (G.toSimpleGraph F).Reachable u v) :
    G.IsForest (insert e F) := by
    obtain ⟨hloop, hinj, hacyc⟩ := hF
    have hloop' : ∀ e' ∈ insert e F, ¬ (G.endpoints e').IsDiag := by
      intro e' he'
      cases he' with
      | inl h =>
        rw [h, huv]
        exact Not.imp hne fun a => a
      | inr h =>
        exact Not.imp (hloop e' h) fun a => a
    have hinj' : Set.InjOn G.endpoints (insert e F) := by
      apply (Set.injOn_insert heF).mpr
      refine ⟨hinj, ?_⟩
      intro he'
      obtain ⟨b, hbF, hbe⟩ := he'
      rw [huv] at hbe
      have hadj : (G.toSimpleGraph F).Adj u v := by
        rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, hne⟩
        rw [← hbe]
        exact Set.mem_image_of_mem G.endpoints hbF
      exact hreach hadj.reachable
    have hacyc' : (G.toSimpleGraph (insert e F)).IsAcyclic := by
      have hsup : G.toSimpleGraph (insert e F) = G.toSimpleGraph F ⊔ SimpleGraph.edge u v := by
        rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph, Set.image_insert_eq]
        rw [huv, Set.insert_eq, SimpleGraph.fromEdgeSet_union]
        exact sup_comm (SimpleGraph.fromEdgeSet {s(u, v)}) (SimpleGraph.fromEdgeSet (G.endpoints '' F))
      rw [hsup]
      exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hreach hacyc
    refine ⟨hloop', hinj', hacyc'⟩

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
            classical
            set ρ : (G.toSimpleGraph s).ConnectedComponent → (G.toSimpleGraph s).ConnectedComponent :=
              fun c => if c = (G.toSimpleGraph s).connectedComponentMk v then
                (G.toSimpleGraph s).connectedComponentMk u else c with hρ_def
            have hR : ∀ x y, (G.toSimpleGraph (insert a s)).Reachable x y →
                ρ ((G.toSimpleGraph s).connectedComponentMk x) =
                  ρ ((G.toSimpleGraph s).connectedComponentMk y) := by
              apply SimpleGraph.reachable_le_of_adj_le
              · intro x; rfl
              · intro x y z hxy hyz; exact hxy.trans hyz
              · intro x y hxy
                rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hxy
                obtain ⟨hxy1, hxyne⟩ := hxy
                rw [Set.image_insert_eq, Set.mem_insert_iff] at hxy1
                rcases hxy1 with h | h
                · rw [huv, Sym2.eq_iff] at h
                  rcases h with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
                  · subst hxu; subst hyv
                    simp [ρ]
                  · subst hxv; subst hyu
                    simp [ρ]
                · have hadjxy : (G.toSimpleGraph s).Adj x y := by
                    rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
                    exact ⟨h, hxyne⟩
                  exact congrArg ρ (SimpleGraph.ConnectedComponent.sound hadjxy.reachable)
            have hψuv : ψ ((G.toSimpleGraph s).connectedComponentMk u) =
                ψ ((G.toSimpleGraph s).connectedComponentMk v) := by
              rw [hψ, hψ]
              exact SimpleGraph.ConnectedComponent.sound hadj.reachable
            have hUmem : (G.toSimpleGraph s).connectedComponentMk u ∈
                (G.toSimpleGraph s).connectedComponentMk '' S := Set.mem_image_of_mem _ huS
            have hVmem : (G.toSimpleGraph s).connectedComponentMk v ∈
                (G.toSimpleGraph s).connectedComponentMk '' S := Set.mem_image_of_mem _ hvS
            have hUVmem : (G.toSimpleGraph s).connectedComponentMk u ∈
                ((G.toSimpleGraph s).connectedComponentMk '' S) \
                  {(G.toSimpleGraph s).connectedComponentMk v} := ⟨hUmem, hcomp⟩
            have himgeq : ψ '' ((G.toSimpleGraph s).connectedComponentMk '' S) =
                ψ '' (((G.toSimpleGraph s).connectedComponentMk '' S) \
                  {(G.toSimpleGraph s).connectedComponentMk v}) := by
              apply Set.Subset.antisymm
              · rintro _ ⟨c, hc, rfl⟩
                by_cases hcv : c = (G.toSimpleGraph s).connectedComponentMk v
                · subst hcv
                  exact ⟨_, hUVmem, hψuv⟩
                · exact ⟨c, ⟨hc, hcv⟩, rfl⟩
              · exact Set.image_mono Set.sdiff_subset
            have hinj : Set.InjOn ψ (((G.toSimpleGraph s).connectedComponentMk '' S) \
                {(G.toSimpleGraph s).connectedComponentMk v}) := by
              rintro c ⟨hc, hcv⟩ d ⟨hd, hdv⟩ hcd
              obtain ⟨x, hxS, rfl⟩ := hc
              obtain ⟨y, hyS, rfl⟩ := hd
              have hreach : (G.toSimpleGraph (insert a s)).Reachable x y := by
                rw [← SimpleGraph.ConnectedComponent.eq, ← hψ, ← hψ]
                exact hcd
              have hRxy := hR x y hreach
              rw [Set.mem_singleton_iff, SimpleGraph.ConnectedComponent.eq] at hcv hdv
              simpa [ρ, hcv, hdv] using hRxy
            have himg : ψ '' ((G.toSimpleGraph s).connectedComponentMk '' S) =
                (G.toSimpleGraph (insert a s)).connectedComponentMk '' S := by
              rw [Set.image_image]
              exact Set.image_congr (fun x _ => hψ x)
            have hcard : ((G.toSimpleGraph s).connectedComponentMk '' S).ncard =
                (ψ '' ((G.toSimpleGraph s).connectedComponentMk '' S)).ncard + 1 := by
              rw [himgeq, hinj.ncard_image]
              exact (Set.ncard_sdiff_singleton_add_one hVmem (hS.image _)).symm
            rw [Multigraph.numComponents, Multigraph.numComponents, ← himg]
            exact hcard
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
