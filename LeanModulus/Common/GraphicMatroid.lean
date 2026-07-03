import LeanModulus.Common.Multigraph
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# The graphic matroid

The cycle (graphic) matroid of a finite multigraph: the matroid on the edge set whose
independent sets are exactly the forests. See `docs/fairest-edge-usage.md` for why this
connection matters: the paper's spanning-tree results are really matroid facts, so we route
through `Matroid.IsBase` rather than reproving them directly.
-/

namespace Multigraph

variable {V E : Type*} [Finite E] (G : Multigraph V E)

private theorem indep_aug {I J : Set E} (hI : G.IsForest I) (hJ : G.IsForest J)
    (hcard : I.ncard < J.ncard) : ∃ e ∈ J, e ∉ I ∧ G.IsForest (insert e I) := by
  by_contra h
  push Not at h
  have hreach : ∀ u v : V, (G.toSimpleGraph J).Reachable u v → (G.toSimpleGraph I).Reachable u v := by
    intro u v hreach
    refine SimpleGraph.reachable_le_of_adj_le ?_ ?_ ?_ u v hreach
    · exact fun x => SimpleGraph.Reachable.refl x
    · exact fun x y z a a_1 => SimpleGraph.Reachable.trans a a_1
    · intro x y hadj
      rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hadj
      obtain ⟨hxy, hne⟩ := hadj
      obtain ⟨e, heJ, hexy⟩ := hxy
      by_cases heI : e ∈ I
      · have hadj : (G.toSimpleGraph I).Adj x y := by
          rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
          refine ⟨?_, hne⟩
          rw [←hexy]
          exact Set.mem_image_of_mem G.endpoints heI
        exact SimpleGraph.Adj.reachable hadj
      · by_contra hr
        have hc : G.IsForest (insert e I) := by
          exact IsForest.insert_of_not_reachable G hI heI hexy hne hr
        exact (iff_false_intro (h e heJ heI)).mp hc
  set S := (G.toSimpleGraph I).support ∪ (G.toSimpleGraph J).support with hS_def
  have hSfin : S.Finite :=
    (G.toSimpleGraph_support_finite (Set.toFinite I)).union
      (G.toSimpleGraph_support_finite (Set.toFinite J))
  have hIeq : I.ncard + G.numComponents I S = S.ncard :=
    IsForest.ncard_add_numComponents G hI (Set.toFinite I) hSfin Set.subset_union_left
  have hJeq : J.ncard + G.numComponents J S = S.ncard :=
    IsForest.ncard_add_numComponents G hJ (Set.toFinite J) hSfin Set.subset_union_right
  have hresp : ∀ v w (p : (G.toSimpleGraph J).Walk v w), p.IsPath →
      (G.toSimpleGraph I).connectedComponentMk v = (G.toSimpleGraph I).connectedComponentMk w :=
    fun v w p _ => SimpleGraph.ConnectedComponent.sound (hreach v w p.reachable)
  set ψ : (G.toSimpleGraph J).ConnectedComponent → (G.toSimpleGraph I).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift (G.toSimpleGraph I).connectedComponentMk hresp
  have hψ : ∀ x, ψ ((G.toSimpleGraph J).connectedComponentMk x) =
      (G.toSimpleGraph I).connectedComponentMk x := by
    intro x
    simp [ψ, SimpleGraph.ConnectedComponent.lift_mk]
  have himg : (G.toSimpleGraph I).connectedComponentMk '' S =
      ψ '' ((G.toSimpleGraph J).connectedComponentMk '' S) := by
    rw [Set.image_image]
    exact Set.image_congr (fun x _ => (hψ x).symm)
  have hle : G.numComponents I S ≤ G.numComponents J S := by
    rw [Multigraph.numComponents, Multigraph.numComponents, himg]
    exact Set.ncard_image_le (hSfin.image _)
  omega

/-- The `IndepMatroid` (independence-axiom presentation of a matroid) whose
independent sets are the forests of `G`. -/
private def indepMatroid : IndepMatroid E :=
  IndepMatroid.ofFinite (E := Set.univ) Set.finite_univ G.IsForest
    (indep_empty := by
      refine ⟨fun e he => absurd he (Set.notMem_empty e), Set.injOn_empty _, ?_⟩
      simp [Multigraph.toSimpleGraph, Set.image_empty, SimpleGraph.fromEdgeSet_empty,
        SimpleGraph.isAcyclic_bot])
    (indep_subset := fun _ _ hJ hIJ => IsForest.subset G hJ hIJ)
    (indep_aug := fun _ _ hI hJ hcard => G.indep_aug hI hJ hcard)
    (subset_ground := fun _ _ => Set.subset_univ _)

/-- The cycle (graphic) matroid of a finite multigraph `G`: the matroid on the
edge set `E` whose independent sets are the forests of `G`. -/
def graphicMatroid : Matroid E := G.indepMatroid.matroid

@[simp] theorem graphicMatroid_indep {I : Set E} :
    G.graphicMatroid.Indep I ↔ G.IsForest I := Iff.rfl

@[simp] theorem graphicMatroid_E : G.graphicMatroid.E = Set.univ := rfl

end Multigraph
