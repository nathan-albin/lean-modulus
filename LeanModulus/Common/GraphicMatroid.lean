-- The cycle (graphic) matroid of a finite multigraph: the matroid on the edge
-- set whose independent sets are exactly the forests. See
-- `docs/fairest-edge-usage.md` for why this connection matters: the paper's
-- spanning-tree results are really matroid facts, so we route through
-- `Matroid.IsBase` rather than reproving them directly.
import LeanModulus.Common.Multigraph
import Mathlib.Combinatorics.Matroid.IndepAxioms

namespace Multigraph

variable {V E : Type*} [Finite E] (G : Multigraph V E)

private theorem indep_aug {I J : Set E} (hI : G.IsForest I) (hJ : G.IsForest J)
    (hcard : I.ncard < J.ncard) : ∃ e ∈ J, e ∉ I ∧ G.IsForest (insert e I) := by
  sorry

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
