-- General `SimpleGraph` facts that supplement Mathlib but aren't already there.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `Reachable` is the smallest equivalence relation containing `Adj`: any equivalence
relation that relates every adjacent pair also relates every reachable pair. -/
theorem reachable_le_of_adj_le {R : V → V → Prop} (hRefl : ∀ x, R x x)
    (hTrans : ∀ x y z, R x y → R y z → R x z) (hAdj : ∀ x y, G.Adj x y → R x y) :
    ∀ x y, G.Reachable x y → R x y := by
  intro x y h
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => apply hRefl
  | tail _ hadj ih =>
    apply hTrans _ _ _ ih
    apply hAdj
    exact hadj

end SimpleGraph
