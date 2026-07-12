import LeanModulus.Common.FamilyOfObjects
import Mathlib.Data.Fintype.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.Order.GroupWithZero.Basic


/-!
# Densities as linear functionals

Establishes continuity properties of pairings of densities through the
StrongDual mechanism. -/

namespace Density

variable {E : Type*} [Fintype E]

/-- A density `η` acts as a linear functional on real-valued edge functions. -/
noncomputable def pairing (η : Density E) : StrongDual ℝ (E → ℝ) :=
  ∑ e, (η e : ℝ) • ContinuousLinearMap.proj e

@[simp]
theorem pairing_apply (η : Density E) (f : E → ℝ) :
  η.pairing f = ∑ e, f e * (η e : ℝ) := by
  simp [pairing, mul_comm]

/-- A bound on a pairing with `η > 0` gives an elementwise bound. -/
theorem apply_le_div_of_pairing_le (η : Density E) (f : E → ℝ) (c : ℝ)
  (h : η.pairing f ≤ c) (hpos : ∀ e, 0 < η e) (hf : ∀ e, 0 ≤ f e):
  ∀ e, f e ≤ c / (η e : ℝ) := by
  intro e
  have hsum : ∑ e, f e * (η e : ℝ) ≤ c := by
    rw [pairing_apply] at h
    exact h
  have he : 0 < (η e : ℝ) := by
    exact NNReal.coe_pos.mpr (hpos e)
  rw [le_div_iff₀ he]
  have hsing :=Finset.single_le_sum (fun e _ => mul_nonneg (hf e) (η e).coe_nonneg) (Finset.mem_univ e)
  exact le_trans hsing hsum

end Density
