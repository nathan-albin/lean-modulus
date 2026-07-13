import LeanModulus.Common.ToReal
import Mathlib.Data.Fintype.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Pairing with a density

The pairing `f ↦ ∑ e, f e * η e` of a density `η : Density E` against real-valued functions
`f : E → ℝ`, bundled as a continuous linear functional (an element of `StrongDual ℝ (E → ℝ)`).
Assembling it from already-bundled pieces (`ContinuousLinearMap.proj`, scalar multiples, sums)
makes linearity and continuity automatic.

For strictly positive `η` the pairing is coercive on nonnegative functions: a bound
`η.pairing f ≤ c` forces the coordinatewise bound `f e ≤ c / η e`. Consequently the sublevel
sets of the pairing over `Density.toReal '' Γ.Adm` are compact — the hypothesis needed to apply
the minimum-at-an-extreme-point machinery of `LeanModulus.Common.ExtremePoints` in the duality
argument.
-/

namespace Density

variable {E : Type*} [Fintype E]

/-- The pairing `f ↦ ∑ e, f e * η e` of the density `η` against real-valued functions,
as a continuous linear functional on `E → ℝ`. -/
noncomputable def pairing (η : Density E) : StrongDual ℝ (E → ℝ) :=
  ∑ e, (η e : ℝ) • ContinuousLinearMap.proj e

@[simp]
theorem pairing_apply (η : Density E) (f : E → ℝ) :
    η.pairing f = ∑ e, f e * (η e : ℝ) := by
  simp [pairing, mul_comm]

/-- If a nonnegative function `f` pairs against a strictly positive density `η` to at most `c`,
then each coordinate satisfies `f e ≤ c / η e`. This is the coercivity estimate that traps
sublevel sets of the pairing in a compact box. -/
theorem apply_le_div_of_pairing_le (η : Density E) (f : E → ℝ) (c : ℝ)
    (h : η.pairing f ≤ c) (hpos : ∀ e, 0 < η e) (hf : ∀ e, 0 ≤ f e) :
    ∀ e, f e ≤ c / (η e : ℝ) := by
  intro e
  have hsum : ∑ e, f e * (η e : ℝ) ≤ c := by
    rw [pairing_apply] at h
    exact h
  have he : 0 < (η e : ℝ) := by
    exact NNReal.coe_pos.mpr (hpos e)
  rw [le_div_iff₀ he]
  have hsing := Finset.single_le_sum (fun e _ => mul_nonneg (hf e) (η e).coe_nonneg)
    (Finset.mem_univ e)
  exact le_trans hsing hsum

end Density

namespace FamilyOfObjects

variable {E : Type*} [Fintype E] (Γ : FamilyOfObjects E)

/-- Sublevel sets of the pairing with a strictly positive density `η`, taken within the image
of the admissible set, are compact: they are closed and trapped in the box
`∏ e, [0, c / η e]` by the coercivity estimate `Density.apply_le_div_of_pairing_le`. -/
theorem isCompact_sublevel_toReal_image_adm (η : Density E) (hη : ∀ e, 0 < η e) (c : ℝ) :
    IsCompact {f ∈ Density.toReal '' Γ.Adm | η.pairing f ≤ c} := by
  have hbox : IsCompact (Set.univ.pi fun e => Set.Icc (0 : ℝ) (c / (η e : ℝ))) :=
    isCompact_univ_pi fun e => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · exact (isClosed_toReal_image_adm Γ).inter
      (isClosed_le η.pairing.continuous continuous_const)
  · rintro f ⟨⟨ρ, hρ, rfl⟩, hle⟩
    rw [Set.mem_univ_pi]
    intro e
    rw [Set.mem_Icc]
    exact ⟨ρ.toReal_nonneg e,
      Density.apply_le_div_of_pairing_le η ρ.toReal c hle hη ρ.toReal_nonneg e⟩

end FamilyOfObjects
