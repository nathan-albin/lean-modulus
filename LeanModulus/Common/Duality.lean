import LeanModulus.Common.ExtremePoints
import LeanModulus.Common.Pairing

/-!
# Weak Fulkerson duality

The weak-duality direction of Fulkerson duality (`one_le_length`): a density admissible for
the Fulkerson dual `Γ.FulkersonDual` has length at least `1` against every density admissible
for `Γ`.

The core argument (`one_le_length_of_pos`) runs on the `E → ℝ` side and is then pulled back:
for strictly positive `η` the pairing has compact sublevel sets over `Density.toReal '' Γ.Adm`
(`LeanModulus.Common.Pairing`), so its minimum is attained at an extreme point
(`LeanModulus.Common.ExtremePoints`), which corresponds to a member of `Γ.FulkersonDual`
(`LeanModulus.Common.ToReal`). The general case follows by perturbing `η` by `δ • 1` and
letting `δ → 0`.
-/

open scoped NNReal

namespace FamilyOfObjects

variable {E : Type*} [Fintype E] (Γ : FamilyOfObjects E)

/-- The pairing with a strictly positive density attains its minimum over the image of a
nonempty admissible set at (the coercion of) a member of the Fulkerson dual. -/
theorem exists_fulkersonDual_isMinOn {η : Density E} (hη : ∀ e, 0 < η e)
    (hne : Γ.Adm.Nonempty) :
    ∃ γ ∈ Γ.FulkersonDual, IsMinOn η.pairing (Density.toReal '' Γ.Adm) (Density.toReal γ) := by
  obtain ⟨ρ₀, hρ₀⟩ := hne
  obtain ⟨x, hxExt, hxMin⟩ :=
    exists_extremePoint_isMinOn η.pairing (Set.mem_image_of_mem _ hρ₀)
      (Γ.isCompact_sublevel_toReal_image_adm η hη (η.pairing ρ₀.toReal))
  obtain ⟨γ, hγ, rfl⟩ := extremePoints_subset hxExt
  exact ⟨γ, mem_fulkersonDual_of_toReal_mem_extremePoints Γ γ hxExt, hxMin⟩

/-- **Weak duality, strictly positive case**: if `η > 0` is admissible for the Fulkerson dual
of `Γ`, then every density admissible for `Γ` has `η`-length at least `1`. -/
theorem one_le_length_of_pos {η : Density E} (hη : ∀ e, 0 < η e)
    (hηAdm : η ∈ Γ.FulkersonDual.Adm)
    {ρ : Density E} (hρ : ρ ∈ Γ.Adm) :
    1 ≤ η.length ρ := by
  obtain ⟨γ, hγ, hMin⟩ := Γ.exists_fulkersonDual_isMinOn hη ⟨ρ, hρ⟩
  have hpair : η.pairing (Density.toReal γ) ≤ η.pairing ρ.toReal :=
    isMinOn_iff.mp hMin ρ.toReal (Set.mem_image_of_mem _ hρ)
  rw [Density.pairing_toReal_eq_length, Density.pairing_toReal_eq_length] at hpair
  have hγ1 : (1 : ℝ) ≤ (η.length γ : ℝ) := by
    exact_mod_cast hηAdm γ hγ
  exact_mod_cast le_trans hγ1 hpair

/-- **Weak duality**: if `η` is admissible for the Fulkerson dual of `Γ`, then every density
admissible for `Γ` has `η`-length at least `1`. The strict-positivity hypothesis of
`one_le_length_of_pos` is removed by perturbing to `η + δ • 1` — still dual-admissible since
lengths are monotone — and letting `δ → 0`. -/
theorem one_le_length {η : Density E} (hηAdm : η ∈ Γ.FulkersonDual.Adm)
    {ρ : Density E} (hρ : ρ ∈ Γ.Adm) :
    1 ≤ η.length ρ := by
  have key : ∀ δ : ℝ≥0, 0 < δ → 1 ≤ η.length ρ + δ * (1 : Density E).length ρ := by
    intro δ hδ
    have hpos : ∀ e, 0 < (η + δ • (1 : Density E)) e := by
      intro e
      have he : (η + δ • (1 : Density E)) e = η e + δ := by simp
      rw [he]
      exact lt_of_lt_of_le hδ le_add_self
    have hAdm : η + δ • (1 : Density E) ∈ Γ.FulkersonDual.Adm := by
      intro γ hγ
      rw [Density.length_add, Density.length_smul]
      exact le_trans (hηAdm γ hγ) le_self_add
    have h := Γ.one_le_length_of_pos hpos hAdm hρ
    rwa [Density.length_add, Density.length_smul] at h
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set L := (1 : Density E).length ρ with hL
  have hL1 : (0 : ℝ≥0) < L + 1 := lt_of_lt_of_le zero_lt_one le_add_self
  refine le_trans (key (ε / (L + 1)) (div_pos hε hL1)) ?_
  gcongr
  rw [div_mul_eq_mul_div, div_le_iff₀ hL1]
  exact mul_le_mul_right le_self_add ε

end FamilyOfObjects
