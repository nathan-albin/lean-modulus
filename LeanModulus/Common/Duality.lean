import LeanModulus.Common.ExtremePoints
import LeanModulus.Common.Pairing

/-!
# Weak Fulkerson duality

Assembly of the weak-duality direction of Fulkerson duality (TODO 1 of the duality plan):
for a strictly positive density `η` admissible for the Fulkerson dual `Γ.FulkersonDual`,
every density admissible for `Γ` has `η`-length at least `1`.

The argument runs entirely on the `E → ℝ` side and is then pulled back: the pairing with `η`
has compact sublevel sets over `Density.toReal '' Γ.Adm` (`LeanModulus.Common.Pairing`), so its
minimum is attained at an extreme point (`LeanModulus.Common.ExtremePoints`), which corresponds
to a member of `Γ.FulkersonDual` (`LeanModulus.Common.ToReal`).

The strict-positivity hypothesis on `η` will be removed later by an `ε`-perturbation argument.
-/

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
    (hηAdm : η ∈ Γ.FulkersonDual.Adm) (hne : Γ.Adm.Nonempty)
    {ρ : Density E} (hρ : ρ ∈ Γ.Adm) :
    1 ≤ η.length ρ := by
  obtain ⟨γ, hγ, hMin⟩ := Γ.exists_fulkersonDual_isMinOn hη hne
  have hpair : η.pairing (Density.toReal γ) ≤ η.pairing ρ.toReal :=
    isMinOn_iff.mp hMin ρ.toReal (Set.mem_image_of_mem _ hρ)
  rw [Density.pairing_toReal_eq_length, Density.pairing_toReal_eq_length] at hpair
  have hγ1 : (1 : ℝ) ≤ (η.length γ : ℝ) := by
    exact_mod_cast hηAdm γ hγ
  exact_mod_cast le_trans hγ1 hpair

end FamilyOfObjects
