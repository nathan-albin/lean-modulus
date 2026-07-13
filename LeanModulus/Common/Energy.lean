import LeanModulus.Common.ExtremePoints
import LeanModulus.Common.Pairing

/-!
# The 2-energy of a density

The weighted 2-energy `∑ e, σ e * ρ e ^ 2` of a density, in both its `ℝ≥0` form
(`Density.energy`) and its real form on `E → ℝ` (`Density.energyReal`), together with the
facts needed for the strong-duality argument: the energy is continuous and coercive, so it has
compact sublevel sets over `Density.toReal '' Γ.Adm` and attains a minimum over a nonempty
admissible set; strict convexity of the square makes the minimizer unique
(`FamilyOfObjects.existsUnique_isMinOn_energy`).
-/

open scoped NNReal

namespace Density

variable {E : Type*} [Fintype E]

/-- The 2-energy of a density `ρ` with respect to the edge weights `σ`:
`∑ e, σ e * ρ e ^ 2`. -/
noncomputable def energy (σ : E → ℝ≥0) (ρ : Density E) : ℝ≥0 :=
  ∑ᶠ e, σ e * ρ e ^ 2

/-- The 2-energy with respect to the edge weights `σ` as a function of real-valued functions
on `E`, for use with the real-analysis machinery. Agrees with `Density.energy` on coercions
of densities (`Density.energyReal_toReal`). -/
noncomputable def energyReal (σ : E → ℝ≥0) (f : E → ℝ) : ℝ :=
  ∑ e, (σ e : ℝ) * f e ^ 2

@[simp]
theorem energyReal_apply (σ : E → ℝ≥0) (f : E → ℝ) :
    energyReal σ f = ∑ e, (σ e : ℝ) * f e ^ 2 :=
  rfl

/-- The real 2-energy of the coercion of a density is the coercion of its `ℝ≥0` 2-energy. -/
theorem energyReal_toReal (σ : E → ℝ≥0) (ρ : Density E) :
    energyReal σ ρ.toReal = (energy σ ρ : ℝ) := by
  rw [energyReal, energy, finsum_eq_sum_of_fintype, NNReal.coe_sum]
  simp [Density.toReal]

/-- The real 2-energy is continuous. -/
theorem continuous_energyReal (σ : E → ℝ≥0) : Continuous (energyReal σ) :=
  continuous_finsetSum _ fun e _ => continuous_const.mul ((continuous_apply e).pow 2)

/-- The real 2-energy is nonnegative. -/
theorem energyReal_nonneg (σ : E → ℝ≥0) (f : E → ℝ) : 0 ≤ energyReal σ f :=
  Finset.sum_nonneg fun e _ => mul_nonneg (σ e).coe_nonneg (sq_nonneg _)

omit [Fintype E] in
/-- The 2-energy of a density is its length against the reweighted density `σ * ρ`. -/
theorem length_mul_eq_energy (σ : E → ℝ≥0) (ρ : Density E) :
    Density.length (σ * ρ) ρ = energy σ ρ := by
  rw [Density.length, energy]
  exact finsum_congr fun e => by rw [Pi.mul_apply]; ring

/-- First-variation expansion of the real 2-energy at the coercion of a density `ρ`:
moving by `t • f` changes the energy by a linear term, the pairing against the reweighted
density `σ * ρ`, plus a quadratic remainder. -/
theorem energyReal_add_smul (σ : E → ℝ≥0) (ρ : Density E) (f : E → ℝ) (t : ℝ) :
    energyReal σ (ρ.toReal + t • f)
      = energyReal σ ρ.toReal + 2 * t * pairing (σ * ρ) f + t ^ 2 * energyReal σ f := by
  simp only [energyReal_apply, pairing_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, NNReal.coe_mul,
    Density.toReal]
  ring

/-- If a nonnegative function `f` has 2-energy at most `c` with respect to strictly positive
edge weights `σ`, then each coordinate satisfies `f e ≤ √(c / σ e)`. This is the coercivity
estimate that traps sublevel sets of the energy in a compact box. -/
theorem apply_le_sqrt_of_energyReal_le (σ : E → ℝ≥0) (f : E → ℝ) (c : ℝ)
    (h : energyReal σ f ≤ c) (hσ : ∀ e, 0 < σ e) (hf : ∀ e, 0 ≤ f e) :
    ∀ e, f e ≤ Real.sqrt (c / σ e) := by
  intro e
  have hterm : (σ e : ℝ) * f e ^ 2 ≤ c :=
    le_trans (Finset.single_le_sum
      (fun e' _ => mul_nonneg (σ e').coe_nonneg (sq_nonneg _)) (Finset.mem_univ e)) h
  have hσe : (0 : ℝ) < σ e := NNReal.coe_pos.mpr (hσ e)
  have hc : (0 : ℝ) ≤ c := le_trans (mul_nonneg (σ e).coe_nonneg (sq_nonneg _)) hterm
  rw [Real.le_sqrt (hf e) (div_nonneg hc hσe.le), le_div_iff₀ hσe]
  linarith [hterm]

end Density

namespace FamilyOfObjects

variable {E : Type*} [Fintype E] (Γ : FamilyOfObjects E)

/-- Sublevel sets of the 2-energy with strictly positive edge weights `σ`, taken within the
image of the admissible set, are compact: they are closed and trapped in the box
`∏ e, [0, √(c / σ e)]` by the coercivity estimate `Density.apply_le_sqrt_of_energyReal_le`. -/
theorem isCompact_sublevel_energy_toReal_image_adm (σ : E → ℝ≥0) (hσ : ∀ e, 0 < σ e) (c : ℝ) :
    IsCompact {f ∈ Density.toReal '' Γ.Adm | Density.energyReal σ f ≤ c} := by
  have hbox : IsCompact (Set.univ.pi fun e => Set.Icc (0 : ℝ) (Real.sqrt (c / σ e))) :=
    isCompact_univ_pi fun e => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · exact (isClosed_toReal_image_adm Γ).inter
      (isClosed_le (Density.continuous_energyReal σ) continuous_const)
  · rintro f ⟨⟨ρ, hρ, rfl⟩, hle⟩
    rw [Set.mem_univ_pi]
    intro e
    rw [Set.mem_Icc]
    exact ⟨ρ.toReal_nonneg e,
      Density.apply_le_sqrt_of_energyReal_le σ ρ.toReal c hle hσ ρ.toReal_nonneg e⟩

/-- The 2-energy with strictly positive edge weights attains a minimum over a nonempty
admissible set. -/
theorem exists_isMinOn_energy (σ : E → ℝ≥0) (hσ : ∀ e, 0 < σ e) (hne : Γ.Adm.Nonempty) :
    ∃ ρ ∈ Γ.Adm, IsMinOn (Density.energy σ) Γ.Adm ρ := by
  obtain ⟨ρ₀, hρ₀⟩ := hne
  obtain ⟨x, hxmem, hxMin⟩ :=
    exists_isMinOn_of_isCompact_sublevel (Density.continuous_energyReal σ).continuousOn
      (Set.mem_image_of_mem _ hρ₀)
      (Γ.isCompact_sublevel_energy_toReal_image_adm σ hσ (Density.energyReal σ ρ₀.toReal))
  obtain ⟨ρ, hρ, rfl⟩ := hxmem
  refine ⟨ρ, hρ, isMinOn_iff.2 fun ρ' hρ' => ?_⟩
  have h := isMinOn_iff.mp hxMin ρ'.toReal (Set.mem_image_of_mem _ hρ')
  rw [Density.energyReal_toReal, Density.energyReal_toReal] at h
  exact_mod_cast h

/-- Weighted squares are midpoint-convex: `s * ((a + b)/2)² ≤ s * (a² + b²)/2` for `s ≥ 0`. -/
private theorem mul_sq_midpoint_le (s a b : ℝ) (hs : 0 ≤ s) :
    s * (2⁻¹ * a + 2⁻¹ * b) ^ 2 ≤ s * (2⁻¹ * a ^ 2 + 2⁻¹ * b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- Weighted squares are strictly midpoint-convex for positive weights and distinct points. -/
private theorem mul_sq_midpoint_lt (s a b : ℝ) (hs : 0 < s) (hab : a ≠ b) :
    s * (2⁻¹ * a + 2⁻¹ * b) ^ 2 < s * (2⁻¹ * a ^ 2 + 2⁻¹ * b ^ 2) := by
  nlinarith [(sq_nonneg (a - b)).lt_of_ne' (pow_ne_zero 2 (sub_ne_zero.mpr hab))]

/-- **Unique energy minimizer**: over a nonempty admissible set,
the 2-energy with strictly positive edge weights has exactly one minimizer. Existence is
`exists_isMinOn_energy`; uniqueness holds because two distinct minimizers would average to an
admissible density of strictly smaller energy. -/
theorem existsUnique_isMinOn_energy (σ : E → ℝ≥0) (hσ : ∀ e, 0 < σ e)
    (hne : Γ.Adm.Nonempty) :
    ∃! ρ, ρ ∈ Γ.Adm ∧ IsMinOn (Density.energy σ) Γ.Adm ρ := by
  obtain ⟨ρ, hρ, hMin⟩ := Γ.exists_isMinOn_energy σ hσ hne
  refine ⟨ρ, ⟨hρ, hMin⟩, ?_⟩
  rintro ρ' ⟨hρ', hMin'⟩
  by_contra hcon
  obtain ⟨e₀, he₀⟩ := Function.ne_iff.mp hcon
  have hmAdm : (2⁻¹ : ℝ≥0) • ρ' + (2⁻¹ : ℝ≥0) • ρ ∈ Γ.Adm :=
    Γ.convex_adm hρ' hρ zero_le zero_le (by norm_num)
  have heq : Density.energy σ ρ' = Density.energy σ ρ :=
    le_antisymm (isMinOn_iff.mp hMin' ρ hρ) (isMinOn_iff.mp hMin ρ' hρ')
  have htoReal : ∀ e, ((2⁻¹ : ℝ≥0) • ρ' + (2⁻¹ : ℝ≥0) • ρ).toReal e
      = 2⁻¹ * ρ'.toReal e + 2⁻¹ * ρ.toReal e := by
    intro e
    simp [Density.toReal]
  have hlt : Density.energyReal σ (((2⁻¹ : ℝ≥0) • ρ' + (2⁻¹ : ℝ≥0) • ρ).toReal)
      < (Density.energy σ ρ : ℝ) := by
    calc Density.energyReal σ (((2⁻¹ : ℝ≥0) • ρ' + (2⁻¹ : ℝ≥0) • ρ).toReal)
        = ∑ e, (σ e : ℝ) * (2⁻¹ * ρ'.toReal e + 2⁻¹ * ρ.toReal e) ^ 2 := by
          rw [Density.energyReal_apply]
          exact Finset.sum_congr rfl fun e _ => by rw [htoReal e]
      _ < ∑ e, (σ e : ℝ) * (2⁻¹ * ρ'.toReal e ^ 2 + 2⁻¹ * ρ.toReal e ^ 2) := by
          refine Finset.sum_lt_sum (fun e _ => mul_sq_midpoint_le _ _ _ (σ e).coe_nonneg)
            ⟨e₀, Finset.mem_univ e₀, mul_sq_midpoint_lt _ _ _ (NNReal.coe_pos.mpr (hσ e₀))
              fun h => he₀ (NNReal.coe_injective h)⟩
      _ = 2⁻¹ * Density.energyReal σ ρ'.toReal + 2⁻¹ * Density.energyReal σ ρ.toReal := by
          rw [Density.energyReal_apply, Density.energyReal_apply, Finset.mul_sum,
            Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = (Density.energy σ ρ : ℝ) := by
          rw [Density.energyReal_toReal, Density.energyReal_toReal, heq]
          ring
  rw [Density.energyReal_toReal] at hlt
  exact absurd (isMinOn_iff.mp hMin _ hmAdm) (not_le.mpr (by exact_mod_cast hlt))

/-- **Variational inequality**: a minimizer `ρ*` of the 2-energy over the admissible set also
minimizes the linear functional `γ ↦ (σ * ρ*).length γ` over the admissible set. Moving from
`ρ*` towards any admissible `ρ` changes the energy at first order by the pairing term of
`Density.energyReal_add_smul`, which must therefore be nonnegative. -/
theorem isMinOn_length_mul_of_isMinOn_energy (σ : E → ℝ≥0) {ρs : Density E}
    (hρs : ρs ∈ Γ.Adm) (hMin : IsMinOn (Density.energy σ) Γ.Adm ρs) :
    IsMinOn (Density.length (σ * ρs)) Γ.Adm ρs := by
  refine isMinOn_iff.2 fun ρ hρ => ?_
  set d : E → ℝ := Density.toReal ρ - ρs.toReal with hd
  set P : ℝ := Density.pairing (σ * ρs) d with hP
  set Q : ℝ := Density.energyReal σ d with hQ
  have hQ0 : 0 ≤ Q := Density.energyReal_nonneg σ d
  -- moving from ρ* towards ρ by t cannot decrease the energy
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ 2 * t * P + t ^ 2 * Q := by
    intro t ht ht1
    set s : ℝ≥0 := t.toNNReal with hs
    have hs1 : s ≤ 1 := by
      rw [hs, ← Real.toNNReal_one]
      exact Real.toNNReal_mono ht1
    have hst : (s : ℝ) = t := Real.coe_toNNReal t ht.le
    have hρt : (1 - s) • ρs + s • ρ ∈ Γ.Adm :=
      Γ.convex_adm hρs hρ zero_le zero_le (tsub_add_cancel_of_le hs1)
    have htoReal : ((1 - s) • ρs + s • ρ).toReal = ρs.toReal + t • d := by
      funext e
      have h1s : ((1 - s : ℝ≥0) : ℝ) = 1 - t := by
        rw [NNReal.coe_sub hs1, hst, NNReal.coe_one]
      simp only [Density.toReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, NNReal.coe_add,
        NNReal.coe_mul, h1s, hst, hd, Pi.sub_apply]
      ring
    have h := isMinOn_iff.mp hMin _ hρt
    have hR : Density.energyReal σ ρs.toReal
        ≤ Density.energyReal σ (((1 - s) • ρs + s • ρ).toReal) := by
      rw [Density.energyReal_toReal, Density.energyReal_toReal]
      exact_mod_cast h
    rw [htoReal, Density.energyReal_add_smul] at hR
    linarith
  -- let t → 0 to isolate the first-order term
  have hP0 : 0 ≤ P := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hQ1 : (0 : ℝ) < Q + 1 := by linarith
    set t : ℝ := min 1 (ε / (Q + 1)) with htdef
    have ht : 0 < t := lt_min one_pos (div_pos hε hQ1)
    have htQ : t * Q ≤ ε := by
      calc t * Q ≤ ε / (Q + 1) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ0
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hQ1]
            nlinarith
    have hk := key t ht (min_le_left _ _)
    nlinarith [mul_le_mul_of_nonneg_left htQ ht.le]
  rw [hP, hd, map_sub, sub_nonneg, Density.pairing_toReal_eq_length,
    Density.pairing_toReal_eq_length] at hP0
  exact_mod_cast hP0

end FamilyOfObjects
