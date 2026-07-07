import LeanModulus.Common.FamilyOfObjects
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The `ℝ≥0` → `ℝ` bridge for densities

The bridge from `Density E := E → ℝ≥0` (see `LeanModulus.Common.FamilyOfObjects`) into `E → ℝ`,
via the coercion `Density.toReal`. Real-analysis tools (compactness, Krein-Milman) aren't
available directly over `ℝ≥0`, so this file collects the algebra of `toReal` (additivity, scalar
multiples), the fact that it's a closed embedding, and the consequences for `Γ.Adm`'s image
(convexity, closedness, nonemptiness) needed to move the duality argument into a locally convex
TVS over `ℝ`.

Everything here genuinely needs `toReal`; facts about `Density E`/`Γ.Adm` that don't mention it
(e.g. their intrinsic `ℝ≥0`-side topology) belong in `LeanModulus.Common.FamilyOfObjects` instead.
-/

open scoped NNReal

namespace Density

variable {E : Type*} [Finite E]

/-- The coercion of a density `E → ℝ≥0` into a real-valued function `E → ℝ`. -/
def toReal (ρ : Density E) : E → ℝ := fun e => (ρ e : ℝ)

omit [Finite E] in
/-- The length with respect to the sum of two densities is the
sum of the lengths. -/
theorem toReal_add (ρ₁ ρ₂ : Density E) :
    (ρ₁ + ρ₂).toReal = ρ₁.toReal + ρ₂.toReal := by
  funext e
  simp [Density.toReal]

omit [Finite E] in
/-- The length with respect to a scalar multiple of a density is
the scalar multiple of the length. -/
theorem toReal_smul (c : ℝ≥0) (ρ : Density E) :
    (c • ρ).toReal = (c : ℝ) • ρ.toReal := by
  funext e
  simp [Density.toReal]

omit [Finite E] in
/-- The coercion of a density `E → ℝ≥0` into a real-valued function `E → ℝ` is a closed embedding. -/
theorem isClosedEmbedding_toReal : Topology.IsClosedEmbedding (Density.toReal : Density E → (E → ℝ)) := by
  have h : (Density.toReal : Density E → (E → ℝ)) = Pi.map (fun _ : E => NNReal.toReal) := rfl
  rw [h]
  exact Topology.IsClosedEmbedding.piMap fun _ => NNReal.isClosedEmbedding_coe

omit [Finite E] in
/-- The image of an open segment under `toReal` is an open segment. -/
theorem toReal_image_openSegment (ρ₁ ρ₂ : Density E) :
    Density.toReal '' (openSegment ℝ≥0 ρ₁ ρ₂) = openSegment ℝ ρ₁.toReal ρ₂.toReal := by
  ext x
  constructor
  · intro hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨a, b, ha, hb, hab, hlin⟩  := hρ
    have hab' : a.toReal + b.toReal = 1 := by norm_cast
    have hlin' : a.toReal • ρ₁.toReal + b.toReal • ρ₂.toReal = ρ.toReal := by
      rw [←toReal_smul, ←toReal_smul, ←toReal_add, hlin]
    refine ⟨a.toReal, b.toReal, ha, hb, hab', hlin' ⟩
  · intro hx
    obtain ⟨a, b, ha, hb, hab, hlin⟩ := hx
    set ρ := a.toNNReal • ρ₁ + b.toNNReal • ρ₂ with hρ
    have ha' : 0 < a.toNNReal := Real.toNNReal_pos.mpr ha
    have hb' : 0 < b.toNNReal := Real.toNNReal_pos.mpr hb
    have hab' : a.toNNReal + b.toNNReal = 1 := by
      rw [←Real.toNNReal_add ha.le hb.le, hab, Real.toNNReal_one]
    refine ⟨ρ, ?_, ?_⟩
    · refine ⟨ a.toNNReal, b.toNNReal, ha', hb', hab', ?_ ⟩
      exact (add_left_inj (b.toNNReal • ρ₂)).mpr rfl
    · rw [hρ, toReal_add, toReal_smul, toReal_smul]
      subst hlin
      rw [Real.coe_toNNReal a ha.le, Real.coe_toNNReal b hb.le]

end Density

namespace FamilyOfObjects

variable {E : Type*} [Finite E] (Γ : FamilyOfObjects E)

/-- The image of `Γ.Adm` under `toReal` is convex. -/
theorem convex_toReal_image_adm : Convex ℝ (Density.toReal '' Γ.Adm) := by
  rw [Convex]
  intro d₁ hd₁
  rw [StarConvex]
  intro d₂ hd₂ θ₁ θ₂ hθ₁ hθ₂ hsum
  rw [Set.image, Set.mem_setOf]
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hd₁
  obtain ⟨ρ₂, hρ₂, rfl⟩ := hd₂
  set ρ := θ₁.toNNReal • ρ₁ + θ₂.toNNReal • ρ₂ with hρ
  refine ⟨ρ, ?_, ?_⟩
  · have hsum' : θ₁.toNNReal + θ₂.toNNReal = 1 := by
      rw [←Real.toNNReal_add hθ₁ hθ₂, hsum, Real.toNNReal_one]
    rw [hρ]
    exact Γ.convex_adm hρ₁ hρ₂ zero_le zero_le hsum'
  · rw [Density.toReal_add, Density.toReal_smul, Density.toReal_smul]
    simp_all only [Real.coe_toNNReal', sup_of_le_left, ρ]

/-- The image of `Γ.Adm` under `toReal` is closed. -/
theorem isClosed_toReal_image_adm : IsClosed (Density.toReal '' Γ.Adm) :=
 Density.isClosedEmbedding_toReal.isClosedMap Γ.Adm (isClosed_adm Γ)

omit [Finite E] in
/-- The image of `Γ.Adm` under `toReal` is nonempty whenever `Γ.Adm` is nonempty. -/
theorem nonempty_toReal_image_adm (Γ : FamilyOfObjects E) (h : Γ.Adm.Nonempty) :
    (Density.toReal '' Γ.Adm).Nonempty := h.image _

end FamilyOfObjects
