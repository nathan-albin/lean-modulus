import LeanModulus.Common.FamilyOfObjects
import Mathlib.Analysis.Convex.Basic
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

/-- The length with respect to the sum of two densities is the
sum of the lengths. -/
theorem toReal_add {E : Type*} (ρ₁ ρ₂ : Density E) :
    (ρ₁ + ρ₂).toReal = ρ₁.toReal + ρ₂.toReal := by
  funext e
  simp only [Density.toReal, Pi.add_apply, NNReal.coe_add]

/-- The length with respect to a scalar multiple of a density is
the scalar multiple of the length. -/
theorem toReal_smul {E : Type*} (c : ℝ≥0) (ρ : Density E) :
    (c • ρ).toReal = (c : ℝ) • ρ.toReal := by
  funext e
  simp only [Density.toReal, Pi.smul_apply]
  exact Real.ext_cauchy rfl

/-- The coercion of a density `E → ℝ≥0` into a real-valued function `E → ℝ` is a closed embedding. -/
theorem isClosedEmbedding_toReal {E : Type*} : Topology.IsClosedEmbedding (Density.toReal : Density E → (E → ℝ)) := by
  have h : (Density.toReal : Density E → (E → ℝ)) = Pi.map (fun _ : E => NNReal.toReal) := rfl
  rw [h]
  exact Topology.IsClosedEmbedding.piMap fun _ => NNReal.isClosedEmbedding_coe

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
      rw [←Real.toNNReal_add, hsum, Real.toNNReal_one]
      exact hθ₁
      exact hθ₂
    rw [hρ]
    exact Γ.convex_adm hρ₁ hρ₂ zero_le zero_le hsum'
  · rw [Density.toReal_add, Density.toReal_smul, Density.toReal_smul]
    simp_all only [Real.coe_toNNReal', sup_of_le_left, ρ]

/-- The image of `Γ.Adm` under `toReal` is closed. -/
theorem isClosed_toReal_image_adm : IsClosed (Density.toReal '' Γ.Adm) := by
  have hToReal : IsClosedMap (Density.toReal : Density E → (E →ℝ)) := by
    exact (Density.isClosedEmbedding_toReal : Topology.IsClosedEmbedding (Density.toReal : Density E → (E → ℝ))).isClosedMap
  exact hToReal Γ.Adm (isClosed_adm Γ)

/-- The image of `Γ.Adm` under `toReal` is nonempty whenever `Γ.Adm` is nonempty. -/
theorem nonempty_toReal_image_adm {E : Type*} (Γ : FamilyOfObjects E) (h : Γ.Adm.Nonempty) :
    (Density.toReal '' Γ.Adm).Nonempty := h.image _

end FamilyOfObjects
