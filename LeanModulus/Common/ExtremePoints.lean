import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Extreme points of sublevel-compact sets

Convex-analysis facts supplementing Mathlib's extreme-point / Krein-Milman API, built towards:
the infimum of a linear functional over a closed convex set is attained at an extreme point of
the set, given a known compact sublevel set.
-/

/-- If `l` is continuous on `s` and has a compact sublevel set `{y ∈ s | l y ≤ l x₀}` at some
`x₀ ∈ s`, then `l` attains its minimum over all of `s`. -/
theorem exists_isMinOn_of_isCompact_sublevel {F : Type*} [TopologicalSpace F] {s : Set F}
    {l : F → ℝ} (hl : ContinuousOn l s) {x₀ : F} (hx₀ : x₀ ∈ s)
    (hK : IsCompact {y ∈ s | l y ≤ l x₀}) :
    ∃ x ∈ s, IsMinOn l s x := by
  have hx₀K : x₀ ∈ {y ∈ s | l y ≤ l x₀} := ⟨hx₀, le_refl _⟩
  obtain ⟨x, hxK, hxmin⟩ :=
    hK.exists_isMinOn ⟨x₀, hx₀K⟩ (hl.mono fun y hy => hy.1)
  rw [isMinOn_iff] at hxmin
  refine ⟨x, hxK.1, isMinOn_iff.2 fun y hy => ?_⟩
  rcases le_total (l y) (l x₀) with h | h
  · exact hxmin y ⟨hy, h⟩
  · exact (hxmin x₀ hx₀K).trans h

/-- The set of minimizers of a continuous linear functional over `s` is an exposed subset of `s`. -/
theorem isExposed_setOf_isMinOn
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (l : StrongDual ℝ F) (s : Set F) :
    IsExposed ℝ s {y ∈ s | IsMinOn l s y} := by
  suffices h : {y ∈ s | IsMinOn l s y} = (-l).toExposed s by
    rw [h]; exact ContinuousLinearMap.toExposed.isExposed
  ext x
  simp [isMinOn_iff, ContinuousLinearMap.toExposed]

/-- The set of minimizers of a continuous linear functional is an extreme subset of `s`. -/
theorem isExtreme_setOf_isMinOn
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (l : StrongDual ℝ F) (s : Set F) :
    IsExtreme ℝ s {y ∈ s | IsMinOn l s y} :=
  (isExposed_setOf_isMinOn l s).isExtreme

/-- The set of minimizers of a continuous linear functional is compact, given a compact
sublevel set at some `x₀ ∈ s`. -/
theorem isCompact_setOf_isMinOn
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (l : StrongDual ℝ F) {s : Set F}
    {x₀ : F} (hx₀ : x₀ ∈ s) (hK : IsCompact {y ∈ s | l y ≤ l x₀}) :
    IsCompact {y ∈ s | IsMinOn l s y} := by
  obtain ⟨xStar, hxStars, hxStarMin⟩ :=
    exists_isMinOn_of_isCompact_sublevel l.continuous.continuousOn hx₀ hK
  suffices h : {y ∈ s | IsMinOn l s y} = {y ∈ s | l y ≤ l x₀} ∩ l ⁻¹' {l xStar} by
    exact h ▸ hK.inter_right (isClosed_singleton.preimage l.continuous)
  ext x
  apply Iff.intro
  simp [isMinOn_iff]
  · intro a
    simp_all only [and_self, true_and]
    intro hmin
    have hxle := hmin xStar hxStars
    exact le_antisymm hxle (isMinOn_iff.mp hxStarMin x a)
  · intro a
    simp_all only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, true_and]
    obtain ⟨left, right⟩ := a
    obtain ⟨left, right_1⟩ := left
    simp_all only
    rw [isMinOn_iff, right, ←isMinOn_iff]
    exact IsMaxOn.undual hxStarMin

/-- **Layer 1 capstone**: In an LCTVS, if `l` is a continuous linear functional on a set `s`
with a compact sublevel set at some `x₀ ∈ s`, then the minimum of `l` over `s` is attained at
an extreme point of `s`. -/
theorem exists_extremePoint_isMinOn
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (l : StrongDual ℝ F) {s : Set F}
    {x₀ : F} (hx₀ : x₀ ∈ s) (hK : IsCompact {y ∈ s | l y ≤ l x₀}) :
    ∃ x ∈ s.extremePoints ℝ, IsMinOn l s x := by
  -- Get a minimizer xStar; it witnesses that M := argmin set is nonempty.
  obtain ⟨xStar, hxStars, hxStarMin⟩ :=
    exists_isMinOn_of_isCompact_sublevel l.continuous.continuousOn hx₀ hK
  have hMnonempty : ({y ∈ s | IsMinOn (↑l) s y}).Nonempty := ⟨xStar, hxStars, hxStarMin⟩
  -- Krein-Milman: M compact + nonempty → M has an extreme point x̂.
  obtain ⟨xHat, hxHat⟩ := (isCompact_setOf_isMinOn l hx₀ hK).extremePoints_nonempty hMnonempty
  -- xHat is extreme in M, M is extreme in s → xHat is extreme in s; xHat ∈ M → IsMinOn l s xHat.
  exact ⟨xHat, (isExtreme_setOf_isMinOn l s).extremePoints_subset_extremePoints hxHat, hxHat.1.2⟩
