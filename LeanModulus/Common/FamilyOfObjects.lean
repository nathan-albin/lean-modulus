import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Families of objects

Families of objects (Section 1.5 of the FEU paper): a common framework for spanning trees,
paths, cuts, etc., each identified with its usage vector.

Everything here is stated over `ℝ≥0`: `Density E := E → ℝ≥0` has no subtraction, only the
semiring/convexity/(intrinsic `ℝ≥0`-Pi) topological structure needed for `Adm`, `Equivalent`,
and `FulkersonDual`. The companion coercion into `E → ℝ` (needed to bring in real-analysis
machinery like Krein-Milman) lives in `LeanModulus.Common.ToReal`; anything that actually needs
that coercion belongs there instead of here.
-/

open scoped NNReal

/-- A *family of objects* on an edge type `E`: a set of usage vectors
`γ : E → ℝ≥0`, one for each object (spanning tree, path, cut, etc.) in the
family. -/
abbrev FamilyOfObjects (E : Type*) := Set (E → ℝ≥0)

namespace FamilyOfObjects

variable {E : Type*}

/-- Every object in `Γ` has positive usage on at least one edge. This rules
out the trivial all-zero object, against which no density could ever be
admissible. -/
def NoZeroObject (Γ : FamilyOfObjects E) : Prop :=
  ∀ γ ∈ Γ, γ ≠ 0

end FamilyOfObjects

/-- A *density* on the edge type `E` assigns a nonnegative cost to each
edge. -/
abbrev Density (E : Type*) := E → ℝ≥0

namespace Density

variable {E : Type*} [Finite E]

/-- The length of an object `γ` with respect to a density `ρ` is the total
cost it incurs: `∑ e, γ e * ρ e`. We use `finsum` (rather than `Finset.sum`
over `Finset.univ`) so that this doesn't need a `Fintype E` instance, only
`Finite E`. -/
noncomputable def length (ρ : Density E) (γ : E → ℝ≥0) : ℝ≥0 :=
  ∑ᶠ e, γ e * ρ e

/-- The length with respect to the sum of two densities is the
sum of the lengths. -/
theorem length_add (ρ₁ ρ₂ : Density E) (γ : E → ℝ≥0) :
    (ρ₁ + ρ₂).length γ = ρ₁.length γ + ρ₂.length γ := by
  rw [length, length, length]
  simp only [Pi.add_apply]
  ring_nf
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

omit [Finite E] in
/-- The length with respect to a scalar multiple of a density is
the scalar multiple of the length. -/
theorem length_smul (ρ : Density E) (c : ℝ≥0) (γ : E → ℝ≥0) :
    (c • ρ).length γ = c * ρ.length γ := by
  rw [length, length]
  simp only [Pi.smul_apply]
  ring_nf
  rw [←finsum_mul]
  ring

/-- A density `ρ` is admissible for a family `Γ` if every object in `Γ` has
length at least `1` with respect to `ρ`. -/
def IsAdmissible (ρ : Density E) (Γ : FamilyOfObjects E) : Prop :=
  ∀ γ ∈ Γ, 1 ≤ ρ.length γ

/-- The length function is continuous (in the topology of densities). -/
theorem continuous_length (γ : E → ℝ≥0) :
    Continuous (fun ρ : Density E => ρ.length γ) := by
  have hE : Fintype E := Fintype.ofFinite E
  simp only [length, finsum_eq_sum_of_fintype]
  exact continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_apply e)

end Density

namespace FamilyOfObjects

variable {E : Type*} [Finite E]

/-- The admissible set of a family `Γ`: all densities admissible for it. -/
def Adm (Γ : FamilyOfObjects E) : Set (Density E) :=
  {ρ | ρ.IsAdmissible Γ}

/-- The admissible set `Adm(Γ)`of a family `Γ` is convex. -/
theorem convex_adm (Γ : FamilyOfObjects E) : Convex ℝ≥0 Γ.Adm := by
  rw [Convex]
  intro ρ₁ hρ₁
  rw [StarConvex]
  intro ρ₂ hρ₂ θ₁ θ₂ hθ₁ hθ₂ hsum
  rw [Adm, Set.mem_setOf, Density.IsAdmissible]
  intro γ hγ
  rw [Density.length_add, Density.length_smul, Density.length_smul]
  have h₁ := hρ₁ γ hγ
  have h₂ := hρ₂ γ hγ
  have h₁' := mul_le_mul_of_nonneg_left h₁ hθ₁
  rw [mul_one] at h₁'
  have h₂' := mul_le_mul_of_nonneg_left h₂ hθ₂
  rw [mul_one] at h₂'
  rw [←hsum]
  exact add_le_add h₁' h₂'

/-- The admissible set `Adm(Γ)`of a family `Γ` is closed. -/
theorem isClosed_adm (Γ : FamilyOfObjects E) : IsClosed Γ.Adm := by
  have hAdm : Γ.Adm = ⋂ γ ∈ Γ, {ρ | 1 ≤ ρ.length γ} := by
    ext ρ
    simp [Adm, Density.IsAdmissible]
  rw [hAdm]
  exact isClosed_biInter fun γ _ => IsClosed.preimage (Density.continuous_length γ) (isClosed_Ici)

/-- Two families of objects are *equivalent* if they have the same admissible
set, i.e. they impose exactly the same constraints on densities. This avoids
over-distinguishing one family from another obtained by adding or removing
redundant objects (objects whose admissibility constraint is implied by the
others). -/
def Equivalent (Γ Γ' : FamilyOfObjects E) : Prop :=
  Γ.Adm = Γ'.Adm

instance : Setoid (FamilyOfObjects E) where
  r := Equivalent
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The Fulkerson dual family of `Γ`: the extreme points of its admissible
set. `Set.extremePoints` only needs a `Semiring`/`SMul` structure (not a full
vector space with subtraction), so this is stated directly over `ℝ≥0`. -/
def FulkersonDual (Γ : FamilyOfObjects E) : FamilyOfObjects E :=
  Set.extremePoints ℝ≥0 Γ.Adm

end FamilyOfObjects
