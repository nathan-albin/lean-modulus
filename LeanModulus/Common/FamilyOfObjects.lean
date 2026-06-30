-- Families of objects (Section 1.5 of the FEU paper): a common framework for
-- spanning trees, paths, cuts, etc., each identified with its usage vector.
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.NNReal.Basic

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

/-- A density `ρ` is admissible for a family `Γ` if every object in `Γ` has
length at least `1` with respect to `ρ`. -/
def IsAdmissible (ρ : Density E) (Γ : FamilyOfObjects E) : Prop :=
  ∀ γ ∈ Γ, 1 ≤ ρ.length γ

end Density

namespace FamilyOfObjects

variable {E : Type*} [Finite E]

/-- The admissible set of a family `Γ`: all densities admissible for it. -/
def Adm (Γ : FamilyOfObjects E) : Set (Density E) :=
  {ρ | ρ.IsAdmissible Γ}

end FamilyOfObjects
