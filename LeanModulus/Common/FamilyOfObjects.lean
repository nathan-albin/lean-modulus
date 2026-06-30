-- Families of objects (Section 1.5 of the FEU paper): a common framework for
-- spanning trees, paths, cuts, etc., each identified with its usage vector.
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
