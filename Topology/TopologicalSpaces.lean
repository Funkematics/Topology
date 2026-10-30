import Mathlib.Data.Finite.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.SetNotation

/-!
# Topological spaces (Sutherland, Chapter 7)

Homework problems on the definition of a topology. Every `sorry` is yours to fill in.

These problems compare topologies as collections of subsets, so a topology on `X`
is modelled the way Sutherland defines it: a family `T : Set (Set X)` satisfying
the axioms T1–T3, recorded in `IsTopology`.
-/

open Set

namespace TopologicalSpaces

variable {X : Type*}

/-- Sutherland's definition of a topology on `X`: a family of subsets containing `∅`
and `X`, closed under arbitrary unions and finite intersections. -/
structure IsTopology (T : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ T
  univ_mem : univ ∈ T
  sUnion_mem : ∀ S ⊆ T, ⋃₀ S ∈ T
  inter_mem : ∀ U ∈ T, ∀ V ∈ T, U ∩ V ∈ T

/-! ## Sutherland 7.2  (HW6)
Give an example of two topologies 𝒯₁, 𝒯₂ on the same set such that neither contains
the other.
-/

theorem ex7_2 : ∃ (X : Type) (T₁ T₂ : Set (Set X)),
    IsTopology T₁ ∧ IsTopology T₂ ∧ ¬ T₁ ⊆ T₂ ∧ ¬ T₂ ⊆ T₁ := by
  sorry

/-! ## Sutherland 7.3  (HW6)
Show that the intersection of two topologies on the same set X is also a topology on
X, but that their union may or may not be a topology. Does the first result extend to
the intersection of an arbitrary family of topologies on X?
-/

theorem ex7_3_inter {T₁ T₂ : Set (Set X)} (h₁ : IsTopology T₁) (h₂ : IsTopology T₂) :
    IsTopology (T₁ ∩ T₂) := by
  sorry

theorem ex7_3_union_may : ∃ (X : Type) (T₁ T₂ : Set (Set X)),
    IsTopology T₁ ∧ IsTopology T₂ ∧ IsTopology (T₁ ∪ T₂) := by
  sorry

theorem ex7_3_union_may_not : ∃ (X : Type) (T₁ T₂ : Set (Set X)),
    IsTopology T₁ ∧ IsTopology T₂ ∧ ¬ IsTopology (T₁ ∪ T₂) := by
  sorry

theorem ex7_3_iInter {ι : Type*} [Nonempty ι] {T : ι → Set (Set X)}
    (hT : ∀ i, IsTopology (T i)) : IsTopology (⋂ i, T i) := by
  sorry

/-! ## Sutherland 7.5  (HW6)
Prove that for any set X the co-finite topology (Example 7.9) does give a topology for
X. Show also that if X is finite then the co-finite topology is the discrete topology.
-/

/-- The co-finite topology: `∅` together with every set whose complement is finite. -/
def cofinite (X : Type*) : Set (Set X) := {U | U = ∅ ∨ Uᶜ.Finite}

theorem ex7_5 : IsTopology (cofinite X) := by
  sorry

theorem ex7_5_finite [Finite X] : cofinite X = univ := by
  sorry

/-! ## Sutherland 7.4  (HW7)
Prove that we get a topology for ℕ = {1, 2, 3, …} by taking the open sets to be ∅, ℕ
and {1, 2, …, n} for each n ∈ ℕ.
(`ℕ+` is the positive naturals, and `Iic n = {1, …, n}` there.)
-/

theorem ex7_4 :
    IsTopology {U : Set ℕ+ | U = ∅ ∨ U = univ ∨ ∃ n : ℕ+, U = Iic n} := by
  sorry

end TopologicalSpaces
