import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Closure, interior and boundary (Sutherland, Chapter 9)

Homework problems on closure, interior and boundary in topological spaces.
Every `sorry` is yours to fill in.

Mathlib calls the boundary `frontier A`, defined as `closure A \ interior A`.
-/

open Set Topology

namespace ClosureInterior

variable {X : Type*} [TopologicalSpace X]

/-! ## Sutherland 9.3  (HW8)
Find open sets U, V ⊆ ℝ such that U ∩ V̄, Ū ∩ V, Ū ∩ V̄, closure (U ∩ V) are all
distinct.
-/

theorem ex9_3 : ∃ U V : Set ℝ, IsOpen U ∧ IsOpen V ∧
    [U ∩ closure V, closure U ∩ V, closure U ∩ closure V, closure (U ∩ V)].Pairwise (· ≠ ·) := by
  sorry

/-! ## Sutherland 9.4  (HW8)
Suppose X is an infinite set with the co-finite topology, and A ⊆ X. Find Ā in the
cases (a) A finite and (b) A infinite.
-/

theorem ex9_4a {α : Type*} [Infinite α] {A : Set (CofiniteTopology α)} (hA : A.Finite) :
    closure A = (sorry : Set (CofiniteTopology α)) := by
  sorry

theorem ex9_4b {α : Type*} [Infinite α] {A : Set (CofiniteTopology α)} (hA : A.Infinite) :
    closure A = (sorry : Set (CofiniteTopology α)) := by
  sorry

/-! ## Sutherland 9.6  (HW8)
(a) Let A₁, …, Aₘ be subsets of a topological space X. Prove that
    closure (⋃ Aᵢ) = ⋃ closure Aᵢ.
(b) For each i in some indexing set I let Aᵢ ⊆ X. Prove that
    ⋃ closure Aᵢ ⊆ closure (⋃ Aᵢ).
-/

theorem ex9_6a {ι : Type*} [Finite ι] (A : ι → Set X) :
    closure (⋃ i, A i) = ⋃ i, closure (A i) := by
  sorry

theorem ex9_6b {ι : Type*} (A : ι → Set X) :
    ⋃ i, closure (A i) ⊆ closure (⋃ i, A i) := by
  sorry

/-! ## Sutherland 9.12  (HW8)
Let X be a topological space and Aᵢ ⊆ X for each i in an indexing set I. Prove that
⋃ Åᵢ is contained in the interior of ⋃ Aᵢ. Give an example to show that this
containment may be strict even when only two sets are involved.
-/

theorem ex9_12 {ι : Type*} (A : ι → Set X) :
    ⋃ i, interior (A i) ⊆ interior (⋃ i, A i) := by
  sorry

theorem ex9_12_strict : ∃ A₁ A₂ : Set ℝ,
    interior A₁ ∪ interior A₂ ≠ interior (A₁ ∪ A₂) := by
  sorry

/-! ## Sutherland 9.13  (HW8)
Suppose A is a subset of a topological space X. Prove that ∂A is closed in X.
-/

theorem ex9_13 (A : Set X) : IsClosed (frontier A) := by
  sorry

/-! ## Sutherland 9.14  (HW8)
Suppose A is a subset of a topological space X. Prove that
(a) A is closed in X iff ∂A ⊆ A,
(b) ∂A = ∅ iff A is open and closed in X.
-/

theorem ex9_14a (A : Set X) : IsClosed A ↔ frontier A ⊆ A := by
  sorry

theorem ex9_14b (A : Set X) : frontier A = ∅ ↔ IsOpen A ∧ IsClosed A := by
  sorry

end ClosureInterior
