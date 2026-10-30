import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Continuity and bases (Sutherland, Chapter 8)

Homework problems on continuous maps, homeomorphisms and bases of topological
spaces. Every `sorry` is yours to fill in.
-/

open Set Filter Topology

namespace Continuity

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ## Sutherland 8.2  (HW7)
Prove that a map f : X → Y of topological spaces is continuous iff it is continuous
at every point of X.
-/

/-- Sutherland's continuity at a point: every open `V ∋ f a` contains `f(U)` for some
open `U ∋ a`. -/
def ContinuousAtPt (f : X → Y) (a : X) : Prop :=
  ∀ V, IsOpen V → f a ∈ V → ∃ U, IsOpen U ∧ a ∈ U ∧ f '' U ⊆ V

theorem ex8_2 (f : X → Y) : Continuous f ↔ ∀ a, ContinuousAtPt f a := by
  sorry

/-! ## Sutherland 8.3  (HW7)
Let 𝕊 be the Sierpinski space of Example 7.7. For A ⊆ X let χ_A : X → {0, 1} be its
characteristic function. Prove that A is open in X iff χ_A : X → 𝕊 is continuous.

Mathlib's `Prop` carries the Sierpinski topology (the open sets are ∅, {True} and
univ), so `True` plays the role of 1 and χ_A is `x ↦ x ∈ A`.
-/

theorem ex8_3 (A : Set X) : IsOpen A ↔ Continuous fun x ↦ x ∈ A := by
  sorry

/-! ## Sutherland 8.4  (HW7)
Prove that equivalence (homeomorphism) of topological spaces is an equivalence
relation.
-/

theorem ex8_4_refl : Nonempty (X ≃ₜ X) := by
  sorry

theorem ex8_4_symm : Nonempty (X ≃ₜ Y) → Nonempty (Y ≃ₜ X) := by
  sorry

theorem ex8_4_trans : Nonempty (X ≃ₜ Y) → Nonempty (Y ≃ₜ Z) → Nonempty (X ≃ₜ Z) := by
  sorry

/-! ## Open bijections  (HW7 #5)
Suppose f : X → Y is a bijection between topological spaces. Show that the following
are equivalent:
* for all sets A ⊆ X, A is open if and only if f(A) is open,
* the functions f and f⁻¹ are continuous.
-/

theorem hw7_5 (f : X ≃ Y) :
    (∀ A : Set X, IsOpen A ↔ IsOpen (f '' A)) ↔ Continuous f ∧ Continuous f.symm := by
  sorry

/-! ## ℝ is homeomorphic to the parabola  (HW7 #6)
Let X = ℝ and let Y be the subset of ℝ² of points (x, x²). The d₁ distance on ℝ²
determines a distance on Y. Show that X and Y are homeomorphic as follows.
(a) Show that if xₙ → x in ℝ then (xₙ, xₙ²) → (x, x²) in Y.
(b) What can you conclude about the map g : X → Y, g(x) = (x, x²)?
(c) Show that if (aₙ, bₙ) is a sequence in Y converging to (a, b) then the sequence
    also converges in ℝ².
(d) Using that the projection π₁ : ℝ² → ℝ is continuous, use part (c) to show that
    π₁|_Y is also continuous.
(e) Now find an argument to show that X and Y are homeomorphic.

(Mathlib's metric on ℝ × ℝ is d_∞ rather than d₁; both give the same topology.)
-/

/-- The parabola `Y = {(x, x²)}` as a subspace of `ℝ²`. -/
def parabola : Set (ℝ × ℝ) := {p | p.2 = p.1 ^ 2}

/-- The map `g(x) = (x, x²)`. -/
def g (x : ℝ) : parabola := ⟨(x, x ^ 2), rfl⟩

theorem hw7_6a {x : ℕ → ℝ} {a : ℝ} (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (g ∘ x) atTop (𝓝 (g a)) := by
  sorry

/-- (b): state what you can conclude about `g` in place of the `sorry`. -/
theorem hw7_6b : (sorry : Prop) := by
  sorry

theorem hw7_6c {p : ℕ → parabola} {q : parabola} (hp : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun n ↦ (p n : ℝ × ℝ)) atTop (𝓝 (q : ℝ × ℝ)) := by
  sorry

theorem hw7_6d : Continuous fun p : parabola ↦ (p : ℝ × ℝ).1 := by
  sorry

theorem hw7_6e : Nonempty (ℝ ≃ₜ parabola) := by
  sorry

/-! ## Sutherland 8.5  (HW7, AI-free)
Prove that the set of all open intervals {(a, b) : a, b ∈ ℝ, a < b} is a basis for the
usual topology on ℝ.
-/

theorem ex8_5 :
    TopologicalSpace.IsTopologicalBasis {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b} := by
  sorry

/-! ## Sutherland 8.6  (HW7)
Prove that a real-valued function f : X → ℝ on a space X is continuous iff for any
x ∈ ℝ the sets f⁻¹(x, ∞) and f⁻¹(-∞, x) are both open in X.
Hint: note that (a, b) = (-∞, b) ∩ (a, ∞).
-/

theorem ex8_6 (f : X → ℝ) :
    Continuous f ↔ ∀ x : ℝ, IsOpen (f ⁻¹' Ioi x) ∧ IsOpen (f ⁻¹' Iio x) := by
  sorry

end Continuity
