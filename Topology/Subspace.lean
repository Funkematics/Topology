/-
  Math F404 — Homework 9 (Sutherland, Chapter 10: Subspaces and product spaces)
  Lean 4 / Mathlib skeleton. Every `sorry` is yours to fill in.

  Note: written against current Mathlib but not compiled here. If a lemma name
  fails, put the cursor on the goal and try `exact?` / `apply?`.
-/
import Mathlib

open Set Topology

namespace HW9

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Sutherland 10.6
Suppose that (A, 𝒯_A) is a subspace of a topological space (X, 𝒯) and let W ⊆ A.
(a) If W is open in A and A is open in X then W is open in X.
(b) If W is closed in A and A is closed in X then W is closed in X.

"W open in A" for W ⊆ X is written as: the preimage of W under the
inclusion A ↪ X, i.e. `((↑) ⁻¹' W : Set A)`, is open in the subtype A.
-/

theorem ex10_6a {A W : Set X} (hWA : W ⊆ A)
    (hW : IsOpen ((↑) ⁻¹' W : Set A)) (hA : IsOpen A) : IsOpen W := by
  sorry

theorem ex10_6b {A W : Set X} (hWA : W ⊆ A)
    (hW : IsClosed ((↑) ⁻¹' W : Set A)) (hA : IsClosed A) : IsClosed W := by
  sorry

/-! ## Sutherland 10.7(b)   (instructor hint: Prop 9.5)
Suppose that f : X → Y is a map of topological spaces. Prove that f is continuous
if X = V₁ ∪ ⋯ ∪ Vₙ where each Vᵢ is a closed subset of X and f|Vᵢ is continuous
for each i.

The finite index set {1,…,n} is modelled by any type ι with `[Finite ι]`.
`(V i).restrict f` is the restriction f|Vᵢ : Vᵢ → Y.
-/

theorem ex10_7b {ι : Type*} [Finite ι] (f : X → Y) (V : ι → Set X)
    (hV : ∀ i, IsClosed (V i)) (hcov : ⋃ i, V i = univ)
    (hf : ∀ i, Continuous ((V i).restrict f)) : Continuous f := by
  sorry

/-! ## Sutherland 10.10
Suppose that X, Y are spaces with subspaces A ⊆ X, B ⊆ Y, and that f : X → Y is a
homeomorphism with f(A) = B. Prove that the maps g : A → B and h : X ∖ A → Y ∖ B
induced by f are both homeomorphisms.

"Induced by f" is recorded by the condition that g and h agree with f on points.
-/

theorem ex10_10 (f : X ≃ₜ Y) {A : Set X} {B : Set Y} (hAB : f '' A = B) :
    (∃ g : A ≃ₜ B, ∀ a, (g a : Y) = f a) ∧
    (∃ h : ↥Aᶜ ≃ₜ ↥Bᶜ, ∀ a, (h a : Y) = f a) := by
  sorry

/-! ## Sutherland 10.11
Suppose that X, Y are topological spaces each with the discrete topology.
Prove that the product topology for X × Y is discrete.

Stated as "every subset is open" so that Mathlib's built-in instance
(`DiscreteTopology (X × Y)`) does not prove it for you.
-/

theorem ex10_11 [DiscreteTopology X] [DiscreteTopology Y] :
    ∀ s : Set (X × Y), IsOpen s := by
  sorry

/-! ## Sutherland 10.15
(a) Prove that if W is open in a topological product X × Y then p_X(W) is open
    in X and p_Y(W) is open in Y.
(b) Give an example of a closed set W ⊆ ℝ × ℝ whose projection p₁(W) on the
    x-axis is not closed in ℝ.
-/

theorem ex10_15a {W : Set (X × Y)} (hW : IsOpen W) :
    IsOpen (Prod.fst '' W) ∧ IsOpen (Prod.snd '' W) := by
  sorry

theorem ex10_15b :
    ∃ W : Set (ℝ × ℝ), IsClosed W ∧ ¬ IsClosed (Prod.fst '' W) := by
  sorry

/-! ## Sutherland 10.16 (i) and (ii)   (AI Free)
Suppose that X, Y are spaces and that A ⊆ X, B ⊆ Y. Prove that
(i)  the interior of A × B is Å × B̊,
(ii) the closure of A × B is Ā × B̄.
-/

theorem ex10_16_i (A : Set X) (B : Set Y) :
    interior (A ×ˢ B) = interior A ×ˢ interior B := by
  sorry

theorem ex10_16_ii (A : Set X) (B : Set Y) :
    closure (A ×ˢ B) = closure A ×ˢ closure B := by
  sorry

/-! ## Sutherland 10.17
Suppose that X × X is the topological product of a space X with itself. Prove that
the map t : X × X → X × X defined by t(x, x') = (x', x) is a homeomorphism.
-/

def ex10_17 : X × X ≃ₜ X × X where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by sorry
  right_inv := by sorry
  continuous_toFun := by sorry
  continuous_invFun := by sorry

end HW9
