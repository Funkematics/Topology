import Mathlib.Topology.MetricSpace.Defs
import Topology.TopologicalSpaces

/-!
# Subspaces and product spaces (Sutherland, Chapter 10)

Homework problems on the subspace topology and the product topology.
Every `sorry` is yours to fill in.

"W open in A" for W ⊆ X is written as: the preimage of W under the inclusion
A ↪ X, i.e. `((↑) ⁻¹' W : Set A)`, is open in the subtype A.
-/

open Set Topology TopologicalSpaces

namespace SubspacesProducts

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Sutherland 10.2  (HW8, AI-free)
Let (X, 𝒯) be a topological space and let A be a non-empty subset of X. Prove that
the family 𝒯_A = {A ∩ U : U ∈ 𝒯} is a topology for A.
(As a family of subsets of the subtype `A`, `A ∩ U` is the preimage `(↑) ⁻¹' U`.)
-/

theorem ex10_2 {α : Type*} {T : Set (Set α)} (hT : IsTopology T) (A : Set α) :
    IsTopology {V : Set A | ∃ U ∈ T, V = (↑) ⁻¹' U} := by
  sorry

/-! ## Sutherland 10.4  (HW8)
Given a metric subspace (A, d_A) of a metric space (X, d), let 𝒯 be the topology on
X induced by d. Prove that the relative topology 𝒯_A induced on A by 𝒯 coincides with
the topology on A induced by the metric d_A.
-/

theorem ex10_4 {M : Type*} [MetricSpace M] (A : Set M) (W : Set A) :
    (∃ U : Set M, IsOpen U ∧ W = (↑) ⁻¹' U) ↔
      ∀ a ∈ W, ∃ ε > 0, {b : A | dist (b : M) a < ε} ⊆ W := by
  sorry

/-! ## Sutherland 10.6  (HW9)
Suppose that (A, 𝒯_A) is a subspace of a topological space (X, 𝒯) and let W ⊆ A.
(a) If W is open in A and A is open in X then W is open in X.
(b) If W is closed in A and A is closed in X then W is closed in X.
-/

theorem ex10_6a {A W : Set X} (hWA : W ⊆ A)
    (hW : IsOpen ((↑) ⁻¹' W : Set A)) (hA : IsOpen A) : IsOpen W := by
  sorry

theorem ex10_6b {A W : Set X} (hWA : W ⊆ A)
    (hW : IsClosed ((↑) ⁻¹' W : Set A)) (hA : IsClosed A) : IsClosed W := by
  sorry

/-! ## Sutherland 10.7(b)  (HW9, hint: Prop 9.5)
Suppose that f : X → Y is a map of topological spaces. Prove that f is continuous
if X = V₁ ∪ ⋯ ∪ Vₙ where each Vᵢ is a closed subset of X and f|Vᵢ is continuous
for each i. [Hint: Recall Exercise 3.13.]

The finite index set {1,…,n} is modelled by any type ι with `[Finite ι]`.
`(V i).domRestrict f` is the restriction f|Vᵢ : Vᵢ → Y.
-/

theorem ex10_7b {ι : Type*} [Finite ι] (f : X → Y) (V : ι → Set X)
    (hV : ∀ i, IsClosed (V i)) (hcov : ⋃ i, V i = univ)
    (hf : ∀ i, Continuous ((V i).domRestrict f)) : Continuous f := by
  sorry

/-! ## Sutherland 10.10  (HW9)
Suppose that X, Y are spaces with subspaces A ⊆ X, B ⊆ Y, and that f : X → Y is a
homeomorphism with f(A) = B. Prove that the maps g : A → B and h : X ∖ A → Y ∖ B
induced by f are both homeomorphisms.

"Induced by f" is recorded by the condition that g and h agree with f on points.
-/

theorem ex10_10 (f : X ≃ₜ Y) {A : Set X} {B : Set Y} (hAB : f '' A = B) :
    (∃ g : A ≃ₜ B, ∀ a, (g a : Y) = f a) ∧
    (∃ h : ↥Aᶜ ≃ₜ ↥Bᶜ, ∀ a, (h a : Y) = f a) := by
  sorry

/-! ## Sutherland 10.11  (HW9)
Suppose that X, Y are topological spaces each with the discrete topology.
Prove that the product topology for X × Y is discrete.

Stated as "every subset is open" so that Mathlib's built-in instance
(`DiscreteTopology (X × Y)`) does not prove it for you.
-/

theorem ex10_11 [DiscreteTopology X] [DiscreteTopology Y] :
    ∀ s : Set (X × Y), IsOpen s := by
  sorry

/-! ## Sutherland 10.15  (HW9)
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

/-! ## Sutherland 10.16 (i) and (ii)  (HW9, AI-free)
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

/-! ## Sutherland 10.17  (HW9)
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

end SubspacesProducts
