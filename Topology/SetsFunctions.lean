import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sets and functions (Sutherland, Chapters 2–3)

Homework problems on set algebra, equivalence relations, images and preimages.
Every `sorry` is yours to fill in.

For "describe the set" problems the right-hand side is a `(sorry : Set _)`
placeholder: replace it with your answer, then prove the equality.
-/

open Set Function

namespace SetsFunctions

variable {α β γ : Type*}

/-! ## Sutherland 2.1  (HW1)
Suppose that C, D are subsets of a set X. Prove that (X ∖ C) ∩ D = D ∖ C.
-/

theorem ex2_1 {X C D : Set α} (hC : C ⊆ X) (hD : D ⊆ X) :
    (X \ C) ∩ D = D \ C := by
  sorry

/-! ## Sutherland 2.2  (HW1)
Suppose that A, V are subsets of a set X. Prove that A ∖ (V ∩ A) = A ∩ (X ∖ V).
-/

theorem ex2_2 {X A V : Set α} (hA : A ⊆ X) (hV : V ⊆ X) :
    A \ (V ∩ A) = A ∩ (X \ V) := by
  sorry

/-! ## Sutherland 2.5  (HW1, AI-free)
Suppose that U₁, U₂ are subsets of a set X and that V₁, V₂ are subsets of a set Y.
Prove that (U₁ × V₁) ∩ (U₂ × V₂) = (U₁ ∩ U₂) × (V₁ ∩ V₂).
-/

theorem ex2_5 (U₁ U₂ : Set α) (V₁ V₂ : Set β) :
    (U₁ ×ˢ V₁) ∩ (U₂ ×ˢ V₂) = (U₁ ∩ U₂) ×ˢ (V₁ ∩ V₂) := by
  sorry

/-! ## Sutherland 2.7  (HW1)
Suppose ∼ is an equivalence relation on a set X. Show that the equivalence classes
partition X: if 𝒞 is the collection of equivalence classes then ⋃_{C ∈ 𝒞} C = X,
and if C, C' ∈ 𝒞 then either C = C' or C ∩ C' = ∅.
-/

/-- The equivalence class of `x` under `r`. -/
def eqClass (r : α → α → Prop) (x : α) : Set α := {y | r x y}

/-- The collection `𝒞` of all equivalence classes of `r`. -/
def eqClasses (r : α → α → Prop) : Set (Set α) := range (eqClass r)

theorem ex2_7_sUnion {r : α → α → Prop} (hr : Equivalence r) :
    ⋃₀ eqClasses r = univ := by
  sorry

theorem ex2_7_eq_or_disjoint {r : α → α → Prop} (hr : Equivalence r) {C C' : Set α}
    (hC : C ∈ eqClasses r) (hC' : C' ∈ eqClasses r) : C = C' ∨ C ∩ C' = ∅ := by
  sorry

/-! ## Sutherland 3.2  (HW1, no formal proof needed)
Let f : ℝ → ℝ be f(x) = sin x. Describe the sets
f([0, π/2]), f([0, ∞)), f⁻¹([0, 1]), f⁻¹([0, 1/2]), f⁻¹([-1, 1]).
-/

theorem ex3_2a : Real.sin '' Icc 0 (Real.pi / 2) = (sorry : Set ℝ) := by
  sorry

theorem ex3_2b : Real.sin '' Ici 0 = (sorry : Set ℝ) := by
  sorry

theorem ex3_2c : Real.sin ⁻¹' Icc 0 1 = (sorry : Set ℝ) := by
  sorry

theorem ex3_2d : Real.sin ⁻¹' Icc 0 (1 / 2) = (sorry : Set ℝ) := by
  sorry

theorem ex3_2e : Real.sin ⁻¹' Icc (-1) 1 = (sorry : Set ℝ) := by
  sorry

/-! ## Sutherland 3.3  (HW1)
Suppose that f : X → Y and g : Y → Z are maps and U ⊆ Z. Prove that
(g ∘ f)⁻¹(U) = f⁻¹(g⁻¹(U)).
-/

theorem ex3_3 (f : α → β) (g : β → γ) (U : Set γ) :
    (g ∘ f) ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  sorry

/-! ## Sutherland 3.4  (HW1)
Let f : ℝ → ℝ² be f(x) = (x, 2x). Describe the sets
f([0, 1]), f⁻¹([0, 1] × [0, 1]), f⁻¹(D) where D = {(x, y) ∈ ℝ² : x² + y² ≤ 1}.
-/

/-- The map `x ↦ (x, 2x)`. -/
def f3_4 (x : ℝ) : ℝ × ℝ := (x, 2 * x)

/-- The closed unit disc. -/
def disc : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

theorem ex3_4a : f3_4 '' Icc 0 1 = (sorry : Set (ℝ × ℝ)) := by
  sorry

theorem ex3_4b : f3_4 ⁻¹' (Icc 0 1 ×ˢ Icc 0 1) = (sorry : Set ℝ) := by
  sorry

theorem ex3_4c : f3_4 ⁻¹' disc = (sorry : Set ℝ) := by
  sorry

/-! ## Sutherland 3.8  (HW1, make your proof as short as possible)
Let f : X → Y be a map and let A, B be subsets of X. Prove that
f(A ∖ B) = f(A) ∖ f(B) if and only if f(A ∖ B) ∩ f(B) = ∅.
Deduce that if f is injective then f(A ∖ B) = f(A) ∖ f(B).
-/

theorem ex3_8 (f : α → β) (A B : Set α) :
    f '' (A \ B) = f '' A \ f '' B ↔ f '' (A \ B) ∩ f '' B = ∅ := by
  sorry

theorem ex3_8_injective {f : α → β} (hf : Injective f) (A B : Set α) :
    f '' (A \ B) = f '' A \ f '' B := by
  sorry

end SetsFunctions
