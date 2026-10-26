import Mathlib

/-!
# From images and preimages to the characteristic property of the subspace topology

A ladder of exercises. Replace each `sorry` with a proof.

* Part 1 — images and preimages as pure set theory
* Part 2 — continuity, phrased entirely through preimages
* Part 3 — build the subspace topology yourself (this is Sutherland 10.2)
* Part 4 — the characteristic property and its consequences

The bridge between Parts 1 and 3: in Mathlib a subset `A : Set X` becomes the
type `↥A` of pairs `⟨x, hx⟩`, and the inclusion `ι` is `Subtype.val : A → X`.
The paper set `A ∩ U` corresponds to the set `Subtype.val ⁻¹' U : Set A`.
So "open in A" literally means "is the preimage of an open set under the
inclusion". The subspace topology is a statement about preimages.

Useful tactics: `ext`, `intro`, `rintro`, `obtain`, `exact`, `constructor`,
`refine`, `simp only [...]`, `rw [...]`, `choose!`.
-/

open Set

namespace SubspaceLadder

/-! ## Part 1: Images and preimages -/

section Sets

variable {X Y Z : Type*}

/-- 1.1 Preimage membership is a direct check on `f x`. Hint: `Iff.rfl`. -/
example (f : X → Y) (B : Set Y) (x : X) : x ∈ f ⁻¹' B ↔ f x ∈ B := by
  constructor
  · intro hx
    unfold Set.preimage at hx
    rw [Set.mem_ofPred_eq] at hx
    exact hx
  · intro hfx
    unfold Set.preimage
    rw [Set.mem_ofPred_eq]
    exact hfx

/-- 1.2 Image membership needs a witness. Hint: also `Iff.rfl`. -/
example (f : X → Y) (A : Set X) (y : Y) : y ∈ f '' A ↔ ∃ x, x ∈ A ∧ f x = y := by
  constructor
  · intro hy
    unfold Set.image at hy
    rw [Set.mem_ofPred_eq] at hy
    obtain ⟨a, ha, hfa⟩ := hy
    exact ⟨a, ha , hfa⟩ 
  · intro h
    obtain ⟨a, ha, hfa⟩ := h
    unfold Set.image
    rw [Set.mem_ofPred_eq]
    use a



/-- 1.3 Preimage respects intersections. Hint: `ext x`, then the two sides
are definitionally equal. -/
theorem preimage_inter' (f : X → Y) (B₁ B₂ : Set Y) :
    f ⁻¹' (B₁ ∩ B₂) = f ⁻¹' B₁ ∩ f ⁻¹' B₂ := by
  sorry

/-- 1.4 Preimage respects arbitrary unions.
Hint: `ext x; simp only [mem_preimage, mem_iUnion]`. -/
theorem preimage_iUnion' {ι : Type*} (f : X → Y) (B : ι → Set Y) :
    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

/-- 1.5 Preimage respects complements. -/
theorem preimage_compl' (f : X → Y) (B : Set Y) : f ⁻¹' Bᶜ = (f ⁻¹' B)ᶜ := by
  sorry

/-- 1.6 Images only give an inclusion for intersections.
Hint: `rintro y ⟨x, ⟨h₁, h₂⟩, rfl⟩`. -/
theorem image_inter_subset' (f : X → Y) (A₁ A₂ : Set X) :
    f '' (A₁ ∩ A₂) ⊆ f '' A₁ ∩ f '' A₂ := by
  sorry

/-- 1.7 ... and equality really can fail: use a constant map on `{0}` and `{1}`.
Hint: `0` lies in the right-hand side; `Set.ext_iff` turns the equation into
a membership statement about the left-hand side, which you can then destruct. -/
example : ∃ A₁ A₂ : Set ℕ,
    (fun _ : ℕ => (0 : ℕ)) '' (A₁ ∩ A₂) ≠
      ((fun _ : ℕ => (0 : ℕ)) '' A₁) ∩ ((fun _ : ℕ => (0 : ℕ)) '' A₂) := by
  sorry

/-- 1.8 Pushing forward a pullback lands inside the original set. -/
theorem image_preimage_subset' (f : X → Y) (B : Set Y) : f '' (f ⁻¹' B) ⊆ B := by
  sorry

/-- 1.9 Pulling back a pushforward contains the original set. -/
theorem subset_preimage_image' (f : X → Y) (A : Set X) : A ⊆ f ⁻¹' (f '' A) := by
  sorry

/-- 1.10 The adjunction between image and preimage: the single most useful
fact about them. -/
theorem image_subset_iff' (f : X → Y) (A : Set X) (B : Set Y) :
    f '' A ⊆ B ↔ A ⊆ f ⁻¹' B := by
  sorry

/-- 1.11 Preimage of a composition. This is what makes Part 4 work.
Hint: `rfl`. -/
theorem preimage_comp' (f : X → Y) (g : Y → Z) (C : Set Z) :
    (g ∘ f) ⁻¹' C = f ⁻¹' (g ⁻¹' C) := by
  sorry

end Sets

/-! ## Part 2: Continuity through preimages

Mathlib's `continuous_def` says
`Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)`.
Use it to prove these from scratch; don't use `Continuous.comp` etc. -/

section Continuity

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 2.1 Composition of continuous maps. Hint: `rw [continuous_def] at hf hg ⊢`,
then use 1.11 (definitionally). -/
theorem comp' {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  sorry

/-- 2.2 The identity is continuous. -/
theorem id' : Continuous (fun x : X => x) := by
  sorry

/-- 2.3 Constant maps are continuous: every preimage is `univ` or `∅`.
Hint: `by_cases h : y ∈ U`, and in each case prove the preimage equals
`univ` or `∅` with `ext x; simp [h]`. -/
theorem const' (y : Y) : Continuous (fun _ : X => y) := by
  sorry

end Continuity

/-! ## Part 3: Build the subspace topology (Sutherland 10.2)

Open sets of `A` are the preimages of open sets of `X` under the inclusion. -/

section Build

variable {X : Type*} [TopologicalSpace X]

/-- 3.1 Translation back to paper: pushing a preimage forward recovers
`A ∩ U`. So `Subtype.val ⁻¹' U` really is "A ∩ U, viewed inside A". -/
theorem image_val_preimage_val (A : Set X) (U : Set X) :
    Subtype.val '' (Subtype.val ⁻¹' U : Set A) = A ∩ U := by
  sorry

/-- 3.2 The subspace topology, built by hand.

Hints:
* `isOpen_univ`: `univ` is the preimage of `univ`.
* `isOpen_inter`: `rintro _ _ ⟨U₁, h₁, rfl⟩ ⟨U₂, h₂, rfl⟩`, then use 1.3.
* `isOpen_sUnion`: after `intro S hS`, the hypothesis says each `t ∈ S`
  comes from *some* open `U`. Use
  `choose! U hU hUV using hS`
  to pick one for every `t` at once (this is the axiom of choice from the
  paper proof). Then use `⋃ t ∈ S, U t` and `isOpen_biUnion`.
  If `choose!` can't see the `∃`, first do
  `change ∀ t ∈ S, ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = t at hS`. -/
def subspace (A : Set X) : TopologicalSpace A where
  IsOpen V := ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = V
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 3.3 Your topology is the same as Mathlib's.
Hint: try `rfl`. -/
example (A : Set X) : subspace A = (inferInstance : TopologicalSpace A) := by
  sorry

end Build

/-! ## Part 4: The characteristic property

From here on, use Mathlib's subspace topology on `↥A`. The key lemma is
`isOpen_induced_iff`, which unpacks "open in A" exactly as in Part 3. -/

section Characteristic

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 4.1 Open in `A` means: preimage of an open set under the inclusion. -/
example (A : Set X) (V : Set A) :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = V := by
  sorry

/-- 4.2 The inclusion is continuous.
Hint: `rw [continuous_def]; intro U hU; exact isOpen_induced_iff.mpr ⟨U, hU, rfl⟩`
— but try it yourself first. -/
theorem continuous_incl (A : Set X) : Continuous (Subtype.val : A → X) := by
  sorry

/-- 4.3 **The characteristic property.**
A map into a subspace is continuous iff it is continuous into the whole space.

Hint for `←`: take `V` open in `A`, use `obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hV`,
and notice that `g ⁻¹' (Subtype.val ⁻¹' U)` is `(Subtype.val ∘ g) ⁻¹' U` by 1.11. -/
theorem char_prop (A : Set X) (g : Z → A) :
    Continuous g ↔ Continuous (Subtype.val ∘ g) := by
  sorry

/-- 4.4 Restricting the domain. `A.restrict f` is `f ∘ Subtype.val`. -/
theorem restrict_continuous (A : Set X) {f : X → Y} (hf : Continuous f) :
    Continuous (A.restrict f) := by
  sorry

/-- 4.5 Restricting the codomain. Hint: `rw [char_prop]` and you are nearly done. -/
theorem codRestrict_continuous (B : Set Y) {f : Z → Y} (hf : Continuous f)
    (h : ∀ z, f z ∈ B) : Continuous (fun z => (⟨f z, h z⟩ : B)) := by
  sorry

/-- The unit circle as a subset of `ℝ × ℝ`. -/
def circle : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- 4.6 The standard parametrization is continuous *into the circle*,
without ever looking at open arcs.
Hints: membership is `by simp [circle, Real.cos_sq_add_sin_sq]`;
continuity into `ℝ × ℝ` is `by fun_prop`; then apply 4.5. -/
theorem wrap_continuous :
    Continuous (fun t : ℝ =>
      (⟨(Real.cos t, Real.sin t), by simp [circle, Real.cos_sq_add_sin_sq]⟩ : circle)) := by
  sorry

end Characteristic

end SubspaceLadder
