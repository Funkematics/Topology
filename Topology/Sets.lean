import Mathlib

variable {X : Type*}
variable (A B : Set X)

--Manual construction of David's Example
example : A \ B = A ∩ Bᶜ := by
  ext x
  constructor 
  · rintro ⟨hA, hB⟩ 
    rw [Set.mem_inter_iff, Set.mem_compl_iff]
    exact ⟨hA, hB⟩
  · rintro ⟨hA, hB⟩
    rw [Set.mem_sdiff]
    rw [Set.mem_compl_iff] at hB
    exact ⟨hA, hB⟩ 

--New "Set Space" for book exercises
variable {U : Type*}
variable {C D X : Set U}

-- Sutherland 2.1
theorem S2_1 (h : C ⊆ X ∧ D ⊆ X) : (X \ C) ∩ D = D \ C := by
  ext x
  constructor
  · rintro ⟨hXC, hD⟩
    rw [Set.mem_sdiff] at hXC
    rw [Set.mem_sdiff]
    have hC : x ∉ C := by exact hXC.right
    exact ⟨hD, hC⟩
  · rintro ⟨hD, hC⟩
    rw [Set.mem_inter_iff]
    rw [Set.mem_sdiff]
    have hX : x ∈ X := h.right hD   --apply hD to h.right to get x ∈ X
    exact ⟨⟨hX, hC⟩, hD⟩

-- Sutherland 2.2
variable {U : Type*}
variable {A V X : Set U}

theorem S2_2 (h : A ⊆ X ∧ V ⊆ X) : A \ (V ∩ A) = A ∩ (X \ V) := by
  ext x
  constructor
  · rintro ⟨hA, hVA⟩
    rw [Set.mem_inter_iff]
    rw [Set.mem_sdiff]
    rw [Set.mem_inter_iff] at hVA
    push_neg at hVA
    have hV : x ∉ V := fun hxV => hVA hxV hA
    have hX : x ∈ X := h.left hA
    exact ⟨hA, hX, hV⟩
  · rintro ⟨hA, hX, hV⟩
    rw [Set.mem_sdiff]
    constructor
    · exact hA
    · rw [Set.mem_inter_iff]
      push Not
      intro hxV
      exfalso
      exact hV hxV


-- Sutherland 2.5
variable {U : Type*}
variable {U_1 U_2 V_1 V_2 X Y : Set U}

theorem S2_5 (h1 : U_1 ⊆ X ∧ U_2 ⊆ X) (h2 : V_1 ⊆ Y ∧ V_2 ⊆ Y) : (U_1 ×ˢ V_1) ∩ (U_2 ×ˢ V_2) = (U_1 ∩ U_2) ×ˢ(V_1 ∩ V_2) := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_prod]
  constructor
  · rintro ⟨⟨hxU1, hyV1⟩, ⟨hxU2, hyV2⟩⟩
    exact ⟨⟨hxU1, hxU2⟩, ⟨hyV1, hyV2⟩⟩
  · rintro ⟨⟨hxU1, hxU2⟩, ⟨hyV1, hyV2⟩⟩
    exact ⟨⟨hxU1, hyV1⟩, ⟨hxU2, hyV2⟩⟩
--Note: Hypothesis was unnecessary


--Sutherland 2.7
variable {X : Type*} (r : X → X → Prop)

def eqClass (x : X) : Set X := {y | r x y}

def eqClasses (r : X → X → Prop) : Set (Set X) := {C | ∃ x, C = eqClass r x}


theorem sUnion_eqClasses (hr : Equivalence r) :
    ⋃₀ eqClasses r = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion.mpr ⟨eqClass r x, ⟨x, rfl⟩, hr.refl x⟩

theorem eqClasses_eq_or_disjoint (hr : Equivalence r) {C C' : Set X}
  (hC : C ∈ eqClasses r) (hC' : C' ∈ eqClasses r) : C = C' ∨ C ∩ C' = ∅ := by
    obtain ⟨a, rfl⟩ := hC
    obtain ⟨b, rfl⟩ := hC'
    by_cases h : (eqClass r a ∩ eqClass r b).Nonempty
    · left
      obtain ⟨z, hza, hzb⟩ := h
      have hab : r a b := hr.trans hza (hr.symm hzb)
      ext w
      constructor
      · intro hwa
        exact hr.trans (hr.symm hab) hwa
      · intro hwb
        exact hr.trans hab hwb
    · right
      rwa [Set.not_nonempty_iff_eq_empty] at h

-- Sutherland 3.3
theorem S3_3 {X Y Z : Type*} (f : X → Y) (g : Y → Z) (U : Set Z) :
    (g ∘ f)⁻¹'U = f⁻¹'(g⁻¹'U) := by
    exact Set.preimage_comp     --via "exact?", we can unfold this for more verbosity
 --   unfold Set.preimage
 --   unfold Function.comp

--Sutherland 3.8

theorem S3_8 {X Y : Type*} (f : X → Y) (A B : Set X) :
    f '' (A \ B) = f '' A \ f '' B ↔ f '' (A \ B) ∩ f '' B = ∅ := by
      constructor
      · intro h
        rw [h]
        ext y
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
        tauto
      · intro h
        apply Set.eq_of_subset_of_subset
        · intro y hy
          sorry
       sorry

    
