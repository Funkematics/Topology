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
    sorry
    

  

  

