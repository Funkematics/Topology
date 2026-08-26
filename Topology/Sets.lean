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

--First Exercise
example  (h : C ⊆ X ∧ D ⊆ X) : (X \ C) ∩ D = D \ C := by
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
    sorry

