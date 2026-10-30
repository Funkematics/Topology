import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.NumberTheory.Real.Irrational

/-!
# Real analysis (Sutherland, Chapter 4)

Homework problems on suprema, sequences, limits and continuity of real functions.
Every `sorry` is yours to fill in.

The course's ε–N and ε–δ definitions are spelled out below so that "prove it
directly from the definition" means what it says. `seqLim_iff_tendsto` connects
`SeqLim` to Mathlib's `Tendsto`, in case you want library results such as the
monotone convergence theorem (`tendsto_atTop_ciInf`).
-/

open Set Filter Topology

namespace RealAnalysis

/-- `x n → ℓ`: for every ε > 0 there is N with |xₙ - ℓ| < ε for all n ≥ N. -/
def SeqLim (x : ℕ → ℝ) (ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n - ℓ| < ε

/-- `(xₙ)` is Cauchy: for every ε > 0 there is N with |xₙ - xₘ| < ε for all m, n ≥ N. -/
def IsCauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |x n - x m| < ε

/-- `a` is a limit point of `Ω`: every punctured δ-neighbourhood of `a` meets `Ω`. -/
def LimitPoint (Ω : Set ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, ∃ x ∈ Ω, 0 < |x - a| ∧ |x - a| < δ

/-- Definition 4.21: `lim_{x → a} f(x) = ℓ` for `f` defined on `Ω`. -/
def FunLim (Ω : Set ℝ) (f : ℝ → ℝ) (a ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Ω, 0 < |x - a| → |x - a| < δ → |f x - ℓ| < ε

/-- `f` is continuous at `a` (ε–δ). -/
def ContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

theorem seqLim_iff_tendsto (x : ℕ → ℝ) (ℓ : ℝ) :
    SeqLim x ℓ ↔ Tendsto x atTop (𝓝 ℓ) := by
  simp [SeqLim, Metric.tendsto_atTop, Real.dist_eq]

/-! ## Nested open intervals  (HW1 #5)
Give examples of collections of open intervals Iᵢ = (aᵢ, bᵢ), i ∈ ℕ, such that
(a) ⋂ Iᵢ = [0, 1]   (give a formal proof)
(b) ⋂ Iᵢ = (0, 1)
(c) ⋂ Iᵢ = (0, 1]
-/

theorem hw1_5a : ∃ a b : ℕ → ℝ, ⋂ i, Ioo (a i) (b i) = Icc 0 1 := by
  sorry

theorem hw1_5b : ∃ a b : ℕ → ℝ, ⋂ i, Ioo (a i) (b i) = Ioo 0 1 := by
  sorry

theorem hw1_5c : ∃ a b : ℕ → ℝ, ⋂ i, Ioo (a i) (b i) = Ioc 0 1 := by
  sorry

/-! ## Sutherland 4.1  (HW2)
Show that if ∅ ≠ A ⊆ B ⊆ ℝ and B is bounded above then A is bounded above and
sup A ≤ sup B.
-/

theorem ex4_1 {A B : Set ℝ} (hA : A.Nonempty) (hAB : A ⊆ B) (hB : BddAbove B) :
    BddAbove A ∧ sSup A ≤ sSup B := by
  sorry

/-! ## Sutherland 4.2  (HW2)
Show that if A and B are non-empty subsets of ℝ which are bounded above then A ∪ B
is bounded above and sup (A ∪ B) = max {sup A, sup B}.
-/

theorem ex4_2 {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA' : BddAbove A) (hB' : BddAbove B) :
    BddAbove (A ∪ B) ∧ sSup (A ∪ B) = max (sSup A) (sSup B) := by
  sorry

/-! ## Approximating the supremum  (HW2 #3, AI-free)
Let A ⊂ ℝ be non-empty and bounded above, and let m = sup A. Show that for every
ε > 0 there exists a ∈ A with m - ε < a ≤ m.
-/

theorem hw2_3 {A : Set ℝ} (hA : A.Nonempty) (hA' : BddAbove A) :
    ∀ ε > 0, ∃ a ∈ A, sSup A - ε < a ∧ a ≤ sSup A := by
  sorry

/-! ## Shifting and scaling limits  (HW2 #4)
Suppose (xₙ) converges to x.
(a) Show that (xₙ₊₁) converges to the same limit.
(b) Show that if c ∈ ℝ then (c xₙ) converges to c x.
-/

theorem hw2_4a {x : ℕ → ℝ} {ℓ : ℝ} (h : SeqLim x ℓ) : SeqLim (fun n ↦ x (n + 1)) ℓ := by
  sorry

theorem hw2_4b {x : ℕ → ℝ} {ℓ : ℝ} (c : ℝ) (h : SeqLim x ℓ) :
    SeqLim (fun n ↦ c * x n) (c * ℓ) := by
  sorry

/-! ## Limits of geometric sequences  (HW2 #5)
Suppose a ∈ ℝ and aⁿ → L. Use the previous problem to show that either L = 0 or
a = 1 (in which case L = 1).
-/

theorem hw2_5 {a L : ℝ} (h : SeqLim (fun n ↦ a ^ n) L) : L = 0 ∨ (a = 1 ∧ L = 1) := by
  sorry

/-! ## aⁿ → 0  (HW2 #6)
Suppose 0 < a < 1. Use the monotone convergence theorem to show aⁿ → 0.
Hint: the previous problem could be helpful.
-/

theorem hw2_6 {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) : SeqLim (fun n ↦ a ^ n) 0 := by
  sorry

/-! ## Irrationals  (HW2 #7)
(a) Knowing that √2 is irrational, show that q√2 is irrational for all q ∈ ℚ.
    (This is false for q = 0, so we assume q ≠ 0.)
(b) Sutherland 4.8: between any two distinct real numbers there is an irrational.
    Hint: consider a/√2 and b/√2 as endpoints first.
-/

theorem hw2_7a {q : ℚ} (hq : q ≠ 0) : Irrational (q * √2) := by
  sorry

theorem ex4_8 {a b : ℝ} (hab : a < b) : ∃ x, Irrational x ∧ a < x ∧ x < b := by
  sorry

/-! ## (-1)ⁿ is not Cauchy  (HW2 #8)
Show directly from the definition that xₙ = (-1)ⁿ is not Cauchy and conclude that it
does not converge.
-/

theorem hw2_8_not_cauchy : ¬ IsCauchy (fun n ↦ (-1 : ℝ) ^ n) := by
  sorry

theorem hw2_8_not_convergent : ¬ ∃ ℓ, SeqLim (fun n ↦ (-1 : ℝ) ^ n) ℓ := by
  sorry

/-! ## Sutherland 4.12  (HW2)
Give an example where f(x) → b as x → a and g(y) → c as y → b, but g(f(x)) ↛ c as
x → a. Hint: assume f and g are defined on all of ℝ, and take f to be really boring.
-/

theorem ex4_12 : ∃ (f g : ℝ → ℝ) (a b c : ℝ),
    FunLim univ f a b ∧ FunLim univ g b c ∧ ¬ FunLim univ (g ∘ f) a c := by
  sorry

/-! ## Reciprocals of limits  (HW3 #1)
Suppose (xₙ) is a real sequence and xₙ → ℓ > 0. Show that there exists N so that if
n ≥ N then xₙ > ℓ/2. Then show 1/xₙ → 1/ℓ.
(In Lean 1/0 = 0, so 1/xₙ is defined for every n; only the tail matters anyway.)
-/

theorem hw3_1a {x : ℕ → ℝ} {ℓ : ℝ} (h : SeqLim x ℓ) (hℓ : 0 < ℓ) :
    ∃ N, ∀ n ≥ N, ℓ / 2 < x n := by
  sorry

theorem hw3_1b {x : ℕ → ℝ} {ℓ : ℝ} (h : SeqLim x ℓ) (hℓ : 0 < ℓ) :
    SeqLim (fun n ↦ 1 / x n) (1 / ℓ) := by
  sorry

/-! ## Sequential characterization of limits  (HW3 #2)
Suppose Ω ⊆ ℝ, that a is a limit point of Ω, and that f : Ω → ℝ. Show that
lim_{x → a} f(x) = ℓ if and only if whenever (xₙ) is a sequence in Ω ∖ {a}
converging to a, f(xₙ) → ℓ.
-/

theorem hw3_2 {Ω : Set ℝ} {a ℓ : ℝ} (f : ℝ → ℝ) (ha : LimitPoint Ω a) :
    FunLim Ω f a ℓ ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ Ω \ {a}) → SeqLim x a → SeqLim (f ∘ x) ℓ := by
  sorry

/-! ## Sutherland 4.13  (HW3)
(a) Prove that for any y, z ∈ ℝ,
    max {y, z} = ½(y + z + |y - z|),  min {y, z} = ½(y + z - |y - z|).
(b) Given that f, g : ℝ → ℝ are continuous at a, prove that h and k are continuous
    at a, where h(x) = max {f(x), g(x)} and k(x) = min {f(x), g(x)}.
-/

theorem ex4_13a (y z : ℝ) :
    max y z = (y + z + |y - z|) / 2 ∧ min y z = (y + z - |y - z|) / 2 := by
  sorry

theorem ex4_13b {f g : ℝ → ℝ} {a : ℝ} (hf : ContAt f a) (hg : ContAt g a) :
    ContAt (fun x ↦ max (f x) (g x)) a ∧ ContAt (fun x ↦ min (f x) (g x)) a := by
  sorry

/-! ## Sutherland 4.14 (listed as "4.1" on HW3, AI-free)
Let f, g : ℝ ∖ {0} → ℝ be f(x) = x sin(1/x), g(x) = sin(1/x).
Prove that lim_{x → 0} f(x) = 0, while lim_{x → 0} g(x) does not exist.
-/

theorem ex4_14_f : FunLim {x | x ≠ 0} (fun x ↦ x * Real.sin (1 / x)) 0 0 := by
  sorry

theorem ex4_14_g : ¬ ∃ ℓ, FunLim {x | x ≠ 0} (fun x ↦ Real.sin (1 / x)) 0 ℓ := by
  sorry

/-! ## Sutherland 4.15  (HW3)
Let f : ℝ → ℝ be f(x) = 0 for x ∈ ℚ and f(x) = 1 for x ∉ ℚ.
Show that f is not continuous at any point of ℝ.
-/

open Classical in
/-- The indicator function of the irrationals. -/
noncomputable def dirichlet (x : ℝ) : ℝ := if Irrational x then 1 else 0

theorem ex4_15 (a : ℝ) : ¬ ContAt dirichlet a := by
  sorry

/-! ## A limit from the definition  (HW3 #6)
Use Definition 4.21 and no more advanced tools to directly show
lim_{x → 2} 1/(x² + 1) = 1/5: start with "let ε > 0", exhibit a candidate δ, and
show that it works.
-/

theorem hw3_6 : FunLim univ (fun x ↦ 1 / (x ^ 2 + 1)) 2 (1 / 5) := by
  sorry

/-! ## Convergence via the distance  (HW3 #7)
For x, y ∈ ℝ define d(x, y) = |y - x|. Show that a sequence of real numbers (xₙ)
converges to ℓ if and only if d(xₙ, ℓ) → 0.
-/

theorem hw3_7 (x : ℕ → ℝ) (ℓ : ℝ) : SeqLim x ℓ ↔ SeqLim (fun n ↦ |ℓ - x n|) 0 := by
  sorry

end RealAnalysis
