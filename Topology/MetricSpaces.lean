import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

/-!
# Metric spaces (Sutherland, Chapters 5–6)

Homework problems on balls, boundedness, open and closed sets, closure, interior and
boundary in metric spaces. Every `sorry` is yours to fill in.

Mathlib's `Metric.ball x r` is the open ball `{y | dist y x < r}`. For problems
about a specific metric (discrete, d₁, d₂, d_∞) that metric is written out below
as a plain function, together with the matching notions of ball, open set and
convergent sequence.

Several statements here are already Mathlib lemmas; the point is to prove them by
hand, e.g. via `Metric.isOpen_iff` or `Metric.mem_closure_iff`.
-/

open Set Filter Topology Metric

namespace MetricSpaces

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-! ### Notions relative to an explicit distance function -/

/-- The open ball of radius `ε` about `x` for the distance function `d`. -/
def ballWrt {α : Type*} (d : α → α → ℝ) (x : α) (ε : ℝ) : Set α := {y | d x y < ε}

/-- `U` is open for the distance function `d`. -/
def IsOpenWrt {α : Type*} (d : α → α → ℝ) (U : Set α) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ballWrt d x ε ⊆ U

/-- `xₙ → a` for the distance function `d`. -/
def ConvergesWrt {α : Type*} (d : α → α → ℝ) (x : ℕ → α) (a : α) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d (x n) a < ε

/-! ## Sutherland 5.1  (HW3)
Given points x, y, z in a metric space (X, d), prove that |d(x, z) - d(y, z)| ≤ d(x, y).
-/

theorem ex5_1 (x y z : X) : |dist x z - dist y z| ≤ dist x y := by
  sorry

/-! ## Distance to a point is continuous  (HW4 #1)
Use Sutherland 5.1 to prove: if X is a metric space and x₀ ∈ X then f : X → ℝ,
f(x) = d(x, x₀), is continuous.
-/

theorem hw4_1 (x₀ : X) : Continuous fun x ↦ dist x x₀ := by
  sorry

/-! ## Sutherland 5.5  (HW4)
Suppose x, y are distinct points in a metric space (X, d) and let ε = d(x, y)/2.
Prove that B_ε(x) and B_ε(y) are disjoint.
-/

theorem ex5_5 {x y : X} (hxy : x ≠ y) :
    Disjoint (ball x (dist x y / 2)) (ball y (dist x y / 2)) := by
  sorry

/-! ## Sutherland 5.6  (HW4)
Suppose x, y are points in a metric space and ε > 0. Show that if y ∈ B_{ε/2}(x)
then B_{ε/2}(y) ⊆ B_ε(x).
-/

theorem ex5_6 {x y : X} {ε : ℝ} (hε : 0 < ε) (hy : y ∈ ball x (ε / 2)) :
    ball y (ε / 2) ⊆ ball x ε := by
  sorry

/-! ## Sutherland 5.8  (HW4)
Suppose (X, d) is a metric space and A ⊆ X. Show that A is bounded (contained in some
ball) iff there is some constant Δ such that d(a, a') ≤ Δ for all a, a' ∈ A.
-/

theorem ex5_8 [Nonempty X] (A : Set X) :
    (∃ x₀ r, A ⊆ ball x₀ r) ↔ ∃ Δ, ∀ a ∈ A, ∀ a' ∈ A, dist a a' ≤ Δ := by
  sorry

/-! ## Sutherland 5.10  (HW4)
Prove that if A, B are bounded subsets of a metric space and A ∩ B ≠ ∅ then
diam (A ∪ B) ≤ diam A + diam B.
-/

theorem ex5_10 {A B : Set X} (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    (hAB : (A ∩ B).Nonempty) : diam (A ∪ B) ≤ diam A + diam B := by
  sorry

/-! ## Sutherland 5.13  (HW4)
Prove that a subset of a metric space is open iff it is a union of open balls.
-/

theorem ex5_13 (U : Set X) :
    IsOpen U ↔ ∃ S : Set (X × ℝ), U = ⋃ p ∈ S, ball p.1 p.2 := by
  sorry

/-! ## Convergence in the discrete metric  (HW4 #7)
Let X be a set with the discrete metric. Show that (xₙ) converges to x iff there is
N ∈ ℕ such that xₙ = x for all n ≥ N: the convergent sequences are exactly the
eventually constant ones.
-/

open Classical in
/-- The discrete metric: `0` if the points agree and `1` otherwise. -/
noncomputable def dDisc {α : Type*} (p q : α) : ℝ := if p = q then 0 else 1

theorem hw4_7 {α : Type*} (x : ℕ → α) (a : α) :
    ConvergesWrt dDisc x a ↔ ∃ N, ∀ n ≥ N, x n = a := by
  sorry

/-! ## Convergence in a product  (HW4 #8)
Let (X, d_X), (Y, d_Y) be metric spaces. Show that (xₙ, yₙ) → (x, y) in X × Y iff
xₙ → x and yₙ → y, when d_{X×Y} is either d₁ or d₂ (page 43).
-/

/-- The metric `d₁((p, q), (p', q')) = d_X(p, p') + d_Y(q, q')`. -/
def d₁ (p q : X × Y) : ℝ := dist p.1 q.1 + dist p.2 q.2

/-- The metric `d₂((p, q), (p', q')) = √(d_X(p, p')² + d_Y(q, q')²)`. -/
noncomputable def d₂ (p q : X × Y) : ℝ := √(dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2)

theorem hw4_8_d₁ (x : ℕ → X) (y : ℕ → Y) (a : X) (b : Y) :
    ConvergesWrt d₁ (fun n ↦ (x n, y n)) (a, b) ↔
      ConvergesWrt dist x a ∧ ConvergesWrt dist y b := by
  sorry

theorem hw4_8_d₂ (x : ℕ → X) (y : ℕ → Y) (a : X) (b : Y) :
    ConvergesWrt d₂ (fun n ↦ (x n, y n)) (a, b) ↔
      ConvergesWrt dist x a ∧ ConvergesWrt dist y b := by
  sorry

/-! ## Staying away from a point  (HW4 #9)
Suppose (xₙ) is a sequence in a metric space (X, d). Show that if x ∈ X and there is
ε > 0 with d(x, xₙ) ≥ ε for all n then xₙ ↛ x.
-/

theorem hw4_9 (x : ℕ → X) (a : X) {ε : ℝ} (hε : 0 < ε) (h : ∀ n, ε ≤ dist a (x n)) :
    ¬ Tendsto x atTop (𝓝 a) := by
  sorry

/-! ## Sequential continuity  (HW4 #10)
Suppose (X, d_X), (Y, d_Y) are metric spaces, f : X → Y and a ∈ X. Then f is
continuous at a iff for every sequence (xₙ) in X converging to a, f(xₙ) → f(a) in Y.
-/

theorem hw4_10 (f : X → Y) (a : X) :
    ContinuousAt f a ↔
      ∀ x : ℕ → X, Tendsto x atTop (𝓝 a) → Tendsto (f ∘ x) atTop (𝓝 (f a)) := by
  sorry

/-! ## Sutherland 5.14  (HW5)
Show that for any x, y ∈ ℝⁿ, d_∞(x, y) ≤ d₂(x, y) ≤ d₁(x, y) ≤ n d_∞(x, y).
-/

/-- The taxicab metric on `ℝⁿ`. -/
def dOne {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, |x i - y i|

/-- The Euclidean metric on `ℝⁿ`. -/
noncomputable def dTwo {n : ℕ} (x y : Fin n → ℝ) : ℝ := √(∑ i, (x i - y i) ^ 2)

/-- The sup metric on `ℝⁿ`. -/
noncomputable def dInf {n : ℕ} (x y : Fin n → ℝ) : ℝ := ⨆ i, |x i - y i|

theorem ex5_14 {n : ℕ} (x y : Fin n → ℝ) :
    dInf x y ≤ dTwo x y ∧ dTwo x y ≤ dOne x y ∧ dOne x y ≤ n * dInf x y := by
  sorry

/-! ## Sutherland 5.15  (HW5)
Suppose X is a non-empty set and d, d' are metrics on X with d(x₁, x₂) ≤ k d'(x₁, x₂)
for all x₁, x₂ ∈ X and some constant k > 0.
(a) Show that B^{d'}_{ε/k}(x) ⊆ B^d_ε(x) for any x ∈ X and any ε > 0.
(b) Deduce that any d-open subset of X is also d'-open.
(c) Show that the open sets in ℝⁿ are the same for the metrics d₁, d₂, d_∞.
-/

theorem ex5_15a {α : Type*} {d d' : α → α → ℝ} {k : ℝ} (hk : 0 < k)
    (h : ∀ x₁ x₂, d x₁ x₂ ≤ k * d' x₁ x₂) (x : α) {ε : ℝ} (hε : 0 < ε) :
    ballWrt d' x (ε / k) ⊆ ballWrt d x ε := by
  sorry

theorem ex5_15b {α : Type*} {d d' : α → α → ℝ} {k : ℝ} (hk : 0 < k)
    (h : ∀ x₁ x₂, d x₁ x₂ ≤ k * d' x₁ x₂) {U : Set α} (hU : IsOpenWrt d U) :
    IsOpenWrt d' U := by
  sorry

theorem ex5_15c {n : ℕ} (U : Set (Fin n → ℝ)) :
    (IsOpenWrt dOne U ↔ IsOpenWrt dTwo U) ∧ (IsOpenWrt dTwo U ↔ IsOpenWrt dInf U) := by
  sorry

/-! ## Sutherland 6.3  (HW5)
Show that if X is a metric space and p ∈ X then {p} is closed. Then show in one line
that any finite subset of X is also closed.
-/

theorem ex6_3_singleton (p : X) : IsClosed ({p} : Set X) := by
  sorry

theorem ex6_3_finite {S : Set X} (hS : S.Finite) : IsClosed S := by
  sorry

/-! ## Sutherland 6.6  (HW5)
Let C[0, 1] be the space of continuous real-valued functions on [0, 1] with the sup
metric, and A ⊆ [0, 1]. Show that {f ∈ C[0, 1] : f(a) = 0 for all a ∈ A} is closed.
-/

theorem ex6_6 (A : Set unitInterval) :
    IsClosed {f : C(unitInterval, ℝ) | ∀ a ∈ A, f a = 0} := by
  sorry

/-! ## Products of closed sets  (HW5 #5, AI-free)
Suppose F is closed in X and G is closed in Y. Show that F × G is closed in X × Y.
You may find it nice to do this quickly using sequence arguments.
-/

theorem hw5_5 {F : Set X} {G : Set Y} (hF : IsClosed F) (hG : IsClosed G) :
    IsClosed (F ×ˢ G) := by
  sorry

/-! ## Sutherland 6.10  (HW6)
Prove that if A is a bounded subset of a metric space then Ā is bounded and
diam Ā = diam A.
-/

theorem ex6_10 {A : Set X} (hA : Bornology.IsBounded A) :
    Bornology.IsBounded (closure A) ∧ diam (closure A) = diam A := by
  sorry

/-! ## Sutherland 6.11  (HW6, no rigor, just brief justification)
Describe the closure of each of the sets in Exercise 6.2:
(a) [1, ∞)   (b) ℝ ∖ ℚ   (c) {n/(n+1) : n ∈ ℕ}   (d) {1/n : n ∈ ℕ, n ≥ 2} ∪ {0, 1, 2}
(Sutherland's ℕ starts at 1.)
-/

theorem ex6_11a : closure (Ici (1 : ℝ)) = (sorry : Set ℝ) := by
  sorry

theorem ex6_11b : closure {x : ℝ | Irrational x} = (sorry : Set ℝ) := by
  sorry

theorem ex6_11c :
    closure {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = n / (n + 1)} = (sorry : Set ℝ) := by
  sorry

theorem ex6_11d :
    closure ({x : ℝ | ∃ n : ℕ, 2 ≤ n ∧ x = 1 / n} ∪ {0, 1, 2}) = (sorry : Set ℝ) := by
  sorry

/-! ## Sutherland 6.16  (HW6, AI-free)
For a point x and a non-empty subset A of a metric space (X, d), define
d(x, A) = inf {d(x, a) : a ∈ A}.
(a) Prove that d(x, A) = 0 iff x ∈ Ā.
(b) Show that if y is another point in X then d(x, A) ≤ d(x, y) + d(y, A).
(c) Prove that x ↦ d(x, A) gives a continuous map from X to ℝ.
-/

/-- `d(x, A) = inf {d(x, a) : a ∈ A}`. -/
noncomputable def distSet (x : X) (A : Set X) : ℝ := sInf (dist x '' A)

theorem ex6_16a {A : Set X} (hA : A.Nonempty) (x : X) :
    distSet x A = 0 ↔ x ∈ closure A := by
  sorry

theorem ex6_16b {A : Set X} (hA : A.Nonempty) (x y : X) :
    distSet x A ≤ dist x y + distSet y A := by
  sorry

theorem ex6_16c {A : Set X} (hA : A.Nonempty) : Continuous fun x ↦ distSet x A := by
  sorry

/-! ## Sutherland 6.21(b)  (HW6)
Prove that the boundary of ℚ in ℝ is ℝ.
-/

theorem ex6_21b : frontier (range ((↑) : ℚ → ℝ)) = univ := by
  sorry

/-! ## Sutherland 6.23  (HW6)
For a subset A of a metric space X, prove:
(a) Å = A ∖ ∂A = Ā ∖ ∂A,
(b) closure (X ∖ A) = X ∖ Å,
(c) ∂A = Ā ∩ closure (X ∖ A) = ∂(X ∖ A),
(d) ∂A is closed in X.
-/

theorem ex6_23a (A : Set X) :
    interior A = A \ frontier A ∧ A \ frontier A = closure A \ frontier A := by
  sorry

theorem ex6_23b (A : Set X) : closure Aᶜ = (interior A)ᶜ := by
  sorry

theorem ex6_23c (A : Set X) :
    frontier A = closure A ∩ closure Aᶜ ∧ closure A ∩ closure Aᶜ = frontier Aᶜ := by
  sorry

theorem ex6_23d (A : Set X) : IsClosed (frontier A) := by
  sorry

end MetricSpaces
