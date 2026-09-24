import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise3108

def Ioo (a b : ℝ) : Set ℝ := Set.Ioo a b
def ConvergentSeries (u : ℕ -> ℝ) : Prop := Summable u
def AbsoluteConvergentSeries (u : ℕ -> ℝ) : Prop := Summable (fun n => |u n|)
def ConvergentProduct (u : ℕ -> ℝ) : Prop := ∃ p : ℝ, HasProd u p
def UniformConvergentOn (s : Set ℝ) (u : ℕ -> ℝ -> ℝ) (L : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn u L atTop s

-- exercise: exercise_3108

variable (f : ℕ -> ℝ -> ℝ) (c : ℕ -> ℝ) (F G L : ℝ -> ℝ) (a b : ℝ)
variable (hab : a < b)
variable (hf_cont : ∀ n : ℕ, 0 < n -> ContinuousOn (f n) (Ioo a b))
variable (hf_bound : ∀ (x : ℝ) (n : ℕ), x ∈ Ioo a b -> 0 < n -> |f n x| ≤ c n)
variable (hc_nonneg : ∀ n : ℕ, 0 < n -> 0 ≤ c n)
variable (hc_conv : ConvergentSeries c)
variable (hF_def : ∀ x : ℝ, x ∈ Ioo a b -> HasProd (fun n : ℕ => 1 + f (n + 1) x) (F x))

theorem proof_gap_exercise_3108_1 :
    Tendsto c atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_3108_2
    (h1 : Tendsto c atTop (𝓝 0)) :
    ∀ x : ℝ, x ∈ Ioo a b -> Tendsto (fun n : ℕ => f n x) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_3108_3
    (h1 : Tendsto c atTop (𝓝 0))
    (h2 : ∀ x : ℝ, x ∈ Ioo a b -> Tendsto (fun n : ℕ => f n x) atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ -> ∀ x : ℝ, x ∈ Ioo a b ->
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ n : ℕ, 0 < n -> N0 ≤ n -> |f n x| < δ := by
  sorry

theorem proof_gap_exercise_3108_4
    (h1 : Tendsto c atTop (𝓝 0))
    (h2 : ∀ x : ℝ, x ∈ Ioo a b -> Tendsto (fun n : ℕ => f n x) atTop (𝓝 0))
    (h3 : ∀ δ : ℝ, 0 < δ -> ∀ x : ℝ, x ∈ Ioo a b ->
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ n : ℕ, 0 < n -> N0 ≤ n -> |f n x| < δ)
    (g : ℕ -> ℝ -> ℝ)
    (hg : ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b -> g = fun k y => f (N0 + k) y) :
    ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b ->
      ∀ k : ℕ, 0 < k -> |g k x| ≤ c (N0 + k) := by
  sorry

theorem proof_gap_exercise_3108_5
    (h1 : Tendsto c atTop (𝓝 0))
    (h2 : ∀ x : ℝ, x ∈ Ioo a b -> Tendsto (fun n : ℕ => f n x) atTop (𝓝 0))
    (h3 : ∀ δ : ℝ, 0 < δ -> ∀ x : ℝ, x ∈ Ioo a b ->
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ n : ℕ, 0 < n -> N0 ≤ n -> |f n x| < δ) :
    ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b -> ConvergentSeries (fun k : ℕ => c (N0 + k)) := by
  sorry

theorem proof_gap_exercise_3108_6
    (g : ℕ -> ℝ -> ℝ)
    (h4 : ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b ->
      ∀ k : ℕ, 0 < k -> |g k x| ≤ c (N0 + k))
    (h5 : ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b -> ConvergentSeries (fun k : ℕ => c (N0 + k))) :
    ∀ x : ℝ, x ∈ Ioo a b -> AbsoluteConvergentSeries (fun k : ℕ => g k x) := by
  sorry

theorem proof_gap_exercise_3108_7
    (g : ℕ -> ℝ -> ℝ)
    (h6 : ∀ x : ℝ, x ∈ Ioo a b -> AbsoluteConvergentSeries (fun k : ℕ => g k x)) :
    ∀ x : ℝ, x ∈ Ioo a b -> ConvergentProduct (fun k : ℕ => 1 + g k x) := by
  sorry

theorem proof_gap_exercise_3108_8
    (g : ℕ -> ℝ -> ℝ)
    (hG_def : ∀ x : ℝ, x ∈ Ioo a b -> HasProd (fun k : ℕ => 1 + g k x) (G x))
    (h7 : ∀ x : ℝ, x ∈ Ioo a b -> ConvergentProduct (fun k : ℕ => 1 + g k x)) :
    ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b ->
      F x = G x * (Finset.range N0).prod (fun i => 1 + f (i + 1) x) := by
  sorry

theorem proof_gap_exercise_3108_9
    (g : ℕ -> ℝ -> ℝ)
    (hG_def : ∀ x : ℝ, x ∈ Ioo a b -> HasProd (fun k : ℕ => 1 + g k x) (G x))
    (h8 : ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b ->
      F x = G x * (Finset.range N0).prod (fun i => 1 + f (i + 1) x)) :
    ∀ x : ℝ, x ∈ Ioo a b -> 0 < G x := by
  sorry

theorem proof_gap_exercise_3108_10
    (g : ℕ -> ℝ -> ℝ)
    (hG_pos : ∀ x : ℝ, x ∈ Ioo a b -> 0 < G x)
    (hL_def : ∀ x : ℝ, x ∈ Ioo a b -> L x = Real.log (G x)) :
    ∀ x : ℝ, x ∈ Ioo a b -> HasSum (fun k : ℕ => Real.log (1 + g k x)) (L x) := by
  sorry

theorem proof_gap_exercise_3108_11 :
    Tendsto (fun u : ℝ => Real.log (1 + u) / u) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_3108_12
    (g : ℕ -> ℝ -> ℝ)
    (h11 : Tendsto (fun u : ℝ => Real.log (1 + u) / u) (𝓝[≠] 0) (𝓝 1)) :
    ∀ N0 : ℕ, ∃ Nstar : ℕ, 0 < Nstar ∧
      ∀ (n : ℕ) (x : ℝ), x ∈ Ioo a b -> Nstar < n ->
          |Real.log (1 + g n x)| ≤ 2 * |g n x| ∧
            2 * |g n x| ≤ 2 * c (n + N0) := by
  sorry

theorem proof_gap_exercise_3108_13
    (h12 : ∀ N0 : ℕ, ∃ Nstar : ℕ, 0 < Nstar ∧
      ∀ (n : ℕ) (x : ℝ), x ∈ Ioo a b -> Nstar < n ->
          |Real.log (1 + (0 : ℝ))| ≤ 2 * |(0 : ℝ)| ∧ 2 * |(0 : ℝ)| ≤ 2 * c (n + N0)) :
    ∀ N0 : ℕ, ConvergentSeries (fun n : ℕ => 2 * c (n + N0)) := by
  sorry

theorem proof_gap_exercise_3108_14
    (g : ℕ -> ℝ -> ℝ)
    (h10 : ∀ x : ℝ, x ∈ Ioo a b -> HasSum (fun k : ℕ => Real.log (1 + g k x)) (L x))
    (h13 : ∀ N0 : ℕ, ConvergentSeries (fun n : ℕ => 2 * c (n + N0))) :
    UniformConvergentOn (Ioo a b)
      (fun n x => (Finset.range n).sum (fun k => Real.log (1 + g k x))) L := by
  sorry

theorem proof_gap_exercise_3108_15
    (g : ℕ -> ℝ -> ℝ)
    (h14 : UniformConvergentOn (Ioo a b)
      (fun n x => (Finset.range n).sum (fun k => Real.log (1 + g k x))) L) :
    ContinuousOn L (Ioo a b) := by
  sorry

theorem proof_gap_exercise_3108_16
    (h9 : ∀ x : ℝ, x ∈ Ioo a b -> 0 < G x)
    (h15 : ContinuousOn L (Ioo a b))
    (hL_def : ∀ x : ℝ, x ∈ Ioo a b -> L x = Real.log (G x)) :
    ContinuousOn G (Ioo a b) := by
  sorry

theorem proof_gap_exercise_3108_17 :
    ∀ N0 : ℕ, ContinuousOn (fun x : ℝ => (Finset.range N0).prod (fun i => 1 + f (i + 1) x)) (Ioo a b) := by
  sorry

theorem proof_gap_exercise_3108_18
    (h8 : ∀ N0 : ℕ, ∀ x : ℝ, x ∈ Ioo a b ->
      F x = G x * (Finset.range N0).prod (fun i => 1 + f (i + 1) x))
    (h16 : ContinuousOn G (Ioo a b))
    (h17 : ∀ N0 : ℕ, ContinuousOn (fun x : ℝ => (Finset.range N0).prod (fun i => 1 + f (i + 1) x)) (Ioo a b)) :
    ContinuousOn F (Ioo a b) := by
  sorry

theorem proof_gap_exercise_3108_19
    (h18 : ContinuousOn F (Ioo a b)) :
    ContinuousOn F (Ioo a b) := by
  sorry

end Exercise3108
