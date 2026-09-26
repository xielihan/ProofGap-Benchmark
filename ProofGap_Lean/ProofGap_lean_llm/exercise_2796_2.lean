import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2796_2

noncomputable def pg2796_sgn (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

def pg2796_rat (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def pg2796_irrat (x : ℝ) : Prop := ¬ pg2796_rat x

noncomputable def pg2796_series (r : ℕ -> ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if 0 < k then |x - r k| /. ((3 : ℕ) ^ k) else 0

noncomputable def pg2796_v (r : ℕ -> ℝ) (x0 : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (|x - r k| - |x0 - r k|) /. (((3 : ℕ) ^ k) * (x - x0))

noncomputable def pg2796_vsum (v : ℕ -> ℝ -> ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if 0 < k then v k x else 0

noncomputable def pg2796_deriv_sum (r : ℕ -> ℝ) (x0 : ℝ) : ℝ :=
  ∑' k : ℕ, if 0 < k then (1 /. ((3 : ℕ) ^ k)) * pg2796_sgn (x0 - r k) else 0

noncomputable def pg2796_puncturedInterval (x0 : ℝ) : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1 ∧ x ≠ x0}

noncomputable def pg2796_except_sum (v : ℕ -> ℝ -> ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if 0 < k ∧ k ≠ m then v k x else 0

noncomputable def pg2796_except_lim_sum (r : ℕ -> ℝ) (m : ℕ) (x0 : ℝ) : ℝ :=
  ∑' k : ℕ, if 0 < k ∧ k ≠ m then (1 /. ((3 : ℕ) ^ k)) * pg2796_sgn (x0 - r k) else 0

def pg2796_base (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ) : Prop :=
  (∀ k : ℕ, 0 < k -> pg2796_rat (r k) ∧ 0 ≤ r k ∧ r k ≤ 1) ∧
  (∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> f x = pg2796_series r x) ∧
  (∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> v k x = pg2796_v r x0 k x)

def pg2796_rational_base (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ) : Prop :=
  pg2796_base r f v ∧
  (∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧ x0 = r m) ∧
  (∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 ->
    ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> v k x = pg2796_v r x0 k x)

theorem proof_gap_exercise_2796_2_1 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
      (f x - f x0) /. (x - x0) = pg2796_vsum v x := by
  sorry

theorem proof_gap_exercise_2796_2_2 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) (h1 : ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> (f x - f x0) /. (x - x0) = pg2796_vsum v x) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
    |(|x - r k| - |x0 - r k|)| ≤ |(x - r k) - (x0 - r k)| := by
  sorry

theorem proof_gap_exercise_2796_2_3 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) (h2 : ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> |(|x - r k| - |x0 - r k|)| ≤ |(x - r k) - (x0 - r k)|) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
    |(x - r k) - (x0 - r k)| = |x - x0| := by
  sorry

theorem proof_gap_exercise_2796_2_4 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
    |(|x - r k| - |x0 - r k|)| ≤ |x - x0| := by
  sorry

theorem proof_gap_exercise_2796_2_5 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
    |v k x| ≤ 1 /. ((3 : ℕ) ^ k) := by
  sorry

theorem proof_gap_exercise_2796_2_6 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) (h5 : ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> |v k x| ≤ 1 /. ((3 : ℕ) ^ k)) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    TendstoUniformlyOn (fun n x => if 0 < n then v n x else 0) (pg2796_vsum v) atTop (pg2796_puncturedInterval x0) := by
  sorry

theorem proof_gap_exercise_2796_2_7 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k -> x0 ≠ r k := by
  sorry

theorem proof_gap_exercise_2796_2_8 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> ∀ k : ℕ, 0 < k ->
    Tendsto (fun x : ℝ => v k x) (𝓝[≠] x0) (𝓝 ((1 /. ((3 : ℕ) ^ k)) * pg2796_sgn (x0 - r k))) := by
  sorry

theorem proof_gap_exercise_2796_2_9 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    Tendsto (fun x : ℝ => (f x - f x0) /. (x - x0)) (𝓝[≠] x0) (𝓝 (limUnder (𝓝[≠] x0) (pg2796_vsum v))) := by
  sorry

theorem proof_gap_exercise_2796_2_10 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    Tendsto (pg2796_vsum v) (𝓝[≠] x0) (𝓝 (pg2796_deriv_sum r x0)) := by
  sorry

theorem proof_gap_exercise_2796_2_11 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    (∑' k : ℕ, if 0 < k then limUnder (𝓝[≠] x0) (fun x : ℝ => v k x) else 0) = pg2796_deriv_sum r x0 := by
  sorry

theorem proof_gap_exercise_2796_2_12 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 ->
    Tendsto (fun x : ℝ => (f x - f x0) /. (x - x0)) (𝓝[≠] x0) (𝓝 (pg2796_deriv_sum r x0)) := by
  sorry

theorem proof_gap_exercise_2796_2_13 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> DifferentiableAt ℝ f x0 := by
  sorry

theorem proof_gap_exercise_2796_2_14 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> deriv f x0 = pg2796_deriv_sum r x0 := by
  sorry

theorem proof_gap_exercise_2796_2_15 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧ m = m := by
  sorry

theorem proof_gap_exercise_2796_2_16 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m := by
  sorry

theorem proof_gap_exercise_2796_2_17 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧ x0 = r m := by
  sorry

theorem proof_gap_exercise_2796_2_18 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∀ k : ℕ, 0 < k -> ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 ->
    v k x = pg2796_v r x0 k x := by
  sorry

theorem proof_gap_exercise_2796_2_19 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> (f x - f x0) /. (x - x0) = v m x + pg2796_except_sum v m x := by
  sorry

theorem proof_gap_exercise_2796_2_20 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> v m x = pg2796_v r x0 m x := by
  sorry

theorem proof_gap_exercise_2796_2_21 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> pg2796_v r x0 m x = |x - x0| /. (((3 : ℕ) ^ m) * (x - x0)) := by
  sorry

theorem proof_gap_exercise_2796_2_22 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> |x - x0| /. (((3 : ℕ) ^ m) * (x - x0)) = (1 /. ((3 : ℕ) ^ m)) * pg2796_sgn (x - x0) := by
  sorry

theorem proof_gap_exercise_2796_2_23 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ∀ x : ℝ, 0 ≤ x -> x ≤ 1 -> x ≠ x0 -> v m x = (1 /. ((3 : ℕ) ^ m)) * pg2796_sgn (x - x0) := by
  sorry

theorem proof_gap_exercise_2796_2_24 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    Tendsto (fun x : ℝ => pg2796_except_sum v m x) (𝓝[≠] x0) (𝓝 (pg2796_except_lim_sum r m x0)) := by
  sorry

theorem proof_gap_exercise_2796_2_25 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    (∑' k : ℕ, if 0 < k ∧ k ≠ m then limUnder (𝓝[≠] x0) (fun x : ℝ => v k x) else 0) = pg2796_except_lim_sum r m x0 := by
  sorry

theorem proof_gap_exercise_2796_2_26 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    Tendsto (fun x : ℝ => pg2796_except_sum v m x) (𝓝[≠] x0) (𝓝 (pg2796_except_lim_sum r m x0)) := by
  sorry

theorem proof_gap_exercise_2796_2_27 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    Tendsto (fun x : ℝ => v m x) (𝓝[>] x0) (𝓝 (1 /. ((3 : ℕ) ^ m))) := by
  sorry

theorem proof_gap_exercise_2796_2_28 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    Tendsto (fun x : ℝ => v m x) (𝓝[<] x0) (𝓝 (-(1 /. ((3 : ℕ) ^ m)))) := by
  sorry

theorem proof_gap_exercise_2796_2_29 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  ∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ∃ m : ℕ, 0 < m ∧
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ => v m x) (𝓝[≠] x0) (𝓝 L) := by
  sorry

theorem proof_gap_exercise_2796_2_30 (r : ℕ -> ℝ) (f : ℝ -> ℝ) (v : ℕ -> ℝ -> ℝ)
  (hbase : pg2796_rational_base r f v) :
  (∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_irrat x0 -> DifferentiableAt ℝ f x0) ∧
  (∀ x0 : ℝ, x0 ∈ Set.Icc 0 1 -> pg2796_rat x0 -> ¬ DifferentiableAt ℝ f x0) := by
  sorry
