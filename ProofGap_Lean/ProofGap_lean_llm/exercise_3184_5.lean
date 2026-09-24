import Mathlib

/-!
Exercise 3184_5
Finite iterated limits are expressed with `Tendsto ... (𝓝 ...)`; the source's
`= ∞` claims are expressed as divergence to `Filter.atTop`.
-/

noncomputable section

open Filter Real
open scoped Topology

def LogBase (x t : ℝ) : ℝ :=
  log t / log x

/-- GAP 1: Change of base for the logarithm on the stated domain. -/
theorem proof_gap_exercise_3184_5_1
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y)) :
    ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x := by
  sorry

/-- GAP 2: For fixed admissible `x`, replace `f x y` by the quotient inside the
inner limit as `y → 0`. -/
theorem proof_gap_exercise_3184_5_2
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x) :
    ∀ x : ℝ, 0 < x → x ≠ 1 →
      (Tendsto (fun y : ℝ => f (x, y)) (𝓝 0) (𝓝 (log x / log x)) ↔
        Tendsto (fun y : ℝ => log (x + y) / log x) (𝓝 0) (𝓝 (log x / log x))) := by
  sorry

/-- GAP 3: Evaluate the inner quotient limit in `y`. -/
theorem proof_gap_exercise_3184_5_3
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x)
    (hlim_eq : ∀ x : ℝ, 0 < x → x ≠ 1 →
      (Tendsto (fun y : ℝ => f (x, y)) (𝓝 0) (𝓝 (log x / log x)) ↔
        Tendsto (fun y : ℝ => log (x + y) / log x) (𝓝 0) (𝓝 (log x / log x)))) :
    ∀ x : ℝ, 0 < x → x ≠ 1 →
      Tendsto (fun y : ℝ => log (x + y) / log x) (𝓝 0) (𝓝 (log x / log x)) := by
  sorry

/-- GAP 4: `log x / log x = 1` for `x > 0`, `x ≠ 1`. -/
theorem proof_gap_exercise_3184_5_4
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x)
    (hlim_y : ∀ x : ℝ, 0 < x → x ≠ 1 →
      Tendsto (fun y : ℝ => log (x + y) / log x) (𝓝 0) (𝓝 (log x / log x))) :
    ∀ x : ℝ, 0 < x → x ≠ 1 → log x / log x = 1 := by
  sorry

/-- GAP 5: Conclude the inner limit is constantly `1` for admissible fixed `x`. -/
theorem proof_gap_exercise_3184_5_5
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x)
    (hlim_y : ∀ x : ℝ, 0 < x → x ≠ 1 →
      Tendsto (fun y : ℝ => log (x + y) / log x) (𝓝 0) (𝓝 (log x / log x)))
    (hquot_one : ∀ x : ℝ, 0 < x → x ≠ 1 → log x / log x = 1) :
    ∀ x : ℝ, 0 < x → x ≠ 1 → Tendsto (fun y : ℝ => f (x, y)) (𝓝 0) (𝓝 1) := by
  sorry

/-- GAP 6: Replace the outer limit of the inner limit by the outer limit of the
constant `1`. -/
theorem proof_gap_exercise_3184_5_6
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hinner : ∀ x : ℝ, 0 < x → x ≠ 1 → g x = 1) :
    (Tendsto g (𝓝 1) (𝓝 1) ↔ Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 1) (𝓝 1)) := by
  sorry

/-- GAP 7: The limit of the constant `1` at `x → 1` is `1`. -/
theorem proof_gap_exercise_3184_5_7
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y)) :
    Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 1) (𝓝 1) := by
  sorry

/-- GAP 8: Conclude the first iterated limit is `1`. -/
theorem proof_gap_exercise_3184_5_8
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (houter_eq : (Tendsto g (𝓝 1) (𝓝 1) ↔
      Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 1) (𝓝 1)))
    (hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 1) (𝓝 1)) :
    Tendsto g (𝓝 1) (𝓝 1) := by
  sorry

/-- GAP 9: For fixed admissible `y`, replace `f x y` by the quotient inside the
limit as `x → 1`. -/
theorem proof_gap_exercise_3184_5_9
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x) :
    ∀ y : ℝ, -1 < y → y ≠ 0 →
      (Tendsto (fun x : ℝ => f (x, y)) (𝓝[≠] 1) atTop ↔
        Tendsto (fun x : ℝ => log (x + y) / log x) (𝓝[≠] 1) atTop) := by
  sorry

/-- GAP 10: Source claim that the fixed-`y` quotient limit diverges to `+∞`. -/
theorem proof_gap_exercise_3184_5_10
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hbase : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = log (x + y) / log x)
    (hreplace : ∀ y : ℝ, -1 < y → y ≠ 0 →
      (Tendsto (fun x : ℝ => f (x, y)) (𝓝[≠] 1) atTop ↔
        Tendsto (fun x : ℝ => log (x + y) / log x) (𝓝[≠] 1) atTop)) :
    ∀ y : ℝ, -1 < y → y ≠ 0 →
      Tendsto (fun x : ℝ => log (x + y) / log x) (𝓝[≠] 1) atTop := by
  sorry

/-- GAP 11: Transfer the `+∞` divergence from the quotient to `f`. -/
theorem proof_gap_exercise_3184_5_11
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hreplace : ∀ y : ℝ, -1 < y → y ≠ 0 →
      (Tendsto (fun x : ℝ => f (x, y)) (𝓝[≠] 1) atTop ↔
        Tendsto (fun x : ℝ => log (x + y) / log x) (𝓝[≠] 1) atTop))
    (hquot_top : ∀ y : ℝ, -1 < y → y ≠ 0 →
      Tendsto (fun x : ℝ => log (x + y) / log x) (𝓝[≠] 1) atTop) :
    ∀ y : ℝ, -1 < y → y ≠ 0 → Tendsto (fun x : ℝ => f (x, y)) (𝓝[≠] 1) atTop := by
  sorry

/-- GAP 12: Replace the outer `y → 0` limit of the inner `x → 1` divergence by
the constant extended value `∞`, represented as `atTop`. -/
theorem proof_gap_exercise_3184_5_12
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (hinner_top : ∀ y : ℝ, -1 < y → y ≠ 0 → Tendsto (fun x : ℝ => f (x, y)) (𝓝[≠] 1) atTop) :
    (Tendsto g (𝓝[≠] 0) atTop ↔ Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) atTop) := by
  sorry

/-- GAP 13: Source claim that the constant infinite value has limit `∞`; encoded
as divergence of a placeholder real function to `atTop`. -/
theorem proof_gap_exercise_3184_5_13
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y)) :
    Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) atTop := by
  sorry

/-- GAP 14: Conclude the second iterated limit is `∞`, represented by
divergence to `atTop`. -/
theorem proof_gap_exercise_3184_5_14
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ x y : ℝ, 0 < x → x ≠ 1 → 0 < x + y → f (x, y) = LogBase x (x + y))
    (houter_eq : (Tendsto g (𝓝[≠] 0) atTop ↔
      Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) atTop))
    (hinfty : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) atTop) :
    Tendsto g (𝓝[≠] 0) atTop := by
  sorry

