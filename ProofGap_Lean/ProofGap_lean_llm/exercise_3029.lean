import Mathlib

/-!
Regenerated from `sources/exercise_3029/*.txt`.

The power series is encoded with `Summable` and `tsum`.  Its convergence
domain is a genuine set of real points where the coefficient series is
summable; the displayed closed forms use real square root, inverse sine, log,
and derivative.
-/

open scoped BigOperators
open Filter

namespace Exercise_3029

noncomputable section

def coeff (n : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ)

def powerTerm (x : ℝ) (n : ℕ) : ℝ :=
  coeff n * x ^ n

def powerSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, powerTerm x n

def convergenceDomain : Set ℝ :=
  {x : ℝ | Summable (fun n : ℕ => powerTerm x n)}

def radiusOfConvergence (c : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => c n * x ^ n)}

def positiveClosedForm (x : ℝ) : ℝ :=
  4 / (4 - x) +
    (4 * Real.sqrt x) / ((4 - x) ^ ((3 : ℝ) / 2)) *
      Real.arcsin (Real.sqrt x / 2)

def negativeClosedForm (x : ℝ) : ℝ :=
  4 / (4 - x) -
    (4 * Real.sqrt |x|) / ((4 - x) ^ ((3 : ℝ) / 2)) *
      Real.log ((Real.sqrt |x| + Real.sqrt (4 - x)) / 2)

def piecewiseClosedForm (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 4 then positiveClosedForm x else negativeClosedForm x

def endpointTerm (sign : ℝ) (n : ℕ) : ℝ :=
  coeff n * sign ^ n

theorem proof_gap_exercise_3029_1
    (S : ℝ → ℝ) (D : Set ℝ) (x t : ℝ) (n : ℕ)
    (a : ℕ → ℝ) (F G g : ℝ → ℝ) (C : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ((((Nat.factorial (n + 1) : ℝ) ^ 2) /
            (Nat.factorial (2 * n + 2) : ℝ)) /
          (((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ))))
      atTop
      (nhds ((1 : ℝ) / 4)) =
    Tendsto
      (fun n : ℕ => ((n + 1 : ℝ) ^ 2) / ((2 * n + 2 : ℝ) * (2 * n + 1 : ℝ)))
      atTop
      (nhds ((1 : ℝ) / 4)) := by
  sorry

theorem proof_gap_exercise_3029_2
    (S : ℝ → ℝ) (D : Set ℝ) (x t : ℝ) (n : ℕ)
    (a : ℕ → ℝ) (F G g : ℝ → ℝ) (C : ℝ)
    (hratio :
      Tendsto
        (fun n : ℕ =>
          ((((Nat.factorial (n + 1) : ℝ) ^ 2) /
              (Nat.factorial (2 * n + 2) : ℝ)) /
            (((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ))))
        atTop
        (nhds ((1 : ℝ) / 4)) =
      Tendsto
        (fun n : ℕ => ((n + 1 : ℝ) ^ 2) / ((2 * n + 2 : ℝ) * (2 * n + 1 : ℝ)))
        atTop
        (nhds ((1 : ℝ) / 4))) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℝ) ^ 2) / ((2 * n + 2 : ℝ) * (2 * n + 1 : ℝ)))
      atTop
      (nhds ((1 : ℝ) / 4)) := by
  sorry

theorem proof_gap_exercise_3029_3
    (S : ℝ → ℝ) (D : Set ℝ) (x t : ℝ) (n : ℕ)
    (a : ℕ → ℝ) (F G g : ℝ → ℝ) (C : ℝ)
    (hratio :
      Tendsto
        (fun n : ℕ =>
          ((((Nat.factorial (n + 1) : ℝ) ^ 2) /
              (Nat.factorial (2 * n + 2) : ℝ)) /
            (((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ))))
        atTop
        (nhds ((1 : ℝ) / 4)) =
      Tendsto
        (fun n : ℕ => ((n + 1 : ℝ) ^ 2) / ((2 * n + 2 : ℝ) * (2 * n + 1 : ℝ)))
        atTop
        (nhds ((1 : ℝ) / 4)))
    (hlim :
      Tendsto
        (fun n : ℕ => ((n + 1 : ℝ) ^ 2) / ((2 * n + 2 : ℝ) * (2 * n + 1 : ℝ)))
        atTop
        (nhds ((1 : ℝ) / 4))) :
    Tendsto
      (fun n : ℕ =>
        ((((Nat.factorial (n + 1) : ℝ) ^ 2) /
            (Nat.factorial (2 * n + 2) : ℝ)) /
          (((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ))))
      atTop
      (nhds ((1 : ℝ) / 4)) := by
  sorry

theorem proof_gap_exercise_3029_4
    (hlim :
      Tendsto
        (fun n : ℕ =>
          ((((Nat.factorial (n + 1) : ℝ) ^ 2) /
              (Nat.factorial (2 * n + 2) : ℝ)) /
            (((Nat.factorial n : ℝ) ^ 2) / (Nat.factorial (2 * n) : ℝ))))
        atTop
        (nhds ((1 : ℝ) / 4))) :
    radiusOfConvergence coeff = 4 := by
  sorry

theorem proof_gap_exercise_3029_5
    (x : ℝ) (hradius : radiusOfConvergence coeff = 4) :
    |x| < 4 → Summable (fun n : ℕ => powerTerm x n) := by
  sorry

theorem proof_gap_exercise_3029_6
    (x : ℝ) (hradius : radiusOfConvergence coeff = 4) :
    |x| > 4 → ¬ Summable (fun n : ℕ => powerTerm x n) := by
  sorry

theorem proof_gap_exercise_3029_7
    (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ m : ℕ, a m = endpointTerm 4 m ∨ a m = endpointTerm (-4) m) :
    |a (n + 1) / a n| = (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) := by
  sorry

theorem proof_gap_exercise_3029_8 (n : ℕ) :
    (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) > 1 := by
  sorry

theorem proof_gap_exercise_3029_9
    (a : ℕ → ℝ) (n : ℕ)
    (hratio : |a (n + 1) / a n| = (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ))
    (hgt : (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) > 1) :
    |a (n + 1) / a n| > 1 := by
  sorry

theorem proof_gap_exercise_3029_10
    (a : ℕ → ℝ)
    (hratio_gt : ∀ n : ℕ, |a (n + 1) / a n| > 1) :
    ¬ Tendsto a atTop (nhds 0) := by
  sorry

theorem proof_gap_exercise_3029_11
    (x : ℝ)
    (hendpoint : ∀ sign : ℝ, sign = 4 ∨ sign = -4 →
      ¬ Tendsto (fun n : ℕ => endpointTerm sign n) atTop (nhds 0)) :
    x = 4 ∨ x = -4 → ¬ Summable (fun n : ℕ => powerTerm x n) := by
  sorry

theorem proof_gap_exercise_3029_12
    (D : Set ℝ)
    (hinside : ∀ x : ℝ, |x| < 4 → x ∈ D)
    (houtside : ∀ x : ℝ, x ∈ D → |x| < 4) :
    D = Set.Ioo (-4 : ℝ) 4 := by
  sorry

theorem proof_gap_exercise_3029_13
    (x t : ℝ) (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (ht : x = (2 * t) ^ 2) :
    0 ≤ t := by
  sorry

theorem proof_gap_exercise_3029_14
    (x t : ℝ) (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (ht : x = (2 * t) ^ 2) (ht_nonneg : 0 ≤ t) :
    t < 1 := by
  sorry

theorem proof_gap_exercise_3029_15
    (x t : ℝ) (F : ℝ → ℝ)
    (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (hF : F t = ∑' n : ℕ, coeff n * (2 * t) ^ (2 * n)) :
    (1 - t ^ 2) * F t - 1 =
      (t / 4) * deriv (fun u : ℝ => 2 * (Real.arcsin u) ^ 2) t := by
  sorry

theorem proof_gap_exercise_3029_16
    (x t : ℝ) (F : ℝ → ℝ)
    (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (hderiv :
      (1 - t ^ 2) * F t - 1 =
        (t / 4) * deriv (fun u : ℝ => 2 * (Real.arcsin u) ^ 2) t) :
    (1 - t ^ 2) * F t - 1 =
      (t / Real.sqrt (1 - t ^ 2)) * Real.arcsin t := by
  sorry

theorem proof_gap_exercise_3029_17
    (x t : ℝ) (F : ℝ → ℝ)
    (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (heq :
      (1 - t ^ 2) * F t - 1 =
        (t / Real.sqrt (1 - t ^ 2)) * Real.arcsin t) :
    F t =
      (1 / (1 - t ^ 2)) *
        (1 + (t / Real.sqrt (1 - t ^ 2)) * Real.arcsin t) := by
  sorry

theorem proof_gap_exercise_3029_18
    (S : ℝ → ℝ) (x t : ℝ)
    (hx_nonneg : 0 ≤ x) (hx_lt : x < 4)
    (ht : x = (2 * t) ^ 2)
    (hF :
      (∑' n : ℕ, coeff n * (2 * t) ^ (2 * n)) =
        (1 / (1 - t ^ 2)) *
          (1 + (t / Real.sqrt (1 - t ^ 2)) * Real.arcsin t))
    (hS : S x = powerSeries x) :
    S x = positiveClosedForm x := by
  sorry

theorem proof_gap_exercise_3029_19
    (x t : ℝ) (hx_gt : -4 < x) (hx_lt : x < 0)
    (ht : x = -((2 * t) ^ 2)) :
    0 < t := by
  sorry

theorem proof_gap_exercise_3029_20
    (x t : ℝ) (hx_gt : -4 < x) (hx_lt : x < 0)
    (ht : x = -((2 * t) ^ 2)) (ht_pos : 0 < t) :
    t < 1 := by
  sorry

theorem proof_gap_exercise_3029_21
    (x t : ℝ) (G g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hG : G t = ∑' n : ℕ, coeff n * (-1 : ℝ) ^ n * (2 * t) ^ (2 * n))
    (hg : g t = ∑' n : ℕ,
      (-1 : ℝ) ^ n * (coeff (n + 1)) * (n + 1 : ℝ) * (2 * t) ^ (2 * n + 1)) :
    1 - (1 + t ^ 2) * G t = t * g t := by
  sorry

theorem proof_gap_exercise_3029_22
    (x t : ℝ) (G g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hrel : 1 - (1 + t ^ 2) * G t = t * g t) :
    (1 + t ^ 2) * deriv g t + t * g t = 1 := by
  sorry

theorem proof_gap_exercise_3029_23
    (x t : ℝ) (g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hode : (1 + t ^ 2) * deriv g t + t * g t = 1) :
    Real.sqrt (1 + t ^ 2) * deriv g t +
        (t / Real.sqrt (1 + t ^ 2)) * g t =
      1 / Real.sqrt (1 + t ^ 2) := by
  sorry

theorem proof_gap_exercise_3029_24
    (x t C : ℝ) (g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hlinear :
      Real.sqrt (1 + t ^ 2) * deriv g t +
          (t / Real.sqrt (1 + t ^ 2)) * g t =
        1 / Real.sqrt (1 + t ^ 2)) :
    Real.sqrt (1 + t ^ 2) * g t =
      Real.log (t + Real.sqrt (1 + t ^ 2)) + C := by
  sorry

theorem proof_gap_exercise_3029_25
    (x t : ℝ) (g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hg : g t = ∑' n : ℕ,
      (-1 : ℝ) ^ n * (coeff (n + 1)) * (n + 1 : ℝ) * (2 * t) ^ (2 * n + 1)) :
    g 0 = 0 := by
  sorry

theorem proof_gap_exercise_3029_26
    (x t C : ℝ) (g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hconst :
      Real.sqrt (1 + t ^ 2) * g t =
        Real.log (t + Real.sqrt (1 + t ^ 2)) + C)
    (hg0 : g 0 = 0) :
    C = 0 := by
  sorry

theorem proof_gap_exercise_3029_27
    (x t C : ℝ) (g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hconst :
      Real.sqrt (1 + t ^ 2) * g t =
        Real.log (t + Real.sqrt (1 + t ^ 2)) + C)
    (hC : C = 0) :
    g t =
      (1 / Real.sqrt (1 + t ^ 2)) *
        Real.log (t + Real.sqrt (1 + t ^ 2)) := by
  sorry

theorem proof_gap_exercise_3029_28
    (x t : ℝ) (G g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (hrel : 1 - (1 + t ^ 2) * G t = t * g t) :
    G t = (1 / (1 + t ^ 2)) * (1 - t * g t) := by
  sorry

theorem proof_gap_exercise_3029_29
    (S : ℝ → ℝ) (x t : ℝ) (G g : ℝ → ℝ)
    (hx_gt : -4 < x) (hx_lt : x < 0)
    (ht : x = -((2 * t) ^ 2))
    (hg :
      g t =
        (1 / Real.sqrt (1 + t ^ 2)) *
          Real.log (t + Real.sqrt (1 + t ^ 2)))
    (hG : G t = (1 / (1 + t ^ 2)) * (1 - t * g t))
    (hS : S x = powerSeries x) :
    S x = negativeClosedForm x := by
  sorry

theorem proof_gap_exercise_3029_30
    (S : ℝ → ℝ) (D : Set ℝ)
    (hD : D = Set.Ioo (-4 : ℝ) 4)
    (hclosed : ∀ x : ℝ, x ∈ D → S x = piecewiseClosedForm x) :
    D = convergenceDomain ∧
      (∀ x : ℝ, x ∈ D → S x = powerSeries x) := by
  sorry

end

end Exercise_3029
