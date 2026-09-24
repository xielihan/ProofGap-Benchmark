import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3655

noncomputable section

def objective (a b : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.1 / a + q.2 / b

def circle : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 = 1}

def epsilon (a b : ℝ) : ℝ :=
  SignType.sign (a * b)

def negativePoint (a b : ℝ) : ℝ × ℝ :=
  (-b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2),
    -a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2))

def positivePoint (a b : ℝ) : ℝ × ℝ :=
  (b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2),
    a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2))

def critical (a b : ℝ) (q : ℝ × ℝ) (lambda : ℝ) : Prop :=
  1 / a + 2 * lambda * q.1 = 0 ∧
    1 / b + 2 * lambda * q.2 = 0 ∧
    q ∈ circle

def minimizers (a b : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ circle ∧ ∀ r ∈ circle, objective a b q ≤ objective a b r}

def maximizers (a b : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ circle ∧ ∀ r ∈ circle, objective a b r ≤ objective a b q}

private theorem objective_geometry (a b : ℝ) (hab : a * b ≠ 0) :
    epsilon a b = a * b / |a * b| ∧
    negativePoint a b ∈ circle ∧
    positivePoint a b ∈ circle ∧
    objective a b (negativePoint a b) =
      -(Real.sqrt (a ^ 2 + b ^ 2) / |a * b|) ∧
    objective a b (positivePoint a b) =
      Real.sqrt (a ^ 2 + b ^ 2) / |a * b| ∧
    ∀ q ∈ circle,
      objective a b (negativePoint a b) ≤ objective a b q ∧
      objective a b q ≤ objective a b (positivePoint a b) ∧
      (objective a b q = objective a b (negativePoint a b) →
        q = negativePoint a b) ∧
      (objective a b q = objective a b (positivePoint a b) →
        q = positivePoint a b) := by
  set_option maxHeartbeats 2000000 in
    have ha : a ≠ 0 := by
      intro ha
      apply hab
      simp [ha]
    have hb : b ≠ 0 := by
      intro hb
      apply hab
      simp [hb]
    have habsne : |a * b| ≠ 0 := abs_ne_zero.mpr hab
    have habspos : 0 < |a * b| := abs_pos.mpr hab
    have hsum : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    have hsqrt : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 hsum
    have hsqrtne : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := hsqrt.ne'
    have hsqrt_sq :
        (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 :=
      Real.sq_sqrt (le_of_lt hsum)
    have heps : epsilon a b = a * b / |a * b| := by
      rcases lt_or_gt_of_ne hab with h | h
      · have hnpos : ¬ 0 < a * b := not_lt_of_ge (le_of_lt h)
        simp [epsilon, SignType.sign, h, hnpos, abs_of_neg h, hab]
      · simp [epsilon, SignType.sign, h, abs_of_pos h, hab]
    have heps_sq : (epsilon a b) ^ 2 = 1 := by
      rw [heps, div_pow, sq_abs]
      field_simp [habsne]
    have hobj (q : ℝ × ℝ) :
        objective a b q =
          epsilon a b * (b * q.1 + a * q.2) / |a * b| := by
      dsimp [objective]
      calc
        q.1 / a + q.2 / b = (b * q.1 + a * q.2) / (a * b) := by
          field_simp [ha, hb]
        _ = epsilon a b * (b * q.1 + a * q.2) / |a * b| := by
          rw [heps]
          field_simp [hab, habsne]
          rw [sq_abs]
          ring
    have hnegc : negativePoint a b ∈ circle := by
      change
        (-b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 +
          (-a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = 1
      calc
        (-b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 +
            (-a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 =
            (a ^ 2 + b ^ 2) * (epsilon a b) ^ 2 /
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by ring
        _ = (a ^ 2 + b ^ 2) /
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by rw [heps_sq, mul_one]
        _ = 1 := by rw [hsqrt_sq]; field_simp [ne_of_gt hsum]
    have hposc : positivePoint a b ∈ circle := by
      change
        (b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 +
          (a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = 1
      calc
        (b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 +
            (a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 =
            (a ^ 2 + b ^ 2) * (epsilon a b) ^ 2 /
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by ring
        _ = (a ^ 2 + b ^ 2) /
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by rw [heps_sq, mul_one]
        _ = 1 := by rw [hsqrt_sq]; field_simp [ne_of_gt hsum]
    have hnegobj :
        objective a b (negativePoint a b) =
          -(Real.sqrt (a ^ 2 + b ^ 2) / |a * b|) := by
      rw [hobj]
      dsimp [negativePoint]
      calc
        epsilon a b *
              (b * (-b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) +
                a * (-a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2))) /
            |a * b| =
            -((a ^ 2 + b ^ 2) * (epsilon a b) ^ 2 /
              (Real.sqrt (a ^ 2 + b ^ 2) * |a * b|)) := by ring
        _ = -(Real.sqrt (a ^ 2 + b ^ 2) / |a * b|) := by
          rw [heps_sq, mul_one]
          field_simp [hsqrtne, habsne] <;> nlinarith [hsqrt_sq]
    have hposobj :
        objective a b (positivePoint a b) =
          Real.sqrt (a ^ 2 + b ^ 2) / |a * b| := by
      rw [hobj]
      dsimp [positivePoint]
      calc
        epsilon a b *
              (b * (b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)) +
                a * (a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2))) /
            |a * b| =
            (a ^ 2 + b ^ 2) * (epsilon a b) ^ 2 /
              (Real.sqrt (a ^ 2 + b ^ 2) * |a * b|) := by ring
        _ = Real.sqrt (a ^ 2 + b ^ 2) / |a * b| := by
          rw [heps_sq, mul_one]
          field_simp [hsqrtne, habsne] <;> nlinarith [hsqrt_sq]
    refine ⟨heps, hnegc, hposc, hnegobj, hposobj, ?_⟩
    intro q hq
    change q.1 ^ 2 + q.2 ^ 2 = 1 at hq
    have hcauchy :
        (b * q.1 + a * q.2) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have hid :
          (b * q.1 + a * q.2) ^ 2 +
              (a * q.1 - b * q.2) ^ 2 =
            (a ^ 2 + b ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by ring
      rw [hq, mul_one] at hid
      nlinarith [sq_nonneg (a * q.1 - b * q.2)]
    have hzsq :
        (epsilon a b * (b * q.1 + a * q.2)) ^ 2 ≤
          a ^ 2 + b ^ 2 := by
      calc
        (epsilon a b * (b * q.1 + a * q.2)) ^ 2 =
            (b * q.1 + a * q.2) ^ 2 := by
          rw [mul_pow, heps_sq, one_mul]
        _ ≤ a ^ 2 + b ^ 2 := hcauchy
    have hzlower :
        -Real.sqrt (a ^ 2 + b ^ 2) ≤
          epsilon a b * (b * q.1 + a * q.2) := by
      nlinarith [hsqrt_sq]
    have hzupper :
        epsilon a b * (b * q.1 + a * q.2) ≤
          Real.sqrt (a ^ 2 + b ^ 2) := by
      nlinarith [hsqrt_sq]
    have hlower :
        objective a b (negativePoint a b) ≤ objective a b q := by
      rw [hnegobj, hobj]
      simpa [neg_div] using
        (div_le_div_iff_of_pos_right habspos).2 hzlower
    have hupper :
        objective a b q ≤ objective a b (positivePoint a b) := by
      rw [hobj, hposobj]
      exact (div_le_div_iff_of_pos_right habspos).2 hzupper
    refine ⟨hlower, hupper, ?_, ?_⟩
    · intro heq
      have hz :
          epsilon a b * (b * q.1 + a * q.2) =
            -Real.sqrt (a ^ 2 + b ^ 2) := by
        rw [hobj, hnegobj] at heq
        field_simp [habsne] at heq
        linarith
      have hbase :
          b * q.1 + a * q.2 =
            -epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          b * q.1 + a * q.2 =
              (epsilon a b) ^ 2 * (b * q.1 + a * q.2) := by
            rw [heps_sq, one_mul]
          _ = epsilon a b *
                (epsilon a b * (b * q.1 + a * q.2)) := by ring
          _ = -epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [hz]
            ring
      have hbase_sq :
          (b * q.1 + a * q.2) ^ 2 = a ^ 2 + b ^ 2 := by
        calc
          (b * q.1 + a * q.2) ^ 2 =
              (epsilon a b * (b * q.1 + a * q.2)) ^ 2 := by
            rw [mul_pow, heps_sq, one_mul]
          _ = a ^ 2 + b ^ 2 := by rw [hz, neg_sq, hsqrt_sq]
      have horth : a * q.1 - b * q.2 = 0 := by
        have hid :
            (b * q.1 + a * q.2) ^ 2 +
                (a * q.1 - b * q.2) ^ 2 =
              (a ^ 2 + b ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by ring
        rw [hq, mul_one, hbase_sq] at hid
        nlinarith [sq_nonneg (a * q.1 - b * q.2)]
      have hxsum :
          (a ^ 2 + b ^ 2) * q.1 =
            -b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          (a ^ 2 + b ^ 2) * q.1 =
              b * (b * q.1 + a * q.2) +
                a * (a * q.1 - b * q.2) := by ring
          _ = -b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [hbase, horth]
            ring
      have hxR :
          q.1 * Real.sqrt (a ^ 2 + b ^ 2) = -b * epsilon a b := by
        apply mul_left_cancel₀ hsqrtne
        calc
          Real.sqrt (a ^ 2 + b ^ 2) *
                (q.1 * Real.sqrt (a ^ 2 + b ^ 2)) =
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * q.1 := by ring
          _ = (a ^ 2 + b ^ 2) * q.1 := by rw [hsqrt_sq]
          _ = -b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := hxsum
          _ = Real.sqrt (a ^ 2 + b ^ 2) * (-b * epsilon a b) := by ring
      have hysum :
          (a ^ 2 + b ^ 2) * q.2 =
            -a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          (a ^ 2 + b ^ 2) * q.2 =
              a * (b * q.1 + a * q.2) -
                b * (a * q.1 - b * q.2) := by ring
          _ = -a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [hbase, horth]
            ring
      have hyR :
          q.2 * Real.sqrt (a ^ 2 + b ^ 2) = -a * epsilon a b := by
        apply mul_left_cancel₀ hsqrtne
        calc
          Real.sqrt (a ^ 2 + b ^ 2) *
                (q.2 * Real.sqrt (a ^ 2 + b ^ 2)) =
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * q.2 := by ring
          _ = (a ^ 2 + b ^ 2) * q.2 := by rw [hsqrt_sq]
          _ = -a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := hysum
          _ = Real.sqrt (a ^ 2 + b ^ 2) * (-a * epsilon a b) := by ring
      apply Prod.ext
      · change q.1 = -b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
        exact (eq_div_iff hsqrtne).2 hxR
      · change q.2 = -a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
        exact (eq_div_iff hsqrtne).2 hyR
    · intro heq
      have hz :
          epsilon a b * (b * q.1 + a * q.2) =
            Real.sqrt (a ^ 2 + b ^ 2) := by
        rw [hobj, hposobj] at heq
        field_simp [habsne] at heq
        linarith
      have hbase :
          b * q.1 + a * q.2 =
            epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          b * q.1 + a * q.2 =
              (epsilon a b) ^ 2 * (b * q.1 + a * q.2) := by
            rw [heps_sq, one_mul]
          _ = epsilon a b *
                (epsilon a b * (b * q.1 + a * q.2)) := by ring
          _ = epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by rw [hz]
      have hbase_sq :
          (b * q.1 + a * q.2) ^ 2 = a ^ 2 + b ^ 2 := by
        calc
          (b * q.1 + a * q.2) ^ 2 =
              (epsilon a b * (b * q.1 + a * q.2)) ^ 2 := by
            rw [mul_pow, heps_sq, one_mul]
          _ = a ^ 2 + b ^ 2 := by rw [hz, hsqrt_sq]
      have horth : a * q.1 - b * q.2 = 0 := by
        have hid :
            (b * q.1 + a * q.2) ^ 2 +
                (a * q.1 - b * q.2) ^ 2 =
              (a ^ 2 + b ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by ring
        rw [hq, mul_one, hbase_sq] at hid
        nlinarith [sq_nonneg (a * q.1 - b * q.2)]
      have hxsum :
          (a ^ 2 + b ^ 2) * q.1 =
            b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          (a ^ 2 + b ^ 2) * q.1 =
              b * (b * q.1 + a * q.2) +
                a * (a * q.1 - b * q.2) := by ring
          _ = b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [hbase, horth]
            ring
      have hxR :
          q.1 * Real.sqrt (a ^ 2 + b ^ 2) = b * epsilon a b := by
        apply mul_left_cancel₀ hsqrtne
        calc
          Real.sqrt (a ^ 2 + b ^ 2) *
                (q.1 * Real.sqrt (a ^ 2 + b ^ 2)) =
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * q.1 := by ring
          _ = (a ^ 2 + b ^ 2) * q.1 := by rw [hsqrt_sq]
          _ = b * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := hxsum
          _ = Real.sqrt (a ^ 2 + b ^ 2) * (b * epsilon a b) := by ring
      have hysum :
          (a ^ 2 + b ^ 2) * q.2 =
            a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc
          (a ^ 2 + b ^ 2) * q.2 =
              a * (b * q.1 + a * q.2) -
                b * (a * q.1 - b * q.2) := by ring
          _ = a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [hbase, horth]
            ring
      have hyR :
          q.2 * Real.sqrt (a ^ 2 + b ^ 2) = a * epsilon a b := by
        apply mul_left_cancel₀ hsqrtne
        calc
          Real.sqrt (a ^ 2 + b ^ 2) *
                (q.2 * Real.sqrt (a ^ 2 + b ^ 2)) =
              (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * q.2 := by ring
          _ = (a ^ 2 + b ^ 2) * q.2 := by rw [hsqrt_sq]
          _ = a * epsilon a b * Real.sqrt (a ^ 2 + b ^ 2) := hysum
          _ = Real.sqrt (a ^ 2 + b ^ 2) * (a * epsilon a b) := by ring
      apply Prod.ext
      · change q.1 = b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
        exact (eq_div_iff hsqrtne).2 hxR
      · change q.2 = a * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
        exact (eq_div_iff hsqrtne).2 hyR

theorem gap1 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → 0 < lambda →
      q.1 = (negativePoint a b).1 := by
  intro q lambda hcrit hlambda
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  have habsne : |a * b| ≠ 0 := abs_ne_zero.mpr hab
  have habspos : 0 < |a * b| := abs_pos.mpr hab
  rcases hcrit with ⟨h₁, h₂, hc⟩
  change q.1 ^ 2 + q.2 ^ 2 = 1 at hc
  have hx : 2 * a * lambda * q.1 = -1 := by
    field_simp [ha] at h₁
    nlinarith [h₁]
  have hy : 2 * b * lambda * q.2 = -1 := by
    field_simp [hb] at h₂
    nlinarith [h₂]
  have hsquare : (2 * lambda * |a * b|) ^ 2 = a ^ 2 + b ^ 2 := by
    calc
      (2 * lambda * |a * b|) ^ 2 =
          (2 * lambda) ^ 2 * |a * b| ^ 2 := by ring
      _ = (2 * a * b * lambda) ^ 2 := by
        rw [sq_abs]
        ring
      _ = (2 * a * b * lambda) ^ 2 * (q.1 ^ 2 + q.2 ^ 2) := by
        rw [hc]
        ring
      _ = b ^ 2 * (2 * a * lambda * q.1) ^ 2 +
          a ^ 2 * (2 * b * lambda * q.2) ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hx, hy]; ring
  have hprod : 0 < 2 * lambda * |a * b| :=
    mul_pos (mul_pos (by norm_num) hlambda) habspos
  have hsqrt :
      Real.sqrt (a ^ 2 + b ^ 2) = 2 * lambda * |a * b| := by
    calc
      Real.sqrt (a ^ 2 + b ^ 2) =
          Real.sqrt ((2 * lambda * |a * b|) ^ 2) :=
        congrArg Real.sqrt hsquare.symm
      _ = 2 * lambda * |a * b| := Real.sqrt_sq (le_of_lt hprod)
  have hsqrtne : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := by
    rw [hsqrt]
    exact hprod.ne'
  have heps := (objective_geometry a b hab).1
  change q.1 = -b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
  apply (eq_div_iff hsqrtne).2
  rw [hsqrt, heps]
  calc
    q.1 * (2 * lambda * |a * b|) =
        (2 * a * lambda * q.1) * (|a * b| / a) := by
      field_simp [ha]
    _ = -(|a * b| / a) := by rw [hx]; ring
    _ = -b * (a * b / |a * b|) := by
      field_simp [ha, habsne]
      rw [sq_abs]
      ring

theorem gap2 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → 0 < lambda →
      q.2 = (negativePoint a b).2 := by
  intro q lambda hcrit hlambda
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  rcases hcrit with ⟨h₁, h₂, hc⟩
  have hx : 2 * a * lambda * q.1 = -1 := by
    field_simp [ha] at h₁
    nlinarith [h₁]
  have hy : 2 * b * lambda * q.2 = -1 := by
    field_simp [hb] at h₂
    nlinarith [h₂]
  have hfac : 2 * lambda ≠ 0 :=
    mul_ne_zero (by norm_num) hlambda.ne'
  have hrel : a * q.1 = b * q.2 := by
    apply mul_left_cancel₀ hfac
    calc
      (2 * lambda) * (a * q.1) = 2 * a * lambda * q.1 := by ring
      _ = -1 := hx
      _ = 2 * b * lambda * q.2 := hy.symm
      _ = (2 * lambda) * (b * q.2) := by ring
  have hq₁ := gap1 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
  have hp :
      a * (negativePoint a b).1 = b * (negativePoint a b).2 := by
    simp [negativePoint]
    ring
  apply mul_left_cancel₀ hb
  calc
    b * q.2 = a * q.1 := hrel.symm
    _ = a * (negativePoint a b).1 := by rw [hq₁]
    _ = b * (negativePoint a b).2 := hp

theorem gap3 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → 0 < lambda →
      objective a b q =
        -(Real.sqrt (a ^ 2 + b ^ 2) / |a * b|) := by
  intro q lambda hcrit hlambda
  have hq : q = negativePoint a b := by
    apply Prod.ext
    · exact gap1 a b hab q lambda hcrit hlambda
    · exact gap2 a b hab q lambda hcrit hlambda
  rw [hq]
  exact (objective_geometry a b hab).2.2.2.1

theorem gap4 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → lambda < 0 →
      q.1 = (positivePoint a b).1 := by
  intro q lambda hcrit hlambda
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  have habsne : |a * b| ≠ 0 := abs_ne_zero.mpr hab
  have habspos : 0 < |a * b| := abs_pos.mpr hab
  rcases hcrit with ⟨h₁, h₂, hc⟩
  change q.1 ^ 2 + q.2 ^ 2 = 1 at hc
  have hx : 2 * a * lambda * q.1 = -1 := by
    field_simp [ha] at h₁
    nlinarith [h₁]
  have hy : 2 * b * lambda * q.2 = -1 := by
    field_simp [hb] at h₂
    nlinarith [h₂]
  have hsquare : (2 * lambda * |a * b|) ^ 2 = a ^ 2 + b ^ 2 := by
    calc
      (2 * lambda * |a * b|) ^ 2 =
          (2 * lambda) ^ 2 * |a * b| ^ 2 := by ring
      _ = (2 * a * b * lambda) ^ 2 := by
        rw [sq_abs]
        ring
      _ = (2 * a * b * lambda) ^ 2 * (q.1 ^ 2 + q.2 ^ 2) := by
        rw [hc]
        ring
      _ = b ^ 2 * (2 * a * lambda * q.1) ^ 2 +
          a ^ 2 * (2 * b * lambda * q.2) ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hx, hy]; ring
  have hprod : 2 * lambda * |a * b| < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hlambda) habspos
  have hnegprod : 0 < -(2 * lambda * |a * b|) := neg_pos.mpr hprod
  have hsqrt :
      Real.sqrt (a ^ 2 + b ^ 2) = -(2 * lambda * |a * b|) := by
    calc
      Real.sqrt (a ^ 2 + b ^ 2) =
          Real.sqrt ((2 * lambda * |a * b|) ^ 2) :=
        congrArg Real.sqrt hsquare.symm
      _ = Real.sqrt ((-(2 * lambda * |a * b|)) ^ 2) := by
        congr 1
        ring
      _ = -(2 * lambda * |a * b|) := Real.sqrt_sq (le_of_lt hnegprod)
  have hsqrtne : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := by
    rw [hsqrt]
    exact hnegprod.ne'
  have heps := (objective_geometry a b hab).1
  change q.1 = b * epsilon a b / Real.sqrt (a ^ 2 + b ^ 2)
  apply (eq_div_iff hsqrtne).2
  rw [hsqrt, heps]
  calc
    q.1 * (-(2 * lambda * |a * b|)) =
        -(2 * a * lambda * q.1) * (|a * b| / a) := by
      field_simp [ha]
    _ = |a * b| / a := by rw [hx]; ring
    _ = b * (a * b / |a * b|) := by
      field_simp [ha, habsne]
      rw [sq_abs]
      ring

theorem gap5 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → lambda < 0 →
      q.2 = (positivePoint a b).2 := by
  intro q lambda hcrit hlambda
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  rcases hcrit with ⟨h₁, h₂, hc⟩
  have hx : 2 * a * lambda * q.1 = -1 := by
    field_simp [ha] at h₁
    nlinarith [h₁]
  have hy : 2 * b * lambda * q.2 = -1 := by
    field_simp [hb] at h₂
    nlinarith [h₂]
  have hfac : 2 * lambda ≠ 0 :=
    mul_ne_zero (by norm_num) hlambda.ne
  have hrel : a * q.1 = b * q.2 := by
    apply mul_left_cancel₀ hfac
    calc
      (2 * lambda) * (a * q.1) = 2 * a * lambda * q.1 := by ring
      _ = -1 := hx
      _ = 2 * b * lambda * q.2 := hy.symm
      _ = (2 * lambda) * (b * q.2) := by ring
  have hq₁ := gap4 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
  have hp :
      a * (positivePoint a b).1 = b * (positivePoint a b).2 := by
    simp [positivePoint]
    ring
  apply mul_left_cancel₀ hb
  calc
    b * q.2 = a * q.1 := hrel.symm
    _ = a * (positivePoint a b).1 := by rw [hq₁]
    _ = b * (positivePoint a b).2 := hp

theorem gap6 (a b : ℝ) (hab : a * b ≠ 0) :
    ∀ q lambda, critical a b q lambda → lambda < 0 →
      objective a b q =
        Real.sqrt (a ^ 2 + b ^ 2) / |a * b| := by
  intro q lambda hcrit hlambda
  have hq : q = positivePoint a b := by
    apply Prod.ext
    · exact gap4 a b hab q lambda hcrit hlambda
    · exact gap5 a b hab q lambda hcrit hlambda
  rw [hq]
  exact (objective_geometry a b hab).2.2.2.2.1

theorem gap7 (a b : ℝ) (hab : a * b ≠ 0) :
    {q | ∃ lambda, critical a b q lambda} =
      ({negativePoint a b, positivePoint a b} : Set (ℝ × ℝ)) := by
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  have habsne : |a * b| ≠ 0 := abs_ne_zero.mpr hab
  have hsum : 0 < a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
  have hsqrt : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 hsum
  rcases objective_geometry a b hab with
    ⟨heps, hnegc, hposc, hnegobj, hposobj, hbounds⟩
  apply Set.ext
  intro q
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨lambda, hcrit⟩
    rcases hcrit with ⟨h₁, h₂, hc⟩
    have hlambda : lambda ≠ 0 := by
      intro hz
      subst lambda
      have hone : 1 / a = 0 := by simpa using h₁
      exact (one_div_ne_zero ha) hone
    rcases lt_or_gt_of_ne hlambda with hlambda | hlambda
    · right
      apply Prod.ext
      · exact gap4 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
      · exact gap5 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
    · left
      apply Prod.ext
      · exact gap1 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
      · exact gap2 a b hab q lambda ⟨h₁, h₂, hc⟩ hlambda
  · intro hq
    rcases hq with hq | hq
    · subst q
      refine ⟨Real.sqrt (a ^ 2 + b ^ 2) / (2 * |a * b|), ?_⟩
      refine ⟨?_, ?_, hnegc⟩
      · dsimp [negativePoint]
        rw [heps]
        field_simp [ha, hb, habsne, hsqrt.ne']
        rw [sq_abs]
        ring
      · dsimp [negativePoint]
        rw [heps]
        field_simp [ha, hb, habsne, hsqrt.ne']
        rw [sq_abs]
        ring
    · subst q
      refine ⟨-(Real.sqrt (a ^ 2 + b ^ 2) / (2 * |a * b|)), ?_⟩
      refine ⟨?_, ?_, hposc⟩
      · dsimp [positivePoint]
        rw [heps]
        field_simp [ha, hb, habsne, hsqrt.ne']
        rw [sq_abs]
        ring
      · dsimp [positivePoint]
        rw [heps]
        field_simp [ha, hb, habsne, hsqrt.ne']
        rw [sq_abs]
        ring

theorem gap8 (a b : ℝ) (hab : a * b ≠ 0) :
    minimizers a b = ({negativePoint a b} : Set (ℝ × ℝ)) := by
  rcases objective_geometry a b hab with
    ⟨heps, hnegc, hposc, hnegobj, hposobj, hbounds⟩
  apply Set.ext
  intro q
  constructor
  · intro hq
    change q ∈ circle ∧
      ∀ r ∈ circle, objective a b q ≤ objective a b r at hq
    have hlower := (hbounds q hq.1).1
    have hupper := hq.2 (negativePoint a b) hnegc
    have heq : objective a b q = objective a b (negativePoint a b) :=
      le_antisymm hupper hlower
    have hpoint := (hbounds q hq.1).2.2.1 heq
    simpa only [Set.mem_singleton_iff] using hpoint
  · intro hq
    have hpoint : q = negativePoint a b := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    change negativePoint a b ∈ circle ∧
      ∀ r ∈ circle,
        objective a b (negativePoint a b) ≤ objective a b r
    exact ⟨hnegc, fun r hr => (hbounds r hr).1⟩

theorem gap9 (a b : ℝ) (hab : a * b ≠ 0) :
    objective a b (negativePoint a b) =
      -(Real.sqrt (a ^ 2 + b ^ 2) / |a * b|) := by
  exact (objective_geometry a b hab).2.2.2.1

theorem gap10 (a b : ℝ) (hab : a * b ≠ 0) :
    maximizers a b = ({positivePoint a b} : Set (ℝ × ℝ)) := by
  rcases objective_geometry a b hab with
    ⟨heps, hnegc, hposc, hnegobj, hposobj, hbounds⟩
  apply Set.ext
  intro q
  constructor
  · intro hq
    change q ∈ circle ∧
      ∀ r ∈ circle, objective a b r ≤ objective a b q at hq
    have hupper := (hbounds q hq.1).2.1
    have hlower := hq.2 (positivePoint a b) hposc
    have heq : objective a b q = objective a b (positivePoint a b) :=
      le_antisymm hupper hlower
    have hpoint := (hbounds q hq.1).2.2.2 heq
    simpa only [Set.mem_singleton_iff] using hpoint
  · intro hq
    have hpoint : q = positivePoint a b := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    change positivePoint a b ∈ circle ∧
      ∀ r ∈ circle,
        objective a b r ≤ objective a b (positivePoint a b)
    exact ⟨hposc, fun r hr => (hbounds r hr).2.1⟩

theorem gap11 (a b : ℝ) (hab : a * b ≠ 0) :
    objective a b (positivePoint a b) =
      Real.sqrt (a ^ 2 + b ^ 2) / |a * b| := by
  exact (objective_geometry a b hab).2.2.2.2.1

end

end ProofGap.Exercise3655
