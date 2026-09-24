import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1574

noncomputable section

def parabolaX (p y : ℝ) : ℝ := y ^ 2 / (2 * p)
def distanceSquared (p y : ℝ) : ℝ :=
  y ^ 4 / (4 * p ^ 2) + 2 * p ^ 2 - 2 * p * y
def optimalY (p : ℝ) : ℝ := Real.cbrt 2 * p
def optimalX (p : ℝ) : ℝ := Real.cbrt 4 / 2 * p

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

private lemma cbrt_cubed_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (Real.cbrt x) ^ 3 = x := by
  unfold Real.cbrt
  rw [← Real.rpow_natCast]
  calc
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℝ) =
        x ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private lemma cbrt_two_cubed : (Real.cbrt 2) ^ 3 = (2 : ℝ) := by
  exact cbrt_cubed_of_nonneg 2 (by norm_num)

private lemma one_lt_real_cbrt_two : 1 < Real.cbrt 2 := by
  let t : ℝ := Real.cbrt 2
  have ht3 : t ^ 3 = 2 := by
    simpa [t] using cbrt_two_cubed
  by_contra h
  have ht : t ≤ 1 := le_of_not_gt h
  have hquad : 0 < t ^ 2 + t + 1 := by
    nlinarith [sq_nonneg (t + (1 / 2 : ℝ))]
  have hmul : 0 ≤ (1 - t) * (t ^ 2 + t + 1) :=
    mul_nonneg (sub_nonneg.mpr ht) hquad.le
  nlinarith [ht3, hmul]

private lemma cbrt_four_eq_cbrt_two_sq :
    Real.cbrt 4 = (Real.cbrt 2) ^ 2 := by
  let t : ℝ := Real.cbrt 2
  let u : ℝ := Real.cbrt 4
  change u = t ^ 2
  have hu3 : u ^ 3 = 4 := by
    simpa [u] using cbrt_cubed_of_nonneg 4 (by norm_num)
  have ht3 : t ^ 3 = 2 := by
    simpa [t] using cbrt_two_cubed
  have ht : 0 < t := by
    have := one_lt_real_cbrt_two
    nlinarith [this]
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have ht4 : 0 < (t ^ 2) ^ 2 := sq_pos_of_pos ht2
  have heqcube : u ^ 3 = (t ^ 2) ^ 3 := by
    calc
      u ^ 3 = 4 := hu3
      _ = (t ^ 3) ^ 2 := by rw [ht3]; norm_num
      _ = (t ^ 2) ^ 3 := by ring
  have hquad : 0 < u ^ 2 + u * t ^ 2 + (t ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (u + t ^ 2 / 2), ht4]
  have hfac :
      (u - t ^ 2) * (u ^ 2 + u * t ^ 2 + (t ^ 2) ^ 2) = 0 := by
    calc
      (u - t ^ 2) * (u ^ 2 + u * t ^ 2 + (t ^ 2) ^ 2) =
          u ^ 3 - (t ^ 2) ^ 3 := by ring
      _ = 0 := by rw [heqcube]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exact False.elim ((ne_of_gt hquad) h)

theorem gap1 (p x y : ℝ) (hp : p ≠ 0) (hpar : y ^ 2 = 2 * p * x) :
    (x - p) ^ 2 + (y - p) ^ 2 = distanceSquared p y := by
  have hden : 2 * p ≠ 0 := mul_ne_zero (by norm_num) hp
  have hx : x = y ^ 2 / (2 * p) := by
    apply (eq_div_iff hden).2
    nlinarith [hpar]
  rw [hx]
  unfold distanceSquared
  field_simp [hp] <;> ring

theorem gap2 (p x y : ℝ) (hpar : y ^ 2 = 2 * p * x) :
    (x - p) ^ 2 + (y - p) ^ 2 =
      x ^ 2 + 2 * p ^ 2 - 2 * p * y := by
  nlinarith [hpar]

theorem gap3 (p y : ℝ) (hp : p ≠ 0) :
    (parabolaX p y) ^ 2 + 2 * p ^ 2 - 2 * p * y =
      distanceSquared p y := by
  unfold parabolaX distanceSquared
  field_simp [hp] <;> ring

theorem gap4 (p y : ℝ) :
    distanceSquared p y =
      y ^ 4 / (4 * p ^ 2) + 2 * p ^ 2 - 2 * p * y := by
  rfl

theorem gap5 (p y : ℝ) (hp : p ≠ 0) :
    deriv (distanceSquared p) y = (y ^ 3 - 2 * p ^ 3) / p ^ 2 := by
  have hsq : HasDerivAt (fun z : ℝ => z * z) (y + y) y := by
    simpa using (hasDerivAt_id y).mul (hasDerivAt_id y)
  have hfourMul :
      HasDerivAt (fun z : ℝ => (z * z) * (z * z))
        ((y + y) * (y * y) + (y * y) * (y + y)) y :=
    hsq.mul hsq
  have hpow4 : HasDerivAt (fun z : ℝ => z ^ 4) (4 * y ^ 3) y := by
    convert hfourMul using 1 <;> ring
  have hquot :
      HasDerivAt (fun z : ℝ => z ^ 4 / (4 * p ^ 2))
        (4 * y ^ 3 / (4 * p ^ 2)) y :=
    hpow4.div_const (4 * p ^ 2)
  have hsum :
      HasDerivAt (fun z : ℝ => z ^ 4 / (4 * p ^ 2) + 2 * p ^ 2)
        (4 * y ^ 3 / (4 * p ^ 2)) y :=
    hquot.add_const (2 * p ^ 2)
  have hlinear :
      HasDerivAt (fun z : ℝ => 2 * p * z) (2 * p) y := by
    convert (hasDerivAt_id y).const_mul (2 * p) using 1 <;> simp
  have hderiv :
      HasDerivAt (distanceSquared p)
        (4 * y ^ 3 / (4 * p ^ 2) - 2 * p) y := by
    simpa [distanceSquared] using hsum.sub hlinear
  rw [hderiv.deriv]
  field_simp [hp] <;> ring

theorem gap6 (p y : ℝ) (hp : 0 < p)
    (hcrit : deriv (distanceSquared p) y = 0) :
    y = optimalY p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  rw [gap5 p y hp0] at hcrit
  field_simp [hp0] at hcrit
  have hycube : y ^ 3 = 2 * p ^ 3 := by
    nlinarith [hcrit]
  let t : ℝ := Real.cbrt 2
  have ht3 : t ^ 3 = 2 := by
    simpa [t] using cbrt_two_cubed
  have ht : 0 < t := by
    have := one_lt_real_cbrt_two
    nlinarith [this]
  have ha : 0 < t * p := mul_pos ht hp
  have ha3 : (t * p) ^ 3 = 2 * p ^ 3 := by
    calc
      (t * p) ^ 3 = t ^ 3 * p ^ 3 := by ring
      _ = 2 * p ^ 3 := by rw [ht3]
  have hquad : 0 < y ^ 2 + y * (t * p) + (t * p) ^ 2 := by
    have ha4 : 0 < (t * p) ^ 2 := sq_pos_of_pos ha
    nlinarith [sq_nonneg (y + (t * p) / 2)]
  have hfac :
      (y - t * p) * (y ^ 2 + y * (t * p) + (t * p) ^ 2) = 0 := by
    calc
      (y - t * p) * (y ^ 2 + y * (t * p) + (t * p) ^ 2) =
          y ^ 3 - (t * p) ^ 3 := by ring
      _ = 0 := by rw [hycube, ha3]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · unfold optimalY
    simpa [t] using sub_eq_zero.mp h
  · exact False.elim ((ne_of_gt hquad) h)

theorem gap7 (p : ℝ) (hp : 0 < p) :
    parabolaX p (optimalY p) = optimalX p := by
  unfold parabolaX optimalY optimalX
  rw [cbrt_four_eq_cbrt_two_sq]
  field_simp [ne_of_gt hp] <;> ring

theorem gap8 (p : ℝ) (hp : 0 < p) :
    IsMinimizerOn (distanceSquared p) Set.univ (optimalY p) := by
  constructor
  · simp
  · intro y hy
    let t : ℝ := Real.cbrt 2
    have ht3 : t ^ 3 = 2 := by
      simpa [t] using cbrt_two_cubed
    have ha3 : (t * p) ^ 3 = 2 * p ^ 3 := by
      rw [mul_pow, ht3]
    change distanceSquared p (t * p) ≤ distanceSquared p y
    have hdiff :
        distanceSquared p y - distanceSquared p (t * p) =
          (y - t * p) ^ 2 *
              ((y + t * p) ^ 2 + 2 * (t * p) ^ 2) /
            (4 * p ^ 2) := by
      calc
        distanceSquared p y - distanceSquared p (t * p) =
            (y ^ 4 - (t * p) ^ 4 -
                8 * p ^ 3 * (y - t * p)) /
              (4 * p ^ 2) := by
                unfold distanceSquared
                field_simp [ne_of_gt hp] <;> ring
        _ = (y ^ 4 - (t * p) ^ 4 -
                4 * (t * p) ^ 3 * (y - t * p)) /
              (4 * p ^ 2) := by
                rw [ha3]
                ring
        _ = (y - t * p) ^ 2 *
              ((y + t * p) ^ 2 + 2 * (t * p) ^ 2) /
            (4 * p ^ 2) := by ring
    have hquad :
        0 ≤ (y + t * p) ^ 2 + 2 * (t * p) ^ 2 := by
      positivity
    have hnum :
        0 ≤ (y - t * p) ^ 2 *
          ((y + t * p) ^ 2 + 2 * (t * p) ^ 2) :=
      mul_nonneg (sq_nonneg _) hquad
    have hden : 0 < 4 * p ^ 2 :=
      mul_pos (by norm_num) (pow_pos hp 2)
    have hnonneg :
        0 ≤ (y - t * p) ^ 2 *
              ((y + t * p) ^ 2 + 2 * (t * p) ^ 2) /
            (4 * p ^ 2) :=
      div_nonneg hnum hden.le
    nlinarith [hdiff, hnonneg]

theorem gap9 (p : ℝ) (hp : 0 < p) :
    Real.sqrt (distanceSquared p (optimalY p)) =
      p * Real.sqrt
        ((Real.cbrt 4 / 2 - 1) ^ 2 + (Real.cbrt 2 - 1) ^ 2) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpar :
      (optimalY p) ^ 2 =
        2 * p * parabolaX p (optimalY p) := by
    unfold parabolaX
    field_simp [hp0] <;> ring
  have hd :=
    gap1 p (parabolaX p (optimalY p)) (optimalY p) hp0 hpar
  rw [gap7 p hp] at hd
  let C : ℝ :=
    (Real.cbrt 4 / 2 - 1) ^ 2 +
      (Real.cbrt 2 - 1) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hds : distanceSquared p (optimalY p) = p ^ 2 * C := by
    calc
      distanceSquared p (optimalY p) =
          (optimalX p - p) ^ 2 + (optimalY p - p) ^ 2 := hd.symm
      _ = p ^ 2 * C := by
        dsimp [C]
        unfold optimalX optimalY
        ring
  rw [hds]
  change Real.sqrt (p ^ 2 * C) = p * Real.sqrt C
  have hprod : 0 ≤ p ^ 2 * C :=
    mul_nonneg (sq_nonneg p) hC
  have hleftsq := Real.sq_sqrt hprod
  have hrightsq := Real.sq_sqrt hC
  have hrsq : (p * Real.sqrt C) ^ 2 = p ^ 2 * C := by
    rw [mul_pow, hrightsq]
  have hleftnonneg := Real.sqrt_nonneg (p ^ 2 * C)
  have hrightnonneg : 0 ≤ p * Real.sqrt C :=
    mul_nonneg hp.le (Real.sqrt_nonneg C)
  nlinarith [hleftsq, hrsq]

theorem gap10 (p : ℝ) (hp : 0 < p) :
    p * Real.sqrt
        ((Real.cbrt 4 / 2 - 1) ^ 2 + (Real.cbrt 2 - 1) ^ 2) =
      p * (Real.cbrt 2 - 1) *
        Real.sqrt (((Real.cbrt 4 - 2) / (2 * (Real.cbrt 2 - 1))) ^ 2 + 1) := by
  let B : ℝ := Real.cbrt 2 - 1
  let A : ℝ := Real.cbrt 4 - 2
  let C : ℝ := (Real.cbrt 4 / 2 - 1) ^ 2 + B ^ 2
  let D : ℝ := (A / (2 * B)) ^ 2 + 1
  have hB : 0 < B := by
    simpa [B] using one_lt_real_cbrt_two
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hCD : C = B ^ 2 * D := by
    dsimp [C, D, A]
    field_simp [ne_of_gt hB] <;> ring
  have hrightsq :
      (B * Real.sqrt D) ^ 2 = B ^ 2 * D := by
    rw [mul_pow, Real.sq_sqrt hD]
  have hrightnonneg : 0 ≤ B * Real.sqrt D :=
    mul_nonneg hB.le (Real.sqrt_nonneg D)
  have hroot : Real.sqrt C = B * Real.sqrt D := by
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, hrightsq]
  change p * Real.sqrt C = p * B * Real.sqrt D
  rw [hroot]
  ring

theorem gap11 (p : ℝ) (hp : 0 < p) :
    p * (Real.cbrt 2 - 1) *
        Real.sqrt (((Real.cbrt 4 - 2) / (2 * (Real.cbrt 2 - 1))) ^ 2 + 1) =
      p * (Real.cbrt 2 - 1) * Real.sqrt ((Real.cbrt 2 + 2) / 2) := by
  let t : ℝ := Real.cbrt 2
  have ht3 : t ^ 3 = 2 := by
    simpa [t] using cbrt_two_cubed
  have ht4 : t ^ 4 = 2 * t := by
    calc
      t ^ 4 = t ^ 3 * t := by ring
      _ = 2 * t := by rw [ht3]
  have hB : 0 < t - 1 := by
    simpa [t] using one_lt_real_cbrt_two
  have hquot :
      (t ^ 2 - 2) / (2 * (t - 1)) = -(t ^ 2) / 2 := by
    field_simp [ne_of_gt hB]
    nlinarith [ht3]
  have hrad :
      ((Real.cbrt 4 - 2) / (2 * (t - 1))) ^ 2 + 1 =
        (t + 2) / 2 := by
    calc
      ((Real.cbrt 4 - 2) / (2 * (t - 1))) ^ 2 + 1 =
          ((t ^ 2 - 2) / (2 * (t - 1))) ^ 2 + 1 := by
            rw [cbrt_four_eq_cbrt_two_sq]
      _ = (-(t ^ 2) / 2) ^ 2 + 1 := by rw [hquot]
      _ = (t + 2) / 2 := by nlinarith [ht4]
  change
    p * (t - 1) *
        Real.sqrt (((Real.cbrt 4 - 2) / (2 * (t - 1))) ^ 2 + 1) =
      p * (t - 1) * Real.sqrt ((t + 2) / 2)
  rw [hrad]

theorem gap12 (p : ℝ) (hp : 0 < p) :
    Real.sqrt (distanceSquared p (optimalY p)) =
      p * (Real.cbrt 2 - 1) * Real.sqrt ((Real.cbrt 2 + 2) / 2) := by
  calc
    Real.sqrt (distanceSquared p (optimalY p)) =
        p * Real.sqrt
          ((Real.cbrt 4 / 2 - 1) ^ 2 +
            (Real.cbrt 2 - 1) ^ 2) := gap9 p hp
    _ = p * (Real.cbrt 2 - 1) *
          Real.sqrt
            (((Real.cbrt 4 - 2) /
                (2 * (Real.cbrt 2 - 1))) ^ 2 + 1) := gap10 p hp
    _ = p * (Real.cbrt 2 - 1) *
          Real.sqrt ((Real.cbrt 2 + 2) / 2) := gap11 p hp

end

end ProofGap.Exercise1574
