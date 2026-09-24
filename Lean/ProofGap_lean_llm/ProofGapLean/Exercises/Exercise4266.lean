import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4266

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  x ^ 4 + 4 * x * y ^ 3

def Q (x y : ℝ) : ℝ :=
  6 * x ^ 2 * y ^ 2 - 5 * y ^ 4

def field (z : Point) : Point :=
  (P z.1 z.2, Q z.1 z.2)

def potential (z : Point) : ℝ :=
  z.1 ^ 5 / 5 + 2 * z.1 ^ 2 * z.2 ^ 3 - z.2 ^ 5

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (U : Point → ℝ) (z v : Point) : ℝ :=
  deriv (fun x => U (x, z.2)) z.1 * v.1 +
    deriv (fun y => U (z.1, y)) z.2 * v.2

def expandedDifferential (z v : Point) : ℝ :=
  z.1 ^ 4 * v.1 +
    2 * z.2 ^ 3 * (2 * z.1 * v.1) +
    2 * z.1 ^ 2 * (3 * z.2 ^ 2 * v.2) -
    5 * z.2 ^ 4 * v.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def brokenPathIntegral : ℝ :=
  (∫ x in (-2 : ℝ)..3, P x 0) +
    ∫ y in (-1 : ℝ)..0, Q (-2) y

private theorem hasDerivAt_pow_succ_of
    {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun t => (f t) ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * (f x) ^ n * f') x := by
  induction n with
  | zero =>
      simpa using h
  | succ n ih =>
      convert ih.mul h using 1 <;>
        simp [pow_succ, Nat.cast_add, Nat.cast_one] <;>
        ring

private theorem potential_hasCoordinateGradientAt (z : Point) :
    HasCoordinateGradientAt potential (field z) z := by
  rcases z with ⟨x, y⟩
  change
    HasDerivAt
        (fun s : ℝ => s ^ 5 / 5 + 2 * s ^ 2 * y ^ 3 - y ^ 5)
        (x ^ 4 + 4 * x * y ^ 3) x ∧
      HasDerivAt
        (fun t : ℝ => x ^ 5 / 5 + 2 * x ^ 2 * t ^ 3 - t ^ 5)
        (6 * x ^ 2 * y ^ 2 - 5 * y ^ 4) y
  constructor
  · convert
      (((hasDerivAt_pow_succ_of (hasDerivAt_id x) 4).div_const 5).add
        ((hasDerivAt_pow_succ_of (hasDerivAt_id x) 1).const_mul
          (2 * y ^ 3))).sub_const (y ^ 5) using 1 <;>
      (try funext u) <;>
      (try simp [id]) <;>
      ring
  · convert
      (((hasDerivAt_pow_succ_of (hasDerivAt_id y) 2).const_mul
        (2 * x ^ 2)).add_const (x ^ 5 / 5)).sub
          (hasDerivAt_pow_succ_of (hasDerivAt_id y) 4) using 1 <;>
      (try funext u) <;>
      (try simp [id]) <;>
      ring

private theorem brokenPathIntegral_eq_sixtytwo :
    brokenPathIntegral = 62 := by
  have hpow4 (a b : ℝ) :
      (∫ x in a..b, x ^ 4) = b ^ 5 / 5 - a ^ 5 / 5 := by
    have hF (x : ℝ) :
        HasDerivAt (fun t : ℝ => t ^ 5 / 5) (x ^ 4) x := by
      convert
        (hasDerivAt_pow_succ_of (hasDerivAt_id x) 4).div_const 5
          using 1 <;>
        (try funext u) <;>
        (try simp [id]) <;>
        ring
    have hd :
        deriv (fun t : ℝ => t ^ 5 / 5) = fun x : ℝ => x ^ 4 := by
      funext x
      exact (hF x).deriv
    calc
      (∫ x in a..b, x ^ 4) =
          ∫ x in a..b, deriv (fun t : ℝ => t ^ 5 / 5) x := by
        rw [hd]
      _ = b ^ 5 / 5 - a ^ 5 / 5 :=
        intervalIntegral.integral_deriv_eq_sub
          (fun x _ => (hF x).differentiableAt)
          (by
            rw [hd]
            exact (continuous_id.pow 4).intervalIntegrable a b)
  have hpoly (a b : ℝ) :
      (∫ y in a..b, 24 * y ^ 2 - 5 * y ^ 4) =
        (8 * b ^ 3 - b ^ 5) - (8 * a ^ 3 - a ^ 5) := by
    have hF (y : ℝ) :
        HasDerivAt (fun t : ℝ => 8 * t ^ 3 - t ^ 5)
          (24 * y ^ 2 - 5 * y ^ 4) y := by
      convert
        (hasDerivAt_pow_succ_of (hasDerivAt_id y) 2).const_mul 8 |>.sub
          (hasDerivAt_pow_succ_of (hasDerivAt_id y) 4) using 1 <;>
        (try funext u) <;>
        (try simp [id]) <;>
        ring
    have hd :
        deriv (fun t : ℝ => 8 * t ^ 3 - t ^ 5) =
          fun y : ℝ => 24 * y ^ 2 - 5 * y ^ 4 := by
      funext y
      exact (hF y).deriv
    have hc : Continuous (fun y : ℝ => 24 * y ^ 2 - 5 * y ^ 4) :=
      (continuous_const.mul (continuous_id.pow 2)).sub
        (continuous_const.mul (continuous_id.pow 4))
    calc
      (∫ y in a..b, 24 * y ^ 2 - 5 * y ^ 4) =
          ∫ y in a..b, deriv (fun t : ℝ => 8 * t ^ 3 - t ^ 5) y := by
        rw [hd]
      _ = (8 * b ^ 3 - b ^ 5) - (8 * a ^ 3 - a ^ 5) :=
        intervalIntegral.integral_deriv_eq_sub
          (fun y _ => (hF y).differentiableAt)
          (by
            rw [hd]
            exact hc.intervalIntegrable a b)
  unfold brokenPathIntegral
  simp [P, Q]
  rw [hpow4 (-2) 3]
  have hsecond :
      (∫ y in (-1 : ℝ)..0, 6 * 2 ^ 2 * y ^ 2 - 5 * y ^ 4) =
        (8 * 0 ^ 3 - 0 ^ 5) -
          (8 * (-1) ^ 3 - (-1) ^ 5) := by
    calc
      (∫ y in (-1 : ℝ)..0, 6 * 2 ^ 2 * y ^ 2 - 5 * y ^ 4) =
          ∫ y in (-1 : ℝ)..0, 24 * y ^ 2 - 5 * y ^ 4 := by
        apply intervalIntegral.integral_congr
        intro y hy
        ring
      _ = (8 * 0 ^ 3 - 0 ^ 5) -
          (8 * (-1) ^ 3 - (-1) ^ 5) := hpoly (-1) 0
  rw [hsecond]
  norm_num

private theorem lineIntegral_eq_potential_sub
    (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ) :
    lineIntegral γ = potential (γ 1) - potential (γ 0) := by
  have hx : ContDiff ℝ 1 (fun t => (γ t).1) := hγ.fst
  have hy : ContDiff ℝ 1 (fun t => (γ t).2) := hγ.snd
  have hdx (t : ℝ) :
      HasDerivAt (fun s => (γ s).1)
        (deriv (fun s => (γ s).1) t) t :=
    (hx.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdy (t : ℝ) :
      HasDerivAt (fun s => (γ s).2)
        (deriv (fun s => (γ s).2) t) t :=
    (hy.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hpot (t : ℝ) :
      HasDerivAt (fun s => potential (γ s))
        (P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
          Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t) t := by
    change HasDerivAt
      (fun s =>
        (γ s).1 ^ 5 / 5 + 2 * (γ s).1 ^ 2 * (γ s).2 ^ 3 -
          (γ s).2 ^ 5)
      (((γ t).1 ^ 4 + 4 * (γ t).1 * (γ t).2 ^ 3) *
          deriv (fun s => (γ s).1) t +
        (6 * (γ t).1 ^ 2 * (γ t).2 ^ 2 - 5 * (γ t).2 ^ 4) *
          deriv (fun s => (γ s).2) t) t
    convert
      (((hasDerivAt_pow_succ_of (hdx t) 4).div_const 5).add
        (((hasDerivAt_pow_succ_of (hdx t) 1).mul
          (hasDerivAt_pow_succ_of (hdy t) 2)).const_mul 2)).sub
            (hasDerivAt_pow_succ_of (hdy t) 4) using 1 <;>
      (try funext u) <;>
      (try simp [id]) <;>
      ring
  have htwo : ContDiff ℝ 1 (fun _ : ℝ => (2 : ℝ)) := contDiff_const
  have hpotential : ContDiff ℝ 1 (fun t => potential (γ t)) := by
    simpa only [potential, mul_assoc] using
      (((hx.pow 5).div_const 5).add
        (htwo.mul ((hx.pow 2).mul (hy.pow 3)))).sub (hy.pow 5)
  have hderiv_cont : Continuous (deriv (fun t => potential (γ t))) := by
    simpa only [deriv] using
      ((hpotential.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  calc
    lineIntegral γ =
        ∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t := by
      simp only [lineIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hpot t).deriv.symm
    _ = potential (γ 1) - potential (γ 0) :=
      intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (hpot t).differentiableAt)
        (hderiv_cont.intervalIntegrable 0 1)

theorem gap1 (x y : ℝ) :
    HasDerivAt (fun s => Q s y) (12 * x * y ^ 2) x := by
  change HasDerivAt
    (fun s : ℝ => 6 * s ^ 2 * y ^ 2 - 5 * y ^ 4)
    (12 * x * y ^ 2) x
  convert
    ((hasDerivAt_pow_succ_of (hasDerivAt_id x) 1).const_mul
      (6 * y ^ 2)).sub_const (5 * y ^ 4) using 1 <;>
    (try funext u) <;>
    (try simp [id]) <;>
    ring

theorem gap2 (x y : ℝ) :
    HasDerivAt (fun t => P x t) (12 * x * y ^ 2) y := by
  change HasDerivAt
    (fun t : ℝ => x ^ 4 + 4 * x * t ^ 3)
    (12 * x * y ^ 2) y
  convert
    ((hasDerivAt_pow_succ_of (hasDerivAt_id y) 2).const_mul
      (4 * x)).add_const (x ^ 4) using 1 <;>
    (try funext u) <;>
    (try simp [id]) <;>
    ring

theorem gap3 (x y : ℝ) :
    deriv (fun s => Q s y) x = deriv (fun t => P x t) y := by
  rw [(gap1 x y).deriv, (gap2 x y).deriv]

theorem gap4 :
    ∃ U : Point → ℝ, ∀ z,
      HasCoordinateGradientAt U (field z) z := by
  exact ⟨potential, fun z => potential_hasCoordinateGradientAt z⟩

theorem gap5 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (-2, -1) (3, 0)) :
    lineIntegral γ = brokenPathIntegral := by
  calc
    lineIntegral γ = potential (γ 1) - potential (γ 0) :=
      lineIntegral_eq_potential_sub γ hγ.1
    _ = 62 := by
      rw [hγ.2.2, hγ.2.1]
      norm_num [potential]
    _ = brokenPathIntegral := brokenPathIntegral_eq_sixtytwo.symm

theorem gap6 :
    brokenPathIntegral = 55 + 7 := by
  calc
    brokenPathIntegral = 62 := brokenPathIntegral_eq_sixtytwo
    _ = 55 + 7 := by norm_num

theorem gap7 :
    (55 : ℝ) + 7 = 62 := by
  norm_num

theorem gap8 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (-2, -1) (3, 0)) :
    lineIntegral γ = 62 := by
  calc
    lineIntegral γ = brokenPathIntegral := gap5 γ hγ
    _ = 55 + 7 := gap6
    _ = 62 := gap7

theorem gap9 (z v : Point) :
    coordinateDifferential (field z) v = expandedDifferential z v := by
  rcases z with ⟨x, y⟩
  rcases v with ⟨a, b⟩
  simp [coordinateDifferential, field, expandedDifferential, P, Q]
  ring

theorem gap10 (z v : Point) :
    expandedDifferential z v = differential potential z v := by
  rcases z with ⟨x, y⟩
  rcases v with ⟨a, b⟩
  have hx :
      deriv (fun s => potential (s, y)) x = P x y := by
    simpa [field] using
      (potential_hasCoordinateGradientAt (x, y)).1.deriv
  have hy :
      deriv (fun t => potential (x, t)) y = Q x y := by
    simpa [field] using
      (potential_hasCoordinateGradientAt (x, y)).2.deriv
  change expandedDifferential (x, y) (a, b) =
    deriv (fun s => potential (s, y)) x * a +
      deriv (fun t => potential (x, t)) y * b
  rw [hx, hy]
  simp [expandedDifferential, P, Q]
  ring

theorem gap11 (z v : Point) :
    coordinateDifferential (field z) v = differential potential z v := by
  rw [gap9 z v, gap10 z v]

theorem gap12 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (-2, -1) (3, 0)) :
    lineIntegral γ = potential (3, 0) - potential (-2, -1) := by
  calc
    lineIntegral γ = 62 := gap8 γ hγ
    _ = potential (3, 0) - potential (-2, -1) := by
      norm_num [potential]

theorem gap13 :
    potential (3, 0) - potential (-2, -1) = 62 := by
  norm_num [potential]

theorem gap14 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (-2, -1) (3, 0)) :
    lineIntegral γ = 62 := by
  exact gap8 γ hγ

end

end ProofGap.Exercise4266
