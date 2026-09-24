import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2863

noncomputable section

def upperUnit (α : ℝ) : ℂ :=
  (Real.cos α : ℂ) + Complex.I * Real.sin α

def lowerUnit (α : ℝ) : ℂ :=
  (Real.cos α : ℂ) - Complex.I * Real.sin α

def complexGeometricTerm (x : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ n * z ^ n

def pairedCosineTerm (x α : ℝ) (n : ℕ) : ℂ :=
  let m := n + 1
  (x : ℂ) ^ m *
    ((Real.cos (m * α) : ℂ) - Complex.I * Real.sin (m * α) +
      (Real.cos (m * α) : ℂ) + Complex.I * Real.sin (m * α))

def cosineSeriesTerm (x α : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  x ^ m * Real.cos (m * α)

private theorem upper_mul_lower (α : ℝ) :
    upperUnit α * lowerUnit α = 1 := by
  have hI : Complex.I * Complex.I = (-1 : ℂ) := by
    norm_num
  have htrigR :
      Real.cos α * Real.cos α + Real.sin α * Real.sin α = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have htrigC :
      (Real.cos α : ℂ) * (Real.cos α : ℂ) +
          (Real.sin α : ℂ) * (Real.sin α : ℂ) = 1 := by
    exact_mod_cast htrigR
  rw [upperUnit, lowerUnit]
  calc
    ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) *
        ((Real.cos α : ℂ) - Complex.I * (Real.sin α : ℂ)) =
        (Real.cos α : ℂ) * (Real.cos α : ℂ) -
          (Complex.I * Complex.I) *
            ((Real.sin α : ℂ) * (Real.sin α : ℂ)) := by ring
    _ = (Real.cos α : ℂ) * (Real.cos α : ℂ) +
          (Real.sin α : ℂ) * (Real.sin α : ℂ) := by
      rw [hI]
      ring
    _ = 1 := htrigC

private theorem upper_add_lower (α : ℝ) :
    upperUnit α + lowerUnit α = 2 * (Real.cos α : ℂ) := by
  rw [upperUnit, lowerUnit]
  ring

private theorem denominator_factor (x α : ℝ) :
    (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) =
      ((x : ℂ) - upperUnit α) * ((x : ℂ) - lowerUnit α) := by
  have hcast :
      (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) =
        (1 : ℂ) - 2 * (x : ℂ) * (Real.cos α : ℂ) + (x : ℂ) ^ 2 := by
    norm_cast
  calc
    (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) =
        (1 : ℂ) - 2 * (x : ℂ) * (Real.cos α : ℂ) + (x : ℂ) ^ 2 := hcast
    _ = (x : ℂ) ^ 2 -
          (x : ℂ) * (upperUnit α + lowerUnit α) +
          upperUnit α * lowerUnit α := by
      rw [upper_add_lower, upper_mul_lower]
      ring
    _ = ((x : ℂ) - upperUnit α) *
          ((x : ℂ) - lowerUnit α) := by ring

private theorem factor_ne_zero (x α : ℝ)
    (hD : 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0) :
    (x : ℂ) - upperUnit α ≠ 0 ∧ (x : ℂ) - lowerUnit α ≠ 0 := by
  have hc : (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hD
  have hp :
      ((x : ℂ) - upperUnit α) * ((x : ℂ) - lowerUnit α) ≠ 0 := by
    rw [← denominator_factor]
    exact hc
  exact mul_ne_zero_iff.mp hp

private theorem denominator_ne_zero_of_abs_lt_one (x α : ℝ)
    (hx : |x| < 1) :
    1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 := by
  intro hzero
  rcases abs_lt.mp hx with ⟨hxneg, hxpos⟩
  have hrepr :
      1 - 2 * x * Real.cos α + x ^ 2 =
        (x - Real.cos α) ^ 2 + (Real.sin α) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  rw [hrepr] at hzero
  have hs : (Real.sin α) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - Real.cos α), sq_nonneg (Real.sin α)]
  have hxc : x = Real.cos α := by
    nlinarith [sq_nonneg (x - Real.cos α), sq_nonneg (Real.sin α)]
  have hx2 : x ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hp : 0 < (x + 1) * (1 - x) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

private theorem norm_upperUnit (α : ℝ) : ‖upperUnit α‖ = 1 := by
  have hsq : Complex.normSq (upperUnit α) = 1 := by
    change
      (upperUnit α).re * (upperUnit α).re +
          (upperUnit α).im * (upperUnit α).im = 1
    simpa [upperUnit, pow_two, add_comm] using
      (Real.sin_sq_add_cos_sq α)
  rw [Complex.norm_def, hsq]
  norm_num

private theorem norm_lowerUnit (α : ℝ) : ‖lowerUnit α‖ = 1 := by
  have hnorm :=
    congrArg (fun z : ℂ => ‖z‖) (upper_mul_lower α)
  simpa [norm_mul, norm_upperUnit] using hnorm

private theorem upperUnit_pow (α : ℝ) (n : ℕ) :
    upperUnit α ^ n =
      (Real.cos ((n : ℝ) * α) : ℂ) +
        Complex.I * Real.sin ((n : ℝ) * α) := by
  induction n with
  | zero => norm_num [upperUnit]
  | succ n ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_succ, add_mul, one_mul,
        Real.cos_add, Real.sin_add]
      apply Complex.ext <;>
        simp [upperUnit] <;>
        ring

private theorem lowerUnit_pow (α : ℝ) (n : ℕ) :
    lowerUnit α ^ n =
      (Real.cos ((n : ℝ) * α) : ℂ) -
        Complex.I * Real.sin ((n : ℝ) * α) := by
  induction n with
  | zero => norm_num [lowerUnit]
  | succ n ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_succ, add_mul, one_mul,
        Real.cos_add, Real.sin_add]
      apply Complex.ext <;>
        simp [lowerUnit] <;>
        ring

private theorem pairedCosineTerm_eq (x α : ℝ) (n : ℕ) :
    pairedCosineTerm x α n =
      (((x : ℂ) * lowerUnit α) ^ (n + 1) +
        ((x : ℂ) * upperUnit α) ^ (n + 1)) := by
  simp only [pairedCosineTerm]
  rw [mul_pow, mul_pow, lowerUnit_pow, upperUnit_pow]
  ring

private theorem half_re_paired (x α : ℝ) (n : ℕ) :
    (1 / 2 : ℝ) * Complex.re (pairedCosineTerm x α n) =
      cosineSeriesTerm x α n := by
  have hxpow :
      (x : ℂ) ^ (n + 1) = ((x ^ (n + 1) : ℝ) : ℂ) := by
    norm_cast
  have hpair :
      pairedCosineTerm x α n =
        (((2 * x ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * α) : ℝ) : ℂ)) := by
    calc
      pairedCosineTerm x α n =
          (2 : ℂ) * ((x ^ (n + 1) : ℝ) : ℂ) *
            (Real.cos (((n + 1 : ℕ) : ℝ) * α) : ℂ) := by
        simp only [pairedCosineTerm]
        rw [hxpow]
        ring
      _ = (((2 * x ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * α) : ℝ) : ℂ)) := by
        norm_cast
  rw [hpair]
  simp only [cosineSeriesTerm]
  change
    (1 / 2 : ℝ) *
        (2 * x ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * α)) =
      x ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α)
  ring

private theorem norm_mul_unit_lt_one (x : ℝ) (z : ℂ)
    (hx : |x| < 1) (hz : ‖z‖ = 1) :
    ‖(x : ℂ) * z‖ < 1 := by
  simpa [norm_mul, hz, Real.norm_eq_abs] using hx

private theorem geometric_tsum_of_unit_norm (x : ℝ) (z : ℂ)
    (hx : |x| < 1) (hz : ‖z‖ = 1) :
    (∑' n, complexGeometricTerm x n z) =
      1 / (1 - (x : ℂ) * z) := by
  have hq : ‖(x : ℂ) * z‖ < 1 :=
    norm_mul_unit_lt_one x z hx hz
  calc
    (∑' n, complexGeometricTerm x n z) =
        ∑' n, ((x : ℂ) * z) ^ n := by
          apply tsum_congr
          intro n
          simp [complexGeometricTerm, mul_pow]
    _ = 1 / (1 - (x : ℂ) * z) := by
      simpa [div_eq_mul_inv] using
        (hasSum_geometric_of_norm_lt_one hq).tsum_eq

private theorem hasSum_paired (x α : ℝ) (hx : |x| < 1) :
    HasSum (fun n => pairedCosineTerm x α n)
      (((x : ℂ) * lowerUnit α) *
          (1 - (x : ℂ) * lowerUnit α)⁻¹ +
        ((x : ℂ) * upperUnit α) *
          (1 - (x : ℂ) * upperUnit α)⁻¹) := by
  let ql : ℂ := (x : ℂ) * lowerUnit α
  let qu : ℂ := (x : ℂ) * upperUnit α
  have hql : ‖ql‖ < 1 := by
    dsimp [ql]
    exact norm_mul_unit_lt_one x (lowerUnit α) hx (norm_lowerUnit α)
  have hqu : ‖qu‖ < 1 := by
    dsimp [qu]
    exact norm_mul_unit_lt_one x (upperUnit α) hx (norm_upperUnit α)
  have hl : HasSum (fun n : ℕ => ql ^ (n + 1))
      (ql * (1 - ql)⁻¹) := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hql).mul_left ql
  have hu : HasSum (fun n : ℕ => qu ^ (n + 1))
      (qu * (1 - qu)⁻¹) := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hqu).mul_left qu
  change HasSum (fun n => pairedCosineTerm x α n)
    (ql * (1 - ql)⁻¹ + qu * (1 - qu)⁻¹)
  simpa only [pairedCosineTerm_eq] using hl.add hu

private theorem half_re_mul (z : ℂ) :
    Complex.re ((1 / 2 : ℂ) * z) =
      (1 / 2 : ℝ) * Complex.re z := by
  norm_num

theorem gap1 :
    ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
      (((x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        -1 - (1 / 2 : ℂ) *
          (upperUnit α / ((x : ℂ) - upperUnit α) +
            lowerUnit α / ((x : ℂ) - lowerUnit α)) := by
  intro x α hD
  rcases factor_ne_zero x α hD with ⟨hu, hl⟩
  have hcast :
      (((x * Real.cos α - x ^ 2) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        (((x * Real.cos α - x ^ 2 : ℝ) : ℂ) /
          ((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) := by
    norm_cast
  have hnum :
      ((x * Real.cos α - x ^ 2 : ℝ) : ℂ) =
        (x : ℂ) * (Real.cos α : ℂ) - (x : ℂ) ^ 2 := by
    norm_cast
  have hp :
      ((x : ℂ) - upperUnit α) * ((x : ℂ) - lowerUnit α) ≠ 0 :=
    mul_ne_zero hu hl
  have hcomb :
      upperUnit α * ((x : ℂ) - lowerUnit α) +
          ((x : ℂ) - upperUnit α) * lowerUnit α =
        2 * ((x : ℂ) * (Real.cos α : ℂ) - 1) := by
    calc
      upperUnit α * ((x : ℂ) - lowerUnit α) +
          ((x : ℂ) - upperUnit α) * lowerUnit α =
          (x : ℂ) * (upperUnit α + lowerUnit α) -
            2 * (upperUnit α * lowerUnit α) := by ring
      _ = 2 * ((x : ℂ) * (Real.cos α : ℂ) - 1) := by
        rw [upper_add_lower, upper_mul_lower]
        ring
  have hfrac :
      upperUnit α / ((x : ℂ) - upperUnit α) +
          lowerUnit α / ((x : ℂ) - lowerUnit α) =
        (2 * ((x : ℂ) * (Real.cos α : ℂ) - 1)) /
          (((x : ℂ) - upperUnit α) *
            ((x : ℂ) - lowerUnit α)) := by
    field_simp [hu, hl]
    exact hcomb
  have hfactor :
      ((x : ℂ) - upperUnit α) * ((x : ℂ) - lowerUnit α) =
        (x : ℂ) ^ 2 - 2 * (x : ℂ) * (Real.cos α : ℂ) + 1 := by
    calc
      ((x : ℂ) - upperUnit α) * ((x : ℂ) - lowerUnit α) =
          (x : ℂ) ^ 2 -
            (x : ℂ) * (upperUnit α + lowerUnit α) +
            upperUnit α * lowerUnit α := by ring
      _ = (x : ℂ) ^ 2 - 2 * (x : ℂ) * (Real.cos α : ℂ) + 1 := by
        rw [upper_add_lower, upper_mul_lower]
        ring
  rw [hcast, hnum, denominator_factor, hfrac]
  field_simp [hp]
  rw [hfactor]
  ring

theorem gap2
    (hpartial :
      ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
        (((x * Real.cos α - x ^ 2) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          -1 - (1 / 2 : ℂ) *
            (upperUnit α / ((x : ℂ) - upperUnit α) +
              lowerUnit α / ((x : ℂ) - lowerUnit α))) :
    ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
      (((x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        -1 + (1 / 2 : ℂ) *
          (1 / (1 - (x : ℂ) * lowerUnit α) +
            1 / (1 - (x : ℂ) * upperUnit α)) := by
  intro x α hD
  rcases factor_ne_zero x α hD with ⟨hu, hl⟩
  have hul : upperUnit α * lowerUnit α = 1 := upper_mul_lower α
  have hlu : lowerUnit α * upperUnit α = 1 := by
    simpa [mul_comm] using hul
  have hune : upperUnit α ≠ 0 := by
    intro h
    rw [h, zero_mul] at hul
    exact zero_ne_one hul
  have hlne : lowerUnit α ≠ 0 := by
    intro h
    rw [h, zero_mul] at hlu
    exact zero_ne_one hlu
  have hidu :
      (x : ℂ) - upperUnit α =
        -upperUnit α * (1 - (x : ℂ) * lowerUnit α) := by
    calc
      (x : ℂ) - upperUnit α =
          (x : ℂ) * (upperUnit α * lowerUnit α) - upperUnit α := by
        rw [hul]
        ring
      _ = -upperUnit α * (1 - (x : ℂ) * lowerUnit α) := by ring
  have hidl :
      (x : ℂ) - lowerUnit α =
        -lowerUnit α * (1 - (x : ℂ) * upperUnit α) := by
    calc
      (x : ℂ) - lowerUnit α =
          (x : ℂ) * (lowerUnit α * upperUnit α) - lowerUnit α := by
        rw [hlu]
        ring
      _ = -lowerUnit α * (1 - (x : ℂ) * upperUnit α) := by ring
  have hleft : 1 - (x : ℂ) * lowerUnit α ≠ 0 := by
    intro h
    apply hu
    rw [hidu, h]
    ring
  have hright : 1 - (x : ℂ) * upperUnit α ≠ 0 := by
    intro h
    apply hl
    rw [hidl, h]
    ring
  have hufrac :
      upperUnit α / ((x : ℂ) - upperUnit α) =
        -1 / (1 - (x : ℂ) * lowerUnit α) := by
    rw [hidu]
    field_simp [hune, hleft]
  have hlfrac :
      lowerUnit α / ((x : ℂ) - lowerUnit α) =
        -1 / (1 - (x : ℂ) * upperUnit α) := by
    rw [hidl]
    field_simp [hlne, hright]
  rw [hpartial x α hD, hufrac, hlfrac]
  ring

theorem gap3
    (hgeometricForm :
      ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
        (((x * Real.cos α - x ^ 2) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          -1 + (1 / 2 : ℂ) *
            (1 / (1 - (x : ℂ) * lowerUnit α) +
              1 / (1 - (x : ℂ) * upperUnit α))) :
    ∀ x α : ℝ, |x| < 1 →
      (((x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        -1 + (1 / 2 : ℂ) *
          ((∑' n, complexGeometricTerm x n (lowerUnit α)) +
            (∑' n, complexGeometricTerm x n (upperUnit α))) := by
  intro x α hx
  have hD := denominator_ne_zero_of_abs_lt_one x α hx
  rw [hgeometricForm x α hD]
  rw [geometric_tsum_of_unit_norm x (lowerUnit α) hx (norm_lowerUnit α)]
  rw [geometric_tsum_of_unit_norm x (upperUnit α) hx (norm_upperUnit α)]

theorem gap4
    (hcomplexSeries :
      ∀ x α : ℝ, |x| < 1 →
        (((x * Real.cos α - x ^ 2) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          -1 + (1 / 2 : ℂ) *
            ((∑' n, complexGeometricTerm x n (lowerUnit α)) +
              (∑' n, complexGeometricTerm x n (upperUnit α)))) :
    ∀ x α : ℝ, |x| < 1 →
      (((x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * (∑' n, pairedCosineTerm x α n) := by
  intro x α hx
  let ql : ℂ := (x : ℂ) * lowerUnit α
  let qu : ℂ := (x : ℂ) * upperUnit α
  have hql : ‖ql‖ < 1 := by
    dsimp [ql]
    exact norm_mul_unit_lt_one x (lowerUnit α) hx (norm_lowerUnit α)
  have hqu : ‖qu‖ < 1 := by
    dsimp [qu]
    exact norm_mul_unit_lt_one x (upperUnit α) hx (norm_upperUnit α)
  have hqlne : ql ≠ 1 := by
    intro h
    rw [h] at hql
    simpa using hql
  have hqune : qu ≠ 1 := by
    intro h
    rw [h] at hqu
    simpa using hqu
  have hlDen : 1 - ql ≠ 0 := sub_ne_zero.mpr hqlne.symm
  have huDen : 1 - qu ≠ 0 := sub_ne_zero.mpr hqune.symm
  rw [hcomplexSeries x α hx]
  rw [geometric_tsum_of_unit_norm x (lowerUnit α) hx (norm_lowerUnit α)]
  rw [geometric_tsum_of_unit_norm x (upperUnit α) hx (norm_upperUnit α)]
  rw [(hasSum_paired x α hx).tsum_eq]
  change
    -1 + (1 / 2 : ℂ) *
        (1 / (1 - ql) + 1 / (1 - qu)) =
      (1 / 2 : ℂ) *
        (ql * (1 - ql)⁻¹ + qu * (1 - qu)⁻¹)
  field_simp [hlDen, huDen]
  ring

theorem gap5
    (hpaired :
      ∀ x α : ℝ, |x| < 1 →
        (((x * Real.cos α - x ^ 2) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          (1 / 2 : ℂ) * (∑' n, pairedCosineTerm x α n)) :
    ∀ x α : ℝ, |x| < 1 →
      (x * Real.cos α - x ^ 2) / (1 - 2 * x * Real.cos α + x ^ 2) =
        ∑' n, cosineSeriesTerm x α n := by
  intro x α hx
  have hp : Summable (fun n => pairedCosineTerm x α n) :=
    (hasSum_paired x α hx).summable
  have hrealHas :
      HasSum (fun n => Complex.re (pairedCosineTerm x α n))
        (Complex.re (∑' n, pairedCosineTerm x α n)) := by
    simpa only [Function.comp_apply] using
      (hp.hasSum.map Complex.reCLM Complex.reCLM.continuous)
  have hmap :
      (∑' n, Complex.re (pairedCosineTerm x α n)) =
        Complex.re (∑' n, pairedCosineTerm x α n) :=
    hrealHas.tsum_eq
  have hscaled :
      HasSum
        (fun n => (1 / 2 : ℝ) *
          Complex.re (pairedCosineTerm x α n))
        ((1 / 2 : ℝ) *
          Complex.re (∑' n, pairedCosineTerm x α n)) :=
    hrealHas.mul_left (1 / 2 : ℝ)
  have hcosHas :
      HasSum (fun n => cosineSeriesTerm x α n)
        ((1 / 2 : ℝ) *
          Complex.re (∑' n, pairedCosineTerm x α n)) := by
    simpa only [half_re_paired] using hscaled
  have hseries :
      (1 / 2 : ℝ) *
          Complex.re (∑' n, pairedCosineTerm x α n) =
        ∑' n, cosineSeriesTerm x α n :=
    hcosHas.tsum_eq.symm
  have hre := congrArg Complex.re (hpaired x α hx)
  rw [half_re_mul] at hre
  change
    (x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) =
      (1 / 2 : ℝ) *
        Complex.re (∑' n, pairedCosineTerm x α n) at hre
  calc
    (x * Real.cos α - x ^ 2) /
        (1 - 2 * x * Real.cos α + x ^ 2) =
        (1 / 2 : ℝ) *
          Complex.re (∑' n, pairedCosineTerm x α n) := hre
    _ = ∑' n, cosineSeriesTerm x α n := hseries

end

end ProofGap.Exercise2863
