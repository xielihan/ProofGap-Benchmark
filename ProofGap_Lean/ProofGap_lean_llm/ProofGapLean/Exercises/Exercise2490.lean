import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2490

noncomputable section

def upperY (a b x : ℝ) : ℝ :=
  b / a * Real.sqrt (a ^ 2 - x ^ 2)

def eccentricity (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - b ^ 2) / a

def xIntegrand (a b x : ℝ) : ℝ :=
  upperY a b x * Real.sqrt (1 + deriv (upperY a b) x ^ 2)

def xSurface (a b : ℝ) : ℝ :=
  2 * Real.pi * ∫ x in -a..a, xIntegrand a b x

def horizontalX (a b y : ℝ) : ℝ :=
  a / b * Real.sqrt (b ^ 2 - y ^ 2)

def cParameter (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 - b ^ 2)

def yIntegrand (a b y : ℝ) : ℝ :=
  horizontalX a b y * Real.sqrt (1 + deriv (horizontalX a b) y ^ 2)

def ySurface (a b : ℝ) : ℝ :=
  2 * Real.pi * ∫ y in -b..b, yIntegrand a b y

private theorem sqrt_mul_sqrt_one_add_sq (u d : ℝ) (hu : 0 ≤ u) :
    u * Real.sqrt (1 + d ^ 2) = Real.sqrt (u ^ 2 + (u * d) ^ 2) := by
  have hq : 0 ≤ 1 + d ^ 2 := by positivity
  have hr : 0 ≤ u ^ 2 + (u * d) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hq
  have hsr := Real.sq_sqrt hr
  have hl : 0 ≤ u * Real.sqrt (1 + d ^ 2) :=
    mul_nonneg hu (Real.sqrt_nonneg _)
  have hh : 0 ≤ Real.sqrt (u ^ 2 + (u * d) ^ 2) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg
    (u * Real.sqrt (1 + d ^ 2) -
      Real.sqrt (u ^ 2 + (u * d) ^ 2))]

private theorem ellipse_root_interval_integral (a e : ℝ)
    (ha : 0 < a) (he : 0 < e) (he1 : e < 1) :
    (∫ x in -a..a, Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2)) =
      a * Real.sqrt (a ^ 2 - e ^ 2 * a ^ 2) +
        a ^ 2 / e * Real.arcsin e := by
  let F : ℝ → ℝ := fun x =>
    x / 2 * Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2) +
      a ^ 2 / (2 * e) * Real.arcsin (e * x / a)
  have hder : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt F (Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2)) x := by
    intro x hx
    have hbounds : -a ≤ x ∧ x ≤ a := by
      simpa [Set.mem_uIcc, ha.le] using hx
    have hx2 : x ^ 2 ≤ a ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbounds.2)
        (by linarith : 0 ≤ a + x)]
    have he2 : e ^ 2 < 1 := by nlinarith [sq_nonneg (1 - e)]
    have hemul : e ^ 2 * x ^ 2 ≤ e ^ 2 * a ^ 2 :=
      mul_le_mul_of_nonneg_left hx2 (sq_nonneg e)
    have heamul : e ^ 2 * a ^ 2 < a ^ 2 := by
      exact (mul_lt_iff_lt_one_left (sq_pos_of_pos ha)).2 he2
    have hr : 0 < a ^ 2 - e ^ 2 * x ^ 2 := by linarith
    have hlo := mul_le_mul_of_nonneg_left hbounds.1 he.le
    have hhi := mul_le_mul_of_nonneg_left hbounds.2 he.le
    have hu : -1 < e * x / a ∧ e * x / a < 1 := by
      constructor
      · rw [lt_div_iff₀ ha]
        nlinarith
      · rw [div_lt_iff₀ ha]
        nlinarith
    have hp : HasDerivAt (fun z : ℝ => a ^ 2 - e ^ 2 * z ^ 2)
        (-2 * e ^ 2 * x) x := by
      convert (hasDerivAt_const x (a ^ 2)).sub
        ((hasDerivAt_const x (e ^ 2)).mul ((hasDerivAt_id x).pow 2)) using 1 <;>
        simp [id_eq] <;> ring
    have hs := hp.sqrt hr.ne'
    have hv : HasDerivAt (fun z : ℝ => e * z / a) (e / a) x := by
      convert ((hasDerivAt_const x e).mul (hasDerivAt_id x)).div_const a using 1 <;>
        simp [id_eq] <;> ring
    have hi := (Real.hasDerivAt_arcsin
      (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x hv
    have ht : 0 < 1 - (e * x / a) ^ 2 := by
      nlinarith [sq_nonneg (e * x / a + 1),
        sq_nonneg (1 - e * x / a)]
    have hrad_eq : a ^ 2 - e ^ 2 * x ^ 2 =
        a ^ 2 * (1 - (e * x / a) ^ 2) := by
      field_simp [ne_of_gt ha] <;> ring
    have hrel : Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2) =
        a * Real.sqrt (1 - (e * x / a) ^ 2) := by
      rw [hrad_eq, Real.sqrt_mul (sq_nonneg a),
        Real.sqrt_sq_eq_abs, abs_of_pos ha]
    have hisimp :
        1 / Real.sqrt (1 - (e * x / a) ^ 2) * (e / a) =
          e / Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2) := by
      rw [hrel]
      field_simp [ne_of_gt ha, Real.sqrt_ne_zero'.2 ht] <;> ring
    have hi' : HasDerivAt
        (Real.arcsin ∘ fun z : ℝ => e * z / a)
        (e / Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2)) x := by
      simpa only [hisimp] using hi
    have hsum := (((hasDerivAt_id x).div_const 2).mul hs).add
      ((hasDerivAt_const x (a ^ 2 / (2 * e))).mul hi')
    dsimp [F]
    convert hsum using 1 <;> try { funext z; rfl }
    simp only [id_eq, zero_mul, zero_add]
    field_simp [ne_of_gt he, Real.sqrt_ne_zero'.2 hr] <;>
      nlinarith [Real.sq_sqrt hr.le]
  have hinner : Continuous (fun x : ℝ => a ^ 2 - e ^ 2 * x ^ 2) :=
    continuous_const.sub
      (continuous_const.mul (continuous_id.pow 2))
  have hcont : Continuous
      (fun x : ℝ => Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.continuous_sqrt.comp hinner)
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (a ^ 2 - e ^ 2 * x ^ 2))
      MeasureTheory.volume (-a) a :=
    hcont.intervalIntegrable (-a) a
  have hFTC := (intervalIntegral.integral_eq_sub_of_hasDerivAt hder) hint
  have hargpos : e * a / a = e := by
    field_simp [ne_of_gt ha] <;> ring
  have hargneg : e * (-a) / a = -e := by
    field_simp [ne_of_gt ha] <;> ring
  have hargneg' : -(e * a) / a = -e := by
    field_simp [ne_of_gt ha] <;> ring
  dsimp [F] at hFTC
  simp [hargpos, hargneg, hargneg', Real.arcsin_neg] at hFTC
  field_simp [ne_of_gt he] at hFTC ⊢ <;>
    nlinarith [hFTC]

private theorem hyperbola_root_interval_integral (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    (∫ y in -b..b, Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) =
      b * Real.sqrt (b ^ 2 + c ^ 2) +
        b ^ 3 / (2 * c) * Real.log
          ((Real.sqrt (b ^ 2 + c ^ 2) + c) /
            (Real.sqrt (b ^ 2 + c ^ 2) - c)) := by
  let q : ℝ := c / b
  have hq : 0 < q := div_pos hc hb
  let F : ℝ → ℝ := fun y =>
    y / 2 * Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2) +
      b ^ 2 / (2 * q) *
        Real.log (q * y + Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2))
  have hder : ∀ y ∈ Set.uIcc (-b) b,
      HasDerivAt F
        (Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) y := by
    intro y hy
    have hr : 0 < b ^ 2 + q ^ 2 * y ^ 2 := by
      dsimp [q]
      positivity
    have hp : HasDerivAt (fun z : ℝ => b ^ 2 + q ^ 2 * z ^ 2)
        (2 * q ^ 2 * y) y := by
      convert (hasDerivAt_const y (b ^ 2)).add
        ((hasDerivAt_const y (q ^ 2)).mul ((hasDerivAt_id y).pow 2)) using 1 <;>
        simp [id_eq] <;> ring
    have hs := hp.sqrt hr.ne'
    have harg : 0 < q * y + Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2) := by
      have hsquare := Real.sq_sqrt hr.le
      have hsnonneg := Real.sqrt_nonneg (b ^ 2 + q ^ 2 * y ^ 2)
      have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
      nlinarith [sq_nonneg (q * y)]
    have hlin : HasDerivAt (fun z : ℝ => q * z) q y := by
      convert (hasDerivAt_const y q).mul (hasDerivAt_id y) using 1 <;>
        simp [id_eq] <;> ring
    have hlog := (hlin.add hs).log harg.ne'
    have hlogsimp :
        (q + 2 * q ^ 2 * y /
            (2 * Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2))) /
          (q * y + Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2)) =
        q / Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2) := by
      field_simp [Real.sqrt_ne_zero'.2 hr, harg.ne'] <;>
        nlinarith [Real.sq_sqrt hr.le]
    have hlog' : HasDerivAt
        (fun z : ℝ => Real.log
          (q * z + Real.sqrt (b ^ 2 + q ^ 2 * z ^ 2)))
        (q / Real.sqrt (b ^ 2 + q ^ 2 * y ^ 2)) y := by
      convert hlog using 1
      simpa using hlogsimp.symm
    have hcq : c ^ 2 / b ^ 2 = q ^ 2 := by
      dsimp [q]
      field_simp [ne_of_gt hb] <;> ring
    have hsum := (((hasDerivAt_id y).div_const 2).mul hs).add
      ((hasDerivAt_const y (b ^ 2 / (2 * q))).mul hlog')
    dsimp [F]
    convert hsum using 1 <;> try { funext z; rfl }
    rw [hcq]
    simp only [id_eq, zero_mul, zero_add]
    field_simp [hq.ne', Real.sqrt_ne_zero'.2 hr] <;>
      nlinarith [Real.sq_sqrt hr.le]
  have hinner : Continuous
      (fun y : ℝ => b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2) :=
    continuous_const.add
      (continuous_const.mul (continuous_id.pow 2))
  have hcont : Continuous
      (fun y : ℝ => Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.continuous_sqrt.comp hinner)
  have hint : IntervalIntegrable
      (fun y : ℝ => Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2))
      MeasureTheory.volume (-b) b :=
    hcont.intervalIntegrable (-b) b
  have hFTC := (intervalIntegral.integral_eq_sub_of_hasDerivAt hder) hint
  have hsplus : 0 < Real.sqrt (b ^ 2 + c ^ 2) + c := by positivity
  have hsminus : 0 < Real.sqrt (b ^ 2 + c ^ 2) - c := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ b ^ 2 + c ^ 2)
    have hn := Real.sqrt_nonneg (b ^ 2 + c ^ 2)
    nlinarith [sq_pos_of_pos hb]
  have hsarg : Real.sqrt (b ^ 2 + (c / b) ^ 2 * b ^ 2) =
      Real.sqrt (b ^ 2 + c ^ 2) := by
    congr 1
    field_simp [ne_of_gt hb] <;> ring
  have hsargneg : Real.sqrt (b ^ 2 + (c / b) ^ 2 * (-b) ^ 2) =
      Real.sqrt (b ^ 2 + c ^ 2) := by
    congr 1
    field_simp [ne_of_gt hb] <;> ring
  have hcb : c / b * b = c := by
    field_simp [ne_of_gt hb] <;> ring
  have hcnb : c / b * (-b) = -c := by
    field_simp [ne_of_gt hb] <;> ring
  have hlog :
      Real.log (c + Real.sqrt (b ^ 2 + c ^ 2)) -
          Real.log (-c + Real.sqrt (b ^ 2 + c ^ 2)) =
        Real.log
          ((Real.sqrt (b ^ 2 + c ^ 2) + c) /
            (Real.sqrt (b ^ 2 + c ^ 2) - c)) := by
    rw [Real.log_div hsplus.ne' hsminus.ne']
    congr 1 <;> ring
  dsimp [F, q] at hFTC
  rw [hsarg, hsargneg, hcb, hcnb] at hFTC
  have hFTC' :
      (∫ y in -b..b, Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) =
        b * Real.sqrt (b ^ 2 + c ^ 2) +
          b ^ 2 / (2 * (c / b)) *
            (Real.log (c + Real.sqrt (b ^ 2 + c ^ 2)) -
              Real.log (-c + Real.sqrt (b ^ 2 + c ^ 2))) := by
    calc
      (∫ y in -b..b, Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) =
          b / 2 * Real.sqrt (b ^ 2 + c ^ 2) +
              b ^ 2 / (2 * (c / b)) *
                Real.log (c + Real.sqrt (b ^ 2 + c ^ 2)) -
            (-b / 2 * Real.sqrt (b ^ 2 + c ^ 2) +
              b ^ 2 / (2 * (c / b)) *
                Real.log (-c + Real.sqrt (b ^ 2 + c ^ 2))) := hFTC
      _ = b * Real.sqrt (b ^ 2 + c ^ 2) +
          b ^ 2 / (2 * (c / b)) *
            (Real.log (c + Real.sqrt (b ^ 2 + c ^ 2)) -
              Real.log (-c + Real.sqrt (b ^ 2 + c ^ 2))) := by ring
  have hcoef : b ^ 2 / (2 * (c / b)) = b ^ 3 / (2 * c) := by
    field_simp [ne_of_gt hb, ne_of_gt hc] <;> ring
  calc
    (∫ y in -b..b, Real.sqrt (b ^ 2 + c ^ 2 / b ^ 2 * y ^ 2)) =
        b * Real.sqrt (b ^ 2 + c ^ 2) +
          b ^ 2 / (2 * (c / b)) *
            (Real.log (c + Real.sqrt (b ^ 2 + c ^ 2)) -
              Real.log (-c + Real.sqrt (b ^ 2 + c ^ 2))) := hFTC'
    _ = b * Real.sqrt (b ^ 2 + c ^ 2) +
        b ^ 2 / (2 * (c / b)) * Real.log
          ((Real.sqrt (b ^ 2 + c ^ 2) + c) /
            (Real.sqrt (b ^ 2 + c ^ 2) - c)) := by rw [hlog]
    _ = b * Real.sqrt (b ^ 2 + c ^ 2) +
        b ^ 3 / (2 * c) * Real.log
          ((Real.sqrt (b ^ 2 + c ^ 2) + c) /
            (Real.sqrt (b ^ 2 + c ^ 2) - c)) := by rw [hcoef]

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hx : |x| ≤ a) :
    upperY a b x ^ 2 = b ^ 2 - b ^ 2 / a ^ 2 * x ^ 2 := by
  unfold upperY
  have hax : -a ≤ x := neg_le_of_abs_le hx
  have hxa : x ≤ a := le_of_abs_le hx
  have hrad : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith
  rw [mul_pow, Real.sq_sqrt hrad]
  field_simp [ne_of_gt ha]

theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : |x| < a) :
    upperY a b x * deriv (upperY a b) x = -b ^ 2 / a ^ 2 * x := by
  have hax : -a < x := (abs_lt.mp hx).1
  have hxa : x < a := (abs_lt.mp hx).2
  have hrad : 0 < a ^ 2 - x ^ 2 := by nlinarith
  have hp : HasDerivAt (fun z : ℝ => a ^ 2 - z ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (a ^ 2)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hs : HasDerivAt (fun z : ℝ => Real.sqrt (a ^ 2 - z ^ 2))
      (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert hp.sqrt hrad.ne' using 1 <;>
      field_simp [Real.sqrt_ne_zero'.2 hrad] <;> ring
  have hu : HasDerivAt (upperY a b)
      ((b / a) * (-x / Real.sqrt (a ^ 2 - x ^ 2))) x := by
    unfold upperY
    convert (hasDerivAt_const x (b / a)).mul hs using 1 <;>
      simp <;> ring
  rw [hu.deriv]
  unfold upperY
  have hspos : 0 < Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hsquare := Real.sq_sqrt hrad.le
  field_simp [ne_of_gt ha, ne_of_gt hspos] <;> nlinarith

theorem gap3 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : |x| < a) :
    xIntegrand a b x =
      Real.sqrt
        (upperY a b x ^ 2 +
          (upperY a b x * deriv (upperY a b) x) ^ 2) := by
  unfold xIntegrand
  apply sqrt_mul_sqrt_one_add_sq
  unfold upperY
  positivity

theorem gap4 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : |x| < a) :
    xIntegrand a b x =
      b / a * Real.sqrt
        (a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2) := by
  rw [gap3 a b x ha hb hx, gap1 a b x ha hx.le, gap2 a b x ha hb hx]
  let T : ℝ := a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2
  let E : ℝ := b ^ 2 - b ^ 2 / a ^ 2 * x ^ 2 + (-b ^ 2 / a ^ 2 * x) ^ 2
  have hax : -a < x := (abs_lt.mp hx).1
  have hxa : x < a := (abs_lt.mp hx).2
  have hrad : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith
  have hT : 0 ≤ T := by
    have hid : T = (a ^ 2 - x ^ 2) + b ^ 2 / a ^ 2 * x ^ 2 := by
      dsimp [T]
      field_simp [ne_of_gt ha]
      ring
    rw [hid]
    positivity
  have hE : E = (b / a) ^ 2 * T := by
    dsimp [E, T]
    field_simp [ne_of_gt ha]
    ring
  have hc : 0 ≤ b / a := div_nonneg hb.le ha.le
  change Real.sqrt E = b / a * Real.sqrt T
  rw [hE, Real.sqrt_mul (sq_nonneg (b / a)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    eccentricity a b ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 := by
  unfold eccentricity
  have hrad : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  rw [div_pow, Real.sq_sqrt hrad]

theorem gap6 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hx : |x| < a) :
    xIntegrand a b x =
      b / a * Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * x ^ 2) := by
  rw [gap4 a b x ha hb hx, gap5 a b ha hb hba]

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    xSurface a b =
      2 * Real.pi * (b / a) *
        ∫ x in -a..a,
          Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * x ^ 2) := by
  unfold xSurface
  have hint : (∫ x in -a..a, xIntegrand a b x) =
      ∫ x in -a..a, (b / a) * Real.sqrt
        (a ^ 2 - eccentricity a b ^ 2 * x ^ 2) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hmem :
        ∀ᵐ x : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc (-a) a)),
          x ∈ Set.uIoc (-a) a :=
      MeasureTheory.ae_restrict_mem measurableSet_uIoc
    have hnea :
        ∀ᵐ x : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc (-a) a)),
          x ≠ a := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.measure_singleton
          (μ := MeasureTheory.volume.restrict (Set.uIoc (-a) a)) a)
    filter_upwards [hmem, hnea] with x hxmem hxa
    rcases (Set.mem_uIoc.mp hxmem) with hbounds | hreverse
    · apply gap6 a b x ha hb hba
      rw [abs_lt]
      exact ⟨hbounds.1, lt_of_le_of_ne hbounds.2 hxa⟩
    · exfalso
      linarith
  rw [hint, intervalIntegral.integral_const_mul]
  ring

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    2 * Real.pi * (b / a) *
        (∫ x in -a..a,
          Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * x ^ 2)) =
      2 * Real.pi * b / a *
        (a * Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * a ^ 2) +
          a ^ 2 / eccentricity a b * Real.arcsin (eccentricity a b)) := by
  have hepos : 0 < eccentricity a b := by
    unfold eccentricity
    have : 0 < a ^ 2 - b ^ 2 := by nlinarith
    positivity
  have helt : eccentricity a b < 1 := by
    unfold eccentricity
    have hsq : Real.sqrt (a ^ 2 - b ^ 2) ^ 2 = a ^ 2 - b ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    have hsnonneg := Real.sqrt_nonneg (a ^ 2 - b ^ 2)
    have hsa : Real.sqrt (a ^ 2 - b ^ 2) < a := by nlinarith
    exact (div_lt_one ha).2 hsa
  rw [ellipse_root_interval_integral a (eccentricity a b) ha hepos helt]
  ring

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    2 * Real.pi * b / a *
        (a * Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * a ^ 2) +
          a ^ 2 / eccentricity a b * Real.arcsin (eccentricity a b)) =
      2 * Real.pi * b *
        (b + a / eccentricity a b * Real.arcsin (eccentricity a b)) := by
  have he := gap5 a b ha hb hba
  have hrootarg : a ^ 2 - eccentricity a b ^ 2 * a ^ 2 = b ^ 2 := by
    rw [he]
    field_simp [ne_of_gt ha]
    ring
  have hsqrt : Real.sqrt (a ^ 2 - eccentricity a b ^ 2 * a ^ 2) = b := by
    rw [hrootarg, Real.sqrt_sq_eq_abs, abs_of_pos hb]
  rw [hsqrt]
  field_simp [ne_of_gt ha]

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    xSurface a b =
      2 * Real.pi * b *
        (b + a / eccentricity a b * Real.arcsin (eccentricity a b)) := by
  rw [gap7 a b ha hb hba, gap8 a b ha hb hba, gap9 a b ha hb hba]

theorem gap11 (a b : ℝ) :
    eccentricity a b = Real.sqrt (a ^ 2 - b ^ 2) / a := by
  rfl

theorem gap12 (a b y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hy : |y| < b) :
    yIntegrand a b y =
      a / b * Real.sqrt
        (b ^ 2 + (a ^ 2 - b ^ 2) / b ^ 2 * y ^ 2) := by
  have hby : -b < y := (abs_lt.mp hy).1
  have hyb : y < b := (abs_lt.mp hy).2
  have hrad : 0 < b ^ 2 - y ^ 2 := by nlinarith
  have hp : HasDerivAt (fun z : ℝ => b ^ 2 - z ^ 2) (-2 * y) y := by
    convert (hasDerivAt_const y (b ^ 2)).sub ((hasDerivAt_id y).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hs : HasDerivAt (fun z : ℝ => Real.sqrt (b ^ 2 - z ^ 2))
      (-y / Real.sqrt (b ^ 2 - y ^ 2)) y := by
    convert hp.sqrt hrad.ne' using 1 <;>
      field_simp [Real.sqrt_ne_zero'.2 hrad] <;> ring
  have hh : HasDerivAt (horizontalX a b)
      ((a / b) * (-y / Real.sqrt (b ^ 2 - y ^ 2))) y := by
    unfold horizontalX
    convert (hasDerivAt_const y (a / b)).mul hs using 1 <;>
      simp <;> ring
  unfold yIntegrand
  rw [hh.deriv]
  have hhorizontal : 0 ≤ horizontalX a b y := by
    unfold horizontalX
    positivity
  rw [sqrt_mul_sqrt_one_add_sq
    (horizontalX a b y)
    ((a / b) * (-y / Real.sqrt (b ^ 2 - y ^ 2))) hhorizontal]
  unfold horizontalX
  let T : ℝ := b ^ 2 + (a ^ 2 - b ^ 2) / b ^ 2 * y ^ 2
  let E : ℝ :=
    (a / b * Real.sqrt (b ^ 2 - y ^ 2)) ^ 2 +
      ((a / b * Real.sqrt (b ^ 2 - y ^ 2)) *
        (a / b * (-y / Real.sqrt (b ^ 2 - y ^ 2)))) ^ 2
  have hT : 0 ≤ T := by
    have hid : T = (b ^ 2 - y ^ 2) + a ^ 2 / b ^ 2 * y ^ 2 := by
      dsimp [T]
      field_simp [ne_of_gt hb]
      ring
    rw [hid]
    positivity
  have hE : E = (a / b) ^ 2 * T := by
    dsimp [E, T]
    field_simp [ne_of_gt hb, Real.sqrt_ne_zero'.2 hrad]
    rw [Real.sq_sqrt hrad.le]
    ring
  have hc : 0 ≤ a / b := div_nonneg ha.le hb.le
  change Real.sqrt E = a / b * Real.sqrt T
  rw [hE, Real.sqrt_mul (sq_nonneg (a / b)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

theorem gap13 (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    cParameter a b ^ 2 = a ^ 2 - b ^ 2 := by
  unfold cParameter
  rw [Real.sq_sqrt]
  nlinarith

theorem gap14 (a b y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hy : |y| < b) :
    yIntegrand a b y =
      a / b * Real.sqrt
        (b ^ 2 + cParameter a b ^ 2 / b ^ 2 * y ^ 2) := by
  rw [gap12 a b y ha hb hba hy, gap13 a b hb.le hba.le]

theorem gap15 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ySurface a b =
      2 * Real.pi * (a / b) *
        ∫ y in -b..b,
          Real.sqrt (b ^ 2 + cParameter a b ^ 2 / b ^ 2 * y ^ 2) := by
  unfold ySurface
  have hint : (∫ y in -b..b, yIntegrand a b y) =
      ∫ y in -b..b, (a / b) * Real.sqrt
        (b ^ 2 + cParameter a b ^ 2 / b ^ 2 * y ^ 2) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hmem :
        ∀ᵐ y : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc (-b) b)),
          y ∈ Set.uIoc (-b) b :=
      MeasureTheory.ae_restrict_mem measurableSet_uIoc
    have hneb :
        ∀ᵐ y : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc (-b) b)),
          y ≠ b := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.measure_singleton
          (μ := MeasureTheory.volume.restrict (Set.uIoc (-b) b)) b)
    filter_upwards [hmem, hneb] with y hymem hyb
    rcases (Set.mem_uIoc.mp hymem) with hbounds | hreverse
    · apply gap14 a b y ha hb hba
      rw [abs_lt]
      exact ⟨hbounds.1, lt_of_le_of_ne hbounds.2 hyb⟩
    · exfalso
      linarith
  rw [hint, intervalIntegral.integral_const_mul]
  ring

theorem gap16 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ySurface a b =
      2 * Real.pi * a *
        (Real.sqrt (b ^ 2 + cParameter a b ^ 2) +
          b ^ 2 / (2 * cParameter a b) *
            Real.log
              ((Real.sqrt (b ^ 2 + cParameter a b ^ 2) + cParameter a b) /
                (Real.sqrt (b ^ 2 + cParameter a b ^ 2) - cParameter a b))) := by
  have hcpos : 0 < cParameter a b := by
    unfold cParameter
    have : 0 < a ^ 2 - b ^ 2 := by nlinarith
    positivity
  rw [gap15 a b ha hb hba,
    hyperbola_root_interval_integral b (cParameter a b) hb hcpos]
  field_simp [ne_of_gt hb]

theorem gap17 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    2 * Real.pi * a *
        (Real.sqrt (b ^ 2 + cParameter a b ^ 2) +
          b ^ 2 / (2 * cParameter a b) *
            Real.log
              ((Real.sqrt (b ^ 2 + cParameter a b ^ 2) + cParameter a b) /
                (Real.sqrt (b ^ 2 + cParameter a b ^ 2) - cParameter a b))) =
      2 * Real.pi * a *
        (a + b ^ 2 / (2 * cParameter a b) *
          Real.log ((a + cParameter a b) / (a - cParameter a b))) := by
  have hc := gap13 a b hb.le hba.le
  have hsarg : b ^ 2 + cParameter a b ^ 2 = a ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (b ^ 2 + cParameter a b ^ 2) = a := by
    rw [hsarg, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hsqrt]

theorem gap18 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ySurface a b =
      2 * Real.pi * a *
        (a + b ^ 2 / (2 * cParameter a b) *
          Real.log ((a + cParameter a b) / (a - cParameter a b))) := by
  rw [gap16 a b ha hb hba, gap17 a b ha hb hba]

theorem gap19 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ySurface a b =
      2 * Real.pi * a *
        (a + b ^ 2 / (2 * a) * (1 / eccentricity a b) *
          Real.log ((1 + eccentricity a b) / (1 - eccentricity a b))) := by
  have hepos : 0 < eccentricity a b := by
    unfold eccentricity
    have : 0 < a ^ 2 - b ^ 2 := by nlinarith
    positivity
  have hce : cParameter a b = a * eccentricity a b := by
    unfold cParameter eccentricity
    field_simp [ne_of_gt ha] <;> ring
  rw [gap18 a b ha hb hba, hce]
  have hratio : (a + a * eccentricity a b) /
      (a - a * eccentricity a b) =
      (1 + eccentricity a b) / (1 - eccentricity a b) := by
    field_simp [ne_of_gt ha] <;> ring
  rw [hratio]
  field_simp [ne_of_gt ha, ne_of_gt hepos] <;> ring

theorem gap20 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    2 * Real.pi * a *
        (a + b ^ 2 / (2 * a) * (1 / eccentricity a b) *
          Real.log ((1 + eccentricity a b) / (1 - eccentricity a b))) =
      2 * Real.pi * a *
        (a + b ^ 2 / a * (1 / eccentricity a b) *
          Real.log (a / b * (1 + eccentricity a b))) := by
  let e := eccentricity a b
  have he2 : e ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 :=
    gap5 a b ha hb hba
  have hepos : 0 < e := by
    dsimp [e, eccentricity]
    have : 0 < a ^ 2 - b ^ 2 := by nlinarith
    positivity
  have helt : e < 1 := by
    dsimp [e, eccentricity]
    have hsq : Real.sqrt (a ^ 2 - b ^ 2) ^ 2 = a ^ 2 - b ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    have hsnonneg := Real.sqrt_nonneg (a ^ 2 - b ^ 2)
    have hsa : Real.sqrt (a ^ 2 - b ^ 2) < a := by nlinarith
    exact (div_lt_one ha).2 hsa
  have hqpos : 0 < a / b * (1 + e) := by positivity
  have hratio : (1 + e) / (1 - e) =
      (a / b * (1 + e)) ^ 2 := by
    have hene : 1 - e ≠ 0 := ne_of_gt (sub_pos.2 helt)
    field_simp [ne_of_gt ha, ne_of_gt hb, hene]
    field_simp [ne_of_gt ha] at he2
    nlinarith
  have hlogsq :
      Real.log ((a / b * (1 + e)) ^ 2) =
        2 * Real.log (a / b * (1 + e)) := by
    rw [show (a / b * (1 + e)) ^ 2 =
      (a / b * (1 + e)) * (a / b * (1 + e)) by ring]
    rw [Real.log_mul hqpos.ne' hqpos.ne']
    ring
  change 2 * Real.pi * a *
      (a + b ^ 2 / (2 * a) * (1 / e) *
        Real.log ((1 + e) / (1 - e))) =
    2 * Real.pi * a *
      (a + b ^ 2 / a * (1 / e) *
        Real.log (a / b * (1 + e)))
  rw [hratio, hlogsq]
  ring

theorem gap21 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ySurface a b =
      2 * Real.pi * a *
        (a + b ^ 2 / a * (1 / eccentricity a b) *
          Real.log (a / b * (1 + eccentricity a b))) := by
  rw [gap19 a b ha hb hba, gap20 a b ha hb hba]

end

end ProofGap.Exercise2490
