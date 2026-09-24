import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Set
open scoped BigOperators Interval Topology

noncomputable section

private def rawIntegrand (n x : ℝ) : ℝ :=
  x / (1 + Real.rpow x n * Real.sin x ^ 2)

private lemma rawIntegrand_pos (n x : ℝ) (hx : 0 < x) :
    0 < rawIntegrand n x := by
  unfold rawIntegrand
  have hr : 0 ≤ Real.rpow x n :=
    Real.rpow_nonneg hx.le _
  have hs : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  exact div_pos hx (by positivity)

private lemma rawIntegrand_nonneg (n x : ℝ) (hx : 0 ≤ x) :
    0 ≤ rawIntegrand n x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rawIntegrand]
  · exact (rawIntegrand_pos n x hx).le

private lemma rawIntegrand_continuousAt (n x : ℝ) (hx0 : 0 < x) :
    ContinuousAt (rawIntegrand n) x := by
  have hrcont :
      ContinuousAt (fun y : ℝ => Real.rpow y n) x :=
    Real.continuousAt_rpow_const x n (Or.inl hx0.ne')
  have hden :
      1 + Real.rpow x n * Real.sin x ^ 2 ≠ 0 := by
    have hr : 0 ≤ Real.rpow x n :=
      Real.rpow_nonneg hx0.le _
    positivity
  exact continuousAt_id.div
    (continuousAt_const.add
      (hrcont.mul (Real.continuous_sin.continuousAt.pow 2)))
    hden

private lemma rawIntegrand_continuousOn_Ioi (n : ℝ) :
    ContinuousOn (rawIntegrand n) (Set.Ioi 0) := by
  intro x hx
  exact (rawIntegrand_continuousAt n x hx).continuousWithinAt

private lemma outer_endpoints (k : ℕ) (hk : 1 ≤ k) :
    0 <
        ((k : ℝ) - 1) * Real.pi + Real.pi / 4 ∧
      ((k : ℝ) - 1) * Real.pi + Real.pi / 4 <
        (k : ℝ) * Real.pi - Real.pi / 4 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · have hbase :
        0 ≤ ((k : ℝ) - 1) * Real.pi :=
      mul_nonneg (sub_nonneg.mpr hkR) Real.pi_pos.le
    nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private lemma raw_outerBlock_pos (n : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    0 <
      ∫ x in ((k : ℝ) - 1) * Real.pi + Real.pi / 4..
          (k : ℝ) * Real.pi - Real.pi / 4,
        rawIntegrand n x := by
  let a : ℝ := ((k : ℝ) - 1) * Real.pi + Real.pi / 4
  let b : ℝ := (k : ℝ) * Real.pi - Real.pi / 4
  have hend := outer_endpoints k hk
  have ha : 0 < a := by simpa [a] using hend.1
  have hab : a < b := by simpa [a, b] using hend.2
  apply intervalIntegral.integral_pos hab
  · exact (rawIntegrand_continuousOn_Ioi n).mono (by
      intro x hx
      exact ha.trans_le hx.1)
  · intro x hx
    exact (rawIntegrand_pos n x (ha.trans hx.1)).le
  · refine ⟨(a + b) / 2, ?_, rawIntegrand_pos n _ ?_⟩
    · constructor <;> linarith
    · linarith

private def kernel (c x : ℝ) : ℝ :=
  1 / (1 + c * Real.sin x ^ 2)

private def kernelPrimitive (c x : ℝ) : ℝ :=
  Real.arctan (Real.sqrt (1 + c) * Real.tan x) /
    Real.sqrt (1 + c)

private lemma kernel_continuous (c : ℝ) (hc : 0 ≤ c) :
    Continuous (kernel c) := by
  unfold kernel
  exact continuous_const.div
    (continuous_const.add
      (continuous_const.mul (Real.continuous_sin.pow 2)))
    (fun x => by
      have hs : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
      positivity)

private lemma hasDerivAt_kernelPrimitive
    (c x : ℝ) (hc : 0 ≤ c)
    (hx : x ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    HasDerivAt (kernelPrimitive c) (kernel c x) x := by
  have hspos : 0 < Real.sqrt (1 + c) :=
    Real.sqrt_pos.2 (by linarith)
  have hcospos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
  have htan := Real.hasDerivAt_tan hcospos.ne'
  have hinner :
      HasDerivAt
        (fun y : ℝ =>
          Real.sqrt (1 + c) * Real.tan y)
        (Real.sqrt (1 + c) * (1 / Real.cos x ^ 2)) x :=
    by
      convert
        (hasDerivAt_const x (Real.sqrt (1 + c))).mul htan
        using 1 <;> simp
  have harctan :=
    (Real.hasDerivAt_arctan
      (Real.sqrt (1 + c) * Real.tan x)).comp x hinner
  have hdiv :=
    harctan.div_const (Real.sqrt (1 + c))
  have hdiv' :
      HasDerivAt (kernelPrimitive c)
        (1 / (1 +
            (Real.sqrt (1 + c) * Real.tan x) ^ 2) *
          (Real.sqrt (1 + c) *
            (1 / Real.cos x ^ 2)) /
          Real.sqrt (1 + c)) x := by
    simpa [kernelPrimitive, Function.comp_def] using hdiv
  convert hdiv' using 1
  · unfold kernel
    have hs_sq :
        Real.sqrt (1 + c) ^ 2 = 1 + c :=
      Real.sq_sqrt (by linarith)
    have htrig := Real.sin_sq_add_cos_sq x
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hspos.ne', hcospos.ne']
    nlinarith

private lemma kernel_interval_eq (c : ℝ) (hc : 0 ≤ c) :
    (∫ x in -(Real.pi / 4)..Real.pi / 4, kernel c x) =
      2 * Real.arctan (Real.sqrt (1 + c)) /
        Real.sqrt (1 + c) := by
  have hab : -(Real.pi / 4) ≤ Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hderiv :
      ∀ x ∈ Set.uIcc (-(Real.pi / 4)) (Real.pi / 4),
        HasDerivAt (kernelPrimitive c) (kernel c x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_kernelPrimitive c x hc hx
  have hkcont :
      ContinuousOn (kernel c)
        (Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :=
    (kernel_continuous c hc).continuousOn
  have hint :
      IntervalIntegrable (kernel c) MeasureTheory.volume
        (-(Real.pi / 4)) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hkcont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold kernelPrimitive
  rw [Real.tan_pi_div_four, Real.tan_neg, Real.tan_pi_div_four]
  rw [mul_one, mul_neg, mul_one, Real.arctan_neg]
  ring

private lemma kernel_interval_lower (c : ℝ) (hc : 0 < c) :
    Real.pi / (2 * Real.sqrt (1 + c)) <
      ∫ x in -(Real.pi / 4)..Real.pi / 4, kernel c x := by
  have hspos : 0 < Real.sqrt (1 + c) :=
    Real.sqrt_pos.2 (by linarith)
  have hs_sq :
      Real.sqrt (1 + c) ^ 2 = 1 + c :=
    Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt (1 + c) := by
    nlinarith [Real.sqrt_nonneg (1 + c)]
  have hatan :
      Real.pi / 4 <
        Real.arctan (Real.sqrt (1 + c)) := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono hs1
  rw [kernel_interval_eq c hc.le]
  calc
    Real.pi / (2 * Real.sqrt (1 + c)) =
        2 * (Real.pi / 4) / Real.sqrt (1 + c) := by ring
    _ < 2 * Real.arctan (Real.sqrt (1 + c)) /
        Real.sqrt (1 + c) := by
      exact div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hatan (by norm_num)) hspos

private lemma kernel_interval_upper (c : ℝ) (hc : 0 ≤ c) :
    (∫ x in -(Real.pi / 4)..Real.pi / 4, kernel c x) <
      Real.pi / Real.sqrt (1 + c) := by
  have hspos : 0 < Real.sqrt (1 + c) :=
    Real.sqrt_pos.2 (by linarith)
  have hatan :=
    Real.arctan_lt_pi_div_two (Real.sqrt (1 + c))
  rw [kernel_interval_eq c hc]
  calc
    2 * Real.arctan (Real.sqrt (1 + c)) /
          Real.sqrt (1 + c) <
        2 * (Real.pi / 2) / Real.sqrt (1 + c) := by
      exact div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hatan (by norm_num)) hspos
    _ = Real.pi / Real.sqrt (1 + c) := by ring

private lemma sin_add_nat_mul_pi_sq (t : ℝ) (k : ℕ) :
    Real.sin (t + (k : ℝ) * Real.pi) ^ 2 =
      Real.sin t ^ 2 := by
  rw [Real.sin_add_nat_mul_pi]
  rw [mul_pow]
  rw [← pow_mul]
  simp

private lemma central_shift (n : ℝ) (k : ℕ) :
    (∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
        (k : ℝ) * Real.pi + Real.pi / 4,
        rawIntegrand n x) =
      ∫ t in -(Real.pi / 4)..Real.pi / 4,
        rawIntegrand n (t + (k : ℝ) * Real.pi) := by
  have h :=
    intervalIntegral.integral_comp_add_right
      (f := rawIntegrand n)
      (a := -(Real.pi / 4)) (b := Real.pi / 4)
      ((k : ℝ) * Real.pi)
  convert h.symm using 1 <;> ring

private lemma central_bounds_x
    (k : ℕ) (hk : 2 ≤ k) (t : ℝ)
    (ht : t ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    0 < ((k : ℝ) - 1) * Real.pi ∧
      ((k : ℝ) - 1) * Real.pi ≤
        t + (k : ℝ) * Real.pi ∧
      t + (k : ℝ) * Real.pi ≤
        ((k : ℝ) + 1) * Real.pi := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have htlo : -Real.pi ≤ t := by
    linarith [ht.1, Real.pi_pos]
  have hthi : t ≤ Real.pi := by
    linarith [ht.2, Real.pi_pos]
  constructor
  · exact mul_pos (sub_pos.mpr (by linarith)) Real.pi_pos
  constructor
  · calc
      ((k : ℝ) - 1) * Real.pi =
          (k : ℝ) * Real.pi - Real.pi := by ring
      _ ≤ t + (k : ℝ) * Real.pi := by linarith
  · calc
      t + (k : ℝ) * Real.pi ≤
          Real.pi + (k : ℝ) * Real.pi := by linarith
      _ = ((k : ℝ) + 1) * Real.pi := by ring

private lemma central_point_lower
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ)
    (ht : t ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    ((k : ℝ) - 1) * Real.pi *
        kernel (Real.rpow (((k : ℝ) + 1) * Real.pi) n) t ≤
      rawIntegrand n (t + (k : ℝ) * Real.pi) := by
  let lo : ℝ := ((k : ℝ) - 1) * Real.pi
  let x : ℝ := t + (k : ℝ) * Real.pi
  let hi : ℝ := ((k : ℝ) + 1) * Real.pi
  have hbounds := central_bounds_x k hk t ht
  have hlo0 : 0 < lo := by simpa [lo] using hbounds.1
  have hlox : lo ≤ x := by simpa [lo, x] using hbounds.2.1
  have hxhi : x ≤ hi := by simpa [x, hi] using hbounds.2.2
  have hx0 : 0 < x := hlo0.trans_le hlox
  have hhi0 : 0 < hi := hx0.trans_le hxhi
  have hrpow :
      Real.rpow x n ≤ Real.rpow hi n :=
    Real.rpow_le_rpow hx0.le hxhi hn
  have hsin :
      Real.sin x ^ 2 = Real.sin t ^ 2 := by
    dsimp [x]
    exact sin_add_nat_mul_pi_sq t k
  have hs0 : 0 ≤ Real.sin t ^ 2 := sq_nonneg _
  have hdenActual :
      0 < 1 + Real.rpow x n * Real.sin x ^ 2 := by
    have hr0 : 0 ≤ Real.rpow x n :=
      Real.rpow_nonneg hx0.le _
    positivity
  have hdenUpper :
      0 < 1 + Real.rpow hi n * Real.sin t ^ 2 := by
    have hr0 : 0 ≤ Real.rpow hi n :=
      Real.rpow_nonneg hhi0.le _
    positivity
  have hdenle :
      1 + Real.rpow x n * Real.sin x ^ 2 ≤
        1 + Real.rpow hi n * Real.sin t ^ 2 := by
    rw [hsin]
    gcongr
  unfold kernel rawIntegrand
  dsimp [lo, x, hi] at *
  calc
    (((k : ℝ) - 1) * Real.pi) *
          (1 /
            (1 +
              Real.rpow (((k : ℝ) + 1) * Real.pi) n *
                Real.sin t ^ 2)) =
        (((k : ℝ) - 1) * Real.pi) /
          (1 +
            Real.rpow (((k : ℝ) + 1) * Real.pi) n *
              Real.sin t ^ 2) := by ring
    _ ≤ (t + (k : ℝ) * Real.pi) /
          (1 +
            Real.rpow (((k : ℝ) + 1) * Real.pi) n *
              Real.sin t ^ 2) := by
      exact div_le_div_of_nonneg_right hlox hdenUpper.le
    _ ≤ (t + (k : ℝ) * Real.pi) /
          (1 +
            Real.rpow (t + (k : ℝ) * Real.pi) n *
              Real.sin (t + (k : ℝ) * Real.pi) ^ 2) := by
      exact div_le_div_of_nonneg_left hx0.le hdenActual hdenle

private lemma central_point_upper
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ)
    (ht : t ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    rawIntegrand n (t + (k : ℝ) * Real.pi) ≤
      ((k : ℝ) + 1) * Real.pi *
        kernel (Real.rpow (((k : ℝ) - 1) * Real.pi) n) t := by
  let lo : ℝ := ((k : ℝ) - 1) * Real.pi
  let x : ℝ := t + (k : ℝ) * Real.pi
  let hi : ℝ := ((k : ℝ) + 1) * Real.pi
  have hbounds := central_bounds_x k hk t ht
  have hlo0 : 0 < lo := by simpa [lo] using hbounds.1
  have hlox : lo ≤ x := by simpa [lo, x] using hbounds.2.1
  have hxhi : x ≤ hi := by simpa [x, hi] using hbounds.2.2
  have hx0 : 0 < x := hlo0.trans_le hlox
  have hhi0 : 0 < hi := hx0.trans_le hxhi
  have hrpow :
      Real.rpow lo n ≤ Real.rpow x n :=
    Real.rpow_le_rpow hlo0.le hlox hn
  have hsin :
      Real.sin x ^ 2 = Real.sin t ^ 2 := by
    dsimp [x]
    exact sin_add_nat_mul_pi_sq t k
  have hs0 : 0 ≤ Real.sin t ^ 2 := sq_nonneg _
  have hdenActual :
      0 < 1 + Real.rpow x n * Real.sin x ^ 2 := by
    have hr0 : 0 ≤ Real.rpow x n :=
      Real.rpow_nonneg hx0.le _
    positivity
  have hdenLower :
      0 < 1 + Real.rpow lo n * Real.sin t ^ 2 := by
    have hr0 : 0 ≤ Real.rpow lo n :=
      Real.rpow_nonneg hlo0.le _
    positivity
  have hdenle :
      1 + Real.rpow lo n * Real.sin t ^ 2 ≤
        1 + Real.rpow x n * Real.sin x ^ 2 := by
    rw [hsin]
    gcongr
  unfold kernel rawIntegrand
  dsimp [lo, x, hi] at *
  calc
    (t + (k : ℝ) * Real.pi) /
          (1 +
            Real.rpow (t + (k : ℝ) * Real.pi) n *
              Real.sin (t + (k : ℝ) * Real.pi) ^ 2) ≤
        (((k : ℝ) + 1) * Real.pi) /
          (1 +
            Real.rpow (t + (k : ℝ) * Real.pi) n *
              Real.sin (t + (k : ℝ) * Real.pi) ^ 2) := by
      exact div_le_div_of_nonneg_right hxhi hdenActual.le
    _ ≤ (((k : ℝ) + 1) * Real.pi) /
          (1 +
            Real.rpow (((k : ℝ) - 1) * Real.pi) n *
              Real.sin t ^ 2) := by
      exact div_le_div_of_nonneg_left hhi0.le hdenLower hdenle
    _ = (((k : ℝ) + 1) * Real.pi) *
          (1 /
            (1 +
              Real.rpow (((k : ℝ) - 1) * Real.pi) n *
                Real.sin t ^ 2)) := by ring

private lemma raw_centralBlock_lower
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k) :
    ((k : ℝ) - 1) * Real.pi ^ 2 /
        (2 * Real.sqrt
          (1 + Real.rpow (((k : ℝ) + 1) * Real.pi) n)) <
      ∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
          (k : ℝ) * Real.pi + Real.pi / 4,
        rawIntegrand n x := by
  let lo : ℝ := ((k : ℝ) - 1) * Real.pi
  let hi : ℝ := ((k : ℝ) + 1) * Real.pi
  let c : ℝ := Real.rpow hi n
  have hlo0 : 0 < lo := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [lo]
    exact mul_pos (sub_pos.mpr (by linarith)) Real.pi_pos
  have hhi0 : 0 < hi := by
    dsimp [hi]
    positivity
  have hc0 : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos hhi0 _
  have hab : -(Real.pi / 4) ≤ Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hfcont :
      ContinuousOn (fun t : ℝ => lo * kernel c t)
        (Set.uIcc (-(Real.pi / 4)) (Real.pi / 4)) :=
    continuousOn_const.mul
      (kernel_continuous c hc0.le).continuousOn
  have hgcont :
      ContinuousOn
        (fun t : ℝ =>
          rawIntegrand n (t + (k : ℝ) * Real.pi))
        (Set.uIcc (-(Real.pi / 4)) (Real.pi / 4)) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have hb := central_bounds_x k hk t ht
    have hx0 :
        0 < t + (k : ℝ) * Real.pi :=
      hb.1.trans_le hb.2.1
    have hinner :
        ContinuousAt
          (fun y : ℝ => y + (k : ℝ) * Real.pi) t :=
      continuousAt_id.add continuousAt_const
    have hrcont :
        ContinuousAt
          (fun y : ℝ =>
            Real.rpow (y + (k : ℝ) * Real.pi) n) t :=
      hinner.rpow_const (Or.inl hx0.ne')
    have hscont :
        ContinuousAt
          (fun y : ℝ =>
            Real.sin (y + (k : ℝ) * Real.pi)) t :=
      by
        simpa [Function.comp_def] using
          Real.continuous_sin.continuousAt.comp hinner
    have hden :
        1 +
          Real.rpow (t + (k : ℝ) * Real.pi) n *
            Real.sin (t + (k : ℝ) * Real.pi) ^ 2 ≠ 0 := by
      have hr0 :=
        Real.rpow_nonneg hx0.le n
      positivity
    exact (hinner.div
      (continuousAt_const.add (hrcont.mul (hscont.pow 2)))
      hden).continuousWithinAt
  have hmono :
      (∫ t in -(Real.pi / 4)..Real.pi / 4,
          lo * kernel c t) ≤
        ∫ t in -(Real.pi / 4)..Real.pi / 4,
          rawIntegrand n (t + (k : ℝ) * Real.pi) := by
    exact intervalIntegral.integral_mono_on hab
      hfcont.intervalIntegrable hgcont.intervalIntegrable
      (by
        intro t ht
        simpa [lo, hi, c] using
          central_point_lower n hn k hk t ht)
  have hkernel := kernel_interval_lower c hc0
  calc
    ((k : ℝ) - 1) * Real.pi ^ 2 /
          (2 * Real.sqrt
            (1 + Real.rpow (((k : ℝ) + 1) * Real.pi) n)) =
        lo * (Real.pi / (2 * Real.sqrt (1 + c))) := by
      dsimp [lo, hi, c]
      ring
    _ < lo *
        (∫ t in -(Real.pi / 4)..Real.pi / 4,
          kernel c t) :=
      mul_lt_mul_of_pos_left hkernel hlo0
    _ = ∫ t in -(Real.pi / 4)..Real.pi / 4,
          lo * kernel c t := by
      exact
        (intervalIntegral.integral_const_mul
          (μ := MeasureTheory.volume)
          (a := -(Real.pi / 4)) (b := Real.pi / 4)
          lo (kernel c)).symm
    _ ≤ ∫ t in -(Real.pi / 4)..Real.pi / 4,
          rawIntegrand n (t + (k : ℝ) * Real.pi) :=
      hmono
    _ = ∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
          (k : ℝ) * Real.pi + Real.pi / 4,
          rawIntegrand n x :=
      (central_shift n k).symm

private lemma raw_centralBlock_upper
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k) :
    (∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
          (k : ℝ) * Real.pi + Real.pi / 4,
          rawIntegrand n x) <
      ((k : ℝ) + 1) * Real.pi ^ 2 /
        Real.sqrt
          (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n) := by
  let lo : ℝ := ((k : ℝ) - 1) * Real.pi
  let hi : ℝ := ((k : ℝ) + 1) * Real.pi
  let c : ℝ := Real.rpow lo n
  have hlo0 : 0 < lo := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [lo]
    exact mul_pos (sub_pos.mpr (by linarith)) Real.pi_pos
  have hhi0 : 0 < hi := by
    dsimp [hi]
    positivity
  have hc0 : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos hlo0 _
  have hab : -(Real.pi / 4) ≤ Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hfcont :
      ContinuousOn
        (fun t : ℝ =>
          rawIntegrand n (t + (k : ℝ) * Real.pi))
        (Set.uIcc (-(Real.pi / 4)) (Real.pi / 4)) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have hb := central_bounds_x k hk t ht
    have hx0 :
        0 < t + (k : ℝ) * Real.pi :=
      hb.1.trans_le hb.2.1
    have hinner :
        ContinuousAt
          (fun y : ℝ => y + (k : ℝ) * Real.pi) t :=
      continuousAt_id.add continuousAt_const
    have hrcont :
        ContinuousAt
          (fun y : ℝ =>
            Real.rpow (y + (k : ℝ) * Real.pi) n) t :=
      hinner.rpow_const (Or.inl hx0.ne')
    have hscont :
        ContinuousAt
          (fun y : ℝ =>
            Real.sin (y + (k : ℝ) * Real.pi)) t :=
      by
        simpa [Function.comp_def] using
          Real.continuous_sin.continuousAt.comp hinner
    have hden :
        1 +
          Real.rpow (t + (k : ℝ) * Real.pi) n *
            Real.sin (t + (k : ℝ) * Real.pi) ^ 2 ≠ 0 := by
      have hr0 :=
        Real.rpow_nonneg hx0.le n
      positivity
    exact (hinner.div
      (continuousAt_const.add (hrcont.mul (hscont.pow 2)))
      hden).continuousWithinAt
  have hgcont :
      ContinuousOn (fun t : ℝ => hi * kernel c t)
        (Set.uIcc (-(Real.pi / 4)) (Real.pi / 4)) :=
    continuousOn_const.mul
      (kernel_continuous c hc0.le).continuousOn
  have hmono :
      (∫ t in -(Real.pi / 4)..Real.pi / 4,
          rawIntegrand n (t + (k : ℝ) * Real.pi)) ≤
        ∫ t in -(Real.pi / 4)..Real.pi / 4,
          hi * kernel c t := by
    exact intervalIntegral.integral_mono_on hab
      hfcont.intervalIntegrable hgcont.intervalIntegrable
      (by
        intro t ht
        simpa [lo, hi, c] using
          central_point_upper n hn k hk t ht)
  have hkernel := kernel_interval_upper c hc0.le
  calc
    (∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
          (k : ℝ) * Real.pi + Real.pi / 4,
          rawIntegrand n x) =
        ∫ t in -(Real.pi / 4)..Real.pi / 4,
          rawIntegrand n (t + (k : ℝ) * Real.pi) :=
      central_shift n k
    _ ≤ ∫ t in -(Real.pi / 4)..Real.pi / 4,
          hi * kernel c t :=
      hmono
    _ = hi *
        (∫ t in -(Real.pi / 4)..Real.pi / 4,
          kernel c t) := by
      exact
        intervalIntegral.integral_const_mul
          (μ := MeasureTheory.volume)
          (a := -(Real.pi / 4)) (b := Real.pi / 4)
          hi (kernel c)
    _ < hi * (Real.pi / Real.sqrt (1 + c)) :=
      mul_lt_mul_of_pos_left hkernel hhi0
    _ = ((k : ℝ) + 1) * Real.pi ^ 2 /
          Real.sqrt
            (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n) := by
      dsimp [lo, hi, c]
      ring

private lemma sin_sq_ge_half
    (y : ℝ) (hy : y ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 4)) :
    (1 / 2 : ℝ) ≤ Real.sin y ^ 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsin0 : 0 ≤ Real.sin y := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos, hy.1, hy.2]
  have hsin :
      Real.sqrt 2 / 2 ≤ Real.sin y := by
    by_cases hyleft : y ≤ Real.pi / 2
    · rw [← Real.sin_pi_div_four]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hyleft hy.1
    · have hz :
          Real.pi / 4 ≤ Real.pi - y ∧
            Real.pi - y ≤ Real.pi / 2 := by
        constructor <;> linarith [hy.2]
      rw [← Real.sin_pi_div_four, ← Real.sin_pi_sub y]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hz.2 hz.1
  nlinarith

private lemma sin_shift_outer_sq
    (x : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Real.sin x ^ 2 =
      Real.sin (x - ((k : ℝ) - 1) * Real.pi) ^ 2 := by
  have heq :
      x =
        (x - ((k : ℝ) - 1) * Real.pi) +
          (k - 1 : ℕ) * Real.pi := by
    have hkcast :
      ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) hk)
    rw [hkcast]
    ring
  calc
    Real.sin x ^ 2 =
        Real.sin
          ((x - ((k : ℝ) - 1) * Real.pi) +
            (k - 1 : ℕ) * Real.pi) ^ 2 :=
      congrArg (fun z : ℝ => Real.sin z ^ 2) heq
    _ = Real.sin (x - ((k : ℝ) - 1) * Real.pi) ^ 2 := by
      rw [Real.sin_add_nat_mul_pi]
      rw [mul_pow, ← pow_mul]
      simp

private lemma outer_point_lt
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ)
    (hx :
      x ∈ Set.Icc
        (((k : ℝ) - 1) * Real.pi + Real.pi / 4)
        ((k : ℝ) * Real.pi - Real.pi / 4)) :
    rawIntegrand n x <
      (k : ℝ) * Real.pi /
        Real.sqrt
          (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n) := by
  let base : ℝ := ((k : ℝ) - 1) * Real.pi
  let top : ℝ := (k : ℝ) * Real.pi
  let c : ℝ := Real.rpow base n
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (sub_nonneg.mpr hkR) Real.pi_pos.le
  have hx0 : 0 < x := by
    have : 0 < base + Real.pi / 4 := by
      positivity
    exact this.trans_le hx.1
  have hxtop : x < top := by
    dsimp [top]
    linarith [hx.2, Real.pi_pos]
  have hbasex : base ≤ x := by
    dsimp [base]
    linarith [hx.1, Real.pi_pos]
  have hrpow :
      c ≤ Real.rpow x n := by
    dsimp [c]
    exact Real.rpow_le_rpow hbase0 hbasex hn
  have hy :
      x - base ∈
        Set.Icc (Real.pi / 4) (3 * Real.pi / 4) := by
    dsimp [base] at *
    constructor <;> linarith [hx.1, hx.2]
  have hsin :
      (1 / 2 : ℝ) ≤ Real.sin x ^ 2 := by
    rw [sin_shift_outer_sq x k hk]
    exact sin_sq_ge_half (x - base) hy
  have hc0 : 0 ≤ c :=
    Real.rpow_nonneg hbase0 _
  have hdenLower :
      Real.sqrt (1 + c) ≤
        1 + Real.rpow x n * Real.sin x ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (1 + c) :=
      Real.sqrt_nonneg _
    have hsqrt_sq :
        Real.sqrt (1 + c) ^ 2 = 1 + c :=
      Real.sq_sqrt (by linarith)
    have hprod :
        c / 2 ≤ Real.rpow x n * Real.sin x ^ 2 := by
      calc
        c / 2 = c * (1 / 2) := by ring
        _ ≤ Real.rpow x n * (1 / 2) := by gcongr
        _ ≤ Real.rpow x n * Real.sin x ^ 2 := by
          gcongr
          exact Real.rpow_nonneg hx0.le _
    have hamgm :
        Real.sqrt (1 + c) ≤ 1 + c / 2 := by
      nlinarith [sq_nonneg c]
    linarith
  have hsqrtpos : 0 < Real.sqrt (1 + c) :=
    Real.sqrt_pos.2 (by linarith)
  have hdenpos :
      0 < 1 + Real.rpow x n * Real.sin x ^ 2 := by
    have hr0 := Real.rpow_nonneg hx0.le n
    have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
    positivity
  unfold rawIntegrand
  dsimp [base, top, c] at *
  calc
    x /
          (1 + Real.rpow x n * Real.sin x ^ 2) ≤
        x /
          Real.sqrt
            (1 +
              Real.rpow (((k : ℝ) - 1) * Real.pi) n) := by
      exact div_le_div_of_nonneg_left hx0.le hsqrtpos hdenLower
    _ < (k : ℝ) * Real.pi /
          Real.sqrt
            (1 +
              Real.rpow (((k : ℝ) - 1) * Real.pi) n) :=
      div_lt_div_of_pos_right hxtop hsqrtpos

private lemma raw_outerBlock_upper
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x in ((k : ℝ) - 1) * Real.pi + Real.pi / 4..
          (k : ℝ) * Real.pi - Real.pi / 4,
          rawIntegrand n x) <
      (k : ℝ) * Real.pi ^ 2 /
        (2 * Real.sqrt
          (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)) := by
  let a : ℝ := ((k : ℝ) - 1) * Real.pi + Real.pi / 4
  let b : ℝ := (k : ℝ) * Real.pi - Real.pi / 4
  let C : ℝ :=
    (k : ℝ) * Real.pi /
      Real.sqrt
        (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)
  have hend := outer_endpoints k hk
  have ha0 : 0 < a := by simpa [a] using hend.1
  have hab : a < b := by simpa [a, b] using hend.2
  have hfcont :
      ContinuousOn (rawIntegrand n) (Set.Icc a b) :=
    (rawIntegrand_continuousOn_Ioi n).mono (by
      intro x hx
      exact ha0.trans_le hx.1)
  have hgcont :
      ContinuousOn (fun _ : ℝ => C) (Set.Icc a b) :=
    continuousOn_const
  have hstrict :
      ∀ x ∈ Set.Icc a b, rawIntegrand n x < C := by
    intro x hx
    simpa [a, b, C] using outer_point_lt n hn k hk x hx
  have hlt :
      (∫ x in a..b, rawIntegrand n x) <
        ∫ x in a..b, C := by
    apply
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hab hfcont hgcont
    · intro x hx
      exact (hstrict x ⟨hx.1.le, hx.2⟩).le
    · refine ⟨(a + b) / 2, ?_, hstrict _ ?_⟩
      · constructor <;> linarith
      · constructor <;> linarith
  calc
    (∫ x in ((k : ℝ) - 1) * Real.pi + Real.pi / 4..
          (k : ℝ) * Real.pi - Real.pi / 4,
          rawIntegrand n x) =
        ∫ x in a..b, rawIntegrand n x := by rfl
    _ < ∫ x in a..b, C := hlt
    _ = (k : ℝ) * Real.pi ^ 2 /
          (2 * Real.sqrt
            (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)) := by
      simp only [intervalIntegral.integral_const]
      dsimp [a, b, C]
      ring

private lemma raw_outerUpper_pos
    (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    0 <
      (k : ℝ) * Real.pi ^ 2 /
        (2 * Real.sqrt
          (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)) := by
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase :
      0 ≤ ((k : ℝ) - 1) * Real.pi :=
    mul_nonneg (sub_nonneg.mpr hkR) Real.pi_pos.le
  have hr0 :
      0 ≤ Real.rpow (((k : ℝ) - 1) * Real.pi) n :=
    Real.rpow_nonneg hbase _
  have hspos :
      0 <
        Real.sqrt
          (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n) :=
    Real.sqrt_pos.2 (by linarith)
  positivity

private lemma rpow_half_sq (x p : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (p / 2) ^ 2 = Real.rpow x p := by
  have h := Real.rpow_mul hx (p / 2) 2
  rw [show p / 2 * 2 = p by ring, Real.rpow_two] at h
  exact h.symm

private lemma rpow_half_le_sqrt_one_add
    (x p : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (p / 2) ≤
      Real.sqrt (1 + Real.rpow x p) := by
  have hleft : 0 ≤ Real.rpow x (p / 2) :=
    Real.rpow_nonneg hx _
  have hright :
      0 ≤ Real.sqrt (1 + Real.rpow x p) :=
    Real.sqrt_nonneg _
  have hsqrt :
    Real.sqrt (1 + Real.rpow x p) ^ 2 =
        1 + Real.rpow x p :=
    Real.sq_sqrt
      (add_nonneg zero_le_one (Real.rpow_nonneg hx p))
  have hpow := rpow_half_sq x p hx
  nlinarith

private lemma shifted_rpow_summable
    (e : ℝ) (he : e < -1) :
    Summable (fun k : ℕ => Real.rpow ((k : ℝ) + 1) e) := by
  have hbase :
      Summable (fun k : ℕ => Real.rpow (k : ℝ) e) :=
    Real.summable_nat_rpow.mpr he
  have hshift :
      Summable
        (fun k : ℕ =>
          Real.rpow ((k + 1 : ℕ) : ℝ) e) :=
    (summable_nat_add_iff 1).2 hbase
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

private lemma shifted_rpow_not_summable
    (e : ℝ) (he : -1 ≤ e) :
    ¬ Summable (fun k : ℕ => Real.rpow ((k : ℝ) + 1) e) := by
  intro hshift
  have hshift' :
      Summable
        (fun k : ℕ =>
          Real.rpow ((k + 1 : ℕ) : ℝ) e) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hbase :
      Summable (fun k : ℕ => Real.rpow (k : ℝ) e) :=
    (summable_nat_add_iff 1).1 hshift'
  have := Real.summable_nat_rpow.mp hbase
  linarith

private def rawOuterUpper (n : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * Real.pi ^ 2 /
    (2 * Real.sqrt
      (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n))

private def rawCentralLower (n : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1) * Real.pi ^ 2 /
    (2 * Real.sqrt
      (1 + Real.rpow (((k : ℝ) + 1) * Real.pi) n))

private def rawCentralUpper (n : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.pi ^ 2 /
    Real.sqrt (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)

private lemma rawOuterUpper_nonneg (n : ℝ) (k : ℕ) :
    0 ≤ rawOuterUpper n (k + 2) := by
  unfold rawOuterUpper
  have hk : (0 : ℝ) ≤ (k + 2 : ℕ) := by positivity
  have hbase :
      0 ≤ (((k + 2 : ℕ) : ℝ) - 1) * Real.pi := by
    have : (1 : ℝ) ≤ (k + 2 : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ k + 2)
    exact mul_nonneg (sub_nonneg.mpr this) Real.pi_pos.le
  have hr0 :
      0 ≤
        Real.rpow
          ((((k + 2 : ℕ) : ℝ) - 1) * Real.pi) n :=
    Real.rpow_nonneg hbase _
  positivity

private lemma rawCentralUpper_nonneg (n : ℝ) (k : ℕ) :
    0 ≤ rawCentralUpper n (k + 2) := by
  unfold rawCentralUpper
  have hnum : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 1 := by
    positivity
  have hbase :
      0 ≤ (((k + 2 : ℕ) : ℝ) - 1) * Real.pi := by
    have : (1 : ℝ) ≤ (k + 2 : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ k + 2)
    exact mul_nonneg (sub_nonneg.mpr this) Real.pi_pos.le
  have hr0 :
      0 ≤
        Real.rpow
          ((((k + 2 : ℕ) : ℝ) - 1) * Real.pi) n :=
    Real.rpow_nonneg hbase _
  positivity

private lemma outerUpper_shift_bound
    (n : ℝ) (hn : 4 < n) (k : ℕ) :
    rawOuterUpper n (k + 2) ≤
      Real.pi ^ 2 *
        Real.rpow ((k : ℝ) + 1) (1 - n / 2) := by
  let u : ℝ := (k : ℝ) + 1
  let base : ℝ := u * Real.pi
  let q : ℝ := n / 2
  have hu0 : 0 < u := by
    dsimp [u]
    positivity
  have hu1 : 1 ≤ u := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    dsimp [u]
    linarith
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    positivity
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hubase : u ≤ base := by
    dsimp [base]
    nlinarith [Real.two_le_pi]
  have hpow :
      Real.rpow u q ≤ Real.rpow base q :=
    Real.rpow_le_rpow hu0.le hubase hq0.le
  have hden :
      Real.rpow u q ≤
        Real.sqrt (1 + Real.rpow base n) :=
    hpow.trans (rpow_half_le_sqrt_one_add base n hbase0)
  have hsqrtpos :
      0 < Real.sqrt (1 + Real.rpow base n) :=
    Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg zero_lt_one
        (Real.rpow_nonneg hbase0 n))
  have hupow : 0 < Real.rpow u q :=
    Real.rpow_pos_of_pos hu0 _
  have hnum :
      (u + 1) * Real.pi ^ 2 ≤
        (2 * u) * Real.pi ^ 2 := by
    have hpi2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    gcongr
    linarith
  have hrsub :
      Real.rpow u (1 - q) =
        u / Real.rpow u q := by
    calc
      Real.rpow u (1 - q) =
          Real.rpow u 1 / Real.rpow u q :=
        Real.rpow_sub hu0 1 q
      _ = u / Real.rpow u q := by
        rw [show Real.rpow u (1 : ℝ) = u from Real.rpow_one u]
  have hcalc :
      (u + 1) * Real.pi ^ 2 /
            (2 * Real.sqrt (1 + Real.rpow base n)) ≤
        Real.pi ^ 2 * Real.rpow u (1 - q) := by
    calc
      (u + 1) * Real.pi ^ 2 /
          (2 * Real.sqrt (1 + Real.rpow base n)) ≤
        (u + 1) * Real.pi ^ 2 /
          (2 * Real.rpow u q) := by
        exact div_le_div_of_nonneg_left
          (by positivity) (mul_pos two_pos hupow)
          (mul_le_mul_of_nonneg_left hden (by norm_num))
      _ ≤ (2 * u) * Real.pi ^ 2 /
          (2 * Real.rpow u q) := by
        exact div_le_div_of_nonneg_right hnum
          (mul_pos two_pos hupow).le
      _ = Real.pi ^ 2 * Real.rpow u (1 - q) := by
        rw [hrsub]
        field_simp [hupow.ne']
  unfold rawOuterUpper
  convert hcalc using 1 <;>
    simp [u, base, q, Nat.cast_add, Nat.cast_ofNat] <;> ring

private lemma centralUpper_shift_bound
    (n : ℝ) (hn : 4 < n) (k : ℕ) :
    rawCentralUpper n (k + 2) ≤
      3 * Real.pi ^ 2 *
        Real.rpow ((k : ℝ) + 1) (1 - n / 2) := by
  let u : ℝ := (k : ℝ) + 1
  let base : ℝ := u * Real.pi
  let q : ℝ := n / 2
  have hu0 : 0 < u := by
    dsimp [u]
    positivity
  have hu1 : 1 ≤ u := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    dsimp [u]
    linarith
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    positivity
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hubase : u ≤ base := by
    dsimp [base]
    nlinarith [Real.two_le_pi]
  have hpow :
      Real.rpow u q ≤ Real.rpow base q :=
    Real.rpow_le_rpow hu0.le hubase hq0.le
  have hden :
      Real.rpow u q ≤
        Real.sqrt (1 + Real.rpow base n) :=
    hpow.trans (rpow_half_le_sqrt_one_add base n hbase0)
  have hsqrtpos :
      0 < Real.sqrt (1 + Real.rpow base n) :=
    Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg zero_lt_one
        (Real.rpow_nonneg hbase0 n))
  have hupow : 0 < Real.rpow u q :=
    Real.rpow_pos_of_pos hu0 _
  have hnum :
      (u + 2) * Real.pi ^ 2 ≤
        (3 * u) * Real.pi ^ 2 := by
    have hpi2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    gcongr
    linarith
  have hrsub :
      Real.rpow u (1 - q) =
        u / Real.rpow u q := by
    calc
      Real.rpow u (1 - q) =
          Real.rpow u 1 / Real.rpow u q :=
        Real.rpow_sub hu0 1 q
      _ = u / Real.rpow u q := by
        rw [show Real.rpow u (1 : ℝ) = u from Real.rpow_one u]
  have hcalc :
      (u + 2) * Real.pi ^ 2 /
            Real.sqrt (1 + Real.rpow base n) ≤
        3 * Real.pi ^ 2 *
          Real.rpow u (1 - q) := by
    calc
      (u + 2) * Real.pi ^ 2 /
          Real.sqrt (1 + Real.rpow base n) ≤
        (u + 2) * Real.pi ^ 2 /
          Real.rpow u q := by
        exact div_le_div_of_nonneg_left
          (by positivity) hupow hden
      _ ≤ (3 * u) * Real.pi ^ 2 /
          Real.rpow u q := by
        exact div_le_div_of_nonneg_right hnum hupow.le
      _ = 3 * Real.pi ^ 2 *
          Real.rpow u (1 - q) := by
        rw [hrsub]
        field_simp [hupow.ne']
  unfold rawCentralUpper
  convert hcalc using 1 <;>
    simp [u, base, q, Nat.cast_add, Nat.cast_ofNat] <;> ring

private lemma raw_outerUpper_summable
    (n : ℝ) (hn : 4 < n) :
    Summable (fun k : ℕ => rawOuterUpper n (k + 2)) := by
  have he : 1 - n / 2 < -1 := by linarith
  have hmajorant :
      Summable
        (fun k : ℕ =>
          Real.pi ^ 2 *
            Real.rpow ((k : ℝ) + 1) (1 - n / 2)) :=
    (shifted_rpow_summable (1 - n / 2) he).mul_left
      (Real.pi ^ 2)
  exact Summable.of_nonneg_of_le
    (rawOuterUpper_nonneg n)
    (outerUpper_shift_bound n hn) hmajorant

private lemma raw_centralUpper_summable
    (n : ℝ) (hn : 4 < n) :
    Summable (fun k : ℕ => rawCentralUpper n (k + 2)) := by
  have he : 1 - n / 2 < -1 := by linarith
  have hmajorant :
      Summable
        (fun k : ℕ =>
          3 * Real.pi ^ 2 *
            Real.rpow ((k : ℝ) + 1) (1 - n / 2)) :=
    (shifted_rpow_summable (1 - n / 2) he).mul_left
      (3 * Real.pi ^ 2)
  exact Summable.of_nonneg_of_le
    (rawCentralUpper_nonneg n)
    (centralUpper_shift_bound n hn) hmajorant

private lemma sqrt_one_add_rpow_le
    (x p : ℝ) (hx : 1 ≤ x) (hp : 0 ≤ p) :
    Real.sqrt (1 + Real.rpow x p) ≤
      Real.sqrt 2 * Real.rpow x (p / 2) := by
  have hs0 : 0 ≤ Real.sqrt (1 + Real.rpow x p) :=
    Real.sqrt_nonneg _
  have hr0 : 0 ≤ Real.rpow x (p / 2) :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs_sq :
      Real.sqrt (1 + Real.rpow x p) ^ 2 =
        1 + Real.rpow x p :=
    Real.sq_sqrt
      (add_nonneg zero_le_one
        (Real.rpow_nonneg (zero_le_one.trans hx) p))
  have hs2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hp_sq :=
    rpow_half_sq x p (zero_le_one.trans hx)
  have hr1 : 1 ≤ Real.rpow x p :=
    Real.one_le_rpow hx hp
  have hrhs_sq :
      (Real.sqrt 2 * Real.rpow x (p / 2)) ^ 2 =
        2 * Real.rpow x p := by
    rw [mul_pow, hs2_sq, hp_sq]
  have hrhs0 :
      0 ≤ Real.sqrt 2 * Real.rpow x (p / 2) :=
    mul_nonneg hs20 hr0
  nlinarith

private lemma rawCentralLower_nonneg (n : ℝ) (k : ℕ) :
    0 ≤ rawCentralLower n (k + 2) := by
  unfold rawCentralLower
  have hnum :
      0 ≤ (((k + 2 : ℕ) : ℝ) - 1) * Real.pi ^ 2 := by
    have hk : (1 : ℝ) ≤ (k + 2 : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ k + 2)
    exact mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg _)
  have hbase :
      0 ≤ (((k + 2 : ℕ) : ℝ) + 1) * Real.pi := by
    positivity
  have hr0 :
      0 ≤ Real.rpow
        ((((k + 2 : ℕ) : ℝ) + 1) * Real.pi) n :=
    Real.rpow_nonneg hbase _
  positivity

private lemma centralLower_shift_lower_bound
    (n : ℝ) (hn0 : 0 ≤ n) (hn4 : n ≤ 4) (k : ℕ) :
    (Real.pi ^ 2 /
          (2 * Real.sqrt 2 *
            Real.rpow (3 * Real.pi) (n / 2))) *
        Real.rpow ((k : ℝ) + 1) (1 - n / 2) ≤
      rawCentralLower n (k + 2) := by
  let u : ℝ := (k : ℝ) + 1
  let v : ℝ := (u + 2) * Real.pi
  let q : ℝ := n / 2
  have hu0 : 0 < u := by
    dsimp [u]
    positivity
  have hu1 : 1 ≤ u := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    dsimp [u]
    linarith
  have hv1 : 1 ≤ v := by
    dsimp [v]
    nlinarith [Real.two_le_pi]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq2 : q ≤ 2 := by
    dsimp [q]
    linarith
  have hvupper :
      v ≤ (3 * Real.pi) * u := by
    dsimp [v]
    have : u + 2 ≤ 3 * u := by linarith
    nlinarith [Real.pi_pos]
  have hpow_v :
      Real.rpow v q ≤
        Real.rpow ((3 * Real.pi) * u) q :=
    Real.rpow_le_rpow (zero_le_one.trans hv1) hvupper hq0
  have hthreepi0 : 0 ≤ 3 * Real.pi := by positivity
  have hmul_rpow :
      Real.rpow ((3 * Real.pi) * u) q =
        Real.rpow (3 * Real.pi) q * Real.rpow u q :=
    Real.mul_rpow hthreepi0 hu0.le
  have hsqrt_bound :
      Real.sqrt (1 + Real.rpow v n) ≤
        Real.sqrt 2 *
          (Real.rpow (3 * Real.pi) q *
            Real.rpow u q) := by
    calc
      Real.sqrt (1 + Real.rpow v n) ≤
          Real.sqrt 2 * Real.rpow v (n / 2) :=
        sqrt_one_add_rpow_le v n hv1 hn0
      _ = Real.sqrt 2 * Real.rpow v q := by rfl
      _ ≤ Real.sqrt 2 *
          Real.rpow ((3 * Real.pi) * u) q := by
        gcongr
      _ = Real.sqrt 2 *
          (Real.rpow (3 * Real.pi) q *
            Real.rpow u q) := by rw [hmul_rpow]
  have hsqrtpos :
      0 < Real.sqrt (1 + Real.rpow v n) :=
    Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg zero_lt_one
        (Real.rpow_nonneg (zero_le_one.trans hv1) n))
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.2 (by norm_num)
  have hconstpow :
      0 < Real.rpow (3 * Real.pi) q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hupow : 0 < Real.rpow u q :=
    Real.rpow_pos_of_pos hu0 _
  have hbigden :
      0 <
        2 * Real.sqrt 2 *
          (Real.rpow (3 * Real.pi) q * Real.rpow u q) := by
    positivity
  have hdencompare :
      2 * Real.sqrt (1 + Real.rpow v n) ≤
        2 * Real.sqrt 2 *
          (Real.rpow (3 * Real.pi) q * Real.rpow u q) := by
    calc
      2 * Real.sqrt (1 + Real.rpow v n) ≤
          2 *
            (Real.sqrt 2 *
              (Real.rpow (3 * Real.pi) q *
                Real.rpow u q)) :=
        mul_le_mul_of_nonneg_left hsqrt_bound
          (by norm_num)
      _ = 2 * Real.sqrt 2 *
          (Real.rpow (3 * Real.pi) q *
            Real.rpow u q) := by ring
  have hrsub :
      Real.rpow u (1 - q) =
        u / Real.rpow u q := by
    calc
      Real.rpow u (1 - q) =
          Real.rpow u 1 / Real.rpow u q :=
        Real.rpow_sub hu0 1 q
      _ = u / Real.rpow u q := by
        rw [show Real.rpow u (1 : ℝ) = u from Real.rpow_one u]
  have hcalc :
      (Real.pi ^ 2 /
            (2 * Real.sqrt 2 *
              Real.rpow (3 * Real.pi) q)) *
          Real.rpow u (1 - q) ≤
        u * Real.pi ^ 2 /
          (2 * Real.sqrt (1 + Real.rpow v n)) := by
    calc
      (Real.pi ^ 2 /
            (2 * Real.sqrt 2 *
              Real.rpow (3 * Real.pi) q)) *
          Real.rpow u (1 - q) =
        u * Real.pi ^ 2 /
          (2 * Real.sqrt 2 *
            (Real.rpow (3 * Real.pi) q *
              Real.rpow u q)) := by
        rw [hrsub]
        field_simp [hs2pos.ne', hconstpow.ne', hupow.ne']
      _ ≤ u * Real.pi ^ 2 /
          (2 * Real.sqrt (1 + Real.rpow v n)) := by
        exact div_le_div_of_nonneg_left
          (by positivity) (mul_pos two_pos hsqrtpos)
          hdencompare
  unfold rawCentralLower
  convert hcalc using 1 <;>
    simp [u, v, q, Nat.cast_add, Nat.cast_ofNat] <;> ring

private lemma raw_centralLower_not_summable
    (n : ℝ) (hn0 : 0 ≤ n) (hn4 : n ≤ 4) :
    ¬ Summable (fun k : ℕ => rawCentralLower n (k + 2)) := by
  let C : ℝ :=
    Real.pi ^ 2 /
      (2 * Real.sqrt 2 *
        Real.rpow (3 * Real.pi) (n / 2))
  have hCpos : 0 < C := by
    dsimp [C]
    have hs2 : 0 < Real.sqrt 2 :=
      Real.sqrt_pos.2 (by norm_num)
    have hp : 0 < Real.rpow (3 * Real.pi) (n / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have he : -1 ≤ 1 - n / 2 := by linarith
  have hnot :
      ¬ Summable
        (fun k : ℕ =>
          C * Real.rpow ((k : ℝ) + 1) (1 - n / 2)) := by
    rw [summable_mul_left_iff hCpos.ne']
    exact shifted_rpow_not_summable (1 - n / 2) he
  intro hs
  apply hnot
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg hCpos.le
      (Real.rpow_nonneg (by positivity) _))
    (by
      intro k
      simpa [C] using
        centralLower_shift_lower_bound n hn0 hn4 k)
    hs

private def rawOuterBlock (n : ℝ) (k : ℕ) : ℝ :=
  ∫ x in ((k : ℝ) - 1) * Real.pi + Real.pi / 4..
      (k : ℝ) * Real.pi - Real.pi / 4,
    rawIntegrand n x

private def rawCentralBlock (n : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
      (k : ℝ) * Real.pi + Real.pi / 4,
    rawIntegrand n x

private lemma rawIntegrand_continuousOn_Ici
    (n : ℝ) (hn : 0 ≤ n) :
    ContinuousOn (rawIntegrand n) (Set.Ici 0) := by
  intro x hx
  unfold rawIntegrand
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y n) x :=
    (Real.continuous_rpow_const hn).continuousAt
  have hden :
      1 + Real.rpow x n * Real.sin x ^ 2 ≠ 0 := by
    have hr0 : 0 ≤ Real.rpow x n :=
      Real.rpow_nonneg hx _
    have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
    positivity
  exact (continuousAt_id.div
    (continuousAt_const.add
      (hr.mul (Real.continuous_sin.continuousAt.pow 2)))
    hden).continuousWithinAt

private lemma raw_intervalIntegrable_nonneg
    (n : ℝ) (hn : 0 ≤ n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (rawIntegrand n)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (rawIntegrand_continuousOn_Ici n hn).mono
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with hx | hx
  · exact ha.trans hx.1
  · exact hb.trans hx.1

private lemma raw_block_decomposition
    (n : ℝ) (hn : 0 ≤ n) (K : ℕ) :
    (∫ x in (0 : ℝ)..(K : ℝ) * Real.pi + Real.pi / 4,
        rawIntegrand n x) =
      (∫ x in (0 : ℝ)..Real.pi / 4, rawIntegrand n x) +
        (∑ k ∈ Finset.range K, rawOuterBlock n (k + 1)) +
        ∑ k ∈ Finset.range K, rawCentralBlock n (k + 1) := by
  induction K with
  | zero =>
      simp
  | succ K ih =>
      let a : ℝ := (K : ℝ) * Real.pi + Real.pi / 4
      let b : ℝ := ((K : ℝ) + 1) * Real.pi - Real.pi / 4
      let c : ℝ := ((K : ℝ) + 1) * Real.pi + Real.pi / 4
      have ha0 : 0 ≤ a := by
        dsimp [a]
        positivity
      have hb0 : 0 ≤ b := by
        dsimp [b]
        have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        nlinarith [Real.pi_pos]
      have hc0 : 0 ≤ c := by
        dsimp [c]
        positivity
      have hi₁ :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume 0 a :=
        raw_intervalIntegrable_nonneg n hn 0 a
          (by norm_num) ha0
      have hi₂ :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume a b :=
        raw_intervalIntegrable_nonneg n hn a b ha0 hb0
      have hi₃ :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume b c :=
        raw_intervalIntegrable_nonneg n hn b c hb0 hc0
      have hadd₁ :=
        intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
      have hi₁₂ :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume 0 b :=
        hi₁.trans hi₂
      have hadd₂ :=
        intervalIntegral.integral_add_adjacent_intervals hi₁₂ hi₃
      have hsplit :
          (∫ x in (0 : ℝ)..c, rawIntegrand n x) =
            (∫ x in (0 : ℝ)..a, rawIntegrand n x) +
              (∫ x in a..b, rawIntegrand n x) +
              ∫ x in b..c, rawIntegrand n x := by
        rw [← hadd₂, ← hadd₁]
      rw [show
        ((K + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 4 = c by
          dsimp [c]
          push_cast
          ring]
      rw [hsplit, ih]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hout :
          (∫ x in a..b, rawIntegrand n x) =
            rawOuterBlock n (K + 1) := by
        unfold rawOuterBlock
        congr 1 <;>
          dsimp [a, b] <;>
          push_cast <;> ring
      have hcentral :
          (∫ x in b..c, rawIntegrand n x) =
            rawCentralBlock n (K + 1) := by
        unfold rawCentralBlock
        congr 1 <;>
          dsimp [b, c] <;>
          push_cast <;> ring
      rw [hout, hcentral]
      ring

private lemma rawCentralBlock_nonneg
    (n : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ rawCentralBlock n k := by
  unfold rawCentralBlock
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 :
      0 ≤ (k : ℝ) * Real.pi - Real.pi / 4 := by
    nlinarith [Real.pi_pos]
  have hab :
      (k : ℝ) * Real.pi - Real.pi / 4 ≤
        (k : ℝ) * Real.pi + Real.pi / 4 := by
    linarith [Real.pi_pos]
  exact intervalIntegral.integral_nonneg hab (by
    intro x hx
    exact rawIntegrand_nonneg n x (ha0.trans hx.1))

private lemma rawInitial_nonneg (n : ℝ) :
    0 ≤
      ∫ x in (0 : ℝ)..Real.pi / 4,
        rawIntegrand n x := by
  exact intervalIntegral.integral_nonneg
    (by positivity) (by
      intro x hx
      exact rawIntegrand_nonneg n x hx.1)

private lemma raw_endpoint_integral_bound
    (n : ℝ) (hn : 4 < n) (N : ℕ) :
    (∫ x in (0 : ℝ)..
        ((N + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 4,
        rawIntegrand n x) ≤
      (∫ x in (0 : ℝ)..Real.pi / 4,
        rawIntegrand n x) +
        rawOuterBlock n 1 + rawCentralBlock n 1 +
        (∑' k : ℕ, rawOuterUpper n (k + 2)) +
        ∑' k : ℕ, rawCentralUpper n (k + 2) := by
  have hn0 : 0 ≤ n := by linarith
  have hdec := raw_block_decomposition n hn0 (N + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hdec
  simp only [Nat.zero_add, Nat.add_assoc] at hdec
  have hosum :
      (∑ k ∈ Finset.range N,
          rawOuterBlock n (k + 1 + 1)) ≤
        ∑' k : ℕ, rawOuterUpper n (k + 2) := by
    calc
      (∑ k ∈ Finset.range N,
          rawOuterBlock n (k + 1 + 1)) ≤
          ∑ k ∈ Finset.range N,
            rawOuterUpper n (k + 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk2 : 1 ≤ k + 2 := by omega
        simpa [rawOuterBlock, rawOuterUpper,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (raw_outerBlock_upper n hn0 (k + 2) hk2).le
      _ ≤ ∑' k : ℕ, rawOuterUpper n (k + 2) :=
        (raw_outerUpper_summable n hn).sum_le_tsum
          (Finset.range N)
          (fun k hk => rawOuterUpper_nonneg n k)
  have hcsum :
      (∑ k ∈ Finset.range N,
          rawCentralBlock n (k + 1 + 1)) ≤
        ∑' k : ℕ, rawCentralUpper n (k + 2) := by
    calc
      (∑ k ∈ Finset.range N,
          rawCentralBlock n (k + 1 + 1)) ≤
          ∑ k ∈ Finset.range N,
            rawCentralUpper n (k + 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk2 : 2 ≤ k + 2 := by omega
        simpa [rawCentralBlock, rawCentralUpper,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (raw_centralBlock_upper n hn0 (k + 2) hk2).le
      _ ≤ ∑' k : ℕ, rawCentralUpper n (k + 2) :=
        (raw_centralUpper_summable n hn).sum_le_tsum
          (Finset.range N)
          (fun k hk => rawCentralUpper_nonneg n k)
  rw [hdec]
  linarith

private lemma raw_integrable_tail_of_gt_four
    (n : ℝ) (hn : 4 < n) :
    MeasureTheory.IntegrableOn (rawIntegrand n) (Set.Ioi 1) := by
  let b : ℕ → ℝ :=
    fun N =>
      ((N + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 4
  let I : ℝ :=
    (∫ x in (0 : ℝ)..Real.pi / 4,
      rawIntegrand n x) +
      rawOuterBlock n 1 + rawCentralBlock n 1 +
      (∑' k : ℕ, rawOuterUpper n (k + 2)) +
      ∑' k : ℕ, rawCentralUpper n (k + 2)
  have hn0 : 0 ≤ n := by linarith
  have hb1 : ∀ N, 1 ≤ b N := by
    intro N
    dsimp [b]
    have hcast : (1 : ℝ) ≤ (N + 1 : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ N + 1)
    nlinarith [Real.two_le_pi, Real.pi_pos]
  have hfi :
      ∀ N,
        MeasureTheory.IntegrableOn (rawIntegrand n)
          (Set.Ioc 1 (b N)) := by
    intro N
    exact
      (raw_intervalIntegrable_nonneg n hn0 1 (b N)
        zero_le_one (zero_le_one.trans (hb1 N))).1
  have hb : Tendsto b atTop atTop := by
    have hmul :
        Tendsto
          (fun N : ℕ =>
            Real.pi * ((N + 1 : ℕ) : ℝ))
          atTop atTop := by
      have hcast :
          Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ))
            atTop atTop := by
        exact tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 1)
      exact hcast.const_mul_atTop Real.pi_pos
    have hadd :=
      tendsto_atTop_add_const_right atTop
        (Real.pi / 4) hmul
    exact hadd.congr (fun N => by
      dsimp [b]
      ring)
  apply
    MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      I 1 hfi hb
  filter_upwards [] with N
  have hnorm :
      (∫ x in (1 : ℝ)..b N, ‖rawIntegrand n x‖) =
        ∫ x in (1 : ℝ)..b N, rawIntegrand n x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (hb1 N)] at hx
    simp only [Real.norm_eq_abs]
    exact abs_of_nonneg
      (rawIntegrand_nonneg n x
        (zero_le_one.trans hx.1))
  have hi01 :=
    raw_intervalIntegrable_nonneg n hn0 0 1
      (by norm_num) zero_le_one
  have hi1b :=
    raw_intervalIntegrable_nonneg n hn0 1 (b N)
      zero_le_one (zero_le_one.trans (hb1 N))
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hi01 hi1b
  have h01 : 0 ≤
      ∫ x in (0 : ℝ)..1, rawIntegrand n x :=
    intervalIntegral.integral_nonneg zero_le_one (by
      intro x hx
      exact rawIntegrand_nonneg n x hx.1)
  rw [hnorm]
  have htail :
      (∫ x in (1 : ℝ)..b N, rawIntegrand n x) ≤
        ∫ x in (0 : ℝ)..b N, rawIntegrand n x := by
    linarith
  exact htail.trans (by
    simpa [b, I] using raw_endpoint_integral_bound n hn N)

private lemma rawIntegrand_le_id
    (n x : ℝ) (hx : 0 ≤ x) :
    rawIntegrand n x ≤ x := by
  unfold rawIntegrand
  have hr0 : 0 ≤ Real.rpow x n :=
    Real.rpow_nonneg hx _
  have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hden : 1 ≤ 1 + Real.rpow x n * Real.sin x ^ 2 := by
    exact le_add_of_nonneg_right (mul_nonneg hr0 hs0)
  exact div_le_self hx hden

private lemma raw_intervalIntegrable_zero_one (n : ℝ) :
    IntervalIntegrable (rawIntegrand n)
      MeasureTheory.volume 0 1 := by
  constructor
  · have hid :
        MeasureTheory.IntegrableOn (fun x : ℝ => x)
          (Set.Ioc 0 1) :=
      (continuous_id.intervalIntegrable 0 1).1
    refine hid.mono' ?_ ?_
    · exact ((rawIntegrand_continuousOn_Ioi n).mono
        Set.Ioc_subset_Ioi_self).aestronglyMeasurable
          measurableSet_Ioc
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
        with x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (rawIntegrand_nonneg n x hx.1.le)]
      exact rawIntegrand_le_id n x hx.1.le
  · simp

private lemma raw_converges_iff_integrable_tail (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A, rawIntegrand n x)
        atTop (𝓝 L)) ↔
      MeasureTheory.IntegrableOn (rawIntegrand n) (Set.Ioi 1) := by
  constructor
  · rintro ⟨L, hL⟩
    let c : ℝ :=
      ∫ x in (0 : ℝ)..1, rawIntegrand n x
    have htail :
        Tendsto
          (fun A : ℝ =>
            ∫ x in (1 : ℝ)..A, rawIntegrand n x)
          atTop (𝓝 (L - c)) := by
      have hsub := hL.sub_const c
      apply hsub.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
      have h01 := raw_intervalIntegrable_zero_one n
      have h1A :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume 1 A := by
        apply ContinuousOn.intervalIntegrable
        apply (rawIntegrand_continuousOn_Ioi n).mono
        intro x hx
        rw [Set.uIcc_of_le hA] at hx
        exact zero_lt_one.trans_le hx.1
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals h01 h1A
      dsimp [c]
      linarith
    apply
      MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
        (g := fun A : ℝ =>
          ∫ x in (1 : ℝ)..A, rawIntegrand n x)
        (g' := rawIntegrand n)
        (a := 1) (l := L - c)
    · intro A hA
      have hA0 : 0 < A := zero_lt_one.trans_le hA
      have hcont := rawIntegrand_continuousAt n A hA0
      have hint :
          IntervalIntegrable (rawIntegrand n)
            MeasureTheory.volume 1 A := by
        apply ContinuousOn.intervalIntegrable
        apply (rawIntegrand_continuousOn_Ioi n).mono
        intro x hx
        rw [Set.uIcc_of_le hA] at hx
        exact zero_lt_one.trans_le hx.1
      exact intervalIntegral.integral_hasDerivAt_right
        hint
        (ContinuousOn.stronglyMeasurableAtFilter
          isOpen_Ioi (rawIntegrand_continuousOn_Ioi n)
          A hA0)
        hcont
    · intro A hA
      exact rawIntegrand_nonneg n A
        (zero_le_one.trans hA.le)
    · exact htail
  · intro hint
    let T : ℝ :=
      ∫ x : ℝ in Set.Ioi 1, rawIntegrand n x
    let c : ℝ :=
      ∫ x in (0 : ℝ)..1, rawIntegrand n x
    refine ⟨c + T, ?_⟩
    have htail :
        Tendsto
          (fun A : ℝ =>
            ∫ x in (1 : ℝ)..A, rawIntegrand n x)
          atTop (𝓝 T) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        1 hint tendsto_id
    have hc :
        Tendsto (fun _ : ℝ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have haddlim := hc.add htail
    apply haddlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    have h01 := raw_intervalIntegrable_zero_one n
    have h1A :
        IntervalIntegrable (rawIntegrand n)
          MeasureTheory.volume 1 A := by
      apply ContinuousOn.intervalIntegrable
      apply (rawIntegrand_continuousOn_Ioi n).mono
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      exact zero_lt_one.trans_le hx.1
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals h01 h1A
    simpa [c, T] using hadd

private lemma raw_centralBlocks_summable_of_integrable
    (n : ℝ) (hn : 0 ≤ n)
    (hint :
      MeasureTheory.IntegrableOn (rawIntegrand n) (Set.Ioi 1)) :
    Summable (fun k : ℕ => rawCentralBlock n (k + 2)) := by
  apply summable_of_sum_range_le
    (fun k => rawCentralBlock_nonneg n (k + 2) (by omega))
    (c :=
      (∫ x in (0 : ℝ)..1, rawIntegrand n x) +
        ∫ x in Set.Ioi (1 : ℝ), rawIntegrand n x)
  intro N
  let b : ℝ :=
    ((N + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 4
  have hb1 : 1 ≤ b := by
    dsimp [b]
    have hcast : (1 : ℝ) ≤ (N + 1 : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ N + 1)
    nlinarith [Real.two_le_pi, Real.pi_pos]
  have hdec := raw_block_decomposition n hn (N + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hdec
  simp only [Nat.zero_add, Nat.add_assoc] at hdec
  have hinit := rawInitial_nonneg n
  have hout1 : 0 ≤ rawOuterBlock n 1 :=
    (raw_outerBlock_pos n 1 (by norm_num)).le
  have hcentral1 : 0 ≤ rawCentralBlock n 1 :=
    rawCentralBlock_nonneg n 1 (by norm_num)
  have houtsum :
      0 ≤
        ∑ k ∈ Finset.range N,
          rawOuterBlock n (k + 1 + 1) := by
    apply Finset.sum_nonneg
    intro k hk
    exact (raw_outerBlock_pos n (k + 1 + 1)
      (by omega)).le
  have hcentral_le_endpoint :
      (∑ k ∈ Finset.range N,
          rawCentralBlock n (k + 2)) ≤
        ∫ x in (0 : ℝ)..b, rawIntegrand n x := by
    have hdec' :
        (∫ x in (0 : ℝ)..b, rawIntegrand n x) =
          (∫ x in (0 : ℝ)..Real.pi / 4,
            rawIntegrand n x) +
            ((∑ k ∈ Finset.range N,
                rawOuterBlock n (k + 1 + 1)) +
              rawOuterBlock n 1) +
            ((∑ k ∈ Finset.range N,
                rawCentralBlock n (k + 1 + 1)) +
              rawCentralBlock n 1) := by
      simpa [b] using hdec
    rw [hdec']
    have hsame :
        (∑ k ∈ Finset.range N,
            rawCentralBlock n (k + 2)) =
          ∑ k ∈ Finset.range N,
            rawCentralBlock n (k + 1 + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.add_assoc]
    rw [hsame]
    linarith
  have h01 := raw_intervalIntegrable_zero_one n
  have h1b :=
    raw_intervalIntegrable_nonneg n hn 1 b
      zero_le_one (zero_le_one.trans hb1)
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h01 h1b
  have htailb :
      MeasureTheory.IntegrableOn (rawIntegrand n) (Set.Ioi b) :=
    hint.mono_set (Set.Ioi_subset_Ioi hb1)
  have htail_eq :=
    intervalIntegral.integral_interval_add_Ioi
      (f := rawIntegrand n) (a := 1) (b := b)
      hint htailb
  have hfar_nonneg :
      0 ≤ ∫ x in Set.Ioi b, rawIntegrand n x := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact rawIntegrand_nonneg n x
      (zero_le_one.trans (hb1.trans_lt hx).le)
  have hendpoint_le :
      (∫ x in (0 : ℝ)..b, rawIntegrand n x) ≤
        (∫ x in (0 : ℝ)..1, rawIntegrand n x) +
          ∫ x in Set.Ioi (1 : ℝ), rawIntegrand n x := by
    linarith
  exact hcentral_le_endpoint.trans hendpoint_le

private lemma raw_not_integrable_tail_of_neg
    (n : ℝ) (hn : n < 0) :
    ¬ MeasureTheory.IntegrableOn
      (rawIntegrand n) (Set.Ioi 1) := by
  intro hint
  have hhalf :
      MeasureTheory.IntegrableOn (fun x : ℝ => x / 2)
        (Set.Ioi 1) := by
    refine hint.mono' ?_ ?_
    · exact
        (continuous_id.div_const (2 : ℝ)).continuousOn.aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with x hx
      have hx1 : 1 ≤ x := hx.le
      have hx0 : 0 < x := zero_lt_one.trans_le hx1
      have hrle : Real.rpow x n ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 hn.le
      have hr0 : 0 ≤ Real.rpow x n :=
        Real.rpow_nonneg hx0.le _
      have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
      have hsle : Real.sin x ^ 2 ≤ 1 := by
        have habs := Real.abs_sin_le_one x
        have hsquare :=
          (sq_le_sq₀ (abs_nonneg (Real.sin x))
            zero_le_one).2 habs
        simpa only [sq_abs, one_pow] using hsquare
      have hden :
          1 + Real.rpow x n * Real.sin x ^ 2 ≤ 2 := by
        have hprod :
            Real.rpow x n * Real.sin x ^ 2 ≤ 1 :=
          calc
            Real.rpow x n * Real.sin x ^ 2 ≤
                1 * 1 :=
              mul_le_mul hrle hsle hs0 zero_le_one
            _ = 1 := mul_one 1
        linarith
      have hdenpos :
          0 < 1 + Real.rpow x n * Real.sin x ^ 2 := by
        positivity
      simpa only [rawIntegrand, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ x / 2),
          abs_of_nonneg (div_nonneg hx0.le hdenpos.le)] using
        (div_le_div_of_nonneg_left hx0.le hdenpos hden :
          x / 2 ≤
            x / (1 + Real.rpow x n * Real.sin x ^ 2))
  have hxint :
      MeasureTheory.IntegrableOn (fun x : ℝ => x)
        (Set.Ioi 1) := by
    have hmul := hhalf.const_mul 2
    have heq :
        (fun x : ℝ => (2 : ℝ) * (x / 2)) =
          fun x : ℝ => x := by
      funext x
      ring
    rw [heq] at hmul
    exact hmul
  have hcrit :=
    (integrableOn_Ioi_rpow_iff (s := (1 : ℝ))
      (t := (1 : ℝ)) zero_lt_one).1
      (by simpa using hxint)
  norm_num at hcrit

private lemma raw_converges_iff_gt_four (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A, rawIntegrand n x)
        atTop (𝓝 L)) ↔
      4 < n := by
  rw [raw_converges_iff_integrable_tail]
  constructor
  · intro hint
    by_cases hnneg : n < 0
    · exact False.elim
        (raw_not_integrable_tail_of_neg n hnneg hint)
    · have hn0 : 0 ≤ n := le_of_not_gt hnneg
      by_contra hn4not
      have hn4 : n ≤ 4 := le_of_not_gt hn4not
      have hblocks :=
        raw_centralBlocks_summable_of_integrable n hn0 hint
      have hlower :
          Summable
            (fun k : ℕ => rawCentralLower n (k + 2)) := by
        exact Summable.of_nonneg_of_le
          (fun k => rawCentralLower_nonneg n k)
          (fun k => by
            simpa [rawCentralBlock, rawCentralLower] using
              (raw_centralBlock_lower n hn0 (k + 2)
                (by omega)).le)
          hblocks
      exact raw_centralLower_not_summable n hn0 hn4 hlower
  · exact raw_integrable_tail_of_gt_four n

private lemma raw_infinite_block_decomposition
    (n : ℝ) (hn : 4 < n) :
    (∫ x in Set.Ioi (0 : ℝ), rawIntegrand n x) =
      (∫ x in (0 : ℝ)..Real.pi / 4, rawIntegrand n x) +
        (∑' k : ℕ, rawOuterBlock n (k + 1)) +
        ∑' k : ℕ, rawCentralBlock n (k + 1) := by
  have hn0 : 0 ≤ n := by linarith
  have htail :=
    raw_integrable_tail_of_gt_four n hn
  have hlocal :
      MeasureTheory.IntegrableOn (rawIntegrand n)
        (Set.Ioc 0 1) :=
    (raw_intervalIntegrable_zero_one n).1
  have hfull :
      MeasureTheory.IntegrableOn (rawIntegrand n)
        (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hlocal.union htail
  have houterTail :
      Summable (fun k : ℕ => rawOuterBlock n (k + 2)) := by
    exact Summable.of_nonneg_of_le
      (fun k =>
        (raw_outerBlock_pos n (k + 2) (by omega)).le)
      (fun k => by
        simpa [rawOuterBlock, rawOuterUpper] using
          (raw_outerBlock_upper n hn0 (k + 2)
            (by omega)).le)
      (raw_outerUpper_summable n hn)
  have hcentralTail :
      Summable
        (fun k : ℕ => rawCentralBlock n (k + 2)) := by
    exact Summable.of_nonneg_of_le
      (fun k =>
        rawCentralBlock_nonneg n (k + 2) (by omega))
      (fun k => by
        simpa [rawCentralBlock, rawCentralUpper] using
          (raw_centralBlock_upper n hn0 (k + 2)
            (by omega)).le)
      (raw_centralUpper_summable n hn)
  have houter :
      Summable (fun k : ℕ => rawOuterBlock n (k + 1)) := by
    apply (summable_nat_add_iff 1).1
    simpa [Nat.add_assoc] using houterTail
  have hcentral :
      Summable
        (fun k : ℕ => rawCentralBlock n (k + 1)) := by
    apply (summable_nat_add_iff 1).1
    simpa [Nat.add_assoc] using hcentralTail
  let b : ℕ → ℝ :=
    fun K => (K : ℝ) * Real.pi + Real.pi / 4
  have hb : Tendsto b atTop atTop := by
    have hcast :
        Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hmul :
        Tendsto (fun K : ℕ => Real.pi * (K : ℝ))
          atTop atTop :=
      hcast.const_mul_atTop Real.pi_pos
    have hadd :=
      tendsto_atTop_add_const_right atTop
        (Real.pi / 4) hmul
    exact hadd.congr (fun K => by
      dsimp [b]
      ring)
  have hIntegral :
      Tendsto
        (fun K : ℕ =>
          ∫ x in (0 : ℝ)..b K, rawIntegrand n x)
        atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ), rawIntegrand n x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      0 hfull hb
  have hSeries :
      Tendsto
        (fun K : ℕ =>
          (∫ x in (0 : ℝ)..Real.pi / 4,
              rawIntegrand n x) +
            (∑ k ∈ Finset.range K,
              rawOuterBlock n (k + 1)) +
            ∑ k ∈ Finset.range K,
              rawCentralBlock n (k + 1))
        atTop
        (𝓝
          ((∫ x in (0 : ℝ)..Real.pi / 4,
              rawIntegrand n x) +
            (∑' k : ℕ, rawOuterBlock n (k + 1)) +
            ∑' k : ℕ, rawCentralBlock n (k + 1))) := by
    exact
      (tendsto_const_nhds.add
        houter.hasSum.tendsto_sum_nat).add
          hcentral.hasSum.tendsto_sum_nat
  have hIntegral' :
      Tendsto
        (fun K : ℕ =>
          ∫ x in (0 : ℝ)..b K, rawIntegrand n x)
        atTop
        (𝓝
          ((∫ x in (0 : ℝ)..Real.pi / 4,
              rawIntegrand n x) +
            (∑' k : ℕ, rawOuterBlock n (k + 1)) +
            ∑' k : ℕ, rawCentralBlock n (k + 1))) := by
    apply hSeries.congr
    intro K
    simpa [b] using (raw_block_decomposition n hn0 K).symm
  exact tendsto_nhds_unique hIntegral hIntegral'

namespace ProofGap.Exercise3746

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def integrand (n x : ℝ) : ℝ :=
  x / (1 + Real.rpow x n * Real.sin x ^ 2)

def partialIntegral (n A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A, integrand n x

def Converges (n : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialIntegral n) atTop (𝓝 L)

def outerBlock (n : ℝ) (k : ℕ) : ℝ :=
  ∫ x in ((k : ℝ) - 1) * Real.pi + Real.pi / 4..
      (k : ℝ) * Real.pi - Real.pi / 4,
    integrand n x

def centralBlock (n : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (k : ℝ) * Real.pi - Real.pi / 4..
      (k : ℝ) * Real.pi + Real.pi / 4,
    integrand n x

def outerUpper (n : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * Real.pi ^ 2 /
    (2 * Real.sqrt
      (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n))

def centralLower (n : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1) * Real.pi ^ 2 /
    (2 * Real.sqrt
      (1 + Real.rpow (((k : ℝ) + 1) * Real.pi) n))

def centralUpper (n : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.pi ^ 2 /
    Real.sqrt (1 + Real.rpow (((k : ℝ) - 1) * Real.pi) n)

theorem gap1 (n : ℝ) (hconv : Converges n) :
    (∫ x in Set.Ioi (0 : ℝ), integrand n x) =
      (∫ x in (0 : ℝ)..Real.pi / 4, integrand n x) +
        (∑' k : ℕ, outerBlock n (k + 1)) +
        ∑' k : ℕ, centralBlock n (k + 1) := by
  have hn : 4 < n := by
    apply (raw_converges_iff_gt_four n).1
    simpa [Converges, partialIntegral, integrand, rawIntegrand] using hconv
  simpa [integrand, rawIntegrand, outerBlock, rawOuterBlock,
      centralBlock, rawCentralBlock] using
    raw_infinite_block_decomposition n hn

theorem gap2 (n : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    0 < outerBlock n k := by
  simpa [outerBlock, integrand, rawIntegrand] using
    raw_outerBlock_pos n k hk

theorem gap3 (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    outerBlock n k < outerUpper n k := by
  simpa [outerBlock, integrand, rawIntegrand, outerUpper] using
    raw_outerBlock_upper n hn k hk

theorem gap4 (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    0 < outerUpper n k := by
  simpa [outerUpper] using raw_outerUpper_pos n hn k hk

theorem gap5 (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k) :
    centralLower n k < centralBlock n k := by
  simpa [centralLower, centralBlock, integrand, rawIntegrand] using
    raw_centralBlock_lower n hn k hk

theorem gap6 (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k) :
    centralBlock n k < centralUpper n k := by
  simpa [centralBlock, integrand, rawIntegrand, centralUpper] using
    raw_centralBlock_upper n hn k hk

theorem gap7 (n : ℝ) (hn : 0 ≤ n) (k : ℕ) (hk : 2 ≤ k) :
    centralLower n k < centralUpper n k := by
  exact (gap5 n hn k hk).trans (gap6 n hn k hk)

theorem gap8 (n : ℝ) (hn : 4 < n) :
    Summable (fun k : ℕ => outerUpper n (k + 2)) := by
  simpa [outerUpper, rawOuterUpper] using
    raw_outerUpper_summable n hn

theorem gap9 (n : ℝ) (hn : 4 < n) :
    Summable (fun k : ℕ => centralUpper n (k + 2)) := by
  simpa [centralUpper, rawCentralUpper] using
    raw_centralUpper_summable n hn

theorem gap10 (n : ℝ) (hn0 : 0 ≤ n) (hn4 : n ≤ 4) :
    ¬ Summable (fun k : ℕ => centralLower n (k + 2)) := by
  simpa [centralLower, rawCentralLower] using
    raw_centralLower_not_summable n hn0 hn4

theorem gap11 (n : ℝ) :
    4 < n ↔ Converges n := by
  simpa [Converges, partialIntegral, integrand, rawIntegrand] using
    (raw_converges_iff_gt_four n).symm

end

end ProofGap.Exercise3746
