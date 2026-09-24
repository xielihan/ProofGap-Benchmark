import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1296_2

noncomputable section

def powerMean (a b s : ℝ) : ℝ :=
  if s = 0 then Real.sqrt (a * b)
  else Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s)

def numerator (a b s : ℝ) : ℝ :=
  Real.rpow a s * Real.log (Real.rpow a s) +
    Real.rpow b s * Real.log (Real.rpow b s) -
    (Real.rpow a s + Real.rpow b s) *
      Real.log ((Real.rpow a s + Real.rpow b s) / 2)

private theorem hasDerivAtRpowExponent (a s : ℝ) (ha : 0 < a) :
    HasDerivAt (fun t : ℝ => Real.rpow a t)
      (Real.rpow a s * Real.log a) s := by
  have hin : HasDerivAt (fun t : ℝ => Real.log a * t) (Real.log a) s := by
    convert (hasDerivAt_const s (Real.log a)).mul (hasDerivAt_id s) using 1 <;>
      ring
  have hout : HasDerivAt (fun t : ℝ => Real.exp (Real.log a * t))
      (Real.exp (Real.log a * s) * Real.log a) s := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (Real.log a * s)).comp s hin
  have heq : (fun t : ℝ => Real.rpow a t) =
      fun t => Real.exp (Real.log a * t) := by
    funext t
    exact Real.rpow_def_of_pos ha t
  have hval : Real.rpow a s = Real.exp (Real.log a * s) :=
    Real.rpow_def_of_pos ha s
  rw [heq, hval]
  exact hout

private theorem hasDerivAtLogPowerMean (a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : s ≠ 0) :
    HasDerivAt (fun t => Real.log (powerMean a b t))
      (-(1 / s ^ 2) *
          Real.log ((Real.rpow a s + Real.rpow b s) / 2) +
        (Real.rpow a s * Real.log a +
          Real.rpow b s * Real.log b) /
          (s * (Real.rpow a s + Real.rpow b s))) s := by
  have hpa : 0 < Real.rpow a s := Real.rpow_pos_of_pos ha s
  have hpb : 0 < Real.rpow b s := Real.rpow_pos_of_pos hb s
  have hsum : Real.rpow a s + Real.rpow b s ≠ 0 := by
    nlinarith
  have hbase : 0 < (Real.rpow a s + Real.rpow b s) / 2 := by
    nlinarith
  have heq : (fun t => Real.log (powerMean a b t)) =ᶠ[nhds s]
      (fun t => (1 / t) *
        Real.log ((Real.rpow a t + Real.rpow b t) / 2)) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    rw [powerMean, if_neg ht]
    have hpta : 0 < Real.rpow a t := Real.rpow_pos_of_pos ha t
    have hptb : 0 < Real.rpow b t := Real.rpow_pos_of_pos hb t
    have hq : 0 < (Real.rpow a t + Real.rpow b t) / 2 := by
      nlinarith
    exact Real.log_rpow hq (1 / t)
  have hpowA := hasDerivAtRpowExponent a s ha
  have hpowB := hasDerivAtRpowExponent b s hb
  have hlog := ((hpowA.add hpowB).div_const 2).log hbase.ne'
  have hraw : HasDerivAt
      (fun t => (1 / t) *
        Real.log ((Real.rpow a t + Real.rpow b t) / 2))
      (-(1 / s ^ 2) *
          Real.log ((Real.rpow a s + Real.rpow b s) / 2) +
        (Real.rpow a s * Real.log a +
          Real.rpow b s * Real.log b) /
          (s * (Real.rpow a s + Real.rpow b s))) s := by
    convert (hasDerivAt_inv hs).mul hlog using 1
    · funext t
      simp [one_div]
    · simp only [Pi.add_apply]
      field_simp [hs, hsum]
  exact hraw.congr_of_eventuallyEq heq

private theorem derivativeFormulaAlgebra (a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : s ≠ 0) :
    -(1 / s ^ 2) *
          Real.log ((Real.rpow a s + Real.rpow b s) / 2) +
        (Real.rpow a s * Real.log a +
          Real.rpow b s * Real.log b) /
          (s * (Real.rpow a s + Real.rpow b s)) =
      numerator a b s /
        (s ^ 2 * (Real.rpow a s + Real.rpow b s)) := by
  have hpa : 0 < Real.rpow a s := Real.rpow_pos_of_pos ha s
  have hpb : 0 < Real.rpow b s := Real.rpow_pos_of_pos hb s
  have hsum : Real.rpow a s + Real.rpow b s ≠ 0 := by
    nlinarith
  have hla : Real.log (Real.rpow a s) = s * Real.log a :=
    Real.log_rpow ha s
  have hlb : Real.log (Real.rpow b s) = s * Real.log b :=
    Real.log_rpow hb s
  unfold numerator
  rw [hla, hlb]
  field_simp [hs, hsum]
  ring

private theorem continuousAtLogPowerMean (a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    ContinuousAt (fun t => Real.log (powerMean a b t)) s := by
  by_cases hs : s = 0
  · subst s
    let g := fun t : ℝ =>
      Real.log ((Real.rpow a t + Real.rpow b t) / 2)
    let m := (Real.log a + Real.log b) / 2
    have hbaseDeriv : HasDerivAt
        (fun t : ℝ => (Real.rpow a t + Real.rpow b t) / 2) m 0 := by
      dsimp [m]
      convert ((hasDerivAtRpowExponent a 0 ha).add
        (hasDerivAtRpowExponent b 0 hb)).div_const 2 using 1 <;>
        norm_num <;> ring
    have hg : HasDerivAt g m 0 := by
      dsimp [g]
      convert hbaseDeriv.log (by norm_num) using 1 <;>
        norm_num
    have hg0 : g 0 = 0 := by
      simp [g]
    have ht : Tendsto (fun t : ℝ => (1 / t) * g t)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds m) := by
      simpa [hg0, div_eq_mul_inv, mul_comm] using hg.tendsto_slope_zero
    have heq : (fun t => Real.log (powerMean a b t))
        =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun t => (1 / t) * g t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht0' : t ≠ 0 := by simpa using ht0
      rw [powerMean, if_neg ht0']
      have hpta : 0 < Real.rpow a t := Real.rpow_pos_of_pos ha t
      have hptb : 0 < Real.rpow b t := Real.rpow_pos_of_pos hb t
      have hq : 0 < (Real.rpow a t + Real.rpow b t) / 2 := by
        nlinarith
      dsimp [g]
      exact Real.log_rpow hq (1 / t)
    have hpunct : Tendsto (fun t => Real.log (powerMean a b t))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds m) :=
      ht.congr' heq.symm
    have hf0 : Real.log (powerMean a b 0) = m := by
      simp [powerMean, m, Real.log_sqrt (mul_pos ha hb).le,
        Real.log_mul ha.ne' hb.ne']
    have heqpoint : (fun t => Real.log (powerMean a b t))
        =ᶠ[nhdsWithin 0 ({0} : Set ℝ)] (fun _ => m) := by
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht0' : t = 0 := by simpa using ht0
      subst t
      exact hf0
    have hpoint : Tendsto (fun t => Real.log (powerMean a b t))
        (nhdsWithin 0 ({0} : Set ℝ)) (nhds m) :=
      tendsto_const_nhds.congr' heqpoint.symm
    have hcover : ({0} : Set ℝ)ᶜ ∪ {0} = Set.univ := by
      classical
      ext x
      by_cases hx : x = 0 <;> simp [hx]
    have hnhds : nhds (0 : ℝ) =
        nhdsWithin 0 ({0} : Set ℝ)ᶜ ⊔ nhdsWithin 0 ({0} : Set ℝ) := by
      calc
        nhds (0 : ℝ) = nhdsWithin 0 Set.univ := by simp
        _ = nhdsWithin 0 (({0} : Set ℝ)ᶜ ∪ {0}) := by rw [hcover]
        _ = nhdsWithin 0 ({0} : Set ℝ)ᶜ ⊔
            nhdsWithin 0 ({0} : Set ℝ) :=
          nhdsWithin_union (0 : ℝ) ({0} : Set ℝ)ᶜ ({0} : Set ℝ)
    show Tendsto (fun t => Real.log (powerMean a b t))
      (nhds 0) (nhds (Real.log (powerMean a b 0)))
    rw [hf0, hnhds]
    exact hpunct.sup hpoint
  · exact (hasDerivAtLogPowerMean a b s ha hb hs).continuousAt

theorem gap1 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    Real.log (powerMean a b s) =
      (1 / s) *
        Real.log ((Real.rpow a s + Real.rpow b s) / 2) := by
  rw [powerMean, if_neg hs]
  have hpa : 0 < Real.rpow a s := Real.rpow_pos_of_pos ha s
  have hpb : 0 < Real.rpow b s := Real.rpow_pos_of_pos hb s
  have hbase : 0 < (Real.rpow a s + Real.rpow b s) / 2 := by
    nlinarith
  exact Real.log_rpow hbase (1 / s)

theorem gap2 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    deriv (fun t => Real.log (powerMean a b t)) s =
      -(1 / s ^ 2) *
          Real.log ((Real.rpow a s + Real.rpow b s) / 2) +
        (Real.rpow a s * Real.log a +
          Real.rpow b s * Real.log b) /
          (s * (Real.rpow a s + Real.rpow b s)) := by
  exact (hasDerivAtLogPowerMean a b s ha hb hs).deriv

theorem gap3 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    deriv (fun t => Real.log (powerMean a b t)) s =
      numerator a b s /
        (s ^ 2 * (Real.rpow a s + Real.rpow b s)) := by
  rw [gap2 a b s ha hb hs]
  exact derivativeFormulaAlgebra a b s ha hb hs

theorem gap4 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    -(1 / s ^ 2) *
          Real.log ((Real.rpow a s + Real.rpow b s) / 2) +
        (Real.rpow a s * Real.log a +
          Real.rpow b s * Real.log b) /
          (s * (Real.rpow a s + Real.rpow b s)) =
      numerator a b s /
        (s ^ 2 * (Real.rpow a s + Real.rpow b s)) := by
  exact derivativeFormulaAlgebra a b s ha hb hs

theorem gap5 (a s : ℝ) (ha : 0 < a) :
    0 < Real.rpow a s := by
  exact Real.rpow_pos_of_pos ha s

theorem gap6 (b s : ℝ) (hb : 0 < b) :
    0 < Real.rpow b s := by
  exact Real.rpow_pos_of_pos hb s

theorem gap7 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hs : s ≠ 0) :
    0 < numerator a b s := by
  let x := Real.rpow a s
  let y := Real.rpow b s
  let m := (x + y) / 2
  have hx : 0 < x := gap5 a s ha
  have hy : 0 < y := gap6 b s hb
  have hm : 0 < m := by
    dsimp [m]
    nlinarith
  have hxy : x ≠ y := by
    intro h
    have hlogs : s * Real.log a = s * Real.log b := by
      calc
        s * Real.log a = Real.log x := by
          dsimp [x]
          symm
          exact Real.log_rpow ha s
        _ = Real.log y := congrArg Real.log h
        _ = s * Real.log b := by
          dsimp [y]
          exact Real.log_rpow hb s
    have hl : Real.log a = Real.log b := by
      have hz : s * (Real.log a - Real.log b) = 0 := by
        linarith
      rcases mul_eq_zero.mp hz with hs0 | hl0
      · exact False.elim (hs hs0)
      · linarith
    apply hab
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ = Real.exp (Real.log b) := by rw [hl]
      _ = b := Real.exp_log hb
  have hmx : 0 < m / x := div_pos hm hx
  have hmy : 0 < m / y := div_pos hm hy
  have hux : Real.log (m / x) ≠ 0 := by
    intro hu
    have hr : m / x = 1 := by
      have he := congrArg Real.exp hu
      simpa [Real.exp_log hmx] using he
    have hmx_eq : m = x := by
      field_simp [ne_of_gt hx] at hr
      exact hr
    apply hxy
    dsimp [m] at hmx_eq
    linarith
  have hlogmx : Real.log (m / x) = Real.log m - Real.log x := by
    rw [Real.log_div hm.ne' hx.ne']
  have hlogmy : Real.log (m / y) = Real.log m - Real.log y := by
    rw [Real.log_div hm.ne' hy.ne']
  have hex : 1 + Real.log (m / x) < Real.exp (Real.log (m / x)) := by
    simpa [add_comm] using Real.add_one_lt_exp hux
  rw [Real.exp_log hmx] at hex
  have hexy : 1 + Real.log (m / y) ≤ Real.exp (Real.log (m / y)) := by
    simpa [add_comm] using Real.add_one_le_exp (Real.log (m / y))
  rw [Real.exp_log hmy] at hexy
  have hxratio : x * (m / x) = m := by
    field_simp [ne_of_gt hx]
  have hyratio : y * (m / y) = m := by
    field_simp [ne_of_gt hy]
  have hxb := mul_lt_mul_of_pos_left hex hx
  have hyb := mul_le_mul_of_nonneg_left hexy hy.le
  rw [hxratio] at hxb
  rw [hyratio] at hyb
  rw [hlogmx] at hxb
  rw [hlogmy] at hyb
  unfold numerator
  change x * Real.log x + y * Real.log y -
      (x + y) * Real.log ((x + y) / 2) > 0
  change x * Real.log x + y * Real.log y -
      (x + y) * Real.log m > 0
  dsimp [m] at hxb hyb ⊢
  nlinarith

theorem gap8 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hs : s ≠ 0) :
    0 < deriv (fun t => Real.log (powerMean a b t)) s := by
  rw [gap3 a b s ha hb hs]
  have hn : 0 < numerator a b s := gap7 a b s ha hb hab hs
  have hpa : 0 < Real.rpow a s := gap5 a s ha
  have hpb : 0 < Real.rpow b s := gap6 b s hb
  have hsum : 0 < Real.rpow a s + Real.rpow b s := by
    linarith
  have hsquare : 0 < s ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hs
  exact div_pos hn (mul_pos hsquare hsum)

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    StrictMono (fun s => Real.log (powerMean a b s)) := by
  let f := fun s => Real.log (powerMean a b s)
  have hsegment : ∀ {u v : ℝ}, u < v → (v ≤ 0 ∨ 0 ≤ u) → f u < f v := by
    intro u v huv huv0
    have hcont : ContinuousOn f (Set.Icc u v) := by
      intro z hz
      exact (continuousAtLogPowerMean a b z ha hb).continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo u v) := by
      intro z hz
      have hz0 : z ≠ 0 := by
        rcases huv0 with hv | hu
        · exact ne_of_lt (lt_of_lt_of_le hz.2 hv)
        · exact ne_of_gt (lt_of_le_of_lt hu hz.1)
      exact (hasDerivAtLogPowerMean a b z ha hb hz0).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f huv hcont hdiff with ⟨z, hz, hzderiv⟩
    have hz0 : z ≠ 0 := by
      rcases huv0 with hv | hu
      · exact ne_of_lt (lt_of_lt_of_le hz.2 hv)
      · exact ne_of_gt (lt_of_le_of_lt hu hz.1)
    have hp : 0 < deriv f z := gap8 a b z ha hb hab hz0
    rw [hzderiv] at hp
    have hden : 0 < v - u := sub_pos.mpr huv
    rcases div_pos_iff.mp hp with hpos | hneg
    · linarith [hpos.1]
    · linarith [hneg.2]
  intro x y hxy
  by_cases hy : y ≤ 0
  · exact hsegment hxy (Or.inl hy)
  by_cases hx : 0 ≤ x
  · exact hsegment hxy (Or.inr hx)
  have hx0 : x < 0 := lt_of_not_ge hx
  have h0y : 0 < y := lt_of_not_ge hy
  exact lt_trans
    (hsegment hx0 (Or.inl le_rfl))
    (hsegment h0y (Or.inr le_rfl))

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    StrictMono (powerMean a b) := by
  have hlog := gap9 a b ha hb hab
  intro x y hxy
  have h := hlog hxy
  have hpx : 0 < powerMean a b x := by
    unfold powerMean
    split_ifs with hx
    · exact Real.sqrt_pos.2 (mul_pos ha hb)
    · have hpa : 0 < Real.rpow a x := Real.rpow_pos_of_pos ha x
      have hpb : 0 < Real.rpow b x := Real.rpow_pos_of_pos hb x
      have hbase : 0 < (Real.rpow a x + Real.rpow b x) / 2 := by
        nlinarith
      exact Real.rpow_pos_of_pos hbase (1 / x)
  have hpy : 0 < powerMean a b y := by
    unfold powerMean
    split_ifs with hy
    · exact Real.sqrt_pos.2 (mul_pos ha hb)
    · have hpa : 0 < Real.rpow a y := Real.rpow_pos_of_pos ha y
      have hpb : 0 < Real.rpow b y := Real.rpow_pos_of_pos hb y
      have hbase : 0 < (Real.rpow a y + Real.rpow b y) / 2 := by
        nlinarith
      exact Real.rpow_pos_of_pos hbase (1 / y)
  have hexp :
      Real.exp (Real.log (powerMean a b x)) <
        Real.exp (Real.log (powerMean a b y)) :=
    Real.exp_lt_exp.mpr h
  simpa [Real.exp_log hpx, Real.exp_log hpy] using hexp

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Monotone (powerMean a b) := by
  by_cases hab : a = b
  · subst b
    have hconst : powerMean a a = fun _ => a := by
      funext s
      unfold powerMean
      split_ifs with hs
      · rw [show a * a = a ^ 2 by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
      · have hhalf : (Real.rpow a s + Real.rpow a s) / 2 =
            Real.rpow a s := by ring
        rw [hhalf]
        have hpos : 0 < Real.rpow a s := Real.rpow_pos_of_pos ha s
        have hrpow :
            Real.rpow (Real.rpow a s) (1 / s) =
              Real.exp (Real.log (Real.rpow a s) * (1 / s)) :=
          Real.rpow_def_of_pos hpos (1 / s)
        rw [hrpow]
        have hlog : Real.log (Real.rpow a s) = s * Real.log a :=
          Real.log_rpow ha s
        have hexp : Real.log (Real.rpow a s) * (1 / s) = Real.log a := by
          rw [hlog]
          field_simp [hs]
        rw [hexp, Real.exp_log ha]
    rw [hconst]
    exact monotone_const
  · exact (gap10 a b ha hb hab).monotone

end

end ProofGap.Exercise1296_2
