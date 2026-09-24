import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3587

noncomputable section

open Asymptotics Filter Topology

def cosineRatio (q : ℝ × ℝ) : ℝ :=
  Real.cos q.1 / Real.cos q.2

def secViaSine (q : ℝ × ℝ) : ℝ :=
  Real.cos q.1 / Real.sqrt (1 - (Real.sin q.2) ^ 2)

def truncatedCosSecProduct (q : ℝ × ℝ) : ℝ :=
  (1 - q.1 ^ 2 / 2) * (1 + q.2 ^ 2 / 2)

def cosineRatioQuadratic (q : ℝ × ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * (q.1 ^ 2 - q.2 ^ 2)

def AgreesToSecondOrder (g p : (ℝ × ℝ) → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 2)

def arctangentExpression (q : ℝ × ℝ) : ℝ :=
  Real.arctan ((1 + q.1 + q.2) / (1 - q.1 + q.2))

def normalizedArctangent (q : ℝ × ℝ) : ℝ :=
  Real.arctan
    ((1 + q.1 / (1 + q.2)) / (1 - q.1 / (1 + q.2)))

def shiftedArctangent (q : ℝ × ℝ) : ℝ :=
  Real.pi / 4 + Real.arctan (q.1 / (1 + q.2))

def arctangentCubic (q : ℝ × ℝ) : ℝ :=
  Real.pi / 4 + q.1 / (1 + q.2) -
    (1 / 3 : ℝ) * (q.1 / (1 + q.2)) ^ 3

def reciprocalStage (q : ℝ × ℝ) : ℝ :=
  Real.pi / 4 + q.1 * (1 - q.2 + q.2 ^ 2)

def arctangentQuadratic (q : ℝ × ℝ) : ℝ :=
  Real.pi / 4 + q.1 - q.1 * q.2

def AgreesToThirdOrder (g p : (ℝ × ℝ) → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 3)

private noncomputable def secant (x : ℝ) : ℝ :=
  (Real.cos x)⁻¹

private theorem cosine_remainder :
    (fun x : ℝ => Real.cos x - (1 - x ^ 2 / 2))
      =o[𝓝 0] (fun x : ℝ => x ^ 2) := by
  have h := taylor_isLittleO_univ (f := Real.cos) (x₀ := (0 : ℝ))
    (n := 2) Real.contDiff_cos
  convert h using 1
  · funext x
    simp [taylor_within_apply, iteratedDerivWithin_univ]
    ring
  · funext x
    ring

private theorem secant_remainder :
    (fun x : ℝ => secant x - (1 + x ^ 2 / 2))
      =o[𝓝 0] (fun x : ℝ => x ^ 2) := by
  let s : Set ℝ := Set.Ioo (-1) 1
  have hcos : ∀ x ∈ s, Real.cos x ≠ 0 := by
    intro x hx
    change (-1 : ℝ) < x ∧ x < 1 at hx
    have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_gt_three]
    exact (Real.cos_pos_of_mem_Ioo hmem).ne'
  have hcd : ContDiffOn ℝ 2 secant s := by
    exact Real.contDiff_cos.contDiffOn.inv hcos
  have ht := taylor_isLittleO (f := secant) (x₀ := (0 : ℝ))
    (n := 2) (s := s) (convex_Ioo (-1) 1) (by norm_num [s]) hcd
  have hnhds : 𝓝[s] (0 : ℝ) = 𝓝 0 := by
    exact nhdsWithin_eq_nhds.mpr
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  rw [hnhds] at ht
  convert ht using 1
  · funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.factorial_zero, Nat.cast_one, inv_one, sub_zero, pow_zero, one_mul,
      one_smul, iteratedDerivWithin_zero, Nat.factorial_one, pow_one,
      iteratedDerivWithin_one]
    have h0 : derivWithin secant s 0 = 0 := by
      rw [derivWithin_of_mem_nhds
        (Ioo_mem_nhds (by norm_num) (by norm_num))]
      unfold secant
      rw [deriv_fun_inv'' Real.differentiableAt_cos]
      · simp
      · simp
    have h2 : iteratedDerivWithin 2 secant s 0 = 1 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo (-1) 1)
        (hcd.contDiffAt (Ioo_mem_nhds (by norm_num) (by norm_num)))
        (by norm_num)]
      rw [show iteratedDeriv 2 secant =
        deriv (iteratedDeriv 1 secant) from iteratedDeriv_succ]
      simp only [iteratedDeriv_one]
      unfold secant
      have hfun :
          deriv (fun x : ℝ => (Real.cos x)⁻¹) =ᶠ[𝓝 (0 : ℝ)]
            fun x => Real.sin x / Real.cos x ^ 2 := by
        filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)] with x hx
        rw [deriv_fun_inv'' Real.differentiableAt_cos (hcos x hx),
          Real.deriv_cos]
        ring
      rw [hfun.deriv_eq]
      convert
        (((Real.hasDerivAt_sin 0).mul
          (((Real.hasDerivAt_cos 0).pow 2).inv (by simp))).deriv) using 1 <;>
        norm_num
    rw [h0, h2]
    norm_num [secant]
    ring
  · funext x
    ring

private theorem cosineRatio_truncated :
    AgreesToSecondOrder cosineRatio truncatedCosSecProduct := by
  have hxO :
      (fun q : ℝ × ℝ => q.1 ^ 2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) := by
    have h :
        (fun q : ℝ × ℝ => q.1)
          =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => q) :=
      isBigO_fst_prod'
    exact h.norm_right.pow 2
  have hyO :
      (fun q : ℝ × ℝ => q.2 ^ 2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) := by
    have h :
        (fun q : ℝ × ℝ => q.2)
          =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => q) :=
      isBigO_snd_prod'
    exact h.norm_right.pow 2
  have hrx :
      (fun q : ℝ × ℝ => Real.cos q.1 - (1 - q.1 ^ 2 / 2))
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    (cosine_remainder.comp_tendsto
      (continuous_fst.tendsto (0, 0))).trans_isBigO hxO
  have hry :
      (fun q : ℝ × ℝ => secant q.2 - (1 + q.2 ^ 2 / 2))
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    (secant_remainder.comp_tendsto
      (continuous_snd.tendsto (0, 0))).trans_isBigO hyO
  have hsecT :
      Tendsto (fun q : ℝ × ℝ => secant q.2)
        (𝓝 (0, 0)) (𝓝 1) := by
    have hc : ContinuousAt secant 0 := by
      unfold secant
      exact Real.continuous_cos.continuousAt.inv₀ (by simp)
    simpa [secant] using hc.tendsto.comp (continuous_snd.tendsto (0, 0))
  have hsecO :
      (fun q : ℝ × ℝ => secant q.2)
        =O[𝓝 (0, 0)] (fun _ : ℝ × ℝ => (1 : ℝ)) :=
    hsecT.isBigO_one ℝ
  have hpolyO :
      (fun q : ℝ × ℝ => 1 - q.1 ^ 2 / 2)
        =O[𝓝 (0, 0)] (fun _ : ℝ × ℝ => (1 : ℝ)) := by
    have hc : Continuous (fun q : ℝ × ℝ => 1 - q.1 ^ 2 / 2) :=
      continuous_const.sub ((continuous_fst.pow 2).div_const 2)
    have ht : Tendsto (fun q : ℝ × ℝ => 1 - q.1 ^ 2 / 2)
        (𝓝 (0, 0)) (𝓝 1) := by
      simpa using hc.tendsto (0, 0)
    exact ht.isBigO_one ℝ
  have h1 :
      (fun q : ℝ × ℝ =>
        (Real.cos q.1 - (1 - q.1 ^ 2 / 2)) * secant q.2)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) := by
    simpa using hrx.mul_isBigO hsecO
  have h2 :
      (fun q : ℝ × ℝ =>
        (1 - q.1 ^ 2 / 2) *
          (secant q.2 - (1 + q.2 ^ 2 / 2)))
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) := by
    simpa using hpolyO.mul_isLittleO hry
  unfold AgreesToSecondOrder cosineRatio truncatedCosSecProduct
  convert h1.add h2 using 1
  · funext q
    simp only [secant, div_eq_mul_inv]
    ring

theorem gap1 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    cosineRatio (x, y) = secViaSine (x, y) := by
  have hmem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_gt_three, (abs_lt.mp hy).1,
      (abs_lt.mp hy).2]
  have hcos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo hmem
  unfold cosineRatio secViaSine
  rw [show 1 - Real.sin y ^ 2 = Real.cos y ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq y]]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hcos]

theorem gap2 :
    AgreesToSecondOrder secViaSine truncatedCosSecProduct := by
  have h := cosineRatio_truncated
  unfold AgreesToSecondOrder at h ⊢
  apply h.congr'
  · filter_upwards [Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ)
      (show 0 < (1 : ℝ) by norm_num)] with q hq
    have hnorm : ‖q‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hq
      change ‖q - (0 : ℝ × ℝ)‖ < 1 at hq
      simpa using hq
    have hx : |q.1| < 1 := by
      rw [Prod.norm_def] at hnorm
      exact lt_of_le_of_lt (le_max_left _ _) hnorm
    have hy : |q.2| < 1 := by
      rw [Prod.norm_def] at hnorm
      exact lt_of_le_of_lt (le_max_right _ _) hnorm
    rw [gap1 q.1 q.2 hx hy]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem gap3 :
    AgreesToSecondOrder cosineRatio truncatedCosSecProduct :=
  cosineRatio_truncated

theorem gap4 :
    AgreesToSecondOrder cosineRatio truncatedCosSecProduct :=
  cosineRatio_truncated

theorem gap5 :
    AgreesToSecondOrder truncatedCosSecProduct cosineRatioQuadratic := by
  have hx :
      (fun q : ℝ × ℝ => q.1)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_fst_prod'.norm_right
  have hy :
      (fun q : ℝ × ℝ => q.2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_snd_prod'.norm_right
  have hxy :
      (fun q : ℝ × ℝ => q.1 ^ 2 * q.2 ^ 2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 4) := by
    convert (hx.pow 2).mul (hy.pow 2) using 1 <;> ring
  have hsmall :
      (fun q : ℝ × ℝ => q.1 ^ 2 * q.2 ^ 2)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    hxy.trans_isLittleO
      (isLittleO_norm_pow_norm_pow (show 2 < 4 by norm_num))
  unfold AgreesToSecondOrder truncatedCosSecProduct cosineRatioQuadratic
  convert hsmall.const_mul_left (-(1 / 4 : ℝ)) using 1
  funext q
  ring

theorem gap6 :
    AgreesToSecondOrder cosineRatio cosineRatioQuadratic := by
  have h3 := gap3
  have h5 := gap5
  unfold AgreesToSecondOrder at h3 h5 ⊢
  convert h3.add h5 using 1
  funext q
  ring

theorem gap7 (x y : ℝ) (hy : |y| < 1) :
    arctangentExpression (x, y) = normalizedArctangent (x, y) := by
  have hne : 1 + y ≠ 0 := by
    nlinarith [(abs_lt.mp hy).1]
  unfold arctangentExpression normalizedArctangent
  congr 1
  field_simp
  ring

theorem gap8 (x y : ℝ) (hy : |y| < 1)
    (hRatio : |x| < 1 + y) :
    normalizedArctangent (x, y) = shiftedArctangent (x, y) := by
  have hpos : 0 < 1 + y := by nlinarith [(abs_lt.mp hy).1]
  let u := x / (1 + y)
  have hu : |u| < 1 := by
    rw [abs_div, abs_of_pos hpos]
    exact (div_lt_one hpos).mpr hRatio
  have hmul : u * 1 < 1 := by
    nlinarith [(abs_lt.mp hu).2]
  have hadd := Real.arctan_add hmul
  unfold normalizedArctangent shiftedArctangent
  change Real.arctan ((1 + u) / (1 - u)) =
    Real.pi / 4 + Real.arctan u
  calc
    Real.arctan ((1 + u) / (1 - u)) =
        Real.arctan ((u + 1) / (1 - u * 1)) := by ring
    _ = Real.arctan u + Real.arctan 1 := hadd.symm
    _ = Real.pi / 4 + Real.arctan u := by
      rw [Real.arctan_one]
      ring

theorem gap9 (x y : ℝ) (hy : |y| < 1)
    (hRatio : |x| < 1 + y) :
    arctangentExpression (x, y) = shiftedArctangent (x, y) := by
  rw [gap7 x y hy, gap8 x y hy hRatio]

private theorem arctangent_remainder :
    (fun x : ℝ => Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3))
      =o[𝓝 0] (fun x : ℝ => x ^ 3) := by
  have h := taylor_isLittleO_univ (f := Real.arctan) (x₀ := (0 : ℝ))
    (n := 3) Real.contDiff_arctan
  convert h using 1
  · funext x
    have htwo :
        iteratedDeriv 2 Real.arctan 0 = 0 := by
      rw [show iteratedDeriv 2 Real.arctan =
        deriv (iteratedDeriv 1 Real.arctan) from iteratedDeriv_succ]
      simp only [iteratedDeriv_one, Real.deriv_arctan]
      have hb : HasDerivAt (fun z : ℝ => 1 + z ^ 2) 0 0 := by
        convert (hasDerivAt_const (0 : ℝ) 1).add
          ((hasDerivAt_id (0 : ℝ)).pow 2) using 1 <;> norm_num
      convert (hb.inv (by norm_num)).deriv using 1 <;> norm_num
    have hfun :
        iteratedDeriv 2 Real.arctan =
          fun z : ℝ => -2 * z / (1 + z ^ 2) ^ 2 := by
      rw [show iteratedDeriv 2 Real.arctan =
        deriv (iteratedDeriv 1 Real.arctan) from iteratedDeriv_succ]
      simp only [iteratedDeriv_one, Real.deriv_arctan]
      funext z
      have hb : HasDerivAt (fun w : ℝ => 1 + w ^ 2) (2 * z) z := by
        convert (hasDerivAt_const z 1).add ((hasDerivAt_id z).pow 2) using 1 <;>
          simp only [id, mul_one] <;> ring
      have hn : 1 + z ^ 2 ≠ 0 := by nlinarith [sq_nonneg z]
      calc
        deriv (fun w : ℝ => 1 / (1 + w ^ 2)) z =
            (0 * (1 + z ^ 2) - 1 * (2 * z)) /
              (1 + z ^ 2) ^ 2 :=
          ((hasDerivAt_const z 1).div hb hn).deriv
        _ = -2 * z / (1 + z ^ 2) ^ 2 := by ring
    have hthree :
        iteratedDeriv 3 Real.arctan 0 = -2 := by
      rw [show iteratedDeriv 3 Real.arctan =
        deriv (iteratedDeriv 2 Real.arctan) from iteratedDeriv_succ,
        hfun]
      have hnum : HasDerivAt (fun z : ℝ => -2 * z) (-2) 0 := by
        convert (hasDerivAt_const (0 : ℝ) (-2)).mul
          (hasDerivAt_id 0) using 1 <;> norm_num
      have hden : HasDerivAt (fun z : ℝ => (1 + z ^ 2) ^ 2) 0 0 := by
        convert
          (((hasDerivAt_const (0 : ℝ) 1).add
            ((hasDerivAt_id (0 : ℝ)).pow 2)).pow 2) using 1 <;>
          norm_num
      convert (hnum.div hden (by norm_num)).deriv using 1 <;> norm_num
    simp [taylor_within_apply, iteratedDerivWithin_univ,
      Real.deriv_arctan, htwo, hthree]
    ring
  · funext x
    ring

private noncomputable def ratioVariable (q : ℝ × ℝ) : ℝ :=
  q.1 / (1 + q.2)

private theorem inverse_one_add_snd_isBigO :
    (fun q : ℝ × ℝ => (1 + q.2)⁻¹)
      =O[𝓝 (0, 0)] (fun _ : ℝ × ℝ => (1 : ℝ)) := by
  have hc : ContinuousAt (fun q : ℝ × ℝ => (1 + q.2)⁻¹) (0, 0) :=
    (continuousAt_const.add continuousAt_snd).inv₀ (by norm_num)
  have ht :
      Tendsto (fun q : ℝ × ℝ => (1 + q.2)⁻¹)
        (𝓝 (0, 0)) (𝓝 1) := by
    simpa using hc.tendsto
  exact ht.isBigO_one ℝ

private theorem ratioVariable_isBigO :
    ratioVariable
      =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) := by
  have hx :
      (fun q : ℝ × ℝ => q.1)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_fst_prod'.norm_right
  unfold ratioVariable
  convert hx.mul inverse_one_add_snd_isBigO using 1 <;>
    simp only [div_eq_mul_inv, mul_one]

private theorem ratioVariable_tendsto :
    Tendsto ratioVariable (𝓝 (0, 0)) (𝓝 0) := by
  have hn : ContinuousAt (fun q : ℝ × ℝ => q.1) (0, 0) :=
    continuousAt_fst
  have hd : ContinuousAt (fun q : ℝ × ℝ => 1 + q.2) (0, 0) :=
    continuousAt_const.add continuousAt_snd
  unfold ratioVariable
  convert (hn.div hd (by norm_num)).tendsto using 1 <;> norm_num

private theorem arctangent_eventually_shifted :
    arctangentExpression =ᶠ[𝓝 (0, 0)] shiftedArctangent := by
  filter_upwards [Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ)
    (show 0 < (1 / 3 : ℝ) by norm_num)] with q hq
  rw [Metric.mem_ball, dist_eq_norm] at hq
  change ‖q - (0 : ℝ × ℝ)‖ < 1 / 3 at hq
  have hnorm : ‖q‖ < 1 / 3 := by simpa using hq
  rw [Prod.norm_def] at hnorm
  have hx : |q.1| < 1 / 3 := by
    exact lt_of_le_of_lt (le_max_left _ _) hnorm
  have hySmall : |q.2| < 1 / 3 := by
    exact lt_of_le_of_lt (le_max_right _ _) hnorm
  have hy : |q.2| < 1 := lt_trans hySmall (by norm_num)
  have hRatio : |q.1| < 1 + q.2 := by
    nlinarith [(abs_lt.mp hySmall).1]
  exact gap9 q.1 q.2 hy hRatio

theorem gap10 :
    AgreesToThirdOrder arctangentExpression arctangentCubic := by
  have ht0 :
      (fun q : ℝ × ℝ =>
        Real.arctan (ratioVariable q) -
          (ratioVariable q - (1 / 3 : ℝ) * ratioVariable q ^ 3))
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 3) :=
    (arctangent_remainder.comp_tendsto ratioVariable_tendsto).trans_isBigO
      (ratioVariable_isBigO.pow 3)
  have hs :
      (fun q : ℝ × ℝ => shiftedArctangent q - arctangentCubic q)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 3) := by
    convert ht0 using 1
    funext q
    simp only [shiftedArctangent, arctangentCubic, ratioVariable]
    ring
  unfold AgreesToThirdOrder
  apply hs.congr'
  · filter_upwards [arctangent_eventually_shifted] with q hq
    rw [hq]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem gap11 :
    AgreesToSecondOrder arctangentCubic reciprocalStage := by
  have hx :
      (fun q : ℝ × ℝ => q.1)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_fst_prod'.norm_right
  have hy :
      (fun q : ℝ × ℝ => q.2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_snd_prod'.norm_right
  have hdegreeFour :
      (fun q : ℝ × ℝ => q.1 * q.2 ^ 3 * (1 + q.2)⁻¹)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 4) := by
    convert (hx.mul (hy.pow 3)).mul inverse_one_add_snd_isBigO using 1 <;>
      ring
  have hfirst :
      (fun q : ℝ × ℝ => -(q.1 * q.2 ^ 3 * (1 + q.2)⁻¹))
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) := by
    convert
      (hdegreeFour.trans_isLittleO
        (isLittleO_norm_pow_norm_pow (show 2 < 4 by norm_num))).const_mul_left
        (-1) using 1
    funext q
    ring
  have hcubic :
      (fun q : ℝ × ℝ => ratioVariable q ^ 3)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    (ratioVariable_isBigO.pow 3).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (show 2 < 3 by norm_num))
  have hsecond :
      (fun q : ℝ × ℝ => -(1 / 3 : ℝ) * ratioVariable q ^ 3)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    hcubic.const_mul_left (-(1 / 3 : ℝ))
  unfold AgreesToSecondOrder
  apply (hfirst.add hsecond).congr'
  · filter_upwards [Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ)
      (show 0 < (1 : ℝ) by norm_num)] with q hq
    rw [Metric.mem_ball, dist_eq_norm] at hq
    change ‖q - (0 : ℝ × ℝ)‖ < 1 at hq
    have hnorm : ‖q‖ < 1 := by simpa using hq
    rw [Prod.norm_def] at hnorm
    have hy : |q.2| < 1 :=
      lt_of_le_of_lt (le_max_right _ _) hnorm
    have hne : 1 + q.2 ≠ 0 := by nlinarith [(abs_lt.mp hy).1]
    unfold arctangentCubic reciprocalStage ratioVariable
    field_simp
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem gap12 :
    AgreesToSecondOrder reciprocalStage arctangentQuadratic := by
  have hx :
      (fun q : ℝ × ℝ => q.1)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_fst_prod'.norm_right
  have hy :
      (fun q : ℝ × ℝ => q.2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖) :=
    isBigO_snd_prod'.norm_right
  have hcubic :
      (fun q : ℝ × ℝ => q.1 * q.2 ^ 2)
        =O[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 3) := by
    convert hx.mul (hy.pow 2) using 1 <;> ring
  have hsmall :
      (fun q : ℝ × ℝ => q.1 * q.2 ^ 2)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    hcubic.trans_isLittleO
      (isLittleO_norm_pow_norm_pow (show 2 < 3 by norm_num))
  unfold AgreesToSecondOrder reciprocalStage arctangentQuadratic
  convert hsmall using 1
  funext q
  ring

theorem gap13 :
    AgreesToSecondOrder arctangentExpression arctangentQuadratic := by
  have h10 := gap10
  have h11 := gap11
  have h12 := gap12
  unfold AgreesToThirdOrder at h10
  unfold AgreesToSecondOrder at h11 h12 ⊢
  have h10' :
      (fun q : ℝ × ℝ =>
        arctangentExpression q - arctangentCubic q)
        =o[𝓝 (0, 0)] (fun q : ℝ × ℝ => ‖q‖ ^ 2) :=
    h10.trans (isLittleO_norm_pow_norm_pow (show 2 < 3 by norm_num))
  convert (h10'.add h11).add h12 using 1
  funext q
  ring

end

end ProofGap.Exercise3587
