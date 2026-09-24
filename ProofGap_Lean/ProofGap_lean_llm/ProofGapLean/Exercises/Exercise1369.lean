import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1369

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def IsLittleOAtTop (f g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x in Filter.atTop, |f x| ≤ ε * |g x|

def cubeSmall (x : ℝ) : ℝ := 1 / x + 1 / x ^ 2 + 1 / x ^ 3
def squareSmall (x : ℝ) : ℝ := 1 / x + 1 / x ^ 2
def cubeRoot (x : ℝ) : ℝ :=
  Real.rpow (x ^ 3 + x ^ 2 + x + 1) (1 / 3)
def squareRoot (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + x + 1)
def cubeNormalized (x : ℝ) : ℝ := Real.rpow (1 + cubeSmall x) (1 / 3)
def squareNormalized (x : ℝ) : ℝ := Real.sqrt (1 + squareSmall x)
def cubeTaylorRemainder (x : ℝ) : ℝ :=
  cubeNormalized x - 1 - (1 / 3 : ℝ) * cubeSmall x
def squareTaylorRemainder (x : ℝ) : ℝ :=
  squareNormalized x - 1 - (1 / 2 : ℝ) * squareSmall x
def cubeRemainder (x : ℝ) : ℝ := cubeRoot x - x - 1 / 3
def squareRemainder (x : ℝ) : ℝ := squareRoot x - x - 1 / 2
def logCorrection (x : ℝ) : ℝ := Real.log (1 + x * Real.exp (-x))
def logRatio (x : ℝ) : ℝ := Real.log (Real.exp x + x) / x
def logRemainder (x : ℝ) : ℝ := logRatio x - 1
def finalExpr (x : ℝ) : ℝ := cubeRoot x - squareRoot x * logRatio x
def combinedRemainder (x : ℝ) : ℝ :=
  cubeRemainder x - squareRemainder x -
    (x + 1 / 2 + squareRemainder x) * logRemainder x

theorem gap1 (x : ℝ) (hx : 0 < x) :
    cubeRoot x = x * cubeNormalized x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsmall : 0 < 1 + cubeSmall x := by
    unfold cubeSmall
    positivity
  have hfactor :
      x ^ 3 + x ^ 2 + x + 1 = x ^ 3 * (1 + cubeSmall x) := by
    unfold cubeSmall
    field_simp [hx0]
    ring
  have hp : Real.rpow (x ^ 3) (1 / 3 : ℝ) = x := by
    convert Real.pow_rpow_inv_natCast hx.le (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
      norm_num
  have hmul :
      Real.rpow (x ^ 3 * (1 + cubeSmall x)) (1 / 3 : ℝ) =
        Real.rpow (x ^ 3) (1 / 3 : ℝ) *
          Real.rpow (1 + cubeSmall x) (1 / 3 : ℝ) := by
    change
      (x ^ 3 * (1 + cubeSmall x)) ^ (1 / 3 : ℝ) =
        (x ^ 3) ^ (1 / 3 : ℝ) * (1 + cubeSmall x) ^ (1 / 3 : ℝ)
    exact Real.mul_rpow (by positivity) hsmall.le
  unfold cubeRoot cubeNormalized
  rw [hfactor, hmul, hp]

theorem gap2 :
    IsLittleOAtTop cubeTaylorRemainder cubeSmall := by
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
      (hasDerivAt_id (𝕜 := ℝ) 0) using 1 <;> ring
  have houter :
      HasDerivAt (fun u : ℝ => Real.rpow u (1 / 3 : ℝ)) (1 / 3) 1 := by
    convert Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ))
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0)) using 1 <;> norm_num
  have houter' :
      HasDerivAt (fun u : ℝ => Real.rpow u (1 / 3 : ℝ)) (1 / 3)
        ((fun u : ℝ => 1 + u) 0) := by
    simpa using houter
  have hd :
      HasDerivAt (fun u : ℝ => Real.rpow (1 + u) (1 / 3 : ℝ)) (1 / 3) 0 := by
    simpa [Function.comp_def] using houter'.comp 0 hinner
  have hs : Filter.Tendsto cubeSmall Filter.atTop (nhds 0) := by
    have hi : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
    have hi2 : Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
      simpa [div_pow] using hi.pow 2
    have hi3 : Filter.Tendsto (fun x : ℝ => 1 / x ^ 3) Filter.atTop (nhds 0) := by
      simpa [div_pow] using hi.pow 3
    change Filter.Tendsto
      (fun x : ℝ => 1 / x + 1 / x ^ 2 + 1 / x ^ 3)
      Filter.atTop (nhds 0)
    simpa only [zero_add] using (hi.add hi2).add hi3
  have h := hd.isLittleO.comp_tendsto hs
  intro ε hε
  have hb := h.bound hε
  simpa [cubeTaylorRemainder, cubeNormalized, Real.norm_eq_abs, mul_comm] using hb

theorem gap3 :
    IsLittleOAtTop cubeRemainder (fun _ => 1) := by
  intro ε hε
  have ht := gap2 (ε / 6) (by positivity)
  have hi : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hi2 : Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
    simpa [div_pow] using hi.pow 2
  have hc : Filter.Tendsto (fun _ : ℝ => (1 / 3 : ℝ)) Filter.atTop
      (nhds (1 / 3 : ℝ)) := tendsto_const_nhds
  have htail :
      Filter.Tendsto (fun x : ℝ => (1 / 3 : ℝ) * (1 / x + 1 / x ^ 2))
        Filter.atTop (nhds 0) := by
    simpa using hc.mul (hi.add hi2)
  have htail' := (Metric.tendsto_nhds.1 htail) (ε / 2) (by positivity)
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := by
    exact Filter.eventually_atTop.2 ⟨1, fun _ hx => hx⟩
  filter_upwards [ht, htail', hlarge] with x htx htailx hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs0 : 0 ≤ cubeSmall x := by
    unfold cubeSmall
    positivity
  have hy1 : 1 / x ≤ 1 := by
    apply (div_le_iff₀ hx0).2
    simpa using hx
  have hyprod : 0 ≤ (1 - 1 / x) * (1 + 1 / x) :=
    mul_nonneg (sub_nonneg.mpr hy1) (by positivity)
  have hbound : x * |cubeSmall x| ≤ 3 := by
    rw [abs_of_nonneg hs0]
    have heq : x * cubeSmall x = 1 + 1 / x + (1 / x) ^ 2 := by
      unfold cubeSmall
      field_simp [ne_of_gt hx0]
    rw [heq]
    nlinarith
  have heq :
      cubeRemainder x =
        x * cubeTaylorRemainder x + (1 / 3 : ℝ) * (1 / x + 1 / x ^ 2) := by
    rw [cubeRemainder, gap1 x hx0]
    unfold cubeTaylorRemainder cubeNormalized cubeSmall
    field_simp [ne_of_gt hx0]
    ring
  rw [heq, abs_one, mul_one]
  have hmain : |x * cubeTaylorRemainder x| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hx0]
    calc
      x * |cubeTaylorRemainder x| ≤ x * ((ε / 6) * |cubeSmall x|) :=
        mul_le_mul_of_nonneg_left htx hx0.le
      _ = (ε / 6) * (x * |cubeSmall x|) := by ring
      _ ≤ ε / 2 := by nlinarith
  rw [Real.dist_eq, sub_zero] at htailx
  exact le_trans (abs_add_le _ _) (by nlinarith [le_of_lt htailx])

theorem gap4 : HasLimitAtTop cubeRemainder 0 := by
  unfold HasLimitAtTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := gap3 (ε / 2) (by positivity)
  filter_upwards [h] with x hx
  have hx' : |cubeRemainder x| ≤ ε / 2 := by
    simpa only [abs_one, mul_one] using hx
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hx' (by linarith)

theorem gap5 :
    HasLimitAtTop (fun x => cubeRoot x - (x + 1 / 3)) 0 := by
  apply gap4.congr'
  exact Filter.Eventually.of_forall fun x => by
    unfold cubeRemainder
    ring

theorem gap6 (x : ℝ) (hx : 0 < x) :
    squareRoot x = x * squareNormalized x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfactor : x ^ 2 + x + 1 = x ^ 2 * (1 + squareSmall x) := by
    unfold squareSmall
    field_simp [hx0]
    ring
  unfold squareRoot squareNormalized
  rw [hfactor, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]

theorem gap7 :
    IsLittleOAtTop squareTaylorRemainder squareSmall := by
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
      (hasDerivAt_id (𝕜 := ℝ) 0) using 1 <;> ring
  have houter : HasDerivAt Real.sqrt (1 / 2) 1 := by
    convert Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have houter' :
      HasDerivAt Real.sqrt (1 / 2) ((fun u : ℝ => 1 + u) 0) := by
    simpa using houter
  have hd : HasDerivAt (fun u : ℝ => Real.sqrt (1 + u)) (1 / 2) 0 := by
    simpa [Function.comp_def] using houter'.comp 0 hinner
  have hs : Filter.Tendsto squareSmall Filter.atTop (nhds 0) := by
    have hi : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
    have hi2 : Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
      simpa [div_pow] using hi.pow 2
    change Filter.Tendsto
      (fun x : ℝ => 1 / x + 1 / x ^ 2) Filter.atTop (nhds 0)
    simpa only [zero_add] using hi.add hi2
  have h := hd.isLittleO.comp_tendsto hs
  intro ε hε
  have hb := h.bound hε
  simpa [squareTaylorRemainder, squareNormalized, Real.norm_eq_abs, mul_comm] using hb

theorem gap8 :
    IsLittleOAtTop squareRemainder (fun _ => 1) := by
  intro ε hε
  have ht := gap7 (ε / 4) (by positivity)
  have hi : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hc : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) Filter.atTop
      (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have htail : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (1 / x))
      Filter.atTop (nhds 0) := by
    simpa using hc.mul hi
  have htail' := (Metric.tendsto_nhds.1 htail) (ε / 2) (by positivity)
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := by
    exact Filter.eventually_atTop.2 ⟨1, fun _ hx => hx⟩
  filter_upwards [ht, htail', hlarge] with x htx htailx hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs0 : 0 ≤ squareSmall x := by
    unfold squareSmall
    positivity
  have hy1 : 1 / x ≤ 1 := by
    apply (div_le_iff₀ hx0).2
    simpa using hx
  have hbound : x * |squareSmall x| ≤ 2 := by
    rw [abs_of_nonneg hs0]
    have heq : x * squareSmall x = 1 + 1 / x := by
      unfold squareSmall
      field_simp [ne_of_gt hx0]
    rw [heq]
    nlinarith
  have heq :
      squareRemainder x =
        x * squareTaylorRemainder x + (1 / 2 : ℝ) * (1 / x) := by
    rw [squareRemainder, gap6 x hx0]
    unfold squareTaylorRemainder squareNormalized squareSmall
    field_simp [ne_of_gt hx0]
    ring
  rw [heq, abs_one, mul_one]
  have hmain : |x * squareTaylorRemainder x| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hx0]
    calc
      x * |squareTaylorRemainder x| ≤ x * ((ε / 4) * |squareSmall x|) :=
        mul_le_mul_of_nonneg_left htx hx0.le
      _ = (ε / 4) * (x * |squareSmall x|) := by ring
      _ ≤ ε / 2 := by nlinarith
  rw [Real.dist_eq, sub_zero] at htailx
  exact le_trans (abs_add_le _ _) (by nlinarith [le_of_lt htailx])

theorem gap9 : HasLimitAtTop squareRemainder 0 := by
  unfold HasLimitAtTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := gap8 (ε / 2) (by positivity)
  filter_upwards [h] with x hx
  have hx' : |squareRemainder x| ≤ ε / 2 := by
    simpa only [abs_one, mul_one] using hx
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hx' (by linarith)

theorem gap10 :
    HasLimitAtTop (fun x => squareRoot x - (x + 1 / 2)) 0 := by
  apply gap9.congr'
  exact Filter.Eventually.of_forall fun x => by
    unfold squareRemainder
    ring

theorem gap11 (x : ℝ) (hx : 0 < x) :
    logRatio x =
      (1 / x) * Real.log (Real.exp x * (1 + x * Real.exp (-x))) := by
  have heq :
      Real.exp x + x = Real.exp x * (1 + x * Real.exp (-x)) := by
    calc
      Real.exp x + x = Real.exp x + x * (Real.exp x * Real.exp (-x)) := by
        rw [← Real.exp_add]
        simp
      _ = Real.exp x * (1 + x * Real.exp (-x)) := by ring
  unfold logRatio
  rw [heq]
  ring

theorem gap12 (x : ℝ) (hx : 0 < x) :
    (1 / x) * Real.log (Real.exp x * (1 + x * Real.exp (-x))) =
      1 + (1 / x) * logCorrection x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hpos : 0 < 1 + x * Real.exp (-x) := by positivity
  rw [Real.log_mul (ne_of_gt (Real.exp_pos x)) (ne_of_gt hpos), Real.log_exp]
  unfold logCorrection
  field_simp [hx0]

theorem gap13 :
    IsLittleOAtTop logRemainder (fun x => 1 / x) := by
  have hexp : Filter.Tendsto (fun x : ℝ => x * Real.exp (-x))
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have harg : Filter.Tendsto (fun x : ℝ => 1 + x * Real.exp (-x))
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hexp
  have hcorr : Filter.Tendsto logCorrection Filter.atTop (nhds 0) := by
    unfold logCorrection
    convert (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg using 1 <;>
      norm_num
  intro ε hε
  have hc := (Metric.tendsto_nhds.1 hcorr) ε hε
  have hpositive : ∀ᶠ x : ℝ in Filter.atTop, 0 < x := by
    exact Filter.eventually_atTop.2
      ⟨1, fun _ hx => lt_of_lt_of_le zero_lt_one hx⟩
  filter_upwards [hc, hpositive] with x hcx hx
  have heq : logRemainder x = (1 / x) * logCorrection x := by
    unfold logRemainder
    rw [gap11 x hx, gap12 x hx]
    ring
  rw [heq, abs_mul]
  rw [Real.dist_eq, sub_zero] at hcx
  calc
    |1 / x| * |logCorrection x| ≤ |1 / x| * ε :=
      mul_le_mul_of_nonneg_left (le_of_lt hcx) (abs_nonneg _)
    _ = ε * |1 / x| := by ring

theorem gap14 (x : ℝ) :
    logRatio x = 1 + logRemainder x := by
  unfold logRemainder
  ring

theorem gap15 : HasLimitAtTop logCorrection 0 := by
  have hexp : Filter.Tendsto (fun x : ℝ => x * Real.exp (-x))
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have harg : Filter.Tendsto (fun x : ℝ => 1 + x * Real.exp (-x))
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hexp
  unfold HasLimitAtTop logCorrection
  convert (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg using 1 <;>
    norm_num

theorem gap16 (x : ℝ) :
    finalExpr x =
      (x + 1 / 3 + cubeRemainder x) -
        (x + 1 / 2 + squareRemainder x) * (1 + logRemainder x) := by
  unfold finalExpr cubeRemainder squareRemainder logRemainder
  ring

theorem gap17 (x : ℝ) :
    (x + 1 / 3 + cubeRemainder x) -
        (x + 1 / 2 + squareRemainder x) * (1 + logRemainder x) =
      -1 / 6 + combinedRemainder x := by
  unfold combinedRemainder
  ring

theorem gap18 : HasLimitAtTop combinedRemainder 0 := by
  have hi : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hhalf :
      Filter.Tendsto (fun x : ℝ => (1 / 2 + squareRemainder x) * (1 / x))
        Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.add gap9).mul hi using 1 <;> ring
  have hfactor :
      Filter.Tendsto (fun x : ℝ => 1 + (1 / 2 + squareRemainder x) * (1 / x))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hhalf
  have hbase :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 + (1 / 2 + squareRemainder x) * (1 / x)) * logCorrection x)
        Filter.atTop (nhds 0) := by
    simpa using hfactor.mul gap15
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ => (x + 1 / 2 + squareRemainder x) * logRemainder x)
        Filter.atTop (nhds 0) := by
    apply hbase.congr'
    have hpositive : ∀ᶠ x : ℝ in Filter.atTop, 0 < x := by
      exact Filter.eventually_atTop.2
        ⟨1, fun _ hx => lt_of_lt_of_le zero_lt_one hx⟩
    filter_upwards [hpositive] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hl : logRemainder x = (1 / x) * logCorrection x := by
      unfold logRemainder
      rw [gap11 x hx, gap12 x hx]
      ring
    rw [hl]
    field_simp [hx0] <;> ring
  unfold HasLimitAtTop combinedRemainder at *
  convert (gap4.sub gap9).sub hproduct using 1 <;> ring

theorem gap19 (x : ℝ) :
    finalExpr x = -1 / 6 + combinedRemainder x := by
  rw [gap16, gap17]

theorem gap20 :
    HasLimitAtTop finalExpr (-1 / 6) ↔
      HasLimitAtTop (fun x => -1 / 6 + combinedRemainder x) (-1 / 6) := by
  constructor
  · intro h
    apply h.congr'
    exact Filter.Eventually.of_forall fun x => gap19 x
  · intro h
    apply h.congr'
    exact Filter.Eventually.of_forall fun x => (gap19 x).symm

theorem gap21 :
    HasLimitAtTop (fun x => -1 / 6 + combinedRemainder x) (-1 / 6) := by
  unfold HasLimitAtTop at *
  convert tendsto_const_nhds.add gap18 using 1 <;> ring

theorem gap22 : HasLimitAtTop finalExpr (-1 / 6) := by
  exact gap20.mpr gap21

end

end ProofGap.Exercise1369
