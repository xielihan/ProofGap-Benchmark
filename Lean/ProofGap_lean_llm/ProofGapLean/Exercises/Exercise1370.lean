import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1370

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def IsLittleOAtTop (f g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x in Filter.atTop, |f x| ≤ ε * |g x|

def firstPower (a x : ℝ) : ℝ :=
  Real.rpow (1 + a / x) (1 / x)
def firstRemainder (a x : ℝ) : ℝ := firstPower a x - 1
def secondPower (a x : ℝ) : ℝ :=
  Real.rpow x (1 / (x + a) - 1 / x)
def secondRemainder (a x : ℝ) : ℝ := secondPower a x - 1
def basePower (x : ℝ) : ℝ := Real.rpow x (1 / x)
def finalExpr (a x : ℝ) : ℝ :=
  Real.rpow (x + a) (1 + 1 / x) -
    Real.rpow x (1 + 1 / (x + a))
def combinedRemainder (a x : ℝ) : ℝ :=
  (x + a) * firstRemainder a x - x * secondRemainder a x
def proxy (a x : ℝ) : ℝ :=
  basePower x * (a + combinedRemainder a x)

private theorem rpow_eq_exp_log_mul (b t : ℝ) (hb : 0 < b) :
    Real.rpow b t = Real.exp (Real.log b * t) := by
  simpa only using (Real.rpow_def_of_pos hb t)

private theorem eventually_gt_atTop_real (c : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, c < x := by
  refine Filter.eventually_atTop.2 ?_
  exact ⟨c + 1, fun b hb => by linarith⟩

private theorem tendsto_of_eventuallyEq_right
    {α β : Type*} {l : Filter α} {l' : Filter β} {f g : α → β}
    (hfg : f =ᶠ[l] g) (hf : Filter.Tendsto f l l') :
    Filter.Tendsto g l l' := by
  intro s hs
  change {x | g x ∈ s} ∈ l
  have hfs : {x | f x ∈ s} ∈ l := hf hs
  filter_upwards [hfs, hfg] with x hxs hxeq
  rwa [← hxeq]

private theorem tendsto_inv_atTop_zero_real :
    Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))

private theorem tendsto_one_add_div (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => 1 + a / x) Filter.atTop (nhds 1) := by
  have hc : Filter.Tendsto (fun _ : ℝ => a) Filter.atTop (nhds a) :=
    tendsto_const_nhds
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  simpa [div_eq_mul_inv] using hone.add (hc.mul tendsto_inv_atTop_zero_real)

private theorem tendsto_log_one_add_div (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + a / x)) Filter.atTop (nhds 0) := by
  have hc : ContinuousAt Real.log (1 : ℝ) :=
    Real.continuousAt_log (by norm_num)
  simpa using hc.tendsto.comp (tendsto_one_add_div a)

private theorem littleOAtTop_mul_right (u g : ℝ → ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsLittleOAtTop (fun x => g x * u x) g := by
  intro ε hε
  have he := (Metric.tendsto_nhds.1 hu) ε hε
  filter_upwards [he] with x hx
  have hu_le : |u x| ≤ ε := by
    simpa [Real.dist_eq] using le_of_lt hx
  rw [abs_mul]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hu_le (abs_nonneg (g x))

private theorem exp_sub_one_littleOAtTop (u : ℝ → ℝ)
    (huo : IsLittleOAtTop u (fun x : ℝ => 1 / x)) :
    IsLittleOAtTop (fun x => Real.exp (u x) - 1) (fun x : ℝ => 1 / x) := by
  intro ε hε
  have hb := huo (ε / 2) (by linarith)
  have hsmall := huo 1 zero_lt_one
  filter_upwards [hb, hsmall, eventually_gt_atTop_real 1] with x hx hux hxone
  have hxpos : 0 < x := lt_trans zero_lt_one hxone
  have hinv : |1 / x| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hxpos)]
    exact (div_le_one hxpos).2 (le_of_lt hxone)
  have huone : |u x| ≤ 1 := by
    calc
      |u x| ≤ 1 * |1 / x| := hux
      _ = |1 / x| := one_mul _
      _ ≤ 1 := hinv
  have hbound : |Real.exp (u x) - 1| ≤ 2 * |u x| :=
    Real.abs_exp_sub_one_le huone
  calc
    |Real.exp (u x) - 1| ≤ 2 * |u x| := hbound
    _ ≤ 2 * ((ε / 2) * |1 / x|) :=
      mul_le_mul_of_nonneg_left hx (by norm_num)
    _ = ε * |1 / x| := by ring

private theorem littleOAtTop_scaled_limits (f : ℝ → ℝ)
    (hf : IsLittleOAtTop f (fun x : ℝ => 1 / x)) :
    Filter.Tendsto f Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun x => x * f x) Filter.atTop (nhds 0) := by
  have hplain : Filter.Tendsto f Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    filter_upwards [hf (ε / 2) (by linarith), eventually_gt_atTop_real 1] with x hbound hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hinv : |1 / x| ≤ 1 := by
      rw [abs_of_pos (one_div_pos.mpr hxpos)]
      exact (div_le_one hxpos).2 (le_of_lt hx)
    rw [Real.dist_eq, sub_zero]
    calc
      |f x| ≤ (ε / 2) * |1 / x| := hbound
      _ ≤ (ε / 2) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by linarith)
      _ < ε := by linarith
  have hscaled : Filter.Tendsto (fun x => x * f x) Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    filter_upwards [hf (ε / 2) (by linarith), eventually_gt_atTop_real 0] with x hbound hx
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hx]
    calc
      x * |f x| ≤ x * ((ε / 2) * |1 / x|) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hx)
      _ = x * ((ε / 2) * (1 / x)) := by
        rw [abs_of_pos (one_div_pos.mpr hx)]
      _ = ε / 2 := by
        field_simp [ne_of_gt hx]
      _ < ε := by linarith
  exact ⟨hplain, hscaled⟩

private theorem tendsto_log_div_atTop_real :
    Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

private theorem tendsto_log_div_add_atTop (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.log x / (x + a)) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    tendsto_log_div_atTop_real
  have hinv :
      Filter.Tendsto (fun x : ℝ => (1 + a / x)⁻¹) Filter.atTop (nhds 1) := by
    simpa using (tendsto_one_add_div a).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod :
      Filter.Tendsto
        (fun x : ℝ => (Real.log x / x) * (1 + a / x)⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using hbase.mul hinv
  have heq :
      (fun x : ℝ => (Real.log x / x) * (1 + a / x)⁻¹) =ᶠ[Filter.atTop]
        fun x : ℝ => Real.log x / (x + a) := by
    filter_upwards [eventually_gt_atTop_real 0, eventually_gt_atTop_real (-a)] with x hx hxa
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hxa0 : x + a ≠ 0 := ne_of_gt (by linarith : 0 < x + a)
    field_simp [hx0, hxa0]
    <;> ring
  exact tendsto_of_eventuallyEq_right heq hprod

theorem gap1 (a x : ℝ) (hx : 0 < x) (hbase : 0 < 1 + a / x) :
    firstPower a x = Real.exp ((1 / x) * Real.log (1 + a / x)) := by
  unfold firstPower
  rw [rpow_eq_exp_log_mul (1 + a / x) (1 / x) hbase]
  congr 1
  ring

theorem gap2 (a : ℝ) :
    IsLittleOAtTop
      (fun x => (1 / x) * Real.log (1 + a / x))
      (fun x => 1 / x) := by
  simpa using
    littleOAtTop_mul_right
      (fun x : ℝ => Real.log (1 + a / x))
      (fun x : ℝ => 1 / x)
      (tendsto_log_one_add_div a)

theorem gap3 (a : ℝ) :
    IsLittleOAtTop (firstRemainder a) (fun x => 1 / x) := by
  let u : ℝ → ℝ := fun x => (1 / x) * Real.log (1 + a / x)
  have huo : IsLittleOAtTop u (fun x : ℝ => 1 / x) := by
    simpa [u] using gap2 a
  have hexp := exp_sub_one_littleOAtTop u huo
  intro ε hε
  have hb := hexp ε hε
  have hinner : Filter.Tendsto (fun x : ℝ => 1 + a / x) Filter.atTop (nhds 1) :=
    tendsto_one_add_div a
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 + a / x :=
    hinner.eventually (eventually_gt_nhds zero_lt_one)
  filter_upwards [hb, hpos, eventually_gt_atTop_real 0] with x hbound hbase hx
  rw [firstRemainder, gap1 a x hx hbase]
  exact hbound

theorem gap4 (a : ℝ) :
    IsLittleOAtTop (fun x => firstPower a x - 1) (fun x => 1 / x) := by
  simpa [firstRemainder] using gap3 a

theorem gap5 (a x : ℝ) (hx : 0 < x) (hxa : x + a ≠ 0) :
    1 / (x + a) - 1 / x = -a / (x * (x + a)) := by
  field_simp [ne_of_gt hx, hxa]
  <;> ring

theorem gap6 (a x : ℝ) (hx : 0 < x) (hxa : x + a ≠ 0) :
    secondPower a x =
      Real.exp ((-a / (x * (x + a))) * Real.log x) := by
  unfold secondPower
  rw [rpow_eq_exp_log_mul x (1 / (x + a) - 1 / x) hx, gap5 a x hx hxa]
  congr 1
  ring

theorem gap7 (a : ℝ) :
    IsLittleOAtTop
      (fun x => (-a / (x * (x + a))) * Real.log x)
      (fun x => 1 / x) := by
  let v : ℝ → ℝ := fun x => (-a / (x + a)) * Real.log x
  have hv0 : Filter.Tendsto v Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => -a) Filter.atTop (nhds (-a)) :=
      tendsto_const_nhds
    have hs := hc.mul (tendsto_log_div_add_atTop a)
    simpa [v, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
  have ho : IsLittleOAtTop (fun x : ℝ => (1 / x) * v x) (fun x : ℝ => 1 / x) :=
    littleOAtTop_mul_right v (fun x : ℝ => 1 / x) hv0
  intro ε hε
  have hb := ho ε hε
  filter_upwards [hb, eventually_gt_atTop_real 0, eventually_gt_atTop_real (-a)] with x hbound hx hxa
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxa0 : x + a ≠ 0 := ne_of_gt (by linarith : 0 < x + a)
  have heq : (1 / x) * v x = (-a / (x * (x + a))) * Real.log x := by
    dsimp [v]
    field_simp [hx0, hxa0]
    <;> ring
  rw [← heq]
  exact hbound

theorem gap8 (a : ℝ) :
    IsLittleOAtTop (secondRemainder a) (fun x => 1 / x) := by
  let u : ℝ → ℝ := fun x => (-a / (x * (x + a))) * Real.log x
  have huo : IsLittleOAtTop u (fun x : ℝ => 1 / x) := by
    simpa [u] using gap7 a
  have hexp := exp_sub_one_littleOAtTop u huo
  intro ε hε
  have hb := hexp ε hε
  filter_upwards [hb, eventually_gt_atTop_real 0, eventually_gt_atTop_real (-a)] with x hbound hx hxa
  have hxa' : x + a ≠ 0 := ne_of_gt (by linarith : 0 < x + a)
  rw [secondRemainder, gap6 a x hx hxa']
  exact hbound

theorem gap9 (a : ℝ) :
    IsLittleOAtTop (fun x => secondPower a x - 1) (fun x => 1 / x) := by
  simpa [secondRemainder] using gap8 a

theorem gap10 : HasLimitAtTop basePower 1 := by
  unfold HasLimitAtTop
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    tendsto_log_div_atTop_real
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (Real.log x / x)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hlog
  have heq : basePower =ᶠ[Filter.atTop] fun x : ℝ => Real.exp (Real.log x / x) := by
    filter_upwards [eventually_gt_atTop_real 0] with x hx
    unfold basePower
    rw [rpow_eq_exp_log_mul x (1 / x) hx]
    congr 1
    ring
  exact tendsto_of_eventuallyEq_right heq.symm hexp

theorem gap11 (a x : ℝ) (hx : 0 < x) (hxa : 0 < x + a) :
    finalExpr a x =
      (x + a) * Real.rpow (x + a) (1 / x) -
        x * Real.rpow x (1 / (x + a)) := by
  have hpow (b t : ℝ) (hb : 0 < b) :
      Real.rpow b (1 + t) = b * Real.rpow b t := by
    calc
      Real.rpow b (1 + t) = Real.exp (Real.log b * (1 + t)) :=
        rpow_eq_exp_log_mul b (1 + t) hb
      _ = Real.exp (Real.log b) * Real.exp (Real.log b * t) := by
        rw [mul_add, Real.exp_add, mul_one]
      _ = b * Real.exp (Real.log b * t) := by rw [Real.exp_log hb]
      _ = b * Real.rpow b t := by
        rw [rpow_eq_exp_log_mul b t hb]
  unfold finalExpr
  rw [hpow (x + a) (1 / x) hxa, hpow x (1 / (x + a)) hx]

theorem gap12 (a x : ℝ) (hx : 0 < x) (hxa : 0 < x + a) :
    (x + a) * Real.rpow (x + a) (1 / x) -
        x * Real.rpow x (1 / (x + a)) =
      (x + a) * basePower x * firstPower a x -
        x * basePower x * secondPower a x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfactor : 0 < 1 + a / x := by
    have heq : 1 + a / x = (x + a) / x := by
      field_simp [hx0]
      <;> ring
    rw [heq]
    exact div_pos hxa hx
  have hmul : x + a = x * (1 + a / x) := by
    field_simp [hx0]
    <;> ring
  have hlog : Real.log (x + a) = Real.log x + Real.log (1 + a / x) := by
    rw [hmul, Real.log_mul (ne_of_gt hx) (ne_of_gt hfactor)]
  have hfirst :
      Real.rpow (x + a) (1 / x) = basePower x * firstPower a x := by
    unfold basePower firstPower
    rw [rpow_eq_exp_log_mul (x + a) (1 / x) hxa,
      rpow_eq_exp_log_mul x (1 / x) hx,
      rpow_eq_exp_log_mul (1 + a / x) (1 / x) hfactor,
      hlog, add_mul, Real.exp_add]
  have hsecond :
      Real.rpow x (1 / (x + a)) = basePower x * secondPower a x := by
    unfold basePower secondPower
    rw [rpow_eq_exp_log_mul x (1 / (x + a)) hx,
      rpow_eq_exp_log_mul x (1 / x) hx,
      rpow_eq_exp_log_mul x (1 / (x + a) - 1 / x) hx,
      ← Real.exp_add]
    congr 1
    ring
  rw [hfirst, hsecond]
  ring

theorem gap13 (a x : ℝ) (hx : 0 < x) (hxa : 0 < x + a) :
    finalExpr a x =
      (x + a) * basePower x * firstPower a x -
        x * basePower x * secondPower a x := by
  rw [gap11 a x hx hxa, gap12 a x hx hxa]

theorem gap14 (a x : ℝ) :
    (x + a) * basePower x * firstPower a x -
        x * basePower x * secondPower a x =
      basePower x *
        ((x + a) * (1 + firstRemainder a x) -
          x * (1 + secondRemainder a x)) := by
  unfold firstRemainder secondRemainder
  ring

theorem gap15 (a x : ℝ) :
    basePower x *
        ((x + a) * (1 + firstRemainder a x) -
          x * (1 + secondRemainder a x)) =
      basePower x * (a + combinedRemainder a x) := by
  unfold combinedRemainder
  ring

theorem gap16 (a x : ℝ) :
    basePower x * (a + combinedRemainder a x) = proxy a x := by
  rfl

theorem gap17 (a x : ℝ) (hx : 0 < x) (hxa : 0 < x + a) :
    finalExpr a x = proxy a x := by
  calc
    finalExpr a x =
        (x + a) * basePower x * firstPower a x -
          x * basePower x * secondPower a x := gap13 a x hx hxa
    _ = basePower x *
        ((x + a) * (1 + firstRemainder a x) -
          x * (1 + secondRemainder a x)) := gap14 a x
    _ = basePower x * (a + combinedRemainder a x) := gap15 a x
    _ = proxy a x := gap16 a x

theorem gap18 (a : ℝ) :
    HasLimitAtTop (finalExpr a) a ↔ HasLimitAtTop (proxy a) a := by
  unfold HasLimitAtTop
  have heq : finalExpr a =ᶠ[Filter.atTop] proxy a := by
    filter_upwards [eventually_gt_atTop_real 0, eventually_gt_atTop_real (-a)] with x hx hxa
    exact gap17 a x hx (by linarith)
  constructor
  · intro hf
    exact tendsto_of_eventuallyEq_right heq hf
  · intro hp
    exact tendsto_of_eventuallyEq_right heq.symm hp

theorem gap19 (a : ℝ) :
    HasLimitAtTop (proxy a) a := by
  unfold HasLimitAtTop
  have hfirst := littleOAtTop_scaled_limits (firstRemainder a) (gap3 a)
  have hsecond := littleOAtTop_scaled_limits (secondRemainder a) (gap8 a)
  have hafirst :
      Filter.Tendsto (fun x : ℝ => a * firstRemainder a x)
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hfirst.1 :
        Filter.Tendsto (fun x : ℝ => a * firstRemainder a x)
          Filter.atTop (nhds (a * 0)))
  have hleft0 :
      Filter.Tendsto (fun x : ℝ => (x + a) * firstRemainder a x)
        Filter.atTop (nhds 0) := by
    have hs := hfirst.2.add hafirst
    have heq :
        (fun x : ℝ => x * firstRemainder a x + a * firstRemainder a x) =ᶠ[Filter.atTop]
          fun x : ℝ => (x + a) * firstRemainder a x :=
      Filter.Eventually.of_forall (fun x => by ring)
    exact tendsto_of_eventuallyEq_right heq (by simpa using hs)
  have hcombined :
      Filter.Tendsto (combinedRemainder a) Filter.atTop (nhds 0) := by
    simpa [combinedRemainder] using hleft0.sub hsecond.2
  have hsum :
      Filter.Tendsto (fun x : ℝ => a + combinedRemainder a x)
        Filter.atTop (nhds a) := by
    simpa using tendsto_const_nhds.add hcombined
  simpa [proxy] using (gap10.mul hsum)

theorem gap20 (a : ℝ) :
    HasLimitAtTop (finalExpr a) a := by
  exact (gap18 a).mpr (gap19 a)

end

end ProofGap.Exercise1370
