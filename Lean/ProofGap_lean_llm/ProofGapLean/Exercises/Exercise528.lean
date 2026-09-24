import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise528

noncomputable section

def angle (x : ℝ) (n : ℕ) : ℝ := x / Real.sqrt n
def seq (x : ℝ) (n : ℕ) : ℝ := Real.cos (angle x n) ^ n
def rewritten (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + Real.tan (angle x n) ^ 2) (-(n : ℝ) / 2)
def exponentialForm (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + Real.tan (angle x n) ^ 2)
    ((1 / Real.tan (angle x n) ^ 2) *
      (Real.tan (angle x n) / angle x n) ^ 2 * (-x ^ 2 / 2))

/-- Source: `proof_gap/exercise_528/1.txt`. -/
private theorem angle_tendsto_zero (x : ℝ) :
    Filter.Tendsto (angle x) Filter.atTop (nhds 0) := by
  have hsqrt :
      Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa [angle, div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv)

private theorem angle_tendsto_zero_ne (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (angle x) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨angle_tendsto_zero x, ?_⟩
  filter_upwards
    [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : 0 < n :=
    Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have hnreal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hnpos
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnreal)
  have ha : angle x n ≠ 0 := by
    unfold angle
    exact div_ne_zero hx hs
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha

private theorem cos_angle_tendsto_one (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => Real.cos (angle x n))
      Filter.atTop (nhds 1) := by
  have hcosAt :
      Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) :=
    Real.continuous_cos.continuousAt
  have hcos0 : Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    simpa only [Real.cos_zero] using hcosAt
  exact hcos0.comp (angle_tendsto_zero x)

private theorem sin_div_tendsto_one :
    Filter.Tendsto (fun z : ℝ => Real.sin z / z)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hslope := (Real.hasDerivAt_sin 0).tendsto_slope
  have hslope' :
      Filter.Tendsto (slope Real.sin 0)
        (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    simpa only [Real.cos_zero] using hslope
  refine hslope'.congr' ?_
  exact Filter.Eventually.of_forall (fun z => by
    simp [slope, div_eq_mul_inv, mul_comm])

private theorem tan_div_angle_tendsto_one (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => Real.tan (angle x n) / angle x n)
      Filter.atTop (nhds 1) := by
  have hsin :
      Filter.Tendsto
        (fun n : ℕ => Real.sin (angle x n) / angle x n)
        Filter.atTop (nhds 1) :=
    sin_div_tendsto_one.comp (angle_tendsto_zero_ne x hx)
  have hquot := hsin.div (cos_angle_tendsto_one x) one_ne_zero
  have hquot' :
      Filter.Tendsto
        ((fun n : ℕ => Real.sin (angle x n) / angle x n) /
          (fun n : ℕ => Real.cos (angle x n)))
        Filter.atTop (nhds 1) := by
    simpa only [div_one] using hquot
  refine hquot'.congr' (Filter.Eventually.of_forall (fun n => ?_))
  change
    (Real.sin (angle x n) / angle x n) / Real.cos (angle x n) =
      Real.tan (angle x n) / angle x n
  rw [Real.tan_eq_sin_div_cos]
  ring

private theorem eventually_tan_angle_ne_zero (x : ℝ) (hx : x ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.tan (angle x n) ≠ 0 := by
  have hpos :=
    (tan_div_angle_tendsto_one x hx).eventually
      (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hpos] with n hn
  intro ht
  have hfalse : (0 : ℝ) < 0 := by simpa [ht] using hn
  exact (lt_irrefl 0) hfalse

private theorem log_one_plus_div_tendsto_one :
    Filter.Tendsto (fun u : ℝ => Real.log (1 + u) / u)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hadd : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa using
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        (hasDerivAt_id (0 : ℝ)))
  have hlogAt :
      HasDerivAt Real.log 1 ((fun u : ℝ => 1 + u) 0) := by
    simpa using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hderiv :
      HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    simpa only [Function.comp_apply, one_mul] using hlogAt.comp 0 hadd
  have hslope :
      Filter.Tendsto (slope (fun u : ℝ => Real.log (1 + u)) 0)
        (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
    hderiv.tendsto_slope
  refine hslope.congr' ?_
  exact Filter.Eventually.of_forall (fun u => by
    simp [slope, div_eq_mul_inv, mul_comm])

theorem gap1 (x L : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (rewritten x) Filter.atTop (nhds L) := by
  have heq : seq x =ᶠ[Filter.atTop] rewritten x := by
    filter_upwards
      [(cos_angle_tendsto_one x).eventually (Ioi_mem_nhds zero_lt_one)] with n hc
    have hc0 : Real.cos (angle x n) ≠ 0 := ne_of_gt hc
    have htrig :
        1 + Real.tan (angle x n) ^ 2 =
          1 / Real.cos (angle x n) ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hc0]
      nlinarith [Real.sin_sq_add_cos_sq (angle x n)]
    have hbase : 0 < 1 / Real.cos (angle x n) ^ 2 :=
      one_div_pos.mpr (pow_pos hc 2)
    have hlog :
        Real.log (1 / Real.cos (angle x n) ^ 2) =
          -2 * Real.log (Real.cos (angle x n)) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    unfold seq rewritten
    rw [htrig]
    calc
      Real.cos (angle x n) ^ n =
          Real.exp
            ((n : ℝ) * Real.log (Real.cos (angle x n))) := by
        symm
        rw [Real.exp_nat_mul, Real.exp_log hc]
      _ = Real.exp
          (Real.log (1 / Real.cos (angle x n) ^ 2) *
            (-(n : ℝ) / 2)) := by
        rw [hlog]
        congr 1
        ring
      _ = Real.rpow (1 / Real.cos (angle x n) ^ 2)
          (-(n : ℝ) / 2) := by
        symm
        exact Real.rpow_def_of_pos hbase _
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_528/2.txt`. -/
theorem gap2 (x L : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (exponentialForm x) Filter.atTop (nhds L) := by
  rw [gap1 x L]
  by_cases hx : x = 0
  · subst x
    have heq : rewritten 0 =ᶠ[Filter.atTop] exponentialForm 0 := by
      exact Filter.Eventually.of_forall (fun n => by
        simp [rewritten, exponentialForm, angle])
    constructor
    · intro h
      exact h.congr' heq
    · intro h
      exact h.congr' heq.symm
  · have heq : rewritten x =ᶠ[Filter.atTop] exponentialForm x := by
      filter_upwards
        [eventually_tan_angle_ne_zero x hx,
          Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n ht hn
      have hnpos : 0 < n :=
        Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
      have hnreal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hnpos
      have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
      have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hspos
      have ha : angle x n ≠ 0 := by
        unfold angle
        exact div_ne_zero hx hs0
      have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (le_of_lt hnreal)
      have hexponent :
          (1 / Real.tan (angle x n) ^ 2) *
              (Real.tan (angle x n) / angle x n) ^ 2 *
                (-x ^ 2 / 2) =
            -(n : ℝ) / 2 := by
        calc
          (1 / Real.tan (angle x n) ^ 2) *
                (Real.tan (angle x n) / angle x n) ^ 2 *
                  (-x ^ 2 / 2) =
              (1 / angle x n ^ 2) * (-x ^ 2 / 2) := by
                field_simp [ht, ha] <;> ring
          _ = -(n : ℝ) / 2 := by
            unfold angle
            field_simp [hx, hs0] <;> nlinarith [hsquare]
      unfold rewritten exponentialForm
      rw [hexponent]
    constructor
    · intro h
      exact h.congr' heq
    · intro h
      exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_528/3.txt`. -/
theorem gap3 (x : ℝ) :
    Filter.Tendsto (exponentialForm x) Filter.atTop
      (nhds (Real.exp (-x ^ 2 / 2))) := by
  by_cases hx : x = 0
  · subst x
    have heq : exponentialForm 0 =ᶠ[Filter.atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
      exact Filter.Eventually.of_forall (fun n => by
        simp [exponentialForm, angle])
    have hconst :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1) := tendsto_const_nhds
    convert hconst.congr' heq.symm using 1 <;> norm_num
  · have hsinAt :
        Filter.Tendsto Real.sin (nhds 0) (nhds (Real.sin 0)) :=
      Real.continuous_sin.continuousAt
    have hsin0 :
        Filter.Tendsto Real.sin (nhds 0) (nhds 0) := by
      simpa only [Real.sin_zero] using hsinAt
    have hsin := hsin0.comp (angle_tendsto_zero x)
    have hquot := hsin.div (cos_angle_tendsto_one x) one_ne_zero
    have htan :
        Filter.Tendsto (fun n : ℕ => Real.tan (angle x n))
          Filter.atTop (nhds 0) := by
      simpa [Real.tan_eq_sin_div_cos] using hquot
    have hu :
        Filter.Tendsto
          (fun n : ℕ => Real.tan (angle x n) ^ 2)
          Filter.atTop (nhds 0) := by
      simpa using htan.pow 2
    have hu_ne :
        Filter.Tendsto
          (fun n : ℕ => Real.tan (angle x n) ^ 2)
          Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hu, ?_⟩
      filter_upwards [eventually_tan_angle_ne_zero x hx] with n ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (pow_ne_zero 2 ht)
    have hlogratio :
        Filter.Tendsto
          (fun n : ℕ =>
            Real.log (1 + Real.tan (angle x n) ^ 2) /
              Real.tan (angle x n) ^ 2)
          Filter.atTop (nhds 1) :=
      log_one_plus_div_tendsto_one.comp hu_ne
    have hproduct :
        Filter.Tendsto
          (fun n : ℕ =>
            (Real.log (1 + Real.tan (angle x n) ^ 2) /
                Real.tan (angle x n) ^ 2) *
              (Real.tan (angle x n) / angle x n) ^ 2 *
                (-x ^ 2 / 2))
          Filter.atTop (nhds (-x ^ 2 / 2)) := by
      simpa using
        ((hlogratio.mul ((tan_div_angle_tendsto_one x hx).pow 2)).mul
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => -x ^ 2 / 2)
              Filter.atTop (nhds (-x ^ 2 / 2))))
    have hexp0 :
        Filter.Tendsto Real.exp (nhds (-x ^ 2 / 2))
          (nhds (Real.exp (-x ^ 2 / 2))) :=
      Real.continuous_exp.continuousAt
    have hexp :
        Filter.Tendsto
          (fun n : ℕ =>
            Real.exp
              ((Real.log (1 + Real.tan (angle x n) ^ 2) /
                  Real.tan (angle x n) ^ 2) *
                (Real.tan (angle x n) / angle x n) ^ 2 *
                  (-x ^ 2 / 2)))
          Filter.atTop (nhds (Real.exp (-x ^ 2 / 2))) := by
      simpa only [Function.comp_apply] using hexp0.comp hproduct
    have heq :
        exponentialForm x =ᶠ[Filter.atTop]
          (fun n : ℕ =>
            Real.exp
              ((Real.log (1 + Real.tan (angle x n) ^ 2) /
                  Real.tan (angle x n) ^ 2) *
                (Real.tan (angle x n) / angle x n) ^ 2 *
                  (-x ^ 2 / 2))) := by
      refine Filter.Eventually.of_forall (fun n => ?_)
      have hbase :
          0 < 1 + Real.tan (angle x n) ^ 2 :=
        add_pos_of_pos_of_nonneg zero_lt_one
          (sq_nonneg (Real.tan (angle x n)))
      unfold exponentialForm
      calc
        Real.rpow (1 + Real.tan (angle x n) ^ 2)
            ((1 / Real.tan (angle x n) ^ 2) *
              (Real.tan (angle x n) / angle x n) ^ 2 *
                (-x ^ 2 / 2)) =
            Real.exp
              (Real.log (1 + Real.tan (angle x n) ^ 2) *
                ((1 / Real.tan (angle x n) ^ 2) *
                  (Real.tan (angle x n) / angle x n) ^ 2 *
                    (-x ^ 2 / 2))) :=
          Real.rpow_def_of_pos hbase _
        _ = Real.exp
              ((Real.log (1 + Real.tan (angle x n) ^ 2) /
                  Real.tan (angle x n) ^ 2) *
                (Real.tan (angle x n) / angle x n) ^ 2 *
                  (-x ^ 2 / 2)) := by
          congr 1
          ring
    exact hexp.congr' heq.symm

/-- Source: `proof_gap/exercise_528/4.txt`. -/
theorem gap4 (x : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds (Real.exp (-x ^ 2 / 2))) := by
  exact (gap2 x (Real.exp (-x ^ 2 / 2))).mpr (gap3 x)

end

end ProofGap.Exercise528
