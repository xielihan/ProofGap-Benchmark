import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1353

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def pow (a x : ℝ) : ℝ := Real.rpow a x
def core (a x : ℝ) : ℝ := pow a x - x * Real.log a
def f₀ (a b x : ℝ) : ℝ :=
  (Real.log (core a x) - Real.log (core b x)) / x ^ 2
def f₁ (a b x : ℝ) : ℝ :=
  (((pow a x - 1) * Real.log a) / core a x -
    ((pow b x - 1) * Real.log b) / core b x) / (2 * x)
def secondTerm (a x : ℝ) : ℝ :=
  (pow a x * Real.log a ^ 2 * core a x -
    (pow a x - 1) ^ 2 * Real.log a ^ 2) / core a x ^ 2
def f₂ (a b x : ℝ) : ℝ := (1 / 2 : ℝ) * (secondTerm a x - secondTerm b x)
def powerForm (a b x : ℝ) : ℝ := Real.rpow (core a x / core b x) (1 / x ^ 2)
def target (a b : ℝ) : ℝ := (Real.log a ^ 2 - Real.log b ^ 2) / 2

private def firstTerm (a x : ℝ) : ℝ :=
  ((pow a x - 1) * Real.log a) / core a x

private lemma pow_eq_exp (a : ℝ) (ha : 0 < a) (x : ℝ) :
    pow a x = Real.exp (Real.log a * x) := by
  change a ^ x = Real.exp (Real.log a * x)
  rw [Real.rpow_def_of_pos ha]

private lemma pow_eq_exp_fun (a : ℝ) (ha : 0 < a) :
    pow a = fun x : ℝ => Real.exp (Real.log a * x) := by
  funext x
  exact pow_eq_exp a ha x

private lemma core_positive (a : ℝ) (ha : 0 < a) (x : ℝ) : 0 < core a x := by
  unfold core
  rw [pow_eq_exp a ha x]
  have h := Real.add_one_le_exp (Real.log a * x)
  nlinarith

private lemma hasDerivAt_pow (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (pow a) (pow a x * Real.log a) x := by
  have hinner : HasDerivAt (fun y : ℝ => Real.log a * y) (Real.log a) x := by
    simpa using (hasDerivAt_const x (Real.log a)).mul (hasDerivAt_id x)
  have h := (Real.hasDerivAt_exp (Real.log a * x)).comp x hinner
  rw [pow_eq_exp_fun a ha]
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h

private lemma hasDerivAt_core (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (core a) ((pow a x - 1) * Real.log a) x := by
  have h := (hasDerivAt_pow a ha x).sub ((hasDerivAt_id x).mul_const (Real.log a))
  convert h using 1 <;> simp [core]
  ring

private lemma hasDerivAt_log_core (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (core a y)) (firstTerm a x) x := by
  have h := (Real.hasDerivAt_log (core_positive a ha x).ne').comp x
    (hasDerivAt_core a ha x)
  simpa [firstTerm, div_eq_mul_inv, mul_comm] using h

private lemma hasDerivAt_firstTerm (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (firstTerm a) (secondTerm a x) x := by
  have hn : HasDerivAt
      (fun y : ℝ => (pow a y - 1) * Real.log a)
      (pow a x * Real.log a ^ 2) x := by
    have h := ((hasDerivAt_pow a ha x).sub_const 1).mul_const (Real.log a)
    convert h using 1 <;> ring
  have h := hn.div (hasDerivAt_core a ha x) (core_positive a ha x).ne'
  convert h using 1 <;> simp [firstTerm, secondTerm]
  field_simp [(core_positive a ha x).ne']

private lemma continuous_pow (a : ℝ) (ha : 0 < a) : Continuous (pow a) := by
  rw [pow_eq_exp_fun a ha]
  fun_prop

private lemma continuousAt_core (a : ℝ) (ha : 0 < a) (x : ℝ) :
    ContinuousAt (core a) x := by
  have hp : ContinuousAt (pow a) x := (continuous_pow a ha).continuousAt
  have hm : ContinuousAt (fun y : ℝ => y * Real.log a) x :=
    continuousAt_id.mul continuousAt_const
  simpa [core] using hp.sub hm

private lemma continuousAt_secondTerm (a : ℝ) (ha : 0 < a) :
    ContinuousAt (secondTerm a) 0 := by
  have hp : ContinuousAt (pow a) 0 := (continuous_pow a ha).continuousAt
  have hc : ContinuousAt (core a) 0 := continuousAt_core a ha 0
  have hc0 : core a 0 ≠ 0 := by
    simp [core, pow]
  have hlog : ContinuousAt (fun _ : ℝ => Real.log a ^ 2) 0 := continuousAt_const
  have hA : ContinuousAt
      (fun x : ℝ => pow a x * Real.log a ^ 2 * core a x) 0 :=
    (hp.mul hlog).mul hc
  have hB : ContinuousAt
      (fun x : ℝ => (pow a x - 1) ^ 2 * Real.log a ^ 2) 0 :=
    ((hp.sub continuousAt_const).pow 2).mul hlog
  have hD : ContinuousAt (fun x : ℝ => core a x ^ 2) 0 := hc.pow 2
  simpa only [secondTerm] using
    (hA.sub hB).div hD (pow_ne_zero 2 hc0)

private theorem limit_second (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₂ a b) (target a b) := by
  unfold HasLimitAtZero
  have hca := continuousAt_secondTerm a ha
  have hcb := continuousAt_secondTerm b hb
  have h := (hca.sub hcb).const_mul (1 / 2 : ℝ)
  have ht : Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) * (secondTerm a x - secondTerm b x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((1 / 2 : ℝ) * (secondTerm a 0 - secondTerm b 0))) :=
    h.tendsto.mono_left inf_le_left
  have hsa : secondTerm a 0 = Real.log a ^ 2 := by
    simp [secondTerm, core, pow]
  have hsb : secondTerm b 0 = Real.log b ^ 2 := by
    simp [secondTerm, core, pow]
  change Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) * (secondTerm a x - secondTerm b x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (target a b))
  convert ht using 1
  simp [target, hsa, hsb, div_eq_mul_inv, mul_comm]

private theorem limit_first (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₁ a b) (target a b) := by
  unfold HasLimitAtZero
  let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have haSlope := (hasDerivAt_firstTerm a ha 0).tendsto_slope
  have hbSlope := (hasDerivAt_firstTerm b hb 0).tendsto_slope
  have hfa0 : firstTerm a 0 = 0 := by
    simp [firstTerm, core, pow]
  have hfb0 : firstTerm b 0 = 0 := by
    simp [firstTerm, core, pow]
  have hsa0 : secondTerm a 0 = Real.log a ^ 2 := by
    simp [secondTerm, core, pow]
  have hsb0 : secondTerm b 0 = Real.log b ^ 2 := by
    simp [secondTerm, core, pow]
  have heqa : slope (firstTerm a) 0 = fun x : ℝ => firstTerm a x / x := by
    funext x
    simp [slope, hfa0, div_eq_mul_inv, mul_comm]
  have heqb : slope (firstTerm b) 0 = fun x : ℝ => firstTerm b x / x := by
    funext x
    simp [slope, hfb0, div_eq_mul_inv, mul_comm]
  have haLim : Filter.Tendsto (fun x : ℝ => firstTerm a x / x) l
      (nhds (Real.log a ^ 2)) := by
    rw [← heqa]
    simpa [l, hsa0] using haSlope
  have hbLim : Filter.Tendsto (fun x : ℝ => firstTerm b x / x) l
      (nhds (Real.log b ^ 2)) := by
    rw [← heqb]
    simpa [l, hsb0] using hbSlope
  have h := (haLim.sub hbLim).const_mul (1 / 2 : ℝ)
  have h' : Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) *
        (firstTerm a x / x - firstTerm b x / x)) l
      (nhds (target a b)) := by
    simpa [target, div_eq_mul_inv, mul_comm] using h
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [f₁, firstTerm]
  field_simp [hx0]

private theorem limit_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₀ a b) (target a b) := by
  unfold HasLimitAtZero
  let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hder : Filter.Tendsto
      (fun x : ℝ =>
        (firstTerm a x - firstTerm b x) / (2 * x)) l
      (nhds (target a b)) := by
    simpa [HasLimitAtZero, f₁, l] using limit_first a b ha hb
  have hnum : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.log (core a y) - Real.log (core b y))
      (firstTerm a x - firstTerm b x) x := by
    intro x
    exact (hasDerivAt_log_core a ha x).sub (hasDerivAt_log_core b hb x)
  have hden : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x
    simpa [mul_comm] using (hasDerivAt_id x).pow 2
  have hnumFull : Filter.Tendsto
      (fun y : ℝ => Real.log (core a y) - Real.log (core b y))
      (nhds 0) (nhds 0) := by
    have hca : ContinuousAt (fun y : ℝ => Real.log (core a y)) 0 :=
      (hasDerivAt_log_core a ha 0).continuousAt
    have hcb : ContinuousAt (fun y : ℝ => Real.log (core b y)) 0 :=
      (hasDerivAt_log_core b hb 0).continuousAt
    simpa [core, pow] using (hca.sub hcb).tendsto
  have hdenCont : ContinuousAt (fun y : ℝ => y ^ 2) 0 :=
    (continuousAt_id : ContinuousAt (fun y : ℝ => y) 0).pow 2
  have hdenFull : Filter.Tendsto (fun y : ℝ => y ^ 2) (nhds 0) (nhds 0) := by
    simpa using hdenCont.tendsto
  have hGTle : nhdsWithin 0 (Set.Ioi 0) ≤ l := by
    dsimp [l]
    exact nhdsWithin_mono 0 (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)
  have hLTle : nhdsWithin 0 (Set.Iio 0) ≤ l := by
    dsimp [l]
    exact nhdsWithin_mono 0 (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_lt hx)
  have hderGT : Filter.Tendsto
      (fun x : ℝ => (firstTerm a x - firstTerm b x) / (2 * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (target a b)) :=
    hder.mono_left hGTle
  have hderLT : Filter.Tendsto
      (fun x : ℝ => (firstTerm a x - firstTerm b x) / (2 * x))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (target a b)) :=
    hder.mono_left hLTle
  have hnum0GT : Filter.Tendsto
      (fun y : ℝ => Real.log (core a y) - Real.log (core b y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hnumFull.mono_left inf_le_left
  have hnum0LT : Filter.Tendsto
      (fun y : ℝ => Real.log (core a y) - Real.log (core b y))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    hnumFull.mono_left inf_le_left
  have hden0GT : Filter.Tendsto (fun y : ℝ => y ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hdenFull.mono_left inf_le_left
  have hden0LT : Filter.Tendsto (fun y : ℝ => y ^ 2)
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    hdenFull.mono_left inf_le_left
  have hdenNeGT :
      ∀ᶠ x in (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))), (2 : ℝ) * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  have hdenNeLT :
      ∀ᶠ x in (nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))), (2 : ℝ) * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_lt hx)
  have hquotGT : Filter.Tendsto
      (fun y : ℝ =>
        (Real.log (core a y) - Real.log (core b y)) / y ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (target a b)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun x : ℝ => firstTerm a x - firstTerm b x)
      (g' := fun x : ℝ => 2 * x)
    all_goals first
      | exact Filter.Eventually.of_forall hnum
      | exact Filter.Eventually.of_forall hden
      | exact hnum0GT
      | exact hden0GT
      | exact hdenNeGT
      | exact hderGT
  have hquotLT : Filter.Tendsto
      (fun y : ℝ =>
        (Real.log (core a y) - Real.log (core b y)) / y ^ 2)
      (nhdsWithin 0 (Set.Iio 0)) (nhds (target a b)) := by
    apply HasDerivAt.lhopital_zero_nhdsLT
      (f' := fun x : ℝ => firstTerm a x - firstTerm b x)
      (g' := fun x : ℝ => 2 * x)
    all_goals first
      | exact Filter.Eventually.of_forall hnum
      | exact Filter.Eventually.of_forall hden
      | exact hnum0LT
      | exact hden0LT
      | exact hdenNeLT
      | exact hderLT
  have hset : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with hxlt | hxeq | hxgt
      · exact Or.inl hxlt
      · exact False.elim (hx hxeq)
      · exact Or.inr hxgt
    · intro hx hxeq
      subst x
      rcases hx with hx | hx
      · exact (lt_irrefl 0 hx)
      · exact (lt_irrefl 0 hx)
  rw [hset, nhdsWithin_union]
  exact hquotLT.sup hquotGT

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₀ a b) (target a b) ↔
      HasLimitAtZero (f₁ a b) (target a b) := by
  constructor
  · intro _
    exact limit_first a b ha hb
  · intro _
    exact limit_zero a b ha hb

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₀ a b) (target a b) ↔
      HasLimitAtZero (f₂ a b) (target a b) := by
  constructor
  · intro _
    exact limit_second a b ha hb
  · intro _
    exact limit_zero a b ha hb

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₂ a b) (target a b) := by
  exact limit_second a b ha hb

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (f₀ a b) (target a b) := by
  exact limit_zero a b ha hb

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (powerForm a b) (Real.exp (target a b)) := by
  unfold HasLimitAtZero
  have hzero := limit_zero a b ha hb
  unfold HasLimitAtZero at hzero
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hzero
  apply hexp.congr'
  filter_upwards with x
  have hca : 0 < core a x := core_positive a ha x
  have hcb : 0 < core b x := core_positive b hb x
  have hdiv : 0 < core a x / core b x := div_pos hca hcb
  have hrpow :
      Real.rpow (core a x / core b x) (1 / x ^ 2) =
        Real.exp (Real.log (core a x / core b x) * (1 / x ^ 2)) := by
    change (core a x / core b x) ^ (1 / x ^ 2) = _
    rw [Real.rpow_def_of_pos hdiv]
  change Real.exp (f₀ a b x) = Real.rpow (core a x / core b x) (1 / x ^ 2)
  rw [hrpow, Real.log_div hca.ne' hcb.ne']
  unfold f₀
  congr 1
  ring

end

end ProofGap.Exercise1353
