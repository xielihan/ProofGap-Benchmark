import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1622

noncomputable section

def lg (x : ℝ) := Real.log x / Real.log 10
def f (x : ℝ) := x * lg x - 1
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def approximant : ℕ → ℝ
  | 1 => 2.5064
  | 2 => 2.5062
  | _ => 0
def ApproxRoot (sample tolerance : ℝ) : Prop :=
  ∃ r ∈ Set.Ioo (2.506 : ℝ) 2.507,
    f r = 0 ∧ |sample - r| < tolerance

private theorem log_ratio_upper {x : ℝ} {m n : ℕ} (hx : 0 < x) (hn : 0 < n) (hm : 0 < m) (hp : x ^ n < (10 : ℝ) ^ m) : Real.log x / Real.log 10 < (m : ℝ) / n := by
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.strictMonoOn_log (pow_pos hx n)
    (pow_pos (by norm_num : (0 : ℝ) < 10) m) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (div_lt_div_iff₀ h10 hn').2
  nlinarith [hlog]

private theorem log_ratio_lower {x : ℝ} {m n : ℕ} (hx : 0 < x) (hn : 0 < n) (hm : 0 < m) (hp : (10 : ℝ) ^ m < x ^ n) : (m : ℝ) / n < Real.log x / Real.log 10 := by
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.strictMonoOn_log
    (pow_pos (by norm_num : (0 : ℝ) < 10) m) (pow_pos hx n) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (div_lt_div_iff₀ hn' h10).2
  nlinarith [hlog]

private theorem hasDerivAt_f {x : ℝ} (hx : x ≠ 0) : HasDerivAt f ((Real.log x + 1) / Real.log 10) x := by
  have h := (hasDerivAt_id x).mul
    ((Real.hasDerivAt_log hx).div_const (Real.log 10))
  have h' := h.sub (hasDerivAt_const x (1 : ℝ))
  simpa [f, lg, div_eq_mul_inv, add_mul, ← mul_assoc, hx] using h'

private theorem deriv_f_formula {x : ℝ} (hx : x ≠ 0) : deriv f x = (Real.log x + 1) / Real.log 10 := by
  exact (hasDerivAt_f hx).deriv

private theorem strictMonoOn_f : StrictMonoOn f (Set.Icc (2.506 : ℝ) 2.507) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2.506) hx.1
  have hy0 : 0 < y := lt_trans hx0 hxy
  have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx.1)
  have hlog := Real.strictMonoOn_log
    (show x ∈ Set.Ioi 0 from hx0) (show y ∈ Set.Ioi 0 from hy0) hxy
  have hprod : x * Real.log x < y * Real.log y := by
    calc
      x * Real.log x < y * Real.log x := mul_lt_mul_of_pos_right hxy hlogx
      _ < y * Real.log y := mul_lt_mul_of_pos_left hlog hy0
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hdiv := (div_lt_div_iff_of_pos_right h10).2 hprod
  simpa [f, lg, div_eq_mul_inv, mul_assoc] using sub_lt_sub_right hdiv 1

private theorem log_plus_one_ratio_lower {x a : ℝ} {m n : ℕ} (hloga : Real.log a < 1) (ha : 0 < a) (hx : 0 < x) (hn : 0 < n) (hp : (10 : ℝ) ^ m < (x * a) ^ n) : (m : ℝ) / n < (Real.log x + 1) / Real.log 10 := by
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.strictMonoOn_log
    (pow_pos (by norm_num : (0 : ℝ) < 10) m) (pow_pos (mul_pos hx ha) n) hp
  rw [Real.log_pow, Real.log_pow, Real.log_mul (ne_of_gt hx) (ne_of_gt ha)] at hlog
  apply (div_lt_div_iff₀ hn' h10).2
  nlinarith [hlog]

private theorem log_plus_one_ratio_upper {x a : ℝ} {m n : ℕ} (hloga : 1 < Real.log a) (ha : 0 < a) (hx : 0 < x) (hn : 0 < n) (hp : (x * a) ^ n < (10 : ℝ) ^ m) : (Real.log x + 1) / Real.log 10 < (m : ℝ) / n := by
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.strictMonoOn_log (pow_pos (mul_pos hx ha) n)
    (pow_pos (by norm_num : (0 : ℝ) < 10) m) hp
  rw [Real.log_pow, Real.log_pow, Real.log_mul (ne_of_gt hx) (ne_of_gt ha)] at hlog
  apply (div_lt_div_iff₀ h10 hn').2
  nlinarith [hlog]

private theorem log_2718_lt_one : Real.log (2.718 : ℝ) < 1 := by
  let r : ℝ := 5001 / 5000
  have hr : 0 < r := by norm_num [r]
  have hp : (2.718 : ℝ) < r ^ 5000 := by
    dsimp [r]
    rw [div_pow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (5000 : ℝ) ^ 5000)).2
    have hpNat : (1359 : ℕ) * 5000 ^ 5000 < 5001 ^ 5000 * 500 := by
      native_decide
    have hpReal : (1359 : ℝ) * (5000 : ℝ) ^ 5000 < (5001 : ℝ) ^ 5000 * 500 := by
      exact_mod_cast hpNat
    rw [show (2.718 : ℝ) = (1359 : ℝ) / 500 by norm_num]
    calc
      ((1359 : ℝ) / 500) * (5000 : ℝ) ^ 5000 =
          ((1359 : ℝ) * (5000 : ℝ) ^ 5000) / 500 := by ring
      _ < ((5001 : ℝ) ^ 5000 * 500) / 500 :=
        div_lt_div_of_pos_right hpReal (by norm_num)
      _ = (5001 : ℝ) ^ 5000 := by ring
  have hlog := Real.strictMonoOn_log (by norm_num : (0 : ℝ) < 2.718)
    (pow_pos hr 5000) hp
  rw [Real.log_pow] at hlog
  have hb := Real.log_le_sub_one_of_pos hr
  norm_num [r] at hb hlog ⊢
  nlinarith

private theorem one_lt_log_27186 : 1 < Real.log (2.7186 : ℝ) := by
  let r : ℝ := 5001 / 5000
  have hr : 0 < r := by norm_num [r]
  have hp : r ^ 5001 < (2.7186 : ℝ) := by
    dsimp [r]
    rw [div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (5000 : ℝ) ^ 5001)).2
    have hpNat : (5001 : ℕ) ^ 5001 * 5000 < 13593 * 5000 ^ 5001 := by
      native_decide
    have hpReal : (5001 : ℝ) ^ 5001 * 5000 <
        (13593 : ℝ) * (5000 : ℝ) ^ 5001 := by
      exact_mod_cast hpNat
    calc
      (5001 : ℝ) ^ 5001 = ((5001 : ℝ) ^ 5001 * 5000) / 5000 := by ring
      _ < ((13593 : ℝ) * (5000 : ℝ) ^ 5001) / 5000 :=
        div_lt_div_of_pos_right hpReal (by norm_num)
      _ = (2.7186 : ℝ) * (5000 : ℝ) ^ 5001 := by
        rw [show (2.7186 : ℝ) = (13593 : ℝ) / 5000 by norm_num]
        ring
  have hlog := Real.strictMonoOn_log (pow_pos hr 5001)
    (by norm_num : (0 : ℝ) < 2.7186) hp
  rw [Real.log_pow] at hlog
  have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at hb
  norm_num [r] at hb hlog ⊢
  nlinarith

theorem gap1 : Approx (f 2.506) (-0.00015) (1 / 100000) := by
  have hl : (391 : ℝ) / 980 < lg 2.506 := by
    apply log_ratio_lower (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.506 : ℝ) = (1253 : ℝ) / 500 by norm_num, div_pow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (500 : ℝ) ^ 980)).2
    have hpNat : (10 : ℕ) ^ 391 * 500 ^ 980 < 1253 ^ 980 := by
      native_decide
    exact_mod_cast hpNat
  have hu : lg 2.506 < (393 : ℝ) / 985 := by
    apply log_ratio_upper (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.506 : ℝ) = (1253 : ℝ) / 500 by norm_num, div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (500 : ℝ) ^ 985)).2
    have hpNat : (1253 : ℕ) ^ 985 < 10 ^ 393 * 500 ^ 985 := by
      native_decide
    exact_mod_cast hpNat
  unfold Approx f
  rw [abs_lt]
  constructor <;> norm_num at hl hu ⊢ <;> nlinarith
theorem gap2 : Approx (f 2.507) 0.00068 (1 / 100000) := by
  have hl : (283 : ℝ) / 709 < lg 2.507 := by
    apply log_ratio_lower (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.507 : ℝ) = (2507 : ℝ) / 1000 by norm_num, div_pow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (1000 : ℝ) ^ 709)).2
    have hpNat : (10 : ℕ) ^ 283 * 1000 ^ 709 < 2507 ^ 709 := by
      native_decide
    exact_mod_cast hpNat
  have hu : lg 2.507 < (378 : ℝ) / 947 := by
    apply log_ratio_upper (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.507 : ℝ) = (2507 : ℝ) / 1000 by norm_num, div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (1000 : ℝ) ^ 947)).2
    have hpNat : (2507 : ℕ) ^ 947 < 10 ^ 378 * 1000 ^ 947 := by
      native_decide
    exact_mod_cast hpNat
  unfold Approx f
  rw [abs_lt]
  constructor <;> norm_num at hl hu ⊢ <;> nlinarith
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (2.506 : ℝ) 2.507) :
    deriv f x > 0 ∧ deriv (deriv f) x > 0 := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hlog10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · rw [deriv_f_formula (ne_of_gt hx0)]
    have hlogx : 0 < Real.log x := Real.log_pos (lt_trans (by norm_num) hx.1)
    positivity
  · have heq : Filter.EventuallyEq (nhds x) (deriv f)
        (fun y : ℝ => (Real.log y + 1) / Real.log 10) := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      exact deriv_f_formula (ne_of_gt hy)
    have hd : HasDerivAt (fun y : ℝ => (Real.log y + 1) / Real.log 10)
        ((x⁻¹) / Real.log 10) x :=
      ((Real.hasDerivAt_log (ne_of_gt hx0)).add_const 1).div_const (Real.log 10)
    have hd' : HasDerivAt (deriv f) ((x⁻¹) / Real.log 10) x :=
      hd.congr_of_eventuallyEq heq
    rw [hd'.deriv]
    positivity
theorem gap4 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (2.506 : ℝ) 2.507 ∧ f ξ = 0 := by
  have ha : f 2.506 < 0 := by
    have h := gap1
    unfold Approx at h
    rw [abs_lt] at h
    norm_num at h ⊢
    linarith
  have hb : 0 < f 2.507 := by
    have h := gap2
    unfold Approx at h
    rw [abs_lt] at h
    norm_num at h ⊢
    linarith
  have hcont : ContinuousOn f (Set.Icc (2.506 : ℝ) 2.507) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2.506) hx.1
    exact (hasDerivAt_f (ne_of_gt hx0)).continuousAt.continuousWithinAt
  have hz : (0 : ℝ) ∈ Set.Icc (f 2.506) (f 2.507) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨ξ, hξ, hξ0⟩ := (intermediate_value_Icc (by norm_num) hcont) hz
  have hξopen : ξ ∈ Set.Ioo (2.506 : ℝ) 2.507 := by
    constructor
    · exact lt_of_le_of_ne hξ.1 (by intro h; subst ξ; linarith)
    · exact lt_of_le_of_ne hξ.2 (by intro h; subst ξ; linarith)
  refine ⟨ξ, ⟨hξopen, hξ0⟩, ?_⟩
  intro y hy
  have hyI : y ∈ Set.Icc (2.506 : ℝ) 2.507 :=
    ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
  have hξI : ξ ∈ Set.Icc (2.506 : ℝ) 2.507 :=
    ⟨le_of_lt hξopen.1, le_of_lt hξopen.2⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := strictMonoOn_f hyI hξI hlt
    linarith [hy.2, hξ0]
  · have hstrict := strictMonoOn_f hξI hyI hgt
    linarith [hy.2, hξ0]
theorem gap5 : approximant 1 = 2.5064 := by
  rfl
theorem gap6 : approximant 2 = 2.5062 := by
  rfl
theorem gap7 : Approx (f 2.5062) 0.00001 (1 / 100000) := by
  have hl : (81 : ℝ) / 203 < lg 2.5062 := by
    apply log_ratio_lower (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.5062 : ℝ) = (12531 : ℝ) / 5000 by norm_num, div_pow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (5000 : ℝ) ^ 203)).2
    have hpNat : (10 : ℕ) ^ 81 * 5000 ^ 203 < 12531 ^ 203 := by
      native_decide
    exact_mod_cast hpNat
  have hu : lg 2.5062 < (812 : ℝ) / 2035 := by
    apply log_ratio_upper (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.5062 : ℝ) = (12531 : ℝ) / 5000 by norm_num, div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (5000 : ℝ) ^ 2035)).2
    have hpNat : (12531 : ℕ) ^ 2035 < 10 ^ 812 * 5000 ^ 2035 := by
      native_decide
    exact_mod_cast hpNat
  unfold Approx f
  rw [abs_lt]
  constructor <;> norm_num at hl hu ⊢ <;> nlinarith
theorem gap8 : ∃ m : ℝ, m = |deriv f 2.506| := by
  exact ⟨|deriv f 2.506|, rfl⟩
theorem gap9 :
    sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (2.506 : ℝ) 2.507) =
      |deriv f 2.506| := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (2.506 : ℝ) 2.507
  have h10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hpos (x : ℝ) (hx : (2.506 : ℝ) ≤ x) : 0 < deriv f x := by
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
    rw [deriv_f_formula (ne_of_gt hx0)]
    have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
    positivity
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hne : S.Nonempty := by
    refine ⟨|deriv f 2.5065|, ⟨2.5065, ?_, rfl⟩⟩
    norm_num
  apply le_antisymm
  · let u : ℕ → ℝ := fun n => 2.506 + (0.001 : ℝ) / ((n : ℝ) + 2)
    have hu (n : ℕ) : u n ∈ Set.Ioo (2.506 : ℝ) 2.507 := by
      dsimp [u]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by linarith
      have hfracpos : 0 < (0.001 : ℝ) / ((n : ℝ) + 2) := div_pos (by norm_num) hn
      have hfrac : (0.001 : ℝ) / ((n : ℝ) + 2) ≤ 0.0005 := by
        apply (div_le_iff₀ hn).2
        nlinarith
      constructor <;> linarith
    have hs (n : ℕ) : sInf S ≤ |deriv f (u n)| :=
      csInf_le hbelow ⟨u n, hu n, rfl⟩
    have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2)
        Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt b
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hnN
      have hcast : (N : ℝ) ≤ n := by
        exact_mod_cast hnN
      linarith
    have hut : Filter.Tendsto u Filter.atTop (nhds (2.506 : ℝ)) := by
      dsimp [u]
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hn)
    have hdcont : ContinuousAt (fun x : ℝ => (Real.log x + 1) / Real.log 10) 2.506 :=
      ((Real.continuousAt_log (by norm_num)).add continuousAt_const).div_const _
    have heq : (fun n => |deriv f (u n)|) =ᶠ[Filter.atTop]
        (fun n => |(Real.log (u n) + 1) / Real.log 10|) := by
      exact Filter.Eventually.of_forall (fun n => by
        have hup : 0 < u n := lt_trans (by norm_num) (hu n).1
        simpa only using congrArg abs (deriv_f_formula (ne_of_gt hup)))
    have ht : Filter.Tendsto (fun n => |deriv f (u n)|) Filter.atTop
        (nhds |deriv f 2.506|) := by
      have hform := hdcont.abs.tendsto.comp hut
      have hend := deriv_f_formula (x := (2.506 : ℝ)) (by norm_num)
      rw [hend]
      exact hform.congr' heq.symm
    have hev : ∀ᶠ n : ℕ in Filter.atTop, sInf S ≤ |deriv f (u n)| :=
      Filter.Eventually.of_forall hs
    have htneg : Filter.Tendsto (fun n : ℕ => -|deriv f (u n)|) Filter.atTop
        (nhds (-|deriv f 2.506|)) := ht.neg
    have hevneg : ∀ᶠ n : ℕ in Filter.atTop, -|deriv f (u n)| ≤ -sInf S :=
      hev.mono (fun _ h => neg_le_neg h)
    have hneg : -|deriv f 2.506| ≤ -sInf S := le_of_tendsto htneg hevneg
    have hfinal : sInf S ≤ |deriv f 2.506| := neg_le_neg_iff.mp hneg
    simpa [S] using hfinal
  · apply le_csInf hne
    rintro z ⟨x, hx, rfl⟩
    have hx0 : 0 < x := lt_trans (by norm_num) hx.1
    change |deriv f 2.506| ≤ |deriv f x|
    rw [abs_of_pos (hpos 2.506 (le_refl _)), abs_of_pos (hpos x (le_of_lt hx.1))]
    rw [deriv_f_formula (by norm_num), deriv_f_formula (ne_of_gt hx0)]
    have hlog := Real.strictMonoOn_log
      (by norm_num : (2.506 : ℝ) ∈ Set.Ioi 0)
      (show x ∈ Set.Ioi 0 from hx0) hx.1
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h10)
theorem gap10 : Approx |deriv f 2.506| 0.8333 (1 / 10000) := by
  rw [deriv_f_formula (by norm_num)]
  have hl : (2083 : ℝ) / 2500 < (Real.log 2.506 + 1) / Real.log 10 := by
    apply log_plus_one_ratio_lower (a := (2.718 : ℝ)) log_2718_lt_one
      (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.506 * 2.718 : ℝ) = (1702827 : ℝ) / 250000 by norm_num, div_pow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (250000 : ℝ) ^ 2500)).2
    have hpNat : (10 : ℕ) ^ 2083 * 250000 ^ 2500 < 1702827 ^ 2500 := by
      native_decide
    exact_mod_cast hpNat
  have hu : (Real.log 2.506 + 1) / Real.log 10 < (4167 : ℝ) / 5000 := by
    apply log_plus_one_ratio_upper (a := (2.7186 : ℝ)) one_lt_log_27186
      (by norm_num) (by norm_num) (by norm_num)
    rw [show (2.506 * 2.7186 : ℝ) = (17032029 : ℝ) / 2500000 by norm_num, div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (2500000 : ℝ) ^ 5000)).2
    have hpNat : (17032029 : ℕ) ^ 5000 < 10 ^ 4167 * 2500000 ^ 5000 := by
      native_decide
    exact_mod_cast hpNat
  have hp : 0 < (Real.log 2.506 + 1) / Real.log 10 := lt_trans (by norm_num) hl
  rw [abs_of_pos hp]
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num at hl hu ⊢ <;> linarith
theorem gap11 :
    ∃ m : ℝ, m = |deriv f 2.506| ∧ Approx m 0.8333 (1 / 10000) := by
  refine ⟨|deriv f 2.506|, rfl, ?_⟩
  exact gap10
theorem gap12 :
    ∃ ξ : ℝ, ξ ∈ Set.Ioo (2.506 : ℝ) 2.507 ∧ f ξ = 0 ∧
      |2.5062 - ξ| ≤ |f 2.5062| / |deriv f 2.506| := by
  obtain ⟨ξ, hξroot, huniq⟩ := gap4
  have hξ := hξroot.1
  have hξ0 := hξroot.2
  have hfpos : 0 < f 2.5062 := by
    have h := gap7
    unfold Approx at h
    rw [abs_lt] at h
    norm_num at h ⊢
    linarith
  have hξlt : ξ < 2.5062 := by
    by_contra h
    have hsξ : 2.5062 ≤ ξ := le_of_not_gt h
    rcases eq_or_lt_of_le hsξ with heq | hlt
    · subst ξ
      linarith
    · have hstrict := strictMonoOn_f
          (by norm_num : (2.5062 : ℝ) ∈ Set.Icc 2.506 2.507)
          ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩ hlt
      linarith
  have hcont : ContinuousOn f (Set.Icc ξ 2.5062) := by
    intro x hx
    have hx0 : 0 < x := lt_trans (by norm_num) (lt_of_lt_of_le hξ.1 hx.1)
    exact (hasDerivAt_f (ne_of_gt hx0)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo ξ 2.5062) := by
    intro x hx
    have hx0 : 0 < x := lt_trans (by norm_num) (lt_trans hξ.1 hx.1)
    exact (hasDerivAt_f (ne_of_gt hx0)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope f hξlt hcont hdiff
  have hc0 : 0 < c := lt_trans (by norm_num) (lt_trans hξ.1 hc.1)
  have hda : 0 < deriv f 2.506 := by
    rw [deriv_f_formula (by norm_num)]
    have hlog : 0 < Real.log (2.506 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hdcmp : deriv f 2.506 ≤ deriv f c := by
    rw [deriv_f_formula (by norm_num), deriv_f_formula (ne_of_gt hc0)]
    have hlog := Real.strictMonoOn_log
      (by norm_num : (2.506 : ℝ) ∈ Set.Ioi 0)
      (show c ∈ Set.Ioi 0 from hc0) (lt_trans hξ.1 hc.1)
    exact div_le_div_of_nonneg_right (by linarith)
      (le_of_lt (Real.log_pos (by norm_num)))
  refine ⟨ξ, hξ, hξ0, ?_⟩
  rw [abs_of_pos (sub_pos.mpr hξlt), abs_of_pos hfpos, abs_of_pos hda]
  rw [hξ0] at hcder
  have hden : 0 < (2.5062 : ℝ) - ξ := sub_pos.mpr hξlt
  have hslope : f 2.5062 / (2.5062 - ξ) = deriv f c := by
    simpa using hcder.symm
  rw [← hslope] at hdcmp
  have hmul : deriv f 2.506 * (2.5062 - ξ) ≤ f 2.5062 :=
    (le_div_iff₀ hden).1 hdcmp
  apply (le_div_iff₀ hda).2
  simpa [mul_comm] using hmul
theorem gap13 :
    |f 2.5062| / |deriv f 2.506| < 0.0001 := by
  have h := gap7
  unfold Approx at h
  rw [abs_lt] at h
  norm_num at h
  have hfpos : 0 < f 2.5062 := by linarith [h.1]
  have hf : |f 2.5062| < (1 : ℝ) / 50000 := by
    rw [abs_of_pos hfpos]
    linarith [h.2]
  have hd : (4 : ℝ) / 5 < |deriv f 2.506| := by
    have hdapp := gap10
    unfold Approx at hdapp
    rw [abs_lt] at hdapp
    norm_num at hdapp ⊢
    linarith
  have hd0 : 0 < |deriv f 2.506| := lt_trans (by norm_num) hd
  apply (div_lt_iff₀ hd0).2
  nlinarith
theorem gap14 : ApproxRoot 2.5062 0.0001 := by
  obtain ⟨ξ, hξ, hξ0, herr⟩ := gap12
  refine ⟨ξ, hξ, hξ0, ?_⟩
  exact lt_of_le_of_lt herr gap13
theorem gap15 : ApproxRoot 2.5062 0.0001 := by
  exact gap14

end
end ProofGap.Exercise1622
