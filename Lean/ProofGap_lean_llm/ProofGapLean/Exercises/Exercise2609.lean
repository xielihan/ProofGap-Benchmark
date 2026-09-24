import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2609

noncomputable section

open Filter

def rootDifference (n : ℕ) : ℝ :=
  Real.sqrt (n + 1) - Real.sqrt n

def term (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (rootDifference n) p * Real.log ((n - 1 : ℝ) / (n + 1))

def rewrittenTerm (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 / (Real.sqrt (n + 1) + Real.sqrt n)) p *
    Real.log (1 - 2 / (n + 1 : ℝ))

def comparison (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (p / 2 + 1)

def converges (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 2))

private theorem rootFactor_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 2) /
      (Real.sqrt ((n : ℝ) + 3) + Real.sqrt ((n : ℝ) + 2)))
      atTop (nhds (1 / 2)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 3) / ((n : ℝ) + 2))
      atTop (nhds 1) := by
    have h : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 2))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    apply h.congr'
    filter_upwards [] with n
    have hm : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hm]
    ring
  have hsqrtComp : Tendsto (fun n : ℕ =>
      Real.sqrt (((n : ℝ) + 3) / ((n : ℝ) + 2))) atTop (nhds 1) := by
    convert (Real.continuous_sqrt.tendsto 1).comp hbase using 1 <;> norm_num
  have hsqrtRatio : Tendsto (fun n : ℕ =>
      Real.sqrt ((n : ℝ) + 3) / Real.sqrt ((n : ℝ) + 2)) atTop (nhds 1) := by
    apply hsqrtComp.congr'
    filter_upwards [] with n
    rw [Real.sqrt_div (by positivity : 0 ≤ (n : ℝ) + 3)]
  have hden : Tendsto (fun n : ℕ =>
      Real.sqrt ((n : ℝ) + 3) / Real.sqrt ((n : ℝ) + 2) + 1)
      atTop (nhds 2) := by
    convert hsqrtRatio.add tendsto_const_nhds using 1 <;> norm_num
  have hinvDen : Tendsto (fun n : ℕ =>
      1 / (Real.sqrt ((n : ℝ) + 3) / Real.sqrt ((n : ℝ) + 2) + 1))
      atTop (nhds (1 / 2)) := by
    convert tendsto_const_nhds.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  apply hinvDen.congr'
  filter_upwards [] with n
  have hs : Real.sqrt ((n : ℝ) + 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp [hs]

private theorem logFactor_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) *
      Real.log (1 - 2 / ((n : ℝ) + 3))) atTop (nhds (-2)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 (Set.compl {0})) (nhds 1) := by
    have hd : HasDerivAt Real.log 1 1 := by
      simpa using Real.hasDerivAt_log one_ne_zero
    have h := hd.tendsto_slope_zero
    convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hxzero : Tendsto (fun n : ℕ => -2 / ((n : ℝ) + 3)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul (-2 : ℝ) hinv
  have hx : Tendsto (fun n : ℕ => -2 / ((n : ℝ) + 3))
      atTop (nhdsWithin 0 (Set.compl {0})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hxzero
    · exact Filter.Eventually.of_forall (fun n =>
        div_ne_zero (by norm_num) (by positivity))
  have hlogComp : Tendsto (fun n : ℕ =>
      Real.log (1 + (-2 / ((n : ℝ) + 3))) / (-2 / ((n : ℝ) + 3)))
      atTop (nhds 1) := hlog.comp hx
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 3))
      atTop (nhds 1) := by
    have h : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 3))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    apply h.congr'
    filter_upwards [] with n
    have hm : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hm]
    ring
  have hmx : Tendsto (fun n : ℕ =>
      ((n : ℝ) + 2) * (-2 / ((n : ℝ) + 3))) atTop (nhds (-2)) := by
    convert Filter.Tendsto.const_mul (-2 : ℝ) hratio using 1 <;> ring
  have hprod : Tendsto (fun n : ℕ =>
      (((n : ℝ) + 2) * (-2 / ((n : ℝ) + 3))) *
        (Real.log (1 + (-2 / ((n : ℝ) + 3))) / (-2 / ((n : ℝ) + 3))))
      atTop (nhds (-2)) := by
    convert hmx.mul hlogComp using 1 <;> ring
  apply hprod.congr'
  filter_upwards [] with n
  have hxne : -2 / ((n : ℝ) + 3) ≠ 0 := by positivity
  field_simp [hxne]
  ring

private theorem rewritten_quotient_eq (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    rewrittenTerm p n / comparison p n =
      Real.rpow (Real.sqrt n / (Real.sqrt (n + 1) + Real.sqrt n)) p *
        ((n : ℝ) * Real.log (1 - 2 / (n + 1 : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hdpos : 0 < Real.sqrt (n + 1) + Real.sqrt n :=
    add_pos (Real.sqrt_pos.2 (by positivity)) hspos
  have hsqrt : Real.sqrt n = Real.rpow n (1 / 2) := Real.sqrt_eq_rpow n
  have hsqrtPow : Real.rpow (Real.sqrt n) p = Real.rpow n (p / 2) := by
    rw [hsqrt]
    calc
      Real.rpow (Real.rpow n (1 / 2)) p = Real.rpow n ((1 / 2) * p) :=
        (Real.rpow_mul hnpos.le (1 / 2) p).symm
      _ = Real.rpow n (p / 2) := by congr 1; ring
  have hroot : Real.rpow (Real.sqrt n / (Real.sqrt (n + 1) + Real.sqrt n)) p =
      Real.rpow n (p / 2) / Real.rpow (Real.sqrt (n + 1) + Real.sqrt n) p := by
    calc
      Real.rpow (Real.sqrt n / (Real.sqrt (n + 1) + Real.sqrt n)) p =
          Real.rpow (Real.sqrt n) p /
            Real.rpow (Real.sqrt (n + 1) + Real.sqrt n) p :=
        Real.div_rpow hspos.le hdpos.le p
      _ = Real.rpow n (p / 2) /
          Real.rpow (Real.sqrt (n + 1) + Real.sqrt n) p := by rw [hsqrtPow]
  have hinv : Real.rpow (1 / (Real.sqrt (n + 1) + Real.sqrt n)) p =
      1 / Real.rpow (Real.sqrt (n + 1) + Real.sqrt n) p := by
    convert Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hdpos.le p using 1 <;>
      norm_num
  have hone : Real.rpow n 1 = (n : ℝ) := by
    simpa using Real.rpow_natCast (n : ℝ) 1
  have hmexp : Real.rpow n (p / 2 + 1) = Real.rpow n (p / 2) * (n : ℝ) := by
    calc
      Real.rpow n (p / 2 + 1) = Real.rpow n (p / 2) * Real.rpow n 1 :=
        Real.rpow_add hnpos (p / 2) 1
      _ = Real.rpow n (p / 2) * (n : ℝ) := by rw [hone]
  have hrden : Real.rpow (Real.sqrt (n + 1) + Real.sqrt n) p ≠ 0 :=
    (Real.rpow_pos_of_pos hdpos p).ne'
  have hrm : Real.rpow n (p / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  unfold rewrittenTerm comparison
  rw [hinv, hmexp, hroot]
  field_simp [hrden, hrm, hnpos.ne']

private theorem rewritten_quotient_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => rewrittenTerm p (n + 2) / comparison p (n + 2))
      atTop (nhds (Real.rpow (1 / 2) p * (-2))) := by
  have hrootPow : Tendsto (fun n : ℕ => Real.rpow
      (Real.sqrt ((n : ℝ) + 2) /
        (Real.sqrt ((n : ℝ) + 3) + Real.sqrt ((n : ℝ) + 2))) p)
      atTop (nhds (Real.rpow (1 / 2) p)) :=
    rootFactor_tendsto.rpow_const (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))
  have hprod := hrootPow.mul logFactor_tendsto
  apply hprod.congr'
  filter_upwards [] with n
  rw [rewritten_quotient_eq p (n + 2) (by omega)]
  push_cast
  ring_nf

private theorem comparison_summable_iff (p : ℝ) :
    Summable (fun n : ℕ => comparison p (n + 2)) ↔ 0 < p := by
  let e : ℝ := -(p / 2 + 1)
  have heq : (fun n : ℕ => comparison p (n + 2)) =
      (fun n : ℕ => Real.rpow (n + 2 : ℕ) e) := by
    funext n
    unfold comparison
    dsimp [e]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ))]
    simp only [one_div]
  rw [heq]
  constructor
  · intro hshift
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      (summable_nat_add_iff 2).mp hshift
    have he := Real.summable_nat_rpow.mp hall
    dsimp [e] at he
    linarith
  · intro hp
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
    exact (summable_nat_add_iff 2).mpr hall

theorem gap1 (p : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    term p n < 0 := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hroot : 0 < rootDifference n := by
    unfold rootDifference
    apply sub_pos.mpr
    apply Real.sqrt_lt_sqrt (by positivity)
    norm_num
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hratio_pos : 0 < (n - 1 : ℝ) / (n + 1) :=
    div_pos (by linarith) hden
  have hratio_lt : (n - 1 : ℝ) / (n + 1) < 1 :=
    (div_lt_one hden).2 (by linarith)
  unfold term
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hroot p)
    (Real.log_neg hratio_pos hratio_lt)

theorem gap2 (p : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    term p n = rewrittenTerm p n := by
  have hsump : 0 < Real.sqrt (n + 1) + Real.sqrt n := by
    exact add_pos (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega)))
  have hroot : rootDifference n =
      1 / (Real.sqrt (n + 1) + Real.sqrt n) := by
    unfold rootDifference
    apply (eq_div_iff hsump.ne').2
    have h1 : Real.sqrt (n + 1) ^ 2 = (n + 1 : ℝ) :=
      Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt n ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hlog : ((n - 1 : ℝ) / (n + 1)) =
      1 - 2 / (n + 1 : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hn1]
    ring
  unfold term rewrittenTerm
  rw [hroot, hlog]

private theorem comparison_isBigO_rewritten (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => comparison p (n + 2))
      (fun n : ℕ => rewrittenTerm p (n + 2)) := by
  let C : ℝ := Real.rpow (1 / 2) p * (-2)
  have hC : C ≠ 0 := mul_ne_zero
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) p).ne' (by norm_num)
  have hinv := (rewritten_quotient_tendsto p).inv₀ hC
  have hrev : Tendsto (fun n : ℕ =>
      comparison p (n + 2) / rewrittenTerm p (n + 2)) atTop (nhds (1 / C)) := by
    have hinv' : Tendsto (fun n : ℕ =>
        (rewrittenTerm p (n + 2) / comparison p (n + 2))⁻¹)
        atTop (nhds (1 / C)) := by
      simpa [C, one_div] using hinv
    apply hinv'.congr'
    filter_upwards [] with n
    have hc : comparison p (n + 2) ≠ 0 := by
      unfold comparison
      exact (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne'
    have ht : rewrittenTerm p (n + 2) ≠ 0 := by
      rw [← gap2 p (n + 2) (by omega)]
      exact (ne_of_lt (gap1 p (n + 2) (by omega)))
    field_simp [hc, ht]
  refine Asymptotics.isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ => comparison p (n + 2))
    (g := fun n : ℕ => rewrittenTerm p (n + 2)) ?_ (1 / C) ?_
  · exact Filter.Eventually.of_forall (fun n hzero =>
      False.elim ((show rewrittenTerm p (n + 2) ≠ 0 by
        rw [← gap2 p (n + 2) (by omega)]
        exact ne_of_lt (gap1 p (n + 2) (by omega))) hzero))
  · simpa only [Pi.div_apply] using hrev

theorem gap3 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => rewrittenTerm p (n + 2))
      (fun n : ℕ => comparison p (n + 2)) := by
  refine Asymptotics.isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ => rewrittenTerm p (n + 2))
    (g := fun n : ℕ => comparison p (n + 2)) ?_
    (Real.rpow (1 / 2) p * (-2)) ?_
  · exact Filter.Eventually.of_forall (fun n hzero =>
      False.elim ((show comparison p (n + 2) ≠ 0 by
        unfold comparison
        exact (one_div_pos.mpr
          (Real.rpow_pos_of_pos (by positivity) _)).ne') hzero))
  · simpa only [Pi.div_apply] using rewritten_quotient_tendsto p

theorem gap4 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => term p (n + 2))
      (fun n : ℕ => comparison p (n + 2)) := by
  apply (gap3 p).congr_left
  exact fun n => (gap2 p (n + 2) (by omega)).symm

theorem gap5 (p : ℝ) (hp : 0 < p) :
    converges p := by
  unfold converges
  exact summable_of_isBigO_nat ((comparison_summable_iff p).2 hp) (gap4 p)

theorem gap6 (p : ℝ) :
    p / 2 + 1 > 1 ↔ p > 0 := by
  constructor <;> intro h <;> linarith

theorem gap7 (p : ℝ) :
    converges p ↔ 0 < p := by
  constructor
  · intro hterm
    have hreverse : Asymptotics.IsBigO atTop
        (fun n : ℕ => comparison p (n + 2))
        (fun n : ℕ => term p (n + 2)) := by
      apply (comparison_isBigO_rewritten p).congr_right
      exact fun n => (gap2 p (n + 2) (by omega)).symm
    exact (comparison_summable_iff p).1
      (summable_of_isBigO_nat hterm hreverse)
  · exact gap5 p

end

end ProofGap.Exercise2609
