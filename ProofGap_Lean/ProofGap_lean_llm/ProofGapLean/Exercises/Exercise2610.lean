import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2610

noncomputable section

open Filter

def sec (x : ℝ) : ℝ := 1 / Real.cos x

def term (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (Real.log (sec (Real.pi / n))) p

def logTanTerm (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (-p) *
    Real.rpow (Real.log (1 + Real.tan (Real.pi / n) ^ 2)) p

def tanModel (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (-p) * Real.rpow (Real.tan (Real.pi / n)) (2 * p)

def powerModel (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (-p) * Real.rpow (Real.pi / n) (2 * p)

def comparison (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (2 * p)

def converges (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 3))

private theorem tendsto_pi_div_nat_add_three :
    Tendsto (fun n : ℕ => Real.pi / ((n + 3 : ℕ) : ℝ)) atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => n + 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hcast : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hshift
  simpa [div_eq_mul_inv] using
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hcast)

private theorem rpow_div_of_pos (a b z : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.rpow (a / b) z = Real.rpow a z / Real.rpow b z := by
  exact Real.div_rpow ha.le hb.le z

private theorem rpow_neg_eq_inv (a : ℝ) (ha : 0 < a) (z : ℝ) :
    Real.rpow a (-z) = 1 / Real.rpow a z := by
  simpa [one_div] using (Real.rpow_neg ha.le z)

private theorem rpow_sq_of_pos (a : ℝ) (ha : 0 < a) (z : ℝ) :
    Real.rpow (a ^ 2) z = Real.rpow a (2 * z) := by
  simpa using (Real.rpow_natCast_mul ha.le 2 z).symm

private theorem isEquivalent_log_one_plus_nhds :
    Asymptotics.IsEquivalent (nhds 0)
      (fun x : ℝ => Real.log (1 + x))
      (fun x : ℝ => x) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0)
  have hout : HasDerivAt Real.log 1 ((fun x : ℝ => 1 + x) 0) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa using hout.comp 0 hinner
  change (fun x : ℝ => Real.log (1 + x) - x) =o[nhds 0]
    (fun x : ℝ => x)
  simpa using hderiv.isLittleO

private theorem isEquivalent_tan_nhds :
    Asymptotics.IsEquivalent (nhds 0) Real.tan (fun x : ℝ => x) := by
  have hderiv : HasDerivAt Real.tan 1 0 := by
    simpa using Real.hasDerivAt_tan (by norm_num : Real.cos 0 ≠ 0)
  change (fun x : ℝ => Real.tan x - x) =o[nhds 0] (fun x : ℝ => x)
  simpa using hderiv.isLittleO

private theorem tan_pi_div_nat_add_three_pos (n : ℕ) :
    0 < Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) := by
  have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 3 by omega)
  have hnthree : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ n + 3 by omega)
  have hx0 : 0 < Real.pi / ((n + 3 : ℕ) : ℝ) := div_pos Real.pi_pos hnpos
  have hxlt : Real.pi / ((n + 3 : ℕ) : ℝ) < Real.pi / 2 := by
    apply (div_lt_iff₀ hnpos).2
    nlinarith [Real.pi_pos]
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos
    (Real.sin_pos_of_pos_of_lt_pi hx0 (by nlinarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo (by constructor <;> nlinarith [Real.pi_pos]))

private theorem isEquivalent_rpow_of_eventually_pos
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) (hg : ∀ᶠ x in l, 0 < g x)
    (hfg : Asymptotics.IsEquivalent l f g) (p : ℝ) :
    Asymptotics.IsEquivalent l
      (fun x => Real.rpow (f x) p)
      (fun x => Real.rpow (g x) p) := by
  have hg_ne : ∀ᶠ x in l, g x ≠ 0 := by
    filter_upwards [hg] with x hx
    exact ne_of_gt hx
  have hratio : Tendsto (fun x => f x / g x) l (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hg_ne).1 hfg
  have hlog : Tendsto (fun x => Real.log (f x / g x)) l (nhds 0) := by
    have hcont : ContinuousAt Real.log (1 : ℝ) :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt
    simpa using hcont.tendsto.comp hratio
  have hpconst : Tendsto (fun _ : α => p) l (nhds p) := tendsto_const_nhds
  have hmul : Tendsto (fun x => Real.log (f x / g x) * p) l (nhds 0) := by
    simpa using hlog.mul hpconst
  have hexp : Tendsto
      (fun x => Real.exp (Real.log (f x / g x) * p)) l (nhds 1) := by
    have hcont : ContinuousAt Real.exp 0 := (Real.hasDerivAt_exp 0).continuousAt
    simpa using hcont.tendsto.comp hmul
  have hgrpow_ne : ∀ᶠ x in l, Real.rpow (g x) p ≠ 0 := by
    filter_upwards [hg] with x hx
    exact ne_of_gt (Real.rpow_pos_of_pos hx p)
  apply (Asymptotics.isEquivalent_iff_tendsto_one hgrpow_ne).2
  have heq :
      (fun x => Real.rpow (f x) p / Real.rpow (g x) p) =ᶠ[l]
      (fun x => Real.exp (Real.log (f x / g x) * p)) := by
    filter_upwards [hf, hg] with x hfx hgx
    calc
      Real.rpow (f x) p / Real.rpow (g x) p =
          Real.rpow (f x / g x) p :=
        (rpow_div_of_pos (f x) (g x) p hfx hgx).symm
      _ = Real.exp (Real.log (f x / g x) * p) :=
        (Real.rpow_def_of_pos (div_pos hfx hgx)) p
  exact (tendsto_congr' heq).2 hexp

private theorem isEquivalent_const_mul
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hfg : Asymptotics.IsEquivalent l f g)
    (hg : ∀ᶠ x in l, g x ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    Asymptotics.IsEquivalent l
      (fun x => c * f x) (fun x => c * g x) := by
  have hratio : Tendsto (fun x => f x / g x) l (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hg).1 hfg
  have hcg : ∀ᶠ x in l, c * g x ≠ 0 := by
    filter_upwards [hg] with x hx
    exact mul_ne_zero hc hx
  apply (Asymptotics.isEquivalent_iff_tendsto_one hcg).2
  have heq : (fun x => (c * f x) / (c * g x)) =ᶠ[l]
      (fun x => f x / g x) := by
    filter_upwards [hg] with x hx
    field_simp [hc, hx]
  exact (tendsto_congr' heq).2 hratio

private theorem summable_of_isEquivalent_nat_pos {f g : ℕ → ℝ}
    (hfg : Asymptotics.IsEquivalent atTop f g) (hg : Summable g)
    (hgpos : ∀ n, 0 < g n) : Summable f := by
  have hg_ne : ∀ᶠ n in atTop, g n ≠ 0 := by
    filter_upwards [] with n
    exact ne_of_gt (hgpos n)
  have hratio : Tendsto (fun n => f n / g n) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hg_ne).1 hfg
  have hlo : ∀ᶠ n in atTop, 0 < f n / g n :=
    (tendsto_order.1 hratio).1 0 (by norm_num)
  have hhi : ∀ᶠ n in atTop, f n / g n < 2 :=
    (tendsto_order.1 hratio).2 2 (by norm_num)
  rcases eventually_atTop.1 (hlo.and hhi) with ⟨N, hN⟩
  have hgShift : Summable (fun n : ℕ => (2 : ℝ) * g (n + N)) :=
    ((summable_nat_add_iff N).2 hg).mul_left (2 : ℝ)
  have hfShift : Summable (fun n : ℕ => f (n + N)) := by
    refine Summable.of_norm_bounded_eventually hgShift ?_
    filter_upwards [] with n
    have hnBounds := hN (n + N) (by omega)
    have hfpos : 0 < f (n + N) := by
      rcases (div_pos_iff.mp hnBounds.1) with hsame | hsame
      · exact hsame.1
      · exact False.elim
          ((not_lt_of_ge (hgpos (n + N)).le) hsame.2)
    have hupper : f (n + N) < (2 : ℝ) * g (n + N) :=
      (div_lt_iff₀ (hgpos (n + N))).mp hnBounds.2
    have htwogpos : 0 < (2 : ℝ) * g (n + N) :=
      mul_pos (by norm_num) (hgpos (n + N))
    simpa [Real.norm_eq_abs, abs_of_pos hfpos, abs_of_pos htwogpos]
      using hupper.le
  exact (summable_nat_add_iff N).1 hfShift

private theorem powerModel_eq_const_mul_comparison (p : ℝ) (n : ℕ)
    (hn : 0 < n) :
    powerModel p n =
      (Real.rpow 2 (-p) * Real.rpow Real.pi (2 * p)) * comparison p n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  unfold powerModel comparison
  rw [rpow_div_of_pos Real.pi (n : ℝ) (2 * p) Real.pi_pos hnpos]
  ring

private theorem powerModel_nat_add_three_pos (p : ℝ) (n : ℕ) :
    0 < powerModel p (n + 3) := by
  have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 3 by omega)
  unfold powerModel
  exact mul_pos
    (Real.rpow_pos_of_pos (by norm_num) (-p))
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos hnpos) (2 * p))

private theorem logTanTerm_nat_add_three_pos (p : ℝ) (n : ℕ) :
    0 < logTanTerm p (n + 3) := by
  have ht := tan_pi_div_nat_add_three_pos n
  have hs : 0 < Real.tan
      (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2 := pow_pos ht 2
  have hlog : 0 < Real.log
      (1 + Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2) :=
    Real.log_pos (by linarith)
  unfold logTanTerm
  exact mul_pos
    (Real.rpow_pos_of_pos (by norm_num) (-p))
    (Real.rpow_pos_of_pos hlog p)

theorem gap1 (p : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    0 < term p n := by
  let x : ℝ := Real.pi / (n : ℝ)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn)
  have hn3 : (3 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < Real.pi / 2 := by
    dsimp [x]
    apply (div_lt_iff₀ hn0).2
    nlinarith [Real.pi_pos]
  have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact hx0.le
    · nlinarith [Real.pi_pos]
  have hcoslt : Real.cos x < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by simp [Real.pi_pos.le])
      hxmem hx0
    simpa using h
  have hcospos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsec : 1 < sec x := by
    unfold sec
    exact one_lt_one_div hcospos hcoslt
  unfold term
  change 0 < Real.rpow (Real.log (sec x)) p
  exact Real.rpow_pos_of_pos (Real.log_pos hsec) p

theorem gap2 (p : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    term p n = logTanTerm p n := by
  let x : ℝ := Real.pi / (n : ℝ)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn)
  have hn3 : (3 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < Real.pi / 2 := by
    dsimp [x]
    apply (div_lt_iff₀ hn0).2
    nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact hx0.le
    · nlinarith [Real.pi_pos]
  have hcoslt : Real.cos x < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by simp [Real.pi_pos.le])
      hxmem hx0
    simpa using h
  have hsec : 1 < sec x := by
    unfold sec
    exact one_lt_one_div hcospos hcoslt
  have htrig : 1 + Real.tan x ^ 2 = sec x ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcospos]
    simpa [add_comm] using Real.sin_sq_add_cos_sq x
  have hlogeq : Real.log (sec x) = Real.log (1 + Real.tan x ^ 2) / 2 := by
    rw [htrig, Real.log_pow]
    norm_num
  have hlogsec : 0 < Real.log (sec x) := Real.log_pos hsec
  have hlogtan : 0 < Real.log (1 + Real.tan x ^ 2) := by
    nlinarith [hlogeq, hlogsec]
  unfold term logTanTerm
  change Real.rpow (Real.log (sec x)) p =
    Real.rpow 2 (-p) * Real.rpow (Real.log (1 + Real.tan x ^ 2)) p
  rw [hlogeq]
  rw [rpow_div_of_pos (Real.log (1 + Real.tan x ^ 2)) 2 p hlogtan
    (by norm_num : (0 : ℝ) < 2)]
  rw [rpow_neg_eq_inv 2 (by norm_num : (0 : ℝ) < 2) p]
  ring

theorem gap3 (p : ℝ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => logTanTerm p (n + 3))
      (fun n : ℕ => tanModel p (n + 3)) := by
  have hx : Tendsto
      (fun n : ℕ => Real.pi / ((n + 3 : ℕ) : ℝ))
      atTop (nhds 0) := tendsto_pi_div_nat_add_three
  have htan : Tendsto
      (fun n : ℕ => Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    have hcont : ContinuousAt Real.tan 0 :=
      (Real.hasDerivAt_tan (by norm_num : Real.cos 0 ≠ 0)).continuousAt
    simpa using hcont.tendsto.comp hx
  have hsq : Tendsto
      (fun n : ℕ => Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2)
      atTop (nhds 0) := by
    simpa using htan.pow 2
  have hbase : Asymptotics.IsEquivalent atTop
      (fun n : ℕ =>
        Real.log (1 + Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2))
      (fun n : ℕ => Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2) :=
    isEquivalent_log_one_plus_nhds.comp_tendsto hsq
  have hfpos : ∀ᶠ n in (atTop : Filter ℕ),
      0 < Real.log (1 + Real.tan
        (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2) := by
    filter_upwards [] with n
    have ht := tan_pi_div_nat_add_three_pos n
    have hs : 0 < Real.tan
        (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2 := pow_pos ht 2
    exact Real.log_pos (by linarith)
  have hgpos : ∀ᶠ n in (atTop : Filter ℕ),
      0 < Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2 := by
    filter_upwards [] with n
    exact pow_pos (tan_pi_div_nat_add_three_pos n) 2
  have hrpow :=
    isEquivalent_rpow_of_eventually_pos hfpos hgpos hbase p
  have hpoweq :
      (fun n : ℕ =>
        Real.rpow (Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) ^ 2) p) =
      (fun n : ℕ =>
        Real.rpow (Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ))) (2 * p)) := by
    funext n
    exact rpow_sq_of_pos
      (Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)))
      (tan_pi_div_nat_add_three_pos n) p
  rw [hpoweq] at hrpow
  have hden_ne : ∀ᶠ n in (atTop : Filter ℕ),
      Real.rpow (Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ))) (2 * p) ≠ 0 := by
    filter_upwards [] with n
    exact ne_of_gt (Real.rpow_pos_of_pos
      (tan_pi_div_nat_add_three_pos n) (2 * p))
  have hc : Real.rpow 2 (-p) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (-p))
  have hscaled := isEquivalent_const_mul hrpow hden_ne
    (Real.rpow 2 (-p)) hc
  simpa [logTanTerm, tanModel] using hscaled

theorem gap4 (p : ℝ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => tanModel p (n + 3))
      (fun n : ℕ => powerModel p (n + 3)) := by
  have hx : Tendsto
      (fun n : ℕ => Real.pi / ((n + 3 : ℕ) : ℝ))
      atTop (nhds 0) := tendsto_pi_div_nat_add_three
  have htan : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)))
      (fun n : ℕ => Real.pi / ((n + 3 : ℕ) : ℝ)) :=
    isEquivalent_tan_nhds.comp_tendsto hx
  have htanpos : ∀ᶠ n in (atTop : Filter ℕ),
      0 < Real.tan (Real.pi / ((n + 3 : ℕ) : ℝ)) := by
    filter_upwards [] with n
    exact tan_pi_div_nat_add_three_pos n
  have hangpos : ∀ᶠ n in (atTop : Filter ℕ),
      0 < Real.pi / ((n + 3 : ℕ) : ℝ) := by
    filter_upwards [] with n
    have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n + 3 by omega)
    exact div_pos Real.pi_pos hnpos
  have hrpow := isEquivalent_rpow_of_eventually_pos
    htanpos hangpos htan (2 * p)
  have hden_ne : ∀ᶠ n in (atTop : Filter ℕ),
      Real.rpow (Real.pi / ((n + 3 : ℕ) : ℝ)) (2 * p) ≠ 0 := by
    filter_upwards [hangpos] with n hn
    exact ne_of_gt (Real.rpow_pos_of_pos hn (2 * p))
  have hc : Real.rpow 2 (-p) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (-p))
  have hscaled := isEquivalent_const_mul hrpow hden_ne
    (Real.rpow 2 (-p)) hc
  simpa [tanModel, powerModel] using hscaled

theorem gap5 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => powerModel p (n + 3))
      (fun n : ℕ => comparison p (n + 3)) := by
  let c : ℝ := Real.rpow 2 (-p) * Real.rpow Real.pi (2 * p)
  have heq : (fun n : ℕ => powerModel p (n + 3)) =
      (fun n : ℕ => c * comparison p (n + 3)) := by
    funext n
    simpa [c] using
      (powerModel_eq_const_mul_comparison p (n + 3) (by omega))
  rw [heq]
  exact (Asymptotics.isBigO_refl
    (fun n : ℕ => comparison p (n + 3)) atTop).const_mul_left c

theorem gap6 (p : ℝ) (hp : 1 / 2 < p) :
    converges p := by
  unfold converges
  have hexp : -(2 * p) < -1 := by linarith
  have hrpow : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(2 * p))) :=
    (Real.summable_nat_rpow).2 hexp
  have hrpowShift : Summable
      (fun n : ℕ => Real.rpow ((n + 3 : ℕ) : ℝ) (-(2 * p))) :=
    (summable_nat_add_iff 3).2 hrpow
  have hcomparisonShift : Summable (fun n : ℕ => comparison p (n + 3)) := by
    refine hrpowShift.congr ?_
    intro n
    have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n + 3 by omega)
    unfold comparison
    exact rpow_neg_eq_inv ((n + 3 : ℕ) : ℝ) hnpos (2 * p)
  let c : ℝ := Real.rpow 2 (-p) * Real.rpow Real.pi (2 * p)
  have hccomp : Summable
      (fun n : ℕ => c * comparison p (n + 3)) :=
    hcomparisonShift.mul_left c
  have hpower : Summable (fun n : ℕ => powerModel p (n + 3)) := by
    refine hccomp.congr ?_
    intro n
    simpa [c] using
      (powerModel_eq_const_mul_comparison p (n + 3) (by omega)).symm
  have hmodel := (gap3 p).trans (gap4 p)
  have hlogTan : Summable (fun n : ℕ => logTanTerm p (n + 3)) :=
    summable_of_isEquivalent_nat_pos hmodel hpower
      (powerModel_nat_add_three_pos p)
  refine hlogTan.congr ?_
  intro n
  exact (gap2 p (n + 3) (by omega)).symm

theorem gap7 (p : ℝ) :
    2 * p > 1 ↔ p > 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem gap8 (p : ℝ) :
    converges p ↔ 1 / 2 < p := by
  constructor
  · intro hconv
    unfold converges at hconv
    have hlogTan : Summable (fun n : ℕ => logTanTerm p (n + 3)) := by
      refine hconv.congr ?_
      intro n
      exact gap2 p (n + 3) (by omega)
    have hmodel := (gap3 p).trans (gap4 p)
    have hpower : Summable (fun n : ℕ => powerModel p (n + 3)) :=
      summable_of_isEquivalent_nat_pos hmodel.symm hlogTan
        (logTanTerm_nat_add_three_pos p)
    let c : ℝ := Real.rpow 2 (-p) * Real.rpow Real.pi (2 * p)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (-p)))
        (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos (2 * p)))
    have heq : ∀ n : ℕ,
        powerModel p (n + 3) = c * comparison p (n + 3) := by
      intro n
      simpa [c] using
        (powerModel_eq_const_mul_comparison p (n + 3) (by omega))
    have hcomparisonShift : Summable (fun n : ℕ => comparison p (n + 3)) := by
      have hi : Summable
          (fun n : ℕ => c⁻¹ * powerModel p (n + 3)) :=
        hpower.mul_left c⁻¹
      refine hi.congr ?_
      intro n
      rw [heq n]
      simp [hc]
    have hrpowShift : Summable
        (fun n : ℕ => Real.rpow ((n + 3 : ℕ) : ℝ) (-(2 * p))) := by
      refine hcomparisonShift.congr ?_
      intro n
      have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < n + 3 by omega)
      unfold comparison
      exact (rpow_neg_eq_inv ((n + 3 : ℕ) : ℝ) hnpos (2 * p)).symm
    have hrpow : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(2 * p))) :=
      (summable_nat_add_iff 3).1 hrpowShift
    have hexp : -(2 * p) < -1 :=
      (Real.summable_nat_rpow).1 hrpow
    linarith
  · exact gap6 p

end

end ProofGap.Exercise2610
