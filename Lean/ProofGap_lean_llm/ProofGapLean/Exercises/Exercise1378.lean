import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Taylor

namespace ProofGap.Exercise1378

noncomputable section

open Filter

def f (x : ℝ) : ℝ :=
  (1 + x) ^ 100 / ((1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60)

def firstFormula (x : ℝ) : ℝ :=
  60 * (1 + x) ^ 99 * (1 + 6 * x) /
    ((1 - 2 * x) ^ 41 * (1 + 2 * x) ^ 61)

def secondFormula (x : ℝ) : ℝ :=
  60 * (1 + x) ^ 98 * (65 + 728 * x + 2196 * x ^ 2 + 48 * x ^ 3) /
    ((1 - 2 * x) ^ 42 * (1 + 2 * x) ^ 62)

def polynomial (x : ℝ) : ℝ := 1 + 60 * x + 1950 * x ^ 2
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

def regular (x : ℝ) : Prop := 1 - 2 * x ≠ 0 ∧ 1 + 2 * x ≠ 0

private theorem deriv_f_formula (x : ℝ) (hx : regular x) :
    deriv f x = firstFormula x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using HasDerivAt.mul hc2 hi
  have hp : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa only [Pi.add_apply, zero_add] using HasDerivAt.add hc1 hi
  have hm : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
    simpa only [Pi.sub_apply, zero_sub] using HasDerivAt.sub hc1 h2x
  have hpp : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
    simpa only [Pi.add_apply, zero_add] using HasDerivAt.add hc1 h2x
  have hn := hp.fun_pow 100
  have hd := HasDerivAt.mul (hm.fun_pow 40) (hpp.fun_pow 60)
  have hden : (1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 40 hx.1) (pow_ne_zero 60 hx.2)
  have hq := (hn.div hd hden).deriv
  unfold f firstFormula
  rw [show deriv (fun y : ℝ =>
    (1 + y) ^ 100 / ((1 - 2 * y) ^ 40 * (1 + 2 * y) ^ 60)) x =
      (100 * (1 + x) ^ 99 *
          ((1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60) -
        (1 + x) ^ 100 *
          ((40 * (1 - 2 * x) ^ 39 * (-2)) * (1 + 2 * x) ^ 60 +
            (1 - 2 * x) ^ 40 * (60 * (1 + 2 * x) ^ 59 * 2))) /
        ((1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60) ^ 2 by
      simpa using hq]
  field_simp [hx.1, hx.2]
  ring

private theorem eventually_regular (x : ℝ) (hx : regular x) :
    ∀ᶠ y in nhds x, regular y := by
  have hm : ContinuousAt (fun y : ℝ => 1 - 2 * y) x := by fun_prop
  have hp : ContinuousAt (fun y : ℝ => 1 + 2 * y) x := by fun_prop
  exact (hm.eventually_ne hx.1).and (hp.eventually_ne hx.2)

private theorem deriv_first_formula (x : ℝ) (hx : regular x) :
    HasDerivAt firstFormula (secondFormula x) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have hc6 : HasDerivAt (fun _ : ℝ => (6 : ℝ)) 0 x :=
    hasDerivAt_const x (6 : ℝ)
  have hc60 : HasDerivAt (fun _ : ℝ => (60 : ℝ)) 0 x :=
    hasDerivAt_const x (60 : ℝ)
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using HasDerivAt.mul hc2 hi
  have h6x : HasDerivAt (fun y : ℝ => 6 * y) 6 x := by
    simpa using HasDerivAt.mul hc6 hi
  have hp : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa only [Pi.add_apply, zero_add] using HasDerivAt.add hc1 hi
  have hm : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
    simpa only [Pi.sub_apply, zero_sub] using HasDerivAt.sub hc1 h2x
  have hpp : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
    simpa only [Pi.add_apply, zero_add] using HasDerivAt.add hc1 h2x
  have h6p : HasDerivAt (fun y : ℝ => 1 + 6 * y) 6 x := by
    simpa only [Pi.add_apply, zero_add] using HasDerivAt.add hc1 h6x
  have hn : HasDerivAt
      (fun y : ℝ => 60 * (1 + y) ^ 99 * (1 + 6 * y))
      (60 * (99 * (1 + x) ^ 98) * (1 + 6 * x) +
        60 * (1 + x) ^ 99 * 6) x := by
    convert HasDerivAt.mul
      (HasDerivAt.mul hc60 (hp.fun_pow 99)) h6p using 1 <;>
      simp [Pi.mul_apply] <;> ring
  have hd : HasDerivAt
      (fun y : ℝ => (1 - 2 * y) ^ 41 * (1 + 2 * y) ^ 61)
      ((41 * (1 - 2 * x) ^ 40 * (-2)) * (1 + 2 * x) ^ 61 +
        (1 - 2 * x) ^ 41 * (61 * (1 + 2 * x) ^ 60 * 2)) x :=
    HasDerivAt.mul (hm.fun_pow 41) (hpp.fun_pow 61)
  have hden : (1 - 2 * x) ^ 41 * (1 + 2 * x) ^ 61 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 41 hx.1) (pow_ne_zero 61 hx.2)
  unfold firstFormula
  refine (hn.div hd hden).congr_deriv ?_
  unfold secondFormula
  field_simp [hx.1, hx.2]
  ring

private theorem second_deriv_formula (x : ℝ) (hx : regular x) :
    deriv (deriv f) x = secondFormula x := by
  have heq : deriv f =ᶠ[nhds x] firstFormula := by
    filter_upwards [eventually_regular x hx] with y hy
    exact deriv_f_formula y hy
  exact ((deriv_first_formula x hx).congr_of_eventuallyEq heq).deriv

theorem gap1 (x : ℝ) (hx : regular x) :
    iterDeriv 1 f x = firstFormula x := by
  exact deriv_f_formula x hx

theorem gap2 (x : ℝ) (hx : regular x) :
    iterDeriv 2 f x = secondFormula x := by
  exact second_deriv_formula x hx

theorem gap3 :
    f 0 = 1 := by
  norm_num [f]

theorem gap4 :
    iterDeriv 1 f 0 = 60 := by
  change deriv f 0 = 60
  rw [deriv_f_formula 0 (by simp [regular])]
  norm_num [firstFormula]

theorem gap5 :
    iterDeriv 2 f 0 = 3900 := by
  change deriv (deriv f) 0 = 3900
  rw [second_deriv_formula 0 (by simp [regular])]
  norm_num [secondFormula]

theorem gap6 :
    AgreesToOrderAt f polynomial 0 2 := by
  let s : Set ℝ := Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)
  have hs0 : (0 : ℝ) ∈ s := by
    simp [s]
    norm_num
  have hn : ContDiff ℝ 2 (fun x : ℝ => (1 + x) ^ 100) := by
    exact (ContDiff.add contDiff_const contDiff_id).pow 100
  have hd : ContDiff ℝ 2
      (fun x : ℝ => (1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60) := by
    have h2x : ContDiff ℝ 2 (fun x : ℝ => 2 * x) :=
      ContDiff.mul contDiff_const contDiff_id
    have hm : ContDiff ℝ 2 (fun x : ℝ => 1 - 2 * x) :=
      ContDiff.sub contDiff_const h2x
    have hp : ContDiff ℝ 2 (fun x : ℝ => 1 + 2 * x) :=
      ContDiff.add contDiff_const h2x
    exact ContDiff.mul (hm.pow 40) (hp.pow 60)
  have hden : ∀ x ∈ s,
      (1 - 2 * x) ^ 40 * (1 + 2 * x) ^ 60 ≠ 0 := by
    intro x hx
    have hm : 1 - 2 * x ≠ 0 := by
      have : 0 < 1 - 2 * x := by
        dsimp [s] at hx
        nlinarith [hx.2]
      exact ne_of_gt this
    have hp : 1 + 2 * x ≠ 0 := by
      have : 0 < 1 + 2 * x := by
        dsimp [s] at hx
        nlinarith [hx.1]
      exact ne_of_gt this
    exact mul_ne_zero (pow_ne_zero 40 hm) (pow_ne_zero 60 hp)
  have hcd : ContDiffOn ℝ 2 f s := by
    unfold f
    exact ContDiffOn.fun_div hn.contDiffOn hd.contDiffOn hden
  have ht := taylor_isLittleO (s := s) (n := 2)
    (convex_Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)) hs0 hcd
  have hsnhds : nhdsWithin (0 : ℝ) s = nhds 0 :=
    IsOpen.nhdsWithin_eq isOpen_Ioo hs0
  rw [hsnhds] at ht
  have hud : UniqueDiffOn ℝ s :=
    uniqueDiffOn_Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)
  have hcat : ContDiffAt ℝ 2 f 0 :=
    (hcd 0 hs0).contDiffAt (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hi0 : iteratedDerivWithin 0 f s 0 = 1 := by
    simp [f]
  have hi1 : iteratedDerivWithin 1 f s 0 = 60 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
      (hcat.of_le (by norm_num)) hs0]
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using gap4
  have hi2 : iteratedDerivWithin 2 f s 0 = 3900 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud hcat hs0]
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using gap5
  have heval : taylorWithinEval f 2 s 0 = polynomial := by
    funext x
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hi0, hi1, hi2, polynomial]
    ring
  unfold AgreesToOrderAt
  rw [← heval]
  exact ht

end

end ProofGap.Exercise1378
