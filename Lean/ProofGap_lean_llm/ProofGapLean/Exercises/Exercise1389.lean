import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1389

noncomputable section

open Filter

def power (x : ℝ) : ℝ := Real.rpow x x
def f (x : ℝ) : ℝ := power x - 1

def firstFormula (x : ℝ) : ℝ :=
  power x * (1 + Real.log x)

def secondFormula (x : ℝ) : ℝ :=
  power x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1)

def thirdFormula (x : ℝ) : ℝ :=
  power x * (1 + Real.log x) ^ 3 +
    2 * Real.rpow x (x - 1) * (1 + Real.log x) +
    Real.rpow x (x - 1) * ((x - 1) / x + Real.log x)

def polynomial (x : ℝ) : ℝ :=
  (x - 1) + (x - 1) ^ 2 + (1 / 2 : ℝ) * (x - 1) ^ 3

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private theorem hasDerivAt_power (x : ℝ) (hx : 0 < x) :
    HasDerivAt power (firstFormula x) x := by
  have h := (hasDerivAt_id x).rpow (hasDerivAt_id x) hx
  dsimp [power, firstFormula] at *
  convert h using 1
  rw [Real.rpow_sub_one hx.ne']
  field_simp

private theorem hasDerivAt_f (x : ℝ) (hx : 0 < x) :
    HasDerivAt f (firstFormula x) x := by
  simpa only [f] using (hasDerivAt_power x hx).sub_const 1

private theorem hasDerivAt_firstFormula (x : ℝ) (hx : 0 < x) :
    HasDerivAt firstFormula (secondFormula x) x := by
  have hlog : HasDerivAt (fun y : ℝ => 1 + Real.log y) (1 / x) x := by
    convert (Real.hasDerivAt_log hx.ne').const_add 1 using 1 <;> ring
  have h := (hasDerivAt_power x hx).mul hlog
  dsimp [firstFormula, secondFormula, power] at *
  convert h using 1
  rw [Real.rpow_sub_one hx.ne']
  field_simp

private theorem hasDerivAt_secondFormula (x : ℝ) (hx : 0 < x) :
    HasDerivAt secondFormula (thirdFormula x) x := by
  have hp : x * Real.rpow x (x - 1) = Real.rpow x x := by
    rw [show Real.rpow x (x - 1) = Real.rpow x x / x from
      Real.rpow_sub_one hx.ne' x]
    field_simp
  have hlog : HasDerivAt (fun y : ℝ => 1 + Real.log y) (1 / x) x := by
    convert (Real.hasDerivAt_log hx.ne').const_add 1 using 1 <;> ring
  have hfirst :=
    (hasDerivAt_power x hx).mul (hlog.pow 2)
  have hexponent : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    (hasDerivAt_id x).sub_const 1
  have hsecond := (hasDerivAt_id x).rpow hexponent hx
  have h := hfirst.add hsecond
  dsimp [firstFormula, secondFormula, thirdFormula, power] at *
  convert h using 1
  rw [Real.rpow_sub_one hx.ne' x, Real.rpow_sub_one hx.ne' (x - 1)]
  field_simp
  linear_combination -(x - 1) * hp

theorem gap1 (x : ℝ) (hx : 0 < x) :
    iterDeriv 1 f x = firstFormula x := by
  simpa [iterDeriv] using (hasDerivAt_f x hx).deriv

theorem gap2 (x : ℝ) (hx : 0 < x) :
    iterDeriv 2 f x = secondFormula x := by
  have heq : deriv f =ᶠ[nhds x] firstFormula := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_f y hy).deriv
  rw [show iterDeriv 2 f x = deriv (deriv f) x by rfl, heq.deriv_eq]
  exact (hasDerivAt_firstFormula x hx).deriv

theorem gap3 (x : ℝ) (hx : 0 < x)
    (hsmooth : ContDiffAt ℝ 3 f x) :
    iterDeriv 3 f x = thirdFormula x := by
  have heq : deriv (deriv f) =ᶠ[nhds x] secondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have heq1 : deriv f =ᶠ[nhds y] firstFormula := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact (hasDerivAt_f z hz).deriv
    rw [heq1.deriv_eq]
    exact (hasDerivAt_firstFormula y hy).deriv
  rw [show iterDeriv 3 f x = deriv (deriv (deriv f)) x by rfl,
    heq.deriv_eq]
  exact (hasDerivAt_secondFormula x hx).deriv

theorem gap4 :
    f 1 = 0 := by
  norm_num [f, power]

theorem gap5 :
    iterDeriv 1 f 1 = 1 := by
  have h := gap1 1 (by norm_num)
  norm_num [firstFormula, power] at h
  exact h

theorem gap6 :
    iterDeriv 2 f 1 = 2 := by
  have h := gap2 1 (by norm_num)
  norm_num [secondFormula, power] at h
  exact h

theorem gap7 :
    iterDeriv 3 f 1 = 3 := by
  have hp : ContDiffAt ℝ 3 power 1 := by
    simpa only [power] using
      contDiffAt_id.rpow contDiffAt_id (by norm_num : (1 : ℝ) ≠ 0)
  have hf : ContDiffAt ℝ 3 f 1 := by
    simpa only [f] using hp.sub contDiffAt_const
  have h := gap3 1 (by norm_num) hf
  norm_num [thirdFormula, power] at h
  exact h

theorem gap8 :
    AgreesToOrderAt f polynomial 1 3 := by
  have hf : ContDiffOn ℝ 3 f (Set.Ioi 0) := by
    have hp : ContDiffOn ℝ 3 power (Set.Ioi 0) := by
      simpa only [power] using contDiffOn_id.rpow contDiffOn_id
        (fun x hx => hx.ne')
    simpa only [f] using hp.sub contDiffOn_const
  have ht := taylor_isLittleO (convex_Ioi (0 : ℝ))
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hf
  rw [isOpen_Ioi.nhdsWithin_eq
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)] at ht
  have heval : taylorWithinEval f 3 (Set.Ioi 0) 1 = polynomial := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
    have h0 : (deriv^[0]) f 1 = 0 := gap4
    have h1 : (deriv^[1]) f 1 = 1 := by
      simpa [iterDeriv] using gap5
    have h2 : (deriv^[2]) f 1 = 2 := by
      simpa [iterDeriv] using gap6
    have h3 : (deriv^[3]) f 1 = 3 := by
      simpa [iterDeriv] using gap7
    rw [h0, h1, h2, h3]
    simp only [smul_eq_mul, Nat.factorial, Nat.cast_ofNat, inv_one,
      one_mul, pow_zero, mul_zero, add_zero]
    dsimp [polynomial]
    ring
  rw [heval] at ht
  exact ht

end

end ProofGap.Exercise1389
