import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1380

noncomputable section

open Filter

def q₂ (x : ℝ) : ℝ := 1 - 2 * x + x ^ 3
def q₃ (x : ℝ) : ℝ := 1 - 3 * x + x ^ 2

def f (x : ℝ) : ℝ :=
  Real.rpow (q₂ x) (1 / 2 : ℝ) - Real.rpow (q₃ x) (1 / 3 : ℝ)

def firstFormula (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (3 * x ^ 2 - 2) * Real.rpow (q₂ x) (-1 / 2 : ℝ) -
    (1 / 3 : ℝ) * (2 * x - 3) * Real.rpow (q₃ x) (-2 / 3 : ℝ)

def secondFormula (x : ℝ) : ℝ :=
  3 * x * Real.rpow (q₂ x) (-1 / 2 : ℝ) -
    (1 / 4 : ℝ) * (3 * x ^ 2 - 2) ^ 2 * Real.rpow (q₂ x) (-3 / 2 : ℝ) -
    (2 / 3 : ℝ) * Real.rpow (q₃ x) (-2 / 3 : ℝ) +
    (2 / 9 : ℝ) * (2 * x - 3) ^ 2 * Real.rpow (q₃ x) (-5 / 3 : ℝ)

def thirdFormula (x : ℝ) : ℝ :=
  3 * Real.rpow (q₂ x) (-1 / 2 : ℝ) -
    (9 / 2 : ℝ) * x * (3 * x ^ 2 - 2) * Real.rpow (q₂ x) (-3 / 2 : ℝ) +
    (3 / 8 : ℝ) * (3 * x ^ 2 - 2) ^ 3 * Real.rpow (q₂ x) (-5 / 2 : ℝ) +
    (4 / 3 : ℝ) * (2 * x - 3) * Real.rpow (q₃ x) (-5 / 3 : ℝ) -
    (10 / 27 : ℝ) * (2 * x - 3) ^ 3 * Real.rpow (q₃ x) (-8 / 3 : ℝ)

def polynomial (x : ℝ) : ℝ := (1 / 6 : ℝ) * x ^ 2 + x ^ 3
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

def regular (x : ℝ) : Prop := 0 < q₂ x ∧ 0 < q₃ x

private theorem hasDeriv_q2 (x : ℝ) :
    HasDerivAt q₂ (3 * x ^ 2 - 2) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using HasDerivAt.mul hc2 hi
  have hx3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert hi.fun_pow 3 using 1 <;> norm_num
  unfold q₂
  convert HasDerivAt.add (HasDerivAt.sub hc1 h2x) hx3 using 1 <;>
    simp <;> ring

private theorem hasDeriv_q3 (x : ℝ) :
    HasDerivAt q₃ (2 * x - 3) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hc3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x :=
    hasDerivAt_const x (3 : ℝ)
  have h3x : HasDerivAt (fun y : ℝ => 3 * y) 3 x := by
    simpa using HasDerivAt.mul hc3 hi
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hi.fun_pow 2
  unfold q₃
  convert HasDerivAt.add (HasDerivAt.sub hc1 h3x) hx2 using 1 <;>
    simp <;> ring

private theorem deriv_f_formula (x : ℝ) (hx : regular x) :
    deriv f x = firstFormula x := by
  have h1 := (hasDeriv_q2 x).rpow_const
    (p := (1 / 2 : ℝ)) (Or.inl (ne_of_gt hx.1))
  have h2 := (hasDeriv_q3 x).rpow_const
    (p := (1 / 3 : ℝ)) (Or.inl (ne_of_gt hx.2))
  have hd := (HasDerivAt.sub h1 h2).deriv
  unfold f firstFormula
  rw [show deriv (fun y : ℝ =>
    Real.rpow (q₂ y) (1 / 2 : ℝ) -
      Real.rpow (q₃ y) (1 / 3 : ℝ)) x =
      ((3 * x ^ 2 - 2) * (1 / 2 : ℝ) *
        Real.rpow (q₂ x) ((1 / 2 : ℝ) - 1)) -
      ((2 * x - 3) * (1 / 3 : ℝ) *
        Real.rpow (q₃ x) ((1 / 3 : ℝ) - 1)) by simpa using hd]
  norm_num
  ring

private theorem eventually_regular (x : ℝ) (hx : regular x) :
    ∀ᶠ y in nhds x, regular y := by
  have hq2 : ContinuousAt q₂ x := by
    unfold q₂
    fun_prop
  have hq3 : ContinuousAt q₃ x := by
    unfold q₃
    fun_prop
  exact
    (hq2.eventually (isOpen_Ioi.mem_nhds hx.1)).and
      (hq3.eventually (isOpen_Ioi.mem_nhds hx.2))

private theorem deriv_first_formula (x : ℝ) (hx : regular x) :
    HasDerivAt firstFormula (secondFormula x) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have hc3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x :=
    hasDerivAt_const x (3 : ℝ)
  have hc12 : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 x :=
    hasDerivAt_const x (1 / 2 : ℝ)
  have hc13 : HasDerivAt (fun _ : ℝ => (1 / 3 : ℝ)) 0 x :=
    hasDerivAt_const x (1 / 3 : ℝ)
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hi.fun_pow 2
  have h3x2 : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
    convert HasDerivAt.mul hc3 hx2 using 1 <;> norm_num <;> ring
  have hu : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2) (6 * x) x := by
    simpa only [Pi.sub_apply, sub_zero] using HasDerivAt.sub h3x2 hc2
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using HasDerivAt.mul hc2 hi
  have hv : HasDerivAt (fun y : ℝ => 2 * y - 3) 2 x := by
    simpa only [Pi.sub_apply, sub_zero] using HasDerivAt.sub h2x hc3
  have hr1 := (hasDeriv_q2 x).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl (ne_of_gt hx.1))
  have hr2 := (hasDeriv_q3 x).rpow_const
    (p := (-2 / 3 : ℝ)) (Or.inl (ne_of_gt hx.2))
  have hA : HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * (3 * y ^ 2 - 2) *
        Real.rpow (q₂ y) (-1 / 2 : ℝ))
      (3 * x * Real.rpow (q₂ x) (-1 / 2 : ℝ) -
        (1 / 4 : ℝ) * (3 * x ^ 2 - 2) ^ 2 *
          Real.rpow (q₂ x) (-3 / 2 : ℝ)) x := by
    have hraw := HasDerivAt.mul (HasDerivAt.mul hc12 hu) hr1
    convert hraw using 1 <;> norm_num <;> ring
  have hB : HasDerivAt
      (fun y : ℝ => (1 / 3 : ℝ) * (2 * y - 3) *
        Real.rpow (q₃ y) (-2 / 3 : ℝ))
      ((2 / 3 : ℝ) * Real.rpow (q₃ x) (-2 / 3 : ℝ) -
        (2 / 9 : ℝ) * (2 * x - 3) ^ 2 *
          Real.rpow (q₃ x) (-5 / 3 : ℝ)) x := by
    have hraw := HasDerivAt.mul (HasDerivAt.mul hc13 hv) hr2
    convert hraw using 1 <;> norm_num <;> ring
  unfold firstFormula
  refine (HasDerivAt.sub hA hB).congr_deriv ?_
  unfold secondFormula
  ring

private theorem second_deriv_formula (x : ℝ) (hx : regular x) :
    deriv (deriv f) x = secondFormula x := by
  have heq : deriv f =ᶠ[nhds x] firstFormula := by
    filter_upwards [eventually_regular x hx] with y hy
    exact deriv_f_formula y hy
  exact ((deriv_first_formula x hx).congr_of_eventuallyEq heq).deriv

private theorem deriv_second_formula (x : ℝ) (hx : regular x) :
    HasDerivAt secondFormula (thirdFormula x) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have hc3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x :=
    hasDerivAt_const x (3 : ℝ)
  have hc14 : HasDerivAt (fun _ : ℝ => (1 / 4 : ℝ)) 0 x :=
    hasDerivAt_const x (1 / 4 : ℝ)
  have hc23 : HasDerivAt (fun _ : ℝ => (2 / 3 : ℝ)) 0 x :=
    hasDerivAt_const x (2 / 3 : ℝ)
  have hc29 : HasDerivAt (fun _ : ℝ => (2 / 9 : ℝ)) 0 x :=
    hasDerivAt_const x (2 / 9 : ℝ)
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hi.fun_pow 2
  have h3x2 : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
    convert HasDerivAt.mul hc3 hx2 using 1 <;> norm_num <;> ring
  have hu : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2) (6 * x) x := by
    simpa only [Pi.sub_apply, sub_zero] using HasDerivAt.sub h3x2 hc2
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using HasDerivAt.mul hc2 hi
  have hv : HasDerivAt (fun y : ℝ => 2 * y - 3) 2 x := by
    simpa only [Pi.sub_apply, sub_zero] using HasDerivAt.sub h2x hc3
  have hr1 := (hasDeriv_q2 x).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl (ne_of_gt hx.1))
  have hr13 := (hasDeriv_q2 x).rpow_const
    (p := (-3 / 2 : ℝ)) (Or.inl (ne_of_gt hx.1))
  have hr2 := (hasDeriv_q3 x).rpow_const
    (p := (-2 / 3 : ℝ)) (Or.inl (ne_of_gt hx.2))
  have hr25 := (hasDeriv_q3 x).rpow_const
    (p := (-5 / 3 : ℝ)) (Or.inl (ne_of_gt hx.2))
  have hT1 : HasDerivAt
      (fun y : ℝ => 3 * y * Real.rpow (q₂ y) (-1 / 2 : ℝ))
      (3 * Real.rpow (q₂ x) (-1 / 2 : ℝ) -
        (3 / 2 : ℝ) * x * (3 * x ^ 2 - 2) *
          Real.rpow (q₂ x) (-3 / 2 : ℝ)) x := by
    have hraw := HasDerivAt.mul (HasDerivAt.mul hc3 hi) hr1
    convert hraw using 1 <;> norm_num <;> ring
  have hT2 : HasDerivAt
      (fun y : ℝ => (1 / 4 : ℝ) * (3 * y ^ 2 - 2) ^ 2 *
        Real.rpow (q₂ y) (-3 / 2 : ℝ))
      (3 * x * (3 * x ^ 2 - 2) *
          Real.rpow (q₂ x) (-3 / 2 : ℝ) -
        (3 / 8 : ℝ) * (3 * x ^ 2 - 2) ^ 3 *
          Real.rpow (q₂ x) (-5 / 2 : ℝ)) x := by
    have hraw := HasDerivAt.mul
      (HasDerivAt.mul hc14 (hu.fun_pow 2)) hr13
    convert hraw using 1 <;> norm_num <;> ring
  have hT3 : HasDerivAt
      (fun y : ℝ => (2 / 3 : ℝ) *
        Real.rpow (q₃ y) (-2 / 3 : ℝ))
      (-(4 / 9 : ℝ) * (2 * x - 3) *
        Real.rpow (q₃ x) (-5 / 3 : ℝ)) x := by
    have hraw := HasDerivAt.mul hc23 hr2
    convert hraw using 1 <;> norm_num <;> ring
  have hT4 : HasDerivAt
      (fun y : ℝ => (2 / 9 : ℝ) * (2 * y - 3) ^ 2 *
        Real.rpow (q₃ y) (-5 / 3 : ℝ))
      ((8 / 9 : ℝ) * (2 * x - 3) *
          Real.rpow (q₃ x) (-5 / 3 : ℝ) -
        (10 / 27 : ℝ) * (2 * x - 3) ^ 3 *
          Real.rpow (q₃ x) (-8 / 3 : ℝ)) x := by
    have hraw := HasDerivAt.mul
      (HasDerivAt.mul hc29 (hv.fun_pow 2)) hr25
    convert hraw using 1 <;> norm_num <;> ring
  unfold secondFormula
  refine (HasDerivAt.add
    (HasDerivAt.sub (HasDerivAt.sub hT1 hT2) hT3) hT4).congr_deriv ?_
  unfold thirdFormula
  ring

private theorem third_deriv_formula (x : ℝ) (hx : regular x) :
    deriv (deriv (deriv f)) x = thirdFormula x := by
  have heq : deriv (deriv f) =ᶠ[nhds x] secondFormula := by
    filter_upwards [eventually_regular x hx] with y hy
    exact second_deriv_formula y hy
  exact ((deriv_second_formula x hx).congr_of_eventuallyEq heq).deriv

theorem gap1 (x : ℝ) (hx : regular x) :
    iterDeriv 1 f x = firstFormula x := by
  exact deriv_f_formula x hx

theorem gap2 (x : ℝ) (hx : regular x) :
    iterDeriv 2 f x = secondFormula x := by
  exact second_deriv_formula x hx

theorem gap3 (x : ℝ) (hx : regular x)
    (hsmooth : ContDiffAt ℝ 3 f x) :
    iterDeriv 3 f x = thirdFormula x := by
  exact third_deriv_formula x hx

theorem gap4 :
    f 0 = 0 := by
  norm_num [f, q₂, q₃]

theorem gap5 :
    iterDeriv 1 f 0 = 0 := by
  change deriv f 0 = 0
  rw [deriv_f_formula 0 (by norm_num [regular, q₂, q₃])]
  norm_num [firstFormula, q₂, q₃]

theorem gap6 :
    iterDeriv 2 f 0 = (1 / 3 : ℝ) := by
  change deriv (deriv f) 0 = (1 / 3 : ℝ)
  rw [second_deriv_formula 0 (by norm_num [regular, q₂, q₃])]
  norm_num [secondFormula, q₂, q₃]

theorem gap7 :
    iterDeriv 3 f 0 = 6 := by
  change deriv (deriv (deriv f)) 0 = 6
  rw [third_deriv_formula 0 (by norm_num [regular, q₂, q₃])]
  norm_num [thirdFormula, q₂, q₃]

theorem gap8 :
    AgreesToOrderAt f polynomial 0 3 := by
  let s : Set ℝ := Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)
  have hs0 : (0 : ℝ) ∈ s := by
    simp [s]
    norm_num
  have hq2pos : ∀ x ∈ s, 0 < q₂ x := by
    intro x hx
    have hxlo : 0 < x + 1 / 4 := by
      dsimp [s] at hx
      linarith [hx.1]
    have hquad : 0 < x ^ 2 - (1 / 4 : ℝ) * x + 1 / 16 := by
      nlinarith [sq_nonneg (x - 1 / 8)]
    have hcubic : -1 / 64 < x ^ 3 := by
      have hp := mul_pos hxlo hquad
      nlinarith [hp]
    unfold q₂
    dsimp [s] at hx
    nlinarith [hx.2, hcubic]
  have hq3pos : ∀ x ∈ s, 0 < q₃ x := by
    intro x hx
    unfold q₃
    dsimp [s] at hx
    nlinarith [sq_nonneg x, hx.2]
  have hcq2 : ContDiff ℝ 3 q₂ := by
    unfold q₂
    have h2x : ContDiff ℝ 3 (fun x : ℝ => 2 * x) :=
      ContDiff.mul contDiff_const contDiff_id
    exact ContDiff.add (ContDiff.sub contDiff_const h2x)
      (contDiff_id.pow 3)
  have hcq3 : ContDiff ℝ 3 q₃ := by
    unfold q₃
    have h3x : ContDiff ℝ 3 (fun x : ℝ => 3 * x) :=
      ContDiff.mul contDiff_const contDiff_id
    exact ContDiff.add (ContDiff.sub contDiff_const h3x)
      (contDiff_id.pow 2)
  have hcd : ContDiffOn ℝ 3 f s := by
    unfold f
    exact ContDiffOn.sub
      (hcq2.contDiffOn.rpow_const_of_ne
        (fun x hx => ne_of_gt (hq2pos x hx)))
      (hcq3.contDiffOn.rpow_const_of_ne
        (fun x hx => ne_of_gt (hq3pos x hx)))
  have ht := taylor_isLittleO (s := s) (n := 3)
    (convex_Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)) hs0 hcd
  have hsnhds : nhdsWithin (0 : ℝ) s = nhds 0 :=
    IsOpen.nhdsWithin_eq isOpen_Ioo hs0
  rw [hsnhds] at ht
  have hud : UniqueDiffOn ℝ s :=
    uniqueDiffOn_Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ)
  have hcat : ContDiffAt ℝ 3 f 0 :=
    (hcd 0 hs0).contDiffAt (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hi0 : iteratedDerivWithin 0 f s 0 = 0 := by
    simp [f, q₂, q₃]
  have hi1 : iteratedDerivWithin 1 f s 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
      (hcat.of_le (by norm_num)) hs0]
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using gap5
  have hi2 : iteratedDerivWithin 2 f s 0 = (1 / 3 : ℝ) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
      (hcat.of_le (by norm_num)) hs0]
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using gap6
  have hi3 : iteratedDerivWithin 3 f s 0 = 6 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud hcat hs0]
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using gap7
  have heval : taylorWithinEval f 3 s 0 = polynomial := by
    funext x
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hi0, hi1, hi2, hi3, polynomial]
    ring
  unfold AgreesToOrderAt
  rw [← heval]
  exact ht

end

end ProofGap.Exercise1380
