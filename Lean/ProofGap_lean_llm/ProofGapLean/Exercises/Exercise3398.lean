import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3398

noncomputable section

def partial1 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => F t b) a

def partial2 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => F a t) b

def partial11 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 F t b) a

def partial12 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 F a t) b

def partial21 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial2 F t b) a

def partial22 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial2 F a t) b

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def arg1 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x * z x y
def arg2 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y * z x y

def evalAt (G : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  G (arg1 z x y) (arg2 z x y)

def F1At (F : ℝ → ℝ → ℝ) := evalAt (partial1 F)
def F2At (F : ℝ → ℝ → ℝ) := evalAt (partial2 F)
def F11At (F : ℝ → ℝ → ℝ) := evalAt (partial11 F)
def F12At (F : ℝ → ℝ → ℝ) := evalAt (partial12 F)
def F21At (F : ℝ → ℝ → ℝ) := evalAt (partial21 F)
def F22At (F : ℝ → ℝ → ℝ) := evalAt (partial22 F)

def denominator (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  x * F1At F z x y + y * F2At F z x y

def solvedPartialX (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  -(z x y * F1At F z x y) / denominator F z x y

def rawSecondX (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  -(1 / (denominator F z x y) ^ 2) *
    (denominator F z x y *
        (F1At F z x y * partialX z x y +
          z x y *
            (F11At F z x y * (z x y + x * partialX z x y) +
              F12At F z x y * y * partialX z x y)) -
      (F1At F z x y +
          x * (F11At F z x y * (z x y + x * partialX z x y) +
            F12At F z x y * y * partialX z x y) +
          y * (F21At F z x y * (z x y + x * partialX z x y) +
            F22At F z x y * y * partialX z x y)) *
        z x y * F1At F z x y)

def closedSecondX (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  -(y ^ 2 * (z x y) ^ 2 *
        ((F1At F z x y) ^ 2 * F22At F z x y -
          2 * F1At F z x y * F2At F z x y * F12At F z x y +
          (F2At F z x y) ^ 2 * F11At F z x y) -
      2 * z x y * (F1At F z x y) ^ 2 * denominator F z x y) /
    (denominator F z x y) ^ 3

private theorem partial1_eq_fderiv (F : ℝ → ℝ → ℝ) (a b : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a, b)) :
    partial1 F a b =
      fderiv ℝ (Function.uncurry F) (a, b) (1, 0) := by
  unfold partial1
  have hp : HasDerivAt (fun t : ℝ => (t, b)) (1, 0) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have h := (hF.hasFDerivAt.comp a hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partial2_eq_fderiv (F : ℝ → ℝ → ℝ) (a b : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a, b)) :
    partial2 F a b =
      fderiv ℝ (Function.uncurry F) (a, b) (0, 1) := by
  unfold partial2
  have hp : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have h := (hF.hasFDerivAt.comp b hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partial12_eq_partial21 (F : ℝ → ℝ → ℝ) (a b : ℝ)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (a, b)) :
    partial12 F a b = partial21 F a b := by
  let G := Function.uncurry F
  let H := fderiv ℝ (fderiv ℝ G) (a, b)
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ G) (a, b) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hFEv := hF.eventually (by simp)
  have hP1 :
      (fun p : ℝ × ℝ => partial1 F p.1 p.2) =ᶠ[nhds (a, b)]
        (fun p => fderiv ℝ G p (1, 0)) := by
    filter_upwards [hFEv] with p hp
    convert partial1_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hP2 :
      (fun p : ℝ × ℝ => partial2 F p.1 p.2) =ᶠ[nhds (a, b)]
        (fun p => fderiv ℝ G p (0, 1)) := by
    filter_upwards [hFEv] with p hp
    convert partial2_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hEval1 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0))
      (H.flip (1, 0)) (a, b) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × ℝ) (a, b))
    convert h using 1 <;> simp [H]
  have hEval2 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (0, 1))
      (H.flip (0, 1)) (a, b) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 1) : ℝ × ℝ) (a, b))
    convert h using 1 <;> simp [H]
  have h12D : HasDerivAt
      (fun t => fderiv ℝ G (a, t) (1, 0)) (H (0, 1) (1, 0)) b := by
    convert (hEval1.comp b (hasFDerivAt_prodMk_right a b)).hasDerivAt
      using 1 <;> simp
  have h21D : HasDerivAt
      (fun t => fderiv ℝ G (t, b) (0, 1)) (H (1, 0) (0, 1)) a := by
    convert (hEval2.comp a (hasFDerivAt_prodMk_left a b)).hasDerivAt
      using 1 <;> simp
  have h12Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP1
      (show Filter.Tendsto (fun t : ℝ => (a, t))
          (nhds b) (nhds (a, b)) by
        simpa using
          (show ContinuousAt (fun t : ℝ => (a, t)) b by fun_prop)))
  have h21Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP2
      (show Filter.Tendsto (fun t : ℝ => (t, b))
          (nhds a) (nhds (a, b)) by
        simpa using
          (show ContinuousAt (fun t : ℝ => (t, b)) a by fun_prop)))
  have h12 : partial12 F a b = H (0, 1) (1, 0) := by
    unfold partial12
    rw [show deriv (fun t => partial1 F a t) b =
      deriv (fun t => fderiv ℝ G (a, t) (1, 0)) b by
        simpa [Function.comp_def] using h12Eq]
    exact h12D.deriv
  have h21 : partial21 F a b = H (1, 0) (0, 1) := by
    unfold partial21
    rw [show deriv (fun t => partial2 F t b) a =
      deriv (fun t => fderiv ℝ G (t, b) (0, 1)) a by
        simpa [Function.comp_def] using h21Eq]
    exact h21D.deriv
  rw [h12, h21]
  exact (hF.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (1, 0)

private theorem hasDerivAt_composite_x
    (F z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F)
      (arg1 z x y, arg2 z x y))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (x, y)) :
    HasDerivAt (fun t => F (t * z t y) (y * z t y))
      (F1At F z x y * (z x y + x * partialX z x y) +
        F2At F z x y * y * partialX z x y) x := by
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hzSliceDiff : DifferentiableAt ℝ (fun t => z t y) x := by
    simpa [Function.uncurry] using
      (hz.comp x hp.hasFDerivAt.differentiableAt)
  have hzLine : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using hzSliceDiff.hasDerivAt
  have ha : HasDerivAt (fun t => t * z t y)
      (z x y + x * partialX z x y) x := by
    simpa [id] using (hasDerivAt_id x).mul hzLine
  have hb : HasDerivAt (fun t => y * z t y)
      (y * partialX z x y) x :=
    hzLine.const_mul y
  have hpair : HasDerivAt
      (fun t => (t * z t y, y * z t y))
      (z x y + x * partialX z x y, y * partialX z x y) x := by
    convert (ha.hasFDerivAt.prodMk hb.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hcomp0 := hF.hasFDerivAt.comp x hpair.hasFDerivAt
  have h1 := partial1_eq_fderiv F (arg1 z x y) (arg2 z x y) hF
  have h2 := partial2_eq_fderiv F (arg1 z x y) (arg2 z x y) hF
  convert hcomp0.hasDerivAt using 1
  unfold F1At F2At evalAt
  rw [h1, h2]
  let L := fderiv ℝ (Function.uncurry F)
    (arg1 z x y, arg2 z x y)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change
    L (1, 0) * (z x y + x * partialX z x y) +
        L (0, 1) * y * partialX z x y =
      L (z x y + x * partialX z x y, y * partialX z x y)
  rw [show
    (z x y + x * partialX z x y, y * partialX z x y) =
      (z x y + x * partialX z x y) • (1, 0) +
        (y * partialX z x y) • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

private theorem secondPartials_eq_fderiv
    (F : ℝ → ℝ → ℝ) (a b : ℝ)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (a, b)) :
    let H := fderiv ℝ (fderiv ℝ (Function.uncurry F)) (a, b)
    partial11 F a b = H (1, 0) (1, 0) ∧
    partial12 F a b = H (0, 1) (1, 0) ∧
    partial21 F a b = H (1, 0) (0, 1) ∧
    partial22 F a b = H (0, 1) (0, 1) := by
  let G := Function.uncurry F
  let H := fderiv ℝ (fderiv ℝ G) (a, b)
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ G) (a, b) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hFEv := hF.eventually (by simp)
  have hP1 :
      (fun p : ℝ × ℝ => partial1 F p.1 p.2) =ᶠ[nhds (a, b)]
        (fun p => fderiv ℝ G p (1, 0)) := by
    filter_upwards [hFEv] with p hp
    convert partial1_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hP2 :
      (fun p : ℝ × ℝ => partial2 F p.1 p.2) =ᶠ[nhds (a, b)]
        (fun p => fderiv ℝ G p (0, 1)) := by
    filter_upwards [hFEv] with p hp
    convert partial2_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hEval1 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0))
      (H.flip (1, 0)) (a, b) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × ℝ) (a, b))
    convert h using 1 <;> simp [H]
  have hEval2 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (0, 1))
      (H.flip (0, 1)) (a, b) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 1) : ℝ × ℝ) (a, b))
    convert h using 1 <;> simp [H]
  have hhor : Filter.Tendsto (fun t : ℝ => (t, b))
      (nhds a) (nhds (a, b)) := by
    simpa using
      (show ContinuousAt (fun t : ℝ => (t, b)) a by fun_prop)
  have hver : Filter.Tendsto (fun t : ℝ => (a, t))
      (nhds b) (nhds (a, b)) := by
    simpa using
      (show ContinuousAt (fun t : ℝ => (a, t)) b by fun_prop)
  have h11D : HasDerivAt
      (fun t => fderiv ℝ G (t, b) (1, 0)) (H (1, 0) (1, 0)) a := by
    convert (hEval1.comp a (hasFDerivAt_prodMk_left a b)).hasDerivAt
      using 1 <;> simp
  have h12D : HasDerivAt
      (fun t => fderiv ℝ G (a, t) (1, 0)) (H (0, 1) (1, 0)) b := by
    convert (hEval1.comp b (hasFDerivAt_prodMk_right a b)).hasDerivAt
      using 1 <;> simp
  have h21D : HasDerivAt
      (fun t => fderiv ℝ G (t, b) (0, 1)) (H (1, 0) (0, 1)) a := by
    convert (hEval2.comp a (hasFDerivAt_prodMk_left a b)).hasDerivAt
      using 1 <;> simp
  have h22D : HasDerivAt
      (fun t => fderiv ℝ G (a, t) (0, 1)) (H (0, 1) (0, 1)) b := by
    convert (hEval2.comp b (hasFDerivAt_prodMk_right a b)).hasDerivAt
      using 1 <;> simp
  have h11Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP1 hhor)
  have h12Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP1 hver)
  have h21Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP2 hhor)
  have h22Eq := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hP2 hver)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold partial11
    rw [show deriv (fun t => partial1 F t b) a =
      deriv (fun t => fderiv ℝ G (t, b) (1, 0)) a by
        simpa [Function.comp_def] using h11Eq]
    exact h11D.deriv
  · unfold partial12
    rw [show deriv (fun t => partial1 F a t) b =
      deriv (fun t => fderiv ℝ G (a, t) (1, 0)) b by
        simpa [Function.comp_def] using h12Eq]
    exact h12D.deriv
  · unfold partial21
    rw [show deriv (fun t => partial2 F t b) a =
      deriv (fun t => fderiv ℝ G (t, b) (0, 1)) a by
        simpa [Function.comp_def] using h21Eq]
    exact h21D.deriv
  · unfold partial22
    rw [show deriv (fun t => partial2 F a t) b =
      deriv (fun t => fderiv ℝ G (a, t) (0, 1)) b by
        simpa [Function.comp_def] using h22Eq]
    exact h22D.deriv

private theorem hasDerivAt_partials_along
    (F : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (t a' b' : ℝ)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (a t, b t))
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => partial1 F (a s) (b s))
        (partial11 F (a t) (b t) * a' +
          partial12 F (a t) (b t) * b') t ∧
      HasDerivAt (fun s => partial2 F (a s) (b s))
        (partial21 F (a t) (b t) * a' +
          partial22 F (a t) (b t) * b') t := by
  let G := Function.uncurry F
  let H := fderiv ℝ (fderiv ℝ G) (a t, b t)
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ G) (a t, b t) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hFEv := hF.eventually (by simp)
  have hP1 :
      (fun p : ℝ × ℝ => partial1 F p.1 p.2) =ᶠ[nhds (a t, b t)]
        (fun p => fderiv ℝ G p (1, 0)) := by
    filter_upwards [hFEv] with p hp
    convert partial1_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hP2 :
      (fun p : ℝ × ℝ => partial2 F p.1 p.2) =ᶠ[nhds (a t, b t)]
        (fun p => fderiv ℝ G p (0, 1)) := by
    filter_upwards [hFEv] with p hp
    convert partial2_eq_fderiv F p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [G]
  have hpair : HasDerivAt (fun s => (a s, b s)) (a', b') t := by
    convert (ha.hasFDerivAt.prodMk hb.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hEval1 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0))
      (H.flip (1, 0)) (a t, b t) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × ℝ) (a t, b t))
    convert h using 1 <;> simp [H]
  have hEval2 : HasFDerivAt
      (fun p : ℝ × ℝ => fderiv ℝ G p (0, 1))
      (H.flip (0, 1)) (a t, b t) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 1) : ℝ × ℝ) (a t, b t))
    convert h using 1 <;> simp [H]
  have hNative1 : HasDerivAt
      (fun s => fderiv ℝ G (a s, b s) (1, 0))
      (H (a', b') (1, 0)) t := by
    convert (hEval1.comp t hpair.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hNative2 : HasDerivAt
      (fun s => fderiv ℝ G (a s, b s) (0, 1))
      (H (a', b') (0, 1)) t := by
    convert (hEval2.comp t hpair.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hP1Line := Filter.EventuallyEq.comp_tendsto hP1 hpair.continuousAt
  have hP2Line := Filter.EventuallyEq.comp_tendsto hP2 hpair.continuousAt
  have hTarget1 : HasDerivAt (fun s => partial1 F (a s) (b s))
      (H (a', b') (1, 0)) t := by
    exact HasDerivAt.congr_of_eventuallyEq hNative1
      (by simpa [Function.comp_def] using hP1Line)
  have hTarget2 : HasDerivAt (fun s => partial2 F (a s) (b s))
      (H (a', b') (0, 1)) t := by
    exact HasDerivAt.congr_of_eventuallyEq hNative2
      (by simpa [Function.comp_def] using hP2Line)
  obtain ⟨h11, h12, h21, h22⟩ :=
    secondPartials_eq_fderiv F (a t) (b t) hF
  constructor
  · convert hTarget1 using 1
    rw [h11, h12]
    rw [show (a', b') = a' • (1, 0) + b' • (0, 1) by ext <;> simp]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    simp [smul_eq_mul]
    ring
  · convert hTarget2 using 1
    rw [h21, h22]
    rw [show (a', b') = a' • (1, 0) + b' • (0, 1) by ext <;> simp]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    simp [smul_eq_mul]
    ring

theorem gap1 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (Function.uncurry F)
        (arg1 z x y, arg2 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 z p.1 p.2) (arg2 z p.1 p.2) = 0) :
    F1At F z x y * (z x y + x * partialX z x y) +
      F2At F z x y * y * partialX z x y = 0 := by
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hzSliceDiff : DifferentiableAt ℝ (fun t => z t y) x := by
    simpa [Function.uncurry] using
      (hzDiff.comp x hp.hasFDerivAt.differentiableAt)
  have hzLine : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using hzSliceDiff.hasDerivAt
  have ha : HasDerivAt (fun t => t * z t y)
      (z x y + x * partialX z x y) x := by
    simpa [id] using (hasDerivAt_id x).mul hzLine
  have hb : HasDerivAt (fun t => y * z t y)
      (y * partialX z x y) x :=
    hzLine.const_mul y
  have hpair : HasDerivAt
      (fun t => (t * z t y, y * z t y))
      (z x y + x * partialX z x y, y * partialX z x y) x :=
    by
      convert (ha.hasFDerivAt.prodMk hb.hasFDerivAt).hasDerivAt using 1 <;>
        simp
  have hcomp0 := hFDiff.hasFDerivAt.comp x hpair.hasFDerivAt
  have hcomp : HasDerivAt
      (fun t => F (t * z t y) (y * z t y))
      (F1At F z x y * (z x y + x * partialX z x y) +
        F2At F z x y * y * partialX z x y) x := by
    have h1 := partial1_eq_fderiv F (arg1 z x y) (arg2 z x y) hFDiff
    have h2 := partial2_eq_fderiv F (arg1 z x y) (arg2 z x y) hFDiff
    convert hcomp0.hasDerivAt using 1
    unfold F1At F2At evalAt
    rw [h1, h2]
    let L := fderiv ℝ (Function.uncurry F)
      (arg1 z x y, arg2 z x y)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    change
      L (1, 0) * (z x y + x * partialX z x y) +
          L (0, 1) * y * partialX z x y =
        L (z x y + x * partialX z x y, y * partialX z x y)
    rw [show
      (z x y + x * partialX z x y, y * partialX z x y) =
        (z x y + x * partialX z x y) • (1, 0) +
          (y * partialX z x y) • (0, 1) by ext <;> simp]
    simp only [map_add, map_smul]
    simp [smul_eq_mul]
    ring
  have hpath : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := by
    simpa using
      (show ContinuousAt (fun t : ℝ => (t, y)) x by fun_prop)
  have he := Filter.EventuallyEq.comp_tendsto hImplicit hpath
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv (fun t => F (t * z t y) (y * z t y)) x =
        deriv (fun _ : ℝ => 0) x := by
    simpa [Function.comp_def, arg1, arg2] using hd
  rw [hcomp.deriv] at hd'
  simpa using hd'

theorem gap2 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hDenominator : denominator F z x y ≠ 0)
    (hXIdentity :
      F1At F z x y * (z x y + x * partialX z x y) +
        F2At F z x y * y * partialX z x y = 0) :
    partialX z x y = solvedPartialX F z x y := by
  unfold solvedPartialX
  rw [eq_div_iff hDenominator]
  unfold denominator
  linear_combination hXIdentity

theorem gap3 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFC2 :
      ContDiffAt ℝ 2 (Function.uncurry F)
        (arg1 z x y, arg2 z x y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 z p.1 p.2) (arg2 z p.1 p.2) = 0)
    (hDenominator : denominator F z x y ≠ 0)
    (hXFormula : partialX z x y = solvedPartialX F z x y) :
    partialXX z x y = rawSecondX F z x y := by
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hzSliceC2 : ContDiffAt ℝ 2 (fun t => z t y) x := by
    simpa [Function.uncurry] using
      hzC2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hzLine : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using
      (hzSliceC2.differentiableAt (by decide)).hasDerivAt
  have hzDLine : HasDerivAt (fun t => partialX z t y)
      (partialXX z x y) x := by
    have hd : DifferentiableAt ℝ (deriv (fun t => z t y)) x :=
      (hzSliceC2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by decide)
    simpa [partialX, partialXX] using hd.hasDerivAt
  let a : ℝ → ℝ := fun t => t * z t y
  let b : ℝ → ℝ := fun t => y * z t y
  have ha : HasDerivAt a (z x y + x * partialX z x y) x := by
    dsimp [a]
    simpa [id] using (hasDerivAt_id x).mul hzLine
  have hb : HasDerivAt b (y * partialX z x y) x := by
    dsimp [b]
    exact hzLine.const_mul y
  have hparts := hasDerivAt_partials_along F a b x
    (z x y + x * partialX z x y) (y * partialX z x y)
    (by simpa [a, b, arg1, arg2] using hFC2) ha hb
  have hF1Line : HasDerivAt
      (fun t => F1At F z t y)
      (F11At F z x y * (z x y + x * partialX z x y) +
        F12At F z x y * y * partialX z x y) x := by
    convert hparts.1 using 1 <;>
      simp [F1At, F11At, F12At, evalAt, arg1, arg2, a, b] <;> ring
  have hF2Line : HasDerivAt
      (fun t => F2At F z t y)
      (F21At F z x y * (z x y + x * partialX z x y) +
        F22At F z x y * y * partialX z x y) x := by
    convert hparts.2 using 1 <;>
      simp [F2At, F21At, F22At, evalAt, arg1, arg2, a, b] <;> ring
  have hDenLine : HasDerivAt
      (fun t => denominator F z t y)
      (F1At F z x y +
        x * (F11At F z x y * (z x y + x * partialX z x y) +
          F12At F z x y * y * partialX z x y) +
        y * (F21At F z x y * (z x y + x * partialX z x y) +
          F22At F z x y * y * partialX z x y)) x := by
    unfold denominator
    convert ((hasDerivAt_id x).mul hF1Line).add
      (hF2Line.const_mul y) using 1 <;> simp [id] <;> ring
  have hNumLine : HasDerivAt
      (fun t => z t y * F1At F z t y)
      (F1At F z x y * partialX z x y +
        z x y *
          (F11At F z x y * (z x y + x * partialX z x y) +
            F12At F z x y * y * partialX z x y)) x := by
    convert hzLine.mul hF1Line using 1 <;> ring
  have hPairLine : HasDerivAt (fun t => (a t, b t))
      (z x y + x * partialX z x y, y * partialX z x y) x := by
    convert (ha.hasFDerivAt.prodMk hb.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hpath : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := hp.continuousAt
  rcases mem_nhds_iff.mp hImplicit with ⟨s, hsSub, hsOpen, hsMem⟩
  have hsLine : ∀ᶠ t : ℝ in nhds x, (t, y) ∈ s :=
    hpath.eventually (hsOpen.mem_nhds hsMem)
  have hFC2Line :=
    hPairLine.continuousAt.eventually (hFC2.eventually (by simp [a, b, arg1, arg2]))
  have hzC2Line := hp.continuousAt.eventually (hzC2.eventually (by simp))
  have hIdentity :
      (fun t =>
        F1At F z t y * (z t y + t * partialX z t y) +
          F2At F z t y * y * partialX z t y) =ᶠ[nhds x]
        (fun _ => 0) := by
    filter_upwards [hsLine, hFC2Line, hzC2Line] with t hts hFt hzt
    have hLocal : ∀ᶠ p : ℝ × ℝ in nhds (t, y),
        F (arg1 z p.1 p.2) (arg2 z p.1 p.2) = 0 :=
      Filter.mem_of_superset (hsOpen.mem_nhds hts) hsSub
    have htPath : Filter.Tendsto (fun r : ℝ => (r, y))
        (nhds t) (nhds (t, y)) := by
      simpa using
        (show ContinuousAt (fun r : ℝ => (r, y)) t by fun_prop)
    have hLocalLine := Filter.EventuallyEq.comp_tendsto hLocal htPath
    have hd := Filter.EventuallyEq.deriv_eq hLocalLine
    have hcomp := hasDerivAt_composite_x F z t y
      (by simpa [a, b, arg1, arg2] using
        hFt.differentiableAt (by decide))
      (hzt.differentiableAt (by decide))
    have hd' :
        deriv (fun r => F (r * z r y) (y * z r y)) t =
          deriv (fun _ : ℝ => 0) t := by
      simpa [Function.comp_def, arg1, arg2] using hd
    rw [hcomp.deriv] at hd'
    simpa using hd'
  have hDenNe := hDenLine.continuousAt.eventually_ne hDenominator
  have hSolved :
      (fun t => partialX z t y) =ᶠ[nhds x]
        (fun t => solvedPartialX F z t y) := by
    filter_upwards [hIdentity, hDenNe] with t ht hdt
    unfold solvedPartialX
    rw [eq_div_iff hdt]
    unfold denominator
    linear_combination ht
  have hSolvedDeriv := Filter.EventuallyEq.deriv_eq hSolved
  have hSolvedLine :=
    hNumLine.neg.div hDenLine hDenominator
  have hd :
      deriv (fun t => partialX z t y) x =
        deriv
          ((-(fun t => z t y * F1At F z t y)) /
            (fun t => denominator F z t y)) x := by
    simpa only [solvedPartialX, Pi.neg_apply, Pi.div_apply] using hSolvedDeriv
  rw [hSolvedLine.deriv] at hd
  unfold partialXX rawSecondX
  change deriv (fun t => partialX z t y) x = _
  rw [hd]
  simp only [Pi.neg_apply]
  field_simp [hDenominator]
  ring

theorem gap4 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFC2 :
      ContDiffAt ℝ 2 (Function.uncurry F)
        (arg1 z x y, arg2 z x y))
    (hDenominator : denominator F z x y ≠ 0)
    (hXFormula : partialX z x y = solvedPartialX F z x y)
    (hRaw : partialXX z x y = rawSecondX F z x y) :
    partialXX z x y = closedSecondX F z x y := by
  have hSym : F21At F z x y = F12At F z x y := by
    unfold F21At F12At evalAt
    exact (partial12_eq_partial21 F _ _ hFC2).symm
  rw [hRaw]
  unfold rawSecondX closedSecondX solvedPartialX denominator at *
  rw [hXFormula, hSym]
  field_simp [hDenominator]
  ring

end

end ProofGap.Exercise3398
