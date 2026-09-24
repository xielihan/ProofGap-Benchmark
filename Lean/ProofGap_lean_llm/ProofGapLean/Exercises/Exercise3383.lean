import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ProofGap.Exercise3383

noncomputable section

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z x t) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY z x t) y

def firstDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialX z x y * dx + partialY z x y * dy

def secondDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX z x y * dx ^ 2 +
    2 * partialXY z x y * dx * dy +
      partialYY z x y * dy ^ 2

def IsC2Surface (a : ℝ) (D : Set (ℝ × ℝ))
    (z : ℝ → ℝ → ℝ) : Prop :=
  IsOpen D ∧ ContDiffOn ℝ 2 (Function.uncurry z) D ∧
    ∀ p ∈ D,
      p.1 ^ 2 + p.2 ^ 2 + z p.1 p.2 ^ 2 = a ^ 2 ∧
        z p.1 p.2 ≠ 0

private lemma partialX_eq_fderiv
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    partialX z p.1 p.2 =
      fderiv ℝ (Function.uncurry z) p (1, 0) := by
  have hdiff :
      DifferentiableAt ℝ (Function.uncurry z) p :=
    (hz.contDiffAt (hD.mem_nhds hp)).differentiableAt (by decide)
  have hline :
      HasDerivAt (fun s : ℝ => (s, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt p.1 hline
  unfold partialX
  simpa [Function.comp_apply, Function.uncurry] using hc.deriv

private lemma partialY_eq_fderiv
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    partialY z p.1 p.2 =
      fderiv ℝ (Function.uncurry z) p (0, 1) := by
  have hdiff :
      DifferentiableAt ℝ (Function.uncurry z) p :=
    (hz.contDiffAt (hD.mem_nhds hp)).differentiableAt (by decide)
  have hline :
      HasDerivAt (fun s : ℝ => (p.1, s)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt p.2 hline
  unfold partialY
  simpa [Function.comp_apply, Function.uncurry] using hc.deriv

private lemma contDiffAt_xline
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    ContDiffAt ℝ 2 (fun s => z s p.2) p.1 := by
  have hcomp :=
    (hz.contDiffAt (hD.mem_nhds hp)).comp p.1
      (contDiffAt_id.prodMk contDiffAt_const)
  simpa [Function.comp_apply, Function.uncurry] using hcomp

private lemma contDiffAt_yline
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    ContDiffAt ℝ 2 (fun s => z p.1 s) p.2 := by
  have hcomp :=
    (hz.contDiffAt (hD.mem_nhds hp)).comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)
  simpa [Function.comp_apply, Function.uncurry] using hcomp

private lemma firstX_identity
    {a : ℝ} {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (h : IsC2Surface a D z) {p : ℝ × ℝ} (hp : p ∈ D) :
    p.1 + z p.1 p.2 * partialX z p.1 p.2 = 0 := by
  have hzDiff :
      DifferentiableAt ℝ (fun s => z s p.2) p.1 :=
    (contDiffAt_xline h.1 h.2.1 hp).differentiableAt (by decide)
  have hzDer :
      HasDerivAt (fun s => z s p.2) (partialX z p.1 p.2) p.1 := by
    simpa [partialX] using hzDiff.hasDerivAt
  have hcalc :=
    (((hasDerivAt_id p.1).pow 2).add
      (hasDerivAt_const p.1 (p.2 ^ 2))).add (hzDer.pow 2)
  have hmem :
      ∀ᶠ s in nhds p.1, (s, p.2) ∈ D := by
    apply (continuousAt_id.prodMk continuousAt_const).eventually_mem
    simpa using h.1.mem_nhds hp
  have heq :
      (fun s => s ^ 2 + p.2 ^ 2 + z s p.2 ^ 2) =ᶠ[nhds p.1]
        (fun _ => a ^ 2) :=
    hmem.mono fun s hs => (h.2.2 (s, p.2) hs).1
  have hzero :
      deriv (fun s => s ^ 2 + p.2 ^ 2 + z s p.2 ^ 2) p.1 = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcalc' :
      deriv (fun s => s ^ 2 + p.2 ^ 2 + z s p.2 ^ 2) p.1 =
        2 * p.1 + 2 * z p.1 p.2 * partialX z p.1 p.2 := by
    convert hcalc.deriv using 1
    all_goals simp
  rw [hcalc'] at hzero
  nlinarith

private lemma firstY_identity
    {a : ℝ} {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (h : IsC2Surface a D z) {p : ℝ × ℝ} (hp : p ∈ D) :
    p.2 + z p.1 p.2 * partialY z p.1 p.2 = 0 := by
  have hzDiff :
      DifferentiableAt ℝ (fun s => z p.1 s) p.2 :=
    (contDiffAt_yline h.1 h.2.1 hp).differentiableAt (by decide)
  have hzDer :
      HasDerivAt (fun s => z p.1 s) (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzDiff.hasDerivAt
  have hcalc :=
    (((hasDerivAt_const p.2 (p.1 ^ 2)).add
      ((hasDerivAt_id p.2).pow 2)).add (hzDer.pow 2))
  have hmem :
      ∀ᶠ s in nhds p.2, (p.1, s) ∈ D := by
    apply (continuousAt_const.prodMk continuousAt_id).eventually_mem
    simpa using h.1.mem_nhds hp
  have heq :
      (fun s => p.1 ^ 2 + s ^ 2 + z p.1 s ^ 2) =ᶠ[nhds p.2]
        (fun _ => a ^ 2) :=
    hmem.mono fun s hs => (h.2.2 (p.1, s) hs).1
  have hzero :
      deriv (fun s => p.1 ^ 2 + s ^ 2 + z p.1 s ^ 2) p.2 = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcalc' :
      deriv (fun s => p.1 ^ 2 + s ^ 2 + z p.1 s ^ 2) p.2 =
        2 * p.2 + 2 * z p.1 p.2 * partialY z p.1 p.2 := by
    convert hcalc.deriv using 1
    all_goals simp
  rw [hcalc'] at hzero
  nlinarith

private lemma differentiableAt_partialX_x
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    DifferentiableAt ℝ (fun s => partialX z s p.2) p.1 := by
  have hd :
      ContDiffAt ℝ 1 (deriv (fun s => z s p.2)) p.1 :=
    (contDiffAt_xline hD hz hp).derivWithin (by decide)
  have hd' :
      ContDiffAt ℝ 1 (fun s => partialX z s p.2) p.1 := by
    simpa [partialX] using hd
  exact hd'.differentiableAt (by decide)

private lemma differentiableAt_partialY_y
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    DifferentiableAt ℝ (fun s => partialY z p.1 s) p.2 := by
  have hd :
      ContDiffAt ℝ 1 (deriv (fun s => z p.1 s)) p.2 :=
    (contDiffAt_yline hD hz hp).derivWithin (by decide)
  have hd' :
      ContDiffAt ℝ 1 (fun s => partialY z p.1 s) p.2 := by
    simpa [partialY] using hd
  exact hd'.differentiableAt (by decide)

private lemma differentiableAt_partialX_y
    {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (hD : IsOpen D)
    (hz : ContDiffOn ℝ 2 (Function.uncurry z) D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    DifferentiableAt ℝ (fun s => partialX z p.1 s) p.2 := by
  have hF :
      ContDiffAt ℝ 2 (Function.uncurry z) p :=
    hz.contDiffAt (hD.mem_nhds hp)
  have hFD :
      ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry z)) p :=
    hF.fderiv_right (by decide)
  have hproxyPlane :
      ContDiffAt ℝ 1
        (fun q => fderiv ℝ (Function.uncurry z) q (1, 0)) p :=
    hFD.clm_apply contDiffAt_const
  have hproxy :
      ContDiffAt ℝ 1
        (fun s => fderiv ℝ (Function.uncurry z) (p.1, s) (1, 0)) p.2 := by
    have hcomp :=
      hproxyPlane.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
    simpa [Function.comp_apply] using hcomp
  have hmem :
      ∀ᶠ s in nhds p.2, (p.1, s) ∈ D := by
    apply (continuousAt_const.prodMk continuousAt_id).eventually_mem
    simpa using hD.mem_nhds hp
  have heq :
      (fun s => partialX z p.1 s) =ᶠ[nhds p.2]
        (fun s => fderiv ℝ (Function.uncurry z) (p.1, s) (1, 0)) :=
    hmem.mono fun s hs => partialX_eq_fderiv hD hz hs
  exact (hproxy.congr_of_eventuallyEq heq).differentiableAt (by decide)

private lemma secondXX_identity
    {a : ℝ} {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (h : IsC2Surface a D z) {p : ℝ × ℝ} (hp : p ∈ D) :
    1 + partialX z p.1 p.2 ^ 2 +
        z p.1 p.2 * partialXX z p.1 p.2 = 0 := by
  have hzDiff :
      DifferentiableAt ℝ (fun s => z s p.2) p.1 :=
    (contDiffAt_xline h.1 h.2.1 hp).differentiableAt (by decide)
  have hxDiff :=
    differentiableAt_partialX_x h.1 h.2.1 hp
  have hzDer :
      HasDerivAt (fun s => z s p.2) (partialX z p.1 p.2) p.1 := by
    simpa [partialX] using hzDiff.hasDerivAt
  have hxDer :
      HasDerivAt (fun s => partialX z s p.2) (partialXX z p.1 p.2) p.1 := by
    simpa [partialXX] using hxDiff.hasDerivAt
  have hcalc := (hasDerivAt_id p.1).add (hzDer.mul hxDer)
  have hmem :
      ∀ᶠ s in nhds p.1, (s, p.2) ∈ D := by
    apply (continuousAt_id.prodMk continuousAt_const).eventually_mem
    simpa using h.1.mem_nhds hp
  have heq :
      (fun s => s + z s p.2 * partialX z s p.2) =ᶠ[nhds p.1]
        (fun _ => 0) :=
    hmem.mono fun s hs => firstX_identity h hs
  have hzero :
      deriv (fun s => s + z s p.2 * partialX z s p.2) p.1 = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcalc' :
      deriv (fun s => s + z s p.2 * partialX z s p.2) p.1 =
        1 + partialX z p.1 p.2 ^ 2 +
          z p.1 p.2 * partialXX z p.1 p.2 := by
    have hfun :
        (fun s => s + z s p.2 * partialX z s p.2) =
          id + (fun s => z s p.2) * fun s => partialX z s p.2 := by
      funext s
      rfl
    rw [hfun]
    convert hcalc.deriv using 1
    all_goals ring
  rwa [hcalc'] at hzero

private lemma secondXY_identity
    {a : ℝ} {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (h : IsC2Surface a D z) {p : ℝ × ℝ} (hp : p ∈ D) :
    partialX z p.1 p.2 * partialY z p.1 p.2 +
        z p.1 p.2 * partialXY z p.1 p.2 = 0 := by
  have hzDiff :
      DifferentiableAt ℝ (fun s => z p.1 s) p.2 :=
    (contDiffAt_yline h.1 h.2.1 hp).differentiableAt (by decide)
  have hxDiff :=
    differentiableAt_partialX_y h.1 h.2.1 hp
  have hzDer :
      HasDerivAt (fun s => z p.1 s) (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzDiff.hasDerivAt
  have hxDer :
      HasDerivAt (fun s => partialX z p.1 s) (partialXY z p.1 p.2) p.2 := by
    simpa [partialXY] using hxDiff.hasDerivAt
  have hcalc :=
    (hasDerivAt_const p.2 p.1).add (hzDer.mul hxDer)
  have hmem :
      ∀ᶠ s in nhds p.2, (p.1, s) ∈ D := by
    apply (continuousAt_const.prodMk continuousAt_id).eventually_mem
    simpa using h.1.mem_nhds hp
  have heq :
      (fun s => p.1 + z p.1 s * partialX z p.1 s) =ᶠ[nhds p.2]
        (fun _ => 0) :=
    hmem.mono fun s hs => firstX_identity h hs
  have hzero :
      deriv (fun s => p.1 + z p.1 s * partialX z p.1 s) p.2 = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcalc' :
      deriv (fun s => p.1 + z p.1 s * partialX z p.1 s) p.2 =
        partialX z p.1 p.2 * partialY z p.1 p.2 +
          z p.1 p.2 * partialXY z p.1 p.2 := by
    have hfun :
        (fun s => p.1 + z p.1 s * partialX z p.1 s) =
          (fun _ => p.1) +
            (fun s => z p.1 s) * fun s => partialX z p.1 s := by
      funext s
      rfl
    rw [hfun]
    convert hcalc.deriv using 1
    all_goals ring
  rw [hcalc'] at hzero
  nlinarith

private lemma secondYY_identity
    {a : ℝ} {D : Set (ℝ × ℝ)} {z : ℝ → ℝ → ℝ}
    (h : IsC2Surface a D z) {p : ℝ × ℝ} (hp : p ∈ D) :
    1 + partialY z p.1 p.2 ^ 2 +
        z p.1 p.2 * partialYY z p.1 p.2 = 0 := by
  have hzDiff :
      DifferentiableAt ℝ (fun s => z p.1 s) p.2 :=
    (contDiffAt_yline h.1 h.2.1 hp).differentiableAt (by decide)
  have hyDiff :=
    differentiableAt_partialY_y h.1 h.2.1 hp
  have hzDer :
      HasDerivAt (fun s => z p.1 s) (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzDiff.hasDerivAt
  have hyDer :
      HasDerivAt (fun s => partialY z p.1 s) (partialYY z p.1 p.2) p.2 := by
    simpa [partialYY] using hyDiff.hasDerivAt
  have hcalc :=
    (hasDerivAt_id p.2).add (hzDer.mul hyDer)
  have hmem :
      ∀ᶠ s in nhds p.2, (p.1, s) ∈ D := by
    apply (continuousAt_const.prodMk continuousAt_id).eventually_mem
    simpa using h.1.mem_nhds hp
  have heq :
      (fun s => s + z p.1 s * partialY z p.1 s) =ᶠ[nhds p.2]
        (fun _ => 0) :=
    hmem.mono fun s hs => firstY_identity h hs
  have hzero :
      deriv (fun s => s + z p.1 s * partialY z p.1 s) p.2 = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcalc' :
      deriv (fun s => s + z p.1 s * partialY z p.1 s) p.2 =
        1 + partialY z p.1 p.2 ^ 2 +
          z p.1 p.2 * partialYY z p.1 p.2 := by
    have hfun :
        (fun s => s + z p.1 s * partialY z p.1 s) =
          id + (fun s => z p.1 s) * fun s => partialY z p.1 s := by
      funext s
      rfl
    rw [hfun]
    convert hcalc.deriv using 1
    all_goals ring
  rwa [hcalc'] at hzero

theorem gap1 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      p.1 * dx + p.2 * dy +
        z p.1 p.2 * firstDifferential z p.1 p.2 dx dy = 0 := by
  intro p hp dx dy
  have hx := firstX_identity h hp
  have hy := firstY_identity h hp
  unfold firstDifferential
  calc
    p.1 * dx + p.2 * dy +
          z p.1 p.2 *
            (partialX z p.1 p.2 * dx + partialY z p.1 p.2 * dy) =
        dx * (p.1 + z p.1 p.2 * partialX z p.1 p.2) +
          dy * (p.2 + z p.1 p.2 * partialY z p.1 p.2) := by ring
    _ = 0 := by rw [hx, hy]; ring

theorem gap2 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      dx ^ 2 + dy ^ 2 +
        (firstDifferential z p.1 p.2 dx dy) ^ 2 +
        z p.1 p.2 * secondDifferential z p.1 p.2 dx dy = 0 := by
  intro p hp dx dy
  have hxx := secondXX_identity h hp
  have hxy := secondXY_identity h hp
  have hyy := secondYY_identity h hp
  unfold firstDifferential secondDifferential
  calc
    dx ^ 2 + dy ^ 2 +
          (partialX z p.1 p.2 * dx + partialY z p.1 p.2 * dy) ^ 2 +
          z p.1 p.2 *
            (partialXX z p.1 p.2 * dx ^ 2 +
              2 * partialXY z p.1 p.2 * dx * dy +
                partialYY z p.1 p.2 * dy ^ 2) =
        dx ^ 2 *
            (1 + partialX z p.1 p.2 ^ 2 +
              z p.1 p.2 * partialXX z p.1 p.2) +
          2 * dx * dy *
            (partialX z p.1 p.2 * partialY z p.1 p.2 +
              z p.1 p.2 * partialXY z p.1 p.2) +
          dy ^ 2 *
            (1 + partialY z p.1 p.2 ^ 2 +
              z p.1 p.2 * partialYY z p.1 p.2) := by ring
    _ = 0 := by rw [hxx, hxy, hyy]; ring

theorem gap3 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential z p.1 p.2 dx dy =
        -(p.1 / z p.1 p.2) * dx -
          (p.2 / z p.1 p.2) * dy := by
  intro p hp dx dy
  have hfirst := gap1 a D z h p hp dx dy
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  unfold firstDifferential at hfirst ⊢
  field_simp [hz]
  nlinarith

theorem gap4 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 = -(p.1 / z p.1 p.2) := by
  intro p hp
  have hg := gap3 a D z h p hp 1 0
  simpa [firstDifferential] using hg

theorem gap5 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialY z p.1 p.2 = -(p.2 / z p.1 p.2) := by
  intro p hp
  have hg := gap3 a D z h p hp 0 1
  simpa [firstDifferential] using hg

theorem gap6 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        -(1 / z p.1 p.2) *
          (dx ^ 2 + dy ^ 2 +
            (firstDifferential z p.1 p.2 dx dy) ^ 2) := by
  intro p hp dx dy
  have hsecond := gap2 a D z h p hp dx dy
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  field_simp [hz]
  nlinarith

theorem gap7 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      -(1 / z p.1 p.2) *
          (dx ^ 2 + dy ^ 2 +
            ((p.1 / z p.1 p.2) * dx +
              (p.2 / z p.1 p.2) * dy) ^ 2) =
        -(1 / z p.1 p.2) * dx ^ 2 -
          (1 / z p.1 p.2) * dy ^ 2 -
          (1 / z p.1 p.2) *
            ((p.1 / z p.1 p.2) * dx +
              (p.2 / z p.1 p.2) * dy) ^ 2 := by
  intro p _ dx dy
  ring

theorem gap8 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        -(1 / z p.1 p.2) * dx ^ 2 -
          (1 / z p.1 p.2) * dy ^ 2 -
          (1 / z p.1 p.2) *
            ((p.1 / z p.1 p.2) * dx +
              (p.2 / z p.1 p.2) * dy) ^ 2 := by
  intro p hp dx dy
  rw [gap6 a D z h p hp dx dy, gap3 a D z h p hp dx dy]
  convert gap7 a D z h p hp dx dy using 1
  all_goals ring

theorem gap9 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        -(1 / z p.1 p.2 * (1 + p.1 ^ 2 / z p.1 p.2 ^ 2)) *
            dx ^ 2 -
          (2 * p.1 * p.2 / z p.1 p.2 ^ 3) * dx * dy -
          (1 / z p.1 p.2 * (1 + p.2 ^ 2 / z p.1 p.2 ^ 2)) *
            dy ^ 2 := by
  intro p hp dx dy
  rw [gap8 a D z h p hp dx dy]
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  field_simp [hz]
  ring

theorem gap10 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 =
        -(z p.1 p.2 ^ 2 + p.1 ^ 2) / z p.1 p.2 ^ 3 := by
  intro p hp
  have hxx := secondXX_identity h hp
  rw [gap4 a D z h p hp] at hxx
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  field_simp [hz] at hxx ⊢
  nlinarith

theorem gap11 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialXY z p.1 p.2 =
        -(p.1 * p.2) / z p.1 p.2 ^ 3 := by
  intro p hp
  have hxy := secondXY_identity h hp
  rw [gap4 a D z h p hp, gap5 a D z h p hp] at hxy
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  field_simp [hz] at hxy ⊢
  nlinarith

theorem gap12 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialYY z p.1 p.2 =
        -(z p.1 p.2 ^ 2 + p.2 ^ 2) / z p.1 p.2 ^ 3 := by
  intro p hp
  have hyy := secondYY_identity h hp
  rw [gap5 a D z h p hp] at hyy
  have hz : z p.1 p.2 ≠ 0 := (h.2.2 p hp).2
  field_simp [hz] at hyy ⊢
  nlinarith

end

end ProofGap.Exercise3383
