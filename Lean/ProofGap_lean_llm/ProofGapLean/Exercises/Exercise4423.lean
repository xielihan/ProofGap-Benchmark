import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace ProofGap.Exercise4423

noncomputable section

open Filter
open scoped Topology

abbrev Vec3 := ℝ × ℝ × ℝ

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def curl (w : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (partialY (fun q => (w q).2.2) p - partialZ (fun q => (w q).2.1) p,
    partialZ (fun q => (w q).1) p - partialX (fun q => (w q).2.2) p,
    partialX (fun q => (w q).2.1) p - partialY (fun q => (w q).1) p)

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

def C2At (w : Vec3 → Vec3) (p : Vec3) : Prop :=
  ContDiffAt ℝ 2 w p

private def eX : Vec3 := (1, 0, 0)
private def eY : Vec3 := (0, 1, 0)
private def eZ : Vec3 := (0, 0, 1)

private lemma partialX_eq_fderiv (f : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) :
    partialX f p = fderiv ℝ f p eX := by
  unfold partialX
  have hs :
      HasFDerivAt (fun x : ℝ => (x, p.2.1, p.2.2))
        ((1 : ℝ →L[ℝ] ℝ).prod
          ((0 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) p.1 := by
    fun_prop
  have hc := hf.hasFDerivAt.comp p.1 hs
  simpa [eX] using hc.hasDerivAt.deriv

private lemma partialY_eq_fderiv (f : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) :
    partialY f p = fderiv ℝ f p eY := by
  unfold partialY
  have hs :
      HasFDerivAt (fun y : ℝ => (p.1, y, p.2.2))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) p.2.1 := by
    fun_prop
  have hc := hf.hasFDerivAt.comp p.2.1 hs
  simpa [eY] using hc.hasDerivAt.deriv

private lemma partialZ_eq_fderiv (f : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) :
    partialZ f p = fderiv ℝ f p eZ := by
  unfold partialZ
  have hs :
      HasFDerivAt (fun z : ℝ => (p.1, p.2.1, z))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) p.2.2 := by
    fun_prop
  have hc := hf.hasFDerivAt.comp p.2.2 hs
  simpa [eZ] using hc.hasDerivAt.deriv

private lemma fderiv_apply_const (f : Vec3 → ℝ) (p v w : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    fderiv ℝ (fun q => fderiv ℝ f q w) p v =
      fderiv ℝ (fderiv ℝ f) p v w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hc (differentiableAt_const w)]
  simp

private lemma partialX_partialY (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialX (fun q => partialY f q) p =
      fderiv ℝ (fderiv ℝ f) p eX eY := by
  have hEq :
      (fun q => partialY f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eY) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialY_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialX_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eX eY hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eY) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma partialY_partialX (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialY (fun q => partialX f q) p =
      fderiv ℝ (fderiv ℝ f) p eY eX := by
  have hEq :
      (fun q => partialX f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eX) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialX_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialY_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eY eX hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eX) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma mixedXY (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialX (fun q => partialY f q) p =
      partialY (fun q => partialX f q) p := by
  rw [partialX_partialY f p hf, partialY_partialX f p hf]
  exact hf.isSymmSndFDerivAt (by simp) eX eY

private lemma partialX_partialZ (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialX (fun q => partialZ f q) p =
      fderiv ℝ (fderiv ℝ f) p eX eZ := by
  have hEq :
      (fun q => partialZ f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eZ) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialZ_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialX_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eX eZ hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eZ) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma partialZ_partialX (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialZ (fun q => partialX f q) p =
      fderiv ℝ (fderiv ℝ f) p eZ eX := by
  have hEq :
      (fun q => partialX f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eX) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialX_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialZ_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eZ eX hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eX) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma mixedXZ (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialX (fun q => partialZ f q) p =
      partialZ (fun q => partialX f q) p := by
  rw [partialX_partialZ f p hf, partialZ_partialX f p hf]
  exact hf.isSymmSndFDerivAt (by simp) eX eZ

private lemma partialY_partialZ (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialY (fun q => partialZ f q) p =
      fderiv ℝ (fderiv ℝ f) p eY eZ := by
  have hEq :
      (fun q => partialZ f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eZ) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialZ_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialY_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eY eZ hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eZ) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma partialZ_partialY (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialZ (fun q => partialY f q) p =
      fderiv ℝ (fderiv ℝ f) p eZ eY := by
  have hEq :
      (fun q => partialY f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eY) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialY_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  rw [partialZ_eq_fderiv]
  · rw [hEq.fderiv_eq]
    exact fderiv_apply_const f p eZ eY hf
  · have hd :
        DifferentiableAt ℝ (fun q => fderiv ℝ f q eY) p := by
      fun_prop
    exact hd.congr_of_eventuallyEq hEq

private lemma mixedYZ (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    partialY (fun q => partialZ f q) p =
      partialZ (fun q => partialY f q) p := by
  rw [partialY_partialZ f p hf, partialZ_partialY f p hf]
  exact hf.isSymmSndFDerivAt (by simp) eY eZ

private lemma partialX_sub (f g : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    partialX (fun q => f q - g q) p = partialX f p - partialX g p := by
  unfold partialX
  simpa only using
    deriv_sub (hf.comp p.1 (by fun_prop)) (hg.comp p.1 (by fun_prop))

private lemma partialY_sub (f g : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    partialY (fun q => f q - g q) p = partialY f p - partialY g p := by
  unfold partialY
  simpa only using
    deriv_sub (hf.comp p.2.1 (by fun_prop)) (hg.comp p.2.1 (by fun_prop))

private lemma partialZ_sub (f g : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    partialZ (fun q => f q - g q) p = partialZ f p - partialZ g p := by
  unfold partialZ
  simpa only using
    deriv_sub (hf.comp p.2.2 (by fun_prop)) (hg.comp p.2.2 (by fun_prop))

private lemma differentiableAt_partialX (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (fun q => partialX f q) p := by
  have hEq :
      (fun q => partialX f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eX) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialX_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q eX) p := by
    fun_prop
  exact hd.congr_of_eventuallyEq hEq

private lemma differentiableAt_partialY (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (fun q => partialY f q) p := by
  have hEq :
      (fun q => partialY f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eY) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialY_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q eY) p := by
    fun_prop
  exact hd.congr_of_eventuallyEq hEq

private lemma differentiableAt_partialZ (f : Vec3 → ℝ) (p : Vec3)
    (hf : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (fun q => partialZ f q) p := by
  have hEq :
      (fun q => partialZ f q) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q eZ) := by
    filter_upwards [hf.eventually (by simp)] with q hq
    exact partialZ_eq_fderiv f q (hq.differentiableAt two_ne_zero)
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q eZ) p := by
    fun_prop
  exact hd.congr_of_eventuallyEq hEq

theorem gap1 (w : Vec3 → Vec3) (p : Vec3) :
    curl w p =
      (partialY (fun q => (w q).2.2) p - partialZ (fun q => (w q).2.1) p,
        partialZ (fun q => (w q).1) p - partialX (fun q => (w q).2.2) p,
        partialX (fun q => (w q).2.1) p - partialY (fun q => (w q).1) p) := by
  rfl

theorem gap2 (w : Vec3 → Vec3) (p : Vec3) :
    divergence (curl w) p =
      partialX
          (fun q =>
            partialY (fun s => (w s).2.2) q -
              partialZ (fun s => (w s).2.1) q) p +
        partialY
          (fun q =>
            partialZ (fun s => (w s).1) q -
              partialX (fun s => (w s).2.2) q) p +
        partialZ
          (fun q =>
            partialX (fun s => (w s).2.1) q -
              partialY (fun s => (w s).1) q) p := by
  rfl

theorem gap3 (w : Vec3 → Vec3) (p : Vec3) (hw : C2At w p) :
    partialX
          (fun q =>
            partialY (fun s => (w s).2.2) q -
              partialZ (fun s => (w s).2.1) q) p +
        partialY
          (fun q =>
            partialZ (fun s => (w s).1) q -
              partialX (fun s => (w s).2.2) q) p +
        partialZ
          (fun q =>
            partialX (fun s => (w s).2.1) q -
              partialY (fun s => (w s).1) q) p =
      0 := by
  have h1 : ContDiffAt ℝ 2 (fun q => (w q).1) p := hw.fst
  have h2 : ContDiffAt ℝ 2 (fun q => (w q).2.1) p := hw.snd.fst
  have h3 : ContDiffAt ℝ 2 (fun q => (w q).2.2) p := hw.snd.snd
  rw [partialX_sub _ _ p
        (differentiableAt_partialY _ p h3)
        (differentiableAt_partialZ _ p h2),
      partialY_sub _ _ p
        (differentiableAt_partialZ _ p h1)
        (differentiableAt_partialX _ p h3),
      partialZ_sub _ _ p
        (differentiableAt_partialX _ p h2)
        (differentiableAt_partialY _ p h1)]
  rw [mixedXY _ p h3, mixedXZ _ p h2, mixedYZ _ p h1]
  ring

theorem gap4 (w : Vec3 → Vec3) (p : Vec3) (hw : C2At w p) :
    divergence (curl w) p = 0 := by
  rw [gap2]
  exact gap3 w p hw

end

end ProofGap.Exercise4423
