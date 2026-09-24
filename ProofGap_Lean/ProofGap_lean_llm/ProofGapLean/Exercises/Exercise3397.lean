import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3397

noncomputable section

def uncurry3 (F : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  F p.1 p.2.1 p.2.2

def partial1 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F t b c) a

def partial2 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F a t c) b

def partial3 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F a b t) c

def partial11 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 F t b c) a

def partial12 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 F a t c) b

def partial13 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 F a b t) c

def partial21 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 F t b c) a

def partial22 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 F a t c) b

def partial23 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 F a b t) c

def partial31 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial3 F t b c) a

def partial32 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial3 F a t c) b

def partial33 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial3 F a b t) c

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def arg1 (x _y : ℝ) : ℝ := x

def arg2 (x y : ℝ) : ℝ := x + y

def arg3 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x + y + z x y

def evalAt (G : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  G (arg1 x y) (arg2 x y) (arg3 z x y)

def F1At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial1 F)
def F2At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial2 F)
def F3At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial3 F)
def F11At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial11 F)
def F12At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial12 F)
def F13At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial13 F)
def F21At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial21 F)
def F22At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial22 F)
def F23At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial23 F)
def F31At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial31 F)
def F32At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial32 F)
def F33At (F : ℝ → ℝ → ℝ → ℝ) := evalAt (partial33 F)

def solvedPartialX (F : ℝ → ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(1 + (F1At F z x y + F2At F z x y) / F3At F z x y)

def solvedPartialY (F : ℝ → ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(1 + F2At F z x y / F3At F z x y)

def rawSecondX (F : ℝ → ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(1 / (F3At F z x y) ^ 2) *
    (F3At F z x y *
        (F11At F z x y + F12At F z x y +
          F13At F z x y * (1 + partialX z x y) +
          F21At F z x y + F22At F z x y +
          F23At F z x y * (1 + partialX z x y)) -
      (F1At F z x y + F2At F z x y) *
        (F31At F z x y + F32At F z x y +
          F33At F z x y * (1 + partialX z x y)))

def closedSecondX (F : ℝ → ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -((F3At F z x y) ^ 2 *
        (F11At F z x y + 2 * F12At F z x y + F22At F z x y) -
      2 * (F1At F z x y + F2At F z x y) * F3At F z x y *
        (F13At F z x y + F23At F z x y) +
      (F1At F z x y + F2At F z x y) ^ 2 * F33At F z x y) /
    (F3At F z x y) ^ 3

private theorem partial1_eq_fderiv (F : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) (hF : DifferentiableAt ℝ (uncurry3 F) (a, b, c)) :
    partial1 F a b c = fderiv ℝ (uncurry3 F) (a, b, c) (1, 0, 0) := by
  unfold partial1
  have hp : HasDerivAt (fun t : ℝ => (t, b, c)) (1, 0, 0) a :=
    (hasDerivAt_id a).prodMk
      ((hasDerivAt_const a b).prodMk (hasDerivAt_const a c))
  have h := (hF.hasFDerivAt.comp a hp.hasFDerivAt).hasDerivAt.deriv
  simpa [uncurry3] using h

private theorem partial2_eq_fderiv (F : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) (hF : DifferentiableAt ℝ (uncurry3 F) (a, b, c)) :
    partial2 F a b c = fderiv ℝ (uncurry3 F) (a, b, c) (0, 1, 0) := by
  unfold partial2
  have hp : HasDerivAt (fun t : ℝ => (a, t, c)) (0, 1, 0) b :=
    (hasDerivAt_const b a).prodMk
      ((hasDerivAt_id b).prodMk (hasDerivAt_const b c))
  have h := (hF.hasFDerivAt.comp b hp.hasFDerivAt).hasDerivAt.deriv
  simpa [uncurry3] using h

private theorem partial3_eq_fderiv (F : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) (hF : DifferentiableAt ℝ (uncurry3 F) (a, b, c)) :
    partial3 F a b c = fderiv ℝ (uncurry3 F) (a, b, c) (0, 0, 1) := by
  unfold partial3
  have hp : HasDerivAt (fun t : ℝ => (a, b, t)) (0, 0, 1) c :=
    (hasDerivAt_const c a).prodMk
      ((hasDerivAt_const c b).prodMk (hasDerivAt_id c))
  have h := (hF.hasFDerivAt.comp c hp.hasFDerivAt).hasDerivAt.deriv
  simpa [uncurry3] using h

private theorem hasDerivAt_outer_triple
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ)
    (t da db dc : ℝ)
    (hF : DifferentiableAt ℝ (uncurry3 F) (a t, b t, c t))
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => F (a s) (b s) (c s))
      (partial1 F (a t) (b t) (c t) * da +
        partial2 F (a t) (b t) (c t) * db +
        partial3 F (a t) (b t) (c t) * dc) t := by
  have hp : HasDerivAt (fun s => (a s, b s, c s)) (da, db, dc) t := by
    convert (ha.hasFDerivAt.prodMk
      (hb.hasFDerivAt.prodMk hc.hasFDerivAt)).hasDerivAt using 1 <;> simp
  have hraw : HasDerivAt (fun s => F (a s) (b s) (c s))
      (fderiv ℝ (uncurry3 F) (a t, b t, c t) (da, db, dc)) t := by
    convert (hF.hasFDerivAt.comp t hp.hasFDerivAt).hasDerivAt using 1 <;>
      simp [uncurry3]
  convert hraw using 1
  rw [partial1_eq_fderiv F _ _ _ hF, partial2_eq_fderiv F _ _ _ hF,
    partial3_eq_fderiv F _ _ _ hF]
  let L := fderiv ℝ (uncurry3 F) (a t, b t, c t)
  change L (1, 0, 0) * da + L (0, 1, 0) * db + L (0, 0, 1) * dc =
    L (da, db, dc)
  rw [show (da, db, dc) =
    da • (1, 0, 0) + db • (0, 1, 0) + dc • (0, 0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

private theorem partials_differentiableAt
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hF : ContDiffAt ℝ 2 (uncurry3 F) (a, b, c)) :
    DifferentiableAt ℝ (uncurry3 (partial1 F)) (a, b, c) ∧
      DifferentiableAt ℝ (uncurry3 (partial2 F)) (a, b, c) ∧
      DifferentiableAt ℝ (uncurry3 (partial3 F)) (a, b, c) := by
  let G := uncurry3 F
  have hDf : DifferentiableAt ℝ (fderiv ℝ G) (a, b, c) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hEv := hF.eventually (by simp)
  have hP1 :
      uncurry3 (partial1 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (1, 0, 0)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using
      partial1_eq_fderiv F p.1 p.2.1 p.2.2
        (by simpa [uncurry3] using hp.differentiableAt (by decide))
  have hP2 :
      uncurry3 (partial2 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (0, 1, 0)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using
      partial2_eq_fderiv F p.1 p.2.1 p.2.2
        (by simpa [uncurry3] using hp.differentiableAt (by decide))
  have hP3 :
      uncurry3 (partial3 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (0, 0, 1)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using
      partial3_eq_fderiv F p.1 p.2.1 p.2.2
        (by simpa [uncurry3] using hp.differentiableAt (by decide))
  have hd1 : DifferentiableAt ℝ
      (fun p => fderiv ℝ G p (1, 0, 0)) (a, b, c) :=
    (hDf.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1, 0, 0) : ℝ × ℝ × ℝ) (a, b, c))).differentiableAt
  have hd2 : DifferentiableAt ℝ
      (fun p => fderiv ℝ G p (0, 1, 0)) (a, b, c) :=
    (hDf.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 1, 0) : ℝ × ℝ × ℝ) (a, b, c))).differentiableAt
  have hd3 : DifferentiableAt ℝ
      (fun p => fderiv ℝ G p (0, 0, 1)) (a, b, c) :=
    (hDf.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 0, 1) : ℝ × ℝ × ℝ) (a, b, c))).differentiableAt
  exact ⟨hd1.congr_of_eventuallyEq hP1, hd2.congr_of_eventuallyEq hP2,
    hd3.congr_of_eventuallyEq hP3⟩

private theorem mixed_partials
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hF : ContDiffAt ℝ 2 (uncurry3 F) (a, b, c)) :
    partial12 F a b c = partial21 F a b c ∧
      partial13 F a b c = partial31 F a b c ∧
      partial23 F a b c = partial32 F a b c := by
  let G := uncurry3 F
  let H := fderiv ℝ (fderiv ℝ G) (a, b, c)
  have hDf : DifferentiableAt ℝ (fderiv ℝ G) (a, b, c) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hEv := hF.eventually (by simp)
  have hP1 :
      uncurry3 (partial1 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (1, 0, 0)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using partial1_eq_fderiv F p.1 p.2.1 p.2.2
      (by simpa [uncurry3] using hp.differentiableAt (by decide))
  have hP2 :
      uncurry3 (partial2 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (0, 1, 0)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using partial2_eq_fderiv F p.1 p.2.1 p.2.2
      (by simpa [uncurry3] using hp.differentiableAt (by decide))
  have hP3 :
      uncurry3 (partial3 F) =ᶠ[nhds (a, b, c)]
        (fun p => fderiv ℝ G p (0, 0, 1)) := by
    filter_upwards [hEv] with p hp
    simpa [uncurry3, G] using partial3_eq_fderiv F p.1 p.2.1 p.2.2
      (by simpa [uncurry3] using hp.differentiableAt (by decide))
  obtain ⟨hd1, hd2, hd3⟩ := partials_differentiableAt F a b c hF
  have he1 := hDf.hasFDerivAt.clm_apply
    (hasFDerivAt_const ((1, 0, 0) : ℝ × ℝ × ℝ) (a, b, c))
  have he2 := hDf.hasFDerivAt.clm_apply
    (hasFDerivAt_const ((0, 1, 0) : ℝ × ℝ × ℝ) (a, b, c))
  have he3 := hDf.hasFDerivAt.clm_apply
    (hasFDerivAt_const ((0, 0, 1) : ℝ × ℝ × ℝ) (a, b, c))
  have entry12 : partial12 F a b c = H (0, 1, 0) (1, 0, 0) := by
    rw [show partial12 F a b c = partial2 (partial1 F) a b c by rfl]
    rw [partial2_eq_fderiv (partial1 F) a b c hd1, hP1.fderiv_eq]
    rw [he1.fderiv]
    simp [H]
  have entry21 : partial21 F a b c = H (1, 0, 0) (0, 1, 0) := by
    rw [show partial21 F a b c = partial1 (partial2 F) a b c by rfl]
    rw [partial1_eq_fderiv (partial2 F) a b c hd2, hP2.fderiv_eq]
    rw [he2.fderiv]
    simp [H]
  have entry13 : partial13 F a b c = H (0, 0, 1) (1, 0, 0) := by
    rw [show partial13 F a b c = partial3 (partial1 F) a b c by rfl]
    rw [partial3_eq_fderiv (partial1 F) a b c hd1, hP1.fderiv_eq]
    rw [he1.fderiv]
    simp [H]
  have entry31 : partial31 F a b c = H (1, 0, 0) (0, 0, 1) := by
    rw [show partial31 F a b c = partial1 (partial3 F) a b c by rfl]
    rw [partial1_eq_fderiv (partial3 F) a b c hd3, hP3.fderiv_eq]
    rw [he3.fderiv]
    simp [H]
  have entry23 : partial23 F a b c = H (0, 0, 1) (0, 1, 0) := by
    rw [show partial23 F a b c = partial3 (partial2 F) a b c by rfl]
    rw [partial3_eq_fderiv (partial2 F) a b c hd2, hP2.fderiv_eq]
    rw [he2.fderiv]
    simp [H]
  have entry32 : partial32 F a b c = H (0, 1, 0) (0, 0, 1) := by
    rw [show partial32 F a b c = partial2 (partial3 F) a b c by rfl]
    rw [partial2_eq_fderiv (partial3 F) a b c hd3, hP3.fderiv_eq]
    rw [he3.fderiv]
    simp [H]
  have hs := hF.isSymmSndFDerivAt (by norm_num)
  exact ⟨by rw [entry12, entry21]; exact hs.eq _ _,
    by rw [entry13, entry31]; exact hs.eq _ _,
    by rw [entry23, entry32]; exact hs.eq _ _⟩

theorem gap1 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (uncurry3 F)
        (arg1 x y, arg2 x y, arg3 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 p.1 p.2) (arg2 p.1 p.2) (arg3 z p.1 p.2) = 0) :
    F1At F z x y + F2At F z x y +
      F3At F z x y * (1 + partialX z x y) = 0 := by
  have hzSlice : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    have hd : DifferentiableAt ℝ (fun t => z t y) x := by
      simpa [Function.uncurry] using
        hzDiff.comp x hp.hasFDerivAt.differentiableAt
    simpa [partialX] using hd.hasDerivAt
  have ha := hasDerivAt_id x
  have hb := (hasDerivAt_id x).add_const y
  have hc : HasDerivAt (fun t => t + y + z t y)
      (1 + partialX z x y) x := (ha.add_const y).add hzSlice
  have hout := hasDerivAt_outer_triple F
    (fun t => t) (fun t => t + y) (fun t => t + y + z t y)
    x 1 1 (1 + partialX z x y)
    (by simpa [arg1, arg2, arg3] using hFDiff) ha hb hc
  have hp : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := by
    simpa using (show ContinuousAt (fun t : ℝ => (t, y)) x by fun_prop)
  have hd := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hImplicit hp)
  have hd' :
      deriv (fun t => F t (t + y) (t + y + z t y)) x =
        deriv (fun _ : ℝ => 0) x := by
    simpa [Function.comp_def, arg1, arg2, arg3] using hd
  rw [hout.deriv] at hd'
  simpa [F1At, F2At, F3At, evalAt, arg1, arg2, arg3] using hd'

theorem gap2 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (uncurry3 F)
        (arg1 x y, arg2 x y, arg3 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 p.1 p.2) (arg2 p.1 p.2) (arg3 z p.1 p.2) = 0) :
    F2At F z x y +
      F3At F z x y * (1 + partialY z x y) = 0 := by
  have hzSlice : HasDerivAt (fun t => z x t) (partialY z x y) y := by
    have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    have hd : DifferentiableAt ℝ (fun t => z x t) y := by
      simpa [Function.uncurry] using
        hzDiff.comp y hp.hasFDerivAt.differentiableAt
    simpa [partialY] using hd.hasDerivAt
  have ha := hasDerivAt_const y x
  have hb := (hasDerivAt_id y).const_add x
  have hc : HasDerivAt (fun t => x + t + z x t)
      (1 + partialY z x y) y := hb.add hzSlice
  have hout := hasDerivAt_outer_triple F
    (fun _ => x) (fun t => x + t) (fun t => x + t + z x t)
    y 0 1 (1 + partialY z x y)
    (by simpa [arg1, arg2, arg3] using hFDiff) ha hb hc
  have hp : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) := by
    simpa using (show ContinuousAt (fun t : ℝ => (x, t)) y by fun_prop)
  have hd := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hImplicit hp)
  have hd' :
      deriv (fun t => F x (x + t) (x + t + z x t)) y =
        deriv (fun _ : ℝ => 0) y := by
    simpa [Function.comp_def, arg1, arg2, arg3] using hd
  rw [hout.deriv] at hd'
  simpa [F1At, F2At, F3At, evalAt, arg1, arg2, arg3] using hd'

theorem gap3 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hF3 : F3At F z x y ≠ 0)
    (hXIdentity :
      F1At F z x y + F2At F z x y +
        F3At F z x y * (1 + partialX z x y) = 0) :
    partialX z x y = solvedPartialX F z x y := by
  unfold solvedPartialX
  rw [show -(1 + (F1At F z x y + F2At F z x y) / F3At F z x y) =
    (-(F3At F z x y + F1At F z x y + F2At F z x y)) /
      F3At F z x y by field_simp [hF3]; ring]
  rw [eq_div_iff hF3]
  linear_combination hXIdentity

theorem gap4 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hF3 : F3At F z x y ≠ 0)
    (hYIdentity :
      F2At F z x y +
        F3At F z x y * (1 + partialY z x y) = 0) :
    partialY z x y = solvedPartialY F z x y := by
  unfold solvedPartialY
  rw [show -(1 + F2At F z x y / F3At F z x y) =
    (-(F3At F z x y + F2At F z x y)) / F3At F z x y by
      field_simp [hF3]]
  rw [eq_div_iff hF3]
  linear_combination hYIdentity

theorem gap5 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFC2 :
      ContDiffAt ℝ 2 (uncurry3 F)
        (arg1 x y, arg2 x y, arg3 z x y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 p.1 p.2) (arg2 p.1 p.2) (arg3 z p.1 p.2) = 0)
    (hF3 : F3At F z x y ≠ 0)
    (hXFormula : partialX z x y = solvedPartialX F z x y) :
    partialXX z x y = rawSecondX F z x y := by
  have hzSliceC2 : ContDiffAt ℝ 2 (fun t => z t y) x := by
    simpa [Function.uncurry] using
      hzC2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hzLine : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using
      (hzSliceC2.differentiableAt (by decide)).hasDerivAt
  have hzD : HasDerivAt (fun t => partialX z t y)
      (partialXX z x y) x := by
    have hd : DifferentiableAt ℝ (deriv (fun t => z t y)) x :=
      (hzSliceC2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by decide)
    simpa [partialX, partialXX] using hd.hasDerivAt
  let A : ℝ → ℝ := fun t => t
  let B : ℝ → ℝ := fun t => t + y
  let C : ℝ → ℝ := fun t => t + y + z t y
  have hA : HasDerivAt A 1 x := hasDerivAt_id x
  have hB : HasDerivAt B 1 x := (hasDerivAt_id x).add_const y
  have hC : HasDerivAt C (1 + partialX z x y) x := by
    exact ((hasDerivAt_id x).add_const y).add hzLine
  obtain ⟨hd1, hd2, hd3⟩ := partials_differentiableAt F
    (A x) (B x) (C x) (by simpa [A, B, C, arg1, arg2, arg3] using hFC2)
  have hP1 := hasDerivAt_outer_triple (partial1 F) A B C x
    1 1 (1 + partialX z x y) hd1 hA hB hC
  have hP2 := hasDerivAt_outer_triple (partial2 F) A B C x
    1 1 (1 + partialX z x y) hd2 hA hB hC
  have hP3 := hasDerivAt_outer_triple (partial3 F) A B C x
    1 1 (1 + partialX z x y) hd3 hA hB hC
  have hF1 : HasDerivAt (fun t => F1At F z t y)
      (F11At F z x y + F12At F z x y +
        F13At F z x y * (1 + partialX z x y)) x := by
    convert hP1 using 1 <;>
      simp [F1At, F11At, F12At, F13At, evalAt, arg1, arg2, arg3,
        A, B, C, partial1, partial2, partial3,
        partial11, partial12, partial13] <;> ring
  have hF2 : HasDerivAt (fun t => F2At F z t y)
      (F21At F z x y + F22At F z x y +
        F23At F z x y * (1 + partialX z x y)) x := by
    convert hP2 using 1 <;>
      simp [F2At, F21At, F22At, F23At, evalAt, arg1, arg2, arg3,
        A, B, C, partial1, partial2, partial3,
        partial21, partial22, partial23] <;> ring
  have hF3Line : HasDerivAt (fun t => F3At F z t y)
      (F31At F z x y + F32At F z x y +
        F33At F z x y * (1 + partialX z x y)) x := by
    convert hP3 using 1 <;>
      simp [F3At, F31At, F32At, F33At, evalAt, arg1, arg2, arg3,
        A, B, C, partial1, partial2, partial3,
        partial31, partial32, partial33] <;> ring
  have hI := (hF1.add hF2).add
    (hF3Line.mul ((hasDerivAt_const x 1).add hzD))
  have hIDeriv : HasDerivAt
      (fun t =>
        F1At F z t y + F2At F z t y +
          F3At F z t y * (1 + partialX z t y))
      ((F11At F z x y + F12At F z x y +
          F13At F z x y * (1 + partialX z x y)) +
        (F21At F z x y + F22At F z x y +
          F23At F z x y * (1 + partialX z x y)) +
        (F31At F z x y + F32At F z x y +
          F33At F z x y * (1 + partialX z x y)) *
            (1 + partialX z x y) +
        F3At F z x y * partialXX z x y) x := by
    convert hI using 1 <;> simp <;> ring
  let path : ℝ → ℝ × ℝ := fun t => (t, y)
  have hpath : Filter.Tendsto path (nhds x) (nhds (x, y)) := by
    simpa [path] using
      (show ContinuousAt (fun t : ℝ => (t, y)) x by fun_prop)
  rcases mem_nhds_iff.mp hImplicit with ⟨s, hsSub, hsOpen, hsMem⟩
  have hsLine : ∀ᶠ t : ℝ in nhds x, path t ∈ s :=
    hpath.eventually (hsOpen.mem_nhds hsMem)
  have hABC : HasDerivAt (fun t => (A t, B t, C t))
      (1, 1, 1 + partialX z x y) x := by
    convert (hA.hasFDerivAt.prodMk
      (hB.hasFDerivAt.prodMk hC.hasFDerivAt)).hasDerivAt using 1 <;> simp
  have hFC2Line := hABC.continuousAt.eventually
    (hFC2.eventually (by simp [A, B, C, arg1, arg2, arg3]))
  have hzC2Line := hpath.eventually (hzC2.eventually (by simp [path]))
  have hIdentity :
      (fun t =>
        F1At F z t y + F2At F z t y +
          F3At F z t y * (1 + partialX z t y)) =ᶠ[nhds x]
        (fun _ => 0) := by
    filter_upwards [hsLine, hFC2Line, hzC2Line] with t hts hFt hzt
    have hLocal : ∀ᶠ p : ℝ × ℝ in nhds (t, y),
        F (arg1 p.1 p.2) (arg2 p.1 p.2) (arg3 z p.1 p.2) = 0 :=
      Filter.mem_of_superset (hsOpen.mem_nhds hts) hsSub
    exact gap1 F z t y
      (by simpa [A, B, C, arg1, arg2, arg3] using
        hFt.differentiableAt (by decide))
      (hzt.differentiableAt (by decide)) hLocal
  have hdEq := Filter.EventuallyEq.deriv_eq hIdentity
  rw [hIDeriv.deriv] at hdEq
  have hSecond :
      (F11At F z x y + F12At F z x y +
          F13At F z x y * (1 + partialX z x y)) +
        (F21At F z x y + F22At F z x y +
          F23At F z x y * (1 + partialX z x y)) +
        (F31At F z x y + F32At F z x y +
          F33At F z x y * (1 + partialX z x y)) *
            (1 + partialX z x y) +
        F3At F z x y * partialXX z x y = 0 := by
    simpa using hdEq
  have hFirst := gap1 F z x y
    (hFC2.differentiableAt (by decide))
    (hzC2.differentiableAt (by decide)) hImplicit
  unfold rawSecondX
  field_simp [hF3]
  linear_combination
    (F3At F z x y) * hSecond -
      (F31At F z x y + F32At F z x y +
        F33At F z x y * (1 + partialX z x y)) * hFirst

theorem gap6 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFC2 :
      ContDiffAt ℝ 2 (uncurry3 F)
        (arg1 x y, arg2 x y, arg3 z x y))
    (hF3 : F3At F z x y ≠ 0)
    (hXFormula : partialX z x y = solvedPartialX F z x y)
    (hRaw : partialXX z x y = rawSecondX F z x y) :
    partialXX z x y = closedSecondX F z x y := by
  obtain ⟨hm12, hm13, hm23⟩ := mixed_partials F
    (arg1 x y) (arg2 x y) (arg3 z x y) hFC2
  have h21 : F21At F z x y = F12At F z x y := by
    unfold F21At F12At evalAt
    exact hm12.symm
  have h31 : F31At F z x y = F13At F z x y := by
    unfold F31At F13At evalAt
    exact hm13.symm
  have h32 : F32At F z x y = F23At F z x y := by
    unfold F32At F23At evalAt
    exact hm23.symm
  rw [hRaw]
  unfold rawSecondX closedSecondX
  rw [hXFormula, h21, h31, h32]
  unfold solvedPartialX
  field_simp [hF3]
  ring

end

end ProofGap.Exercise3397
