import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3509

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f t y z) x

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f x t z) y

def partial13 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f x y t) z

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x t z) y

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x y t) z

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial3 f x y t) z

def coord1 (x1 x2 x3 : ℝ) : ℝ := x2 + x3 - x1

def coord2 (x1 x2 x3 : ℝ) : ℝ := x1 + x3 - x2

def coord3 (x1 x2 x3 : ℝ) : ℝ := x1 + x2 - x3

def C2 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial1 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial2 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial3 f p.1 p.2.1 p.2.2)

def physicalOperator (f : ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 : ℝ) : ℝ :=
  partial11 f x1 x2 x3 + partial22 f x1 x2 x3 + partial33 f x1 x2 x3 +
    partial12 f x1 x2 x3 + partial13 f x1 x2 x3 + partial23 f x1 x2 x3

def transformedLaplacian (f : ℝ → ℝ → ℝ → ℝ) (y1 y2 y3 : ℝ) : ℝ :=
  partial11 f y1 y2 y3 + partial22 f y1 y2 y3 + partial33 f y1 y2 y3

private theorem partial1_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) (x, (y, z))) :
    partial1 f x y z =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
        (x, (y, z)) (1, (0, 0)) := by
  unfold partial1
  have hp : HasDerivAt (fun t : ℝ => (t, (y, z))) (1, (0, 0)) x :=
    (hasDerivAt_id x).prodMk
      ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa using h

private theorem partial2_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) (x, (y, z))) :
    partial2 f x y z =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
        (x, (y, z)) (0, (1, 0)) := by
  unfold partial2
  have hp : HasDerivAt (fun t : ℝ => (x, (t, z))) (0, (1, 0)) y :=
    (hasDerivAt_const y x).prodMk
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt.deriv
  simpa using h

private theorem partial3_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) (x, (y, z))) :
    partial3 f x y z =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
        (x, (y, z)) (0, (0, 1)) := by
  unfold partial3
  have hp : HasDerivAt (fun t : ℝ => (x, (y, t))) (0, (0, 1)) z :=
    (hasDerivAt_const z x).prodMk
      ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have h := (hf.hasFDerivAt.comp z hp.hasFDerivAt).hasDerivAt.deriv
  simpa using h

private theorem hasDerivAt_comp3
    (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ → ℝ) (t du dv dw : ℝ)
    (hf : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (u t, (v t, w t)))
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t)
    (hw : HasDerivAt w dw t) :
    HasDerivAt (fun s => f (u s) (v s) (w s))
      (partial1 f (u t) (v t) (w t) * du +
        partial2 f (u t) (v t) (w t) * dv +
        partial3 f (u t) (v t) (w t) * dw) t := by
  let F : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => f p.1 p.2.1 p.2.2
  let L := fderiv ℝ F (u t, (v t, w t))
  have hp : HasDerivAt (fun s => (u s, (v s, w s)))
      (du, (dv, dw)) t := hu.prodMk (hv.prodMk hw)
  have hraw : HasDerivAt (fun s => f (u s) (v s) (w s))
      (L (du, (dv, dw))) t := by
    simpa [F, L] using
      (hf.hasFDerivAt.comp t hp.hasFDerivAt).hasDerivAt
  have hdecomp :
      (du, (dv, dw)) =
        du • (1, (0, 0)) + dv • (0, (1, 0)) + dw • (0, (0, 1)) := by
    ext <;> simp
  rw [hdecomp] at hraw
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply] at hraw
  rw [partial1_eq_fderiv f (u t) (v t) (w t) hf,
    partial2_eq_fderiv f (u t) (v t) (w t) hf,
    partial3_eq_fderiv f (u t) (v t) (w t) hf]
  convert hraw using 1 <;> simp [F, L, smul_eq_mul] <;> ring

private abbrev uncurry3 (f : ℝ → ℝ → ℝ → ℝ) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private theorem fderiv_eq_coordinate_sum
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry3 f)) :
    fderiv ℝ (uncurry3 f) =
      fun p =>
        (partial1 f p.1 p.2.1 p.2.2) •
            (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
          (partial2 f p.1 p.2.1 p.2.2) •
            ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
              (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
          (partial3 f p.1 p.2.1 p.2.2) •
            ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
              (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  have h1 := partial1_eq_fderiv f p.1 p.2.1 p.2.2 (hf p)
  have h2 := partial2_eq_fderiv f p.1 p.2.1 p.2.2 (hf p)
  have h3 := partial3_eq_fderiv f p.1 p.2.1 p.2.2 (hf p)
  rw [h1, h2, h3]
  rw [show v =
      v.1 • (1, (0, 0)) + v.2.1 • (0, (1, 0)) +
        v.2.2 • (0, (0, 1)) by ext <;> simp]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  simp [smul_eq_mul]

private theorem fderiv_differentiable_of_C2
    (f : ℝ → ℝ → ℝ → ℝ) (hf : C2 f) :
    Differentiable ℝ (fderiv ℝ (uncurry3 f)) := by
  rw [fderiv_eq_coordinate_sum f hf.1]
  have h1 : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => partial1 f p.1 p.2.1 p.2.2) := hf.2.1
  have h2 : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => partial2 f p.1 p.2.1 p.2.2) := hf.2.2.1
  have h3 : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => partial3 f p.1 p.2.1 p.2.2) := hf.2.2.2
  exact ((h1.smul (differentiable_const _)).add
    (h2.smul (differentiable_const _))).add
      (h3.smul (differentiable_const _))

private theorem fderiv_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hDF : Differentiable ℝ (fderiv ℝ F))
    (p v w : E) :
    fderiv ℝ (fun q : E => fderiv ℝ F q v) p w =
      fderiv ℝ (fderiv ℝ F) p w v := by
  have hA :
      HasFDerivAt (fderiv ℝ F)
        (fderiv ℝ (fderiv ℝ F) p) p :=
    (hDF p).hasFDerivAt
  have hB :
      HasFDerivAt (fun _ : E => v) (0 : E →L[ℝ] E) p :=
    hasFDerivAt_const (x := p) v
  have h := hA.clm_apply hB
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L w) h.fderiv
  simpa using heq

private theorem mixed13_eq
    (f : ℝ → ℝ → ℝ → ℝ) (hf : C2 f) (a b c : ℝ) :
    partial1 (partial3 f) a b c = partial3 (partial1 f) a b c := by
  let p : ℝ × (ℝ × ℝ) := (a, (b, c))
  let e1 : ℝ × (ℝ × ℝ) := (1, (0, 0))
  let e3 : ℝ × (ℝ × ℝ) := (0, (0, 1))
  let H := fderiv ℝ (fderiv ℝ (uncurry3 f)) p
  have hDf : Differentiable ℝ (fderiv ℝ (uncurry3 f)) :=
    fderiv_differentiable_of_C2 f hf
  have hsymm : H e1 e3 = H e3 e1 := by
    exact second_derivative_symmetric
      (fun q => (hf.1 q).hasFDerivAt) (hDf p).hasFDerivAt e1 e3
  have heq1 :
      uncurry3 (partial1 f) =
        fun q => fderiv ℝ (uncurry3 f) q e1 := by
    funext q
    simpa [uncurry3, e1] using
      partial1_eq_fderiv f q.1 q.2.1 q.2.2 (hf.1 q)
  have heq3 :
      uncurry3 (partial3 f) =
        fun q => fderiv ℝ (uncurry3 f) q e3 := by
    funext q
    simpa [uncurry3, e3] using
      partial3_eq_fderiv f q.1 q.2.1 q.2.2 (hf.1 q)
  have hl :
      partial1 (partial3 f) a b c = H e1 e3 := by
    rw [partial1_eq_fderiv (partial3 f) a b c (hf.2.2.2 p)]
    change fderiv ℝ (uncurry3 (partial3 f)) p e1 = H e1 e3
    rw [heq3]
    exact fderiv_fderiv_apply _ hDf p e3 e1
  have hr :
      partial3 (partial1 f) a b c = H e3 e1 := by
    rw [partial3_eq_fderiv (partial1 f) a b c (hf.2.1 p)]
    change fderiv ℝ (uncurry3 (partial1 f)) p e3 = H e3 e1
    rw [heq1]
    exact fderiv_fderiv_apply _ hDf p e1 e3
  rw [hl, hr]
  exact hsymm

private theorem partial1_comp_coords (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2))
    (x1 x2 x3 : ℝ) :
    partial1
        (fun a b c => f (coord1 a b c) (coord2 a b c) (coord3 a b c))
        x1 x2 x3 =
      -partial1 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) +
        partial2 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) +
        partial3 f (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) := by
  unfold partial1
  have h1 : HasDerivAt (fun t => coord1 t x2 x3) (-1) x1 := by
    convert ((hasDerivAt_const x1 (x2 + x3)).sub (hasDerivAt_id x1)) using 1 <;>
      simp [coord1]
  have h2 : HasDerivAt (fun t => coord2 t x2 x3) 1 x1 := by
    convert ((hasDerivAt_id x1).add_const x3).sub_const x2 using 1 <;>
      simp [coord2]
  have h3 : HasDerivAt (fun t => coord3 t x2 x3) 1 x1 := by
    convert ((hasDerivAt_id x1).add_const x2).sub_const x3 using 1 <;>
      simp [coord3]
  convert (hasDerivAt_comp3 f _ _ _ x1 (-1) 1 1
    hf.differentiableAt h1 h2 h3).deriv using 1 <;>
      simp only [partial1, partial2, partial3] <;> ring

private theorem partial2_comp_coords (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2))
    (x1 x2 x3 : ℝ) :
    partial2
        (fun a b c => f (coord1 a b c) (coord2 a b c) (coord3 a b c))
        x1 x2 x3 =
      partial1 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) -
        partial2 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) +
        partial3 f (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) := by
  unfold partial2
  have h1 : HasDerivAt (fun t => coord1 x1 t x3) 1 x2 := by
    convert ((hasDerivAt_id x2).add_const x3).sub_const x1 using 1 <;>
      simp [coord1]
  have h2 : HasDerivAt (fun t => coord2 x1 t x3) (-1) x2 := by
    convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2)) using 1 <;>
      simp [coord2]
  have h3 : HasDerivAt (fun t => coord3 x1 t x3) 1 x2 := by
    convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3 using 1 <;>
      simp [coord3]
  convert (hasDerivAt_comp3 f _ _ _ x2 1 (-1) 1
    hf.differentiableAt h1 h2 h3).deriv using 1 <;>
      simp only [partial1, partial2, partial3] <;> ring

private theorem partial3_comp_coords (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2))
    (x1 x2 x3 : ℝ) :
    partial3
        (fun a b c => f (coord1 a b c) (coord2 a b c) (coord3 a b c))
        x1 x2 x3 =
      partial1 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) +
        partial2 f (coord1 x1 x2 x3) (coord2 x1 x2 x3) (coord3 x1 x2 x3) -
        partial3 f (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) := by
  unfold partial3
  have h1 : HasDerivAt (fun t => coord1 x1 x2 t) 1 x3 := by
    convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1 using 1 <;>
      simp [coord1]
  have h2 : HasDerivAt (fun t => coord2 x1 x2 t) 1 x3 := by
    convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2 using 1 <;>
      simp [coord2]
  have h3 : HasDerivAt (fun t => coord3 x1 x2 t) (-1) x3 := by
    convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3)) using 1 <;>
      simp [coord3]
  convert (hasDerivAt_comp3 f _ _ _ x3 1 1 (-1)
    hf.differentiableAt h1 h2 h3).deriv using 1 <;>
      simp only [partial1, partial2, partial3] <;> ring

theorem gap1 (f F : ℝ → ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x1 x2 x3,
      f x1 x2 x3 = F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
        (coord3 x1 x2 x3)) :
    ∀ x1 x2 x3,
      partial1 f x1 x2 x3 =
        -partial1 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial2 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial3 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) := by
  intro x1 x2 x3
  have heq :
      (fun t => f t x2 x3) =
        (fun t => F (coord1 t x2 x3) (coord2 t x2 x3) (coord3 t x2 x3)) := by
    funext t
    exact hComp t x2 x3
  unfold partial1
  rw [heq]
  exact partial1_comp_coords F hF.1 x1 x2 x3

theorem gap2 (f F : ℝ → ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x1 x2 x3,
      f x1 x2 x3 = F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
        (coord3 x1 x2 x3)) :
    ∀ x1 x2 x3,
      partial2 f x1 x2 x3 =
        partial1 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) -
          partial2 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial3 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) := by
  intro x1 x2 x3
  have heq :
      (fun t => f x1 t x3) =
        (fun t => F (coord1 x1 t x3) (coord2 x1 t x3) (coord3 x1 t x3)) := by
    funext t
    exact hComp x1 t x3
  unfold partial2
  rw [heq]
  exact partial2_comp_coords F hF.1 x1 x2 x3

theorem gap3 (f F : ℝ → ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x1 x2 x3,
      f x1 x2 x3 = F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
        (coord3 x1 x2 x3)) :
    ∀ x1 x2 x3,
      partial3 f x1 x2 x3 =
        partial1 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial2 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) -
          partial3 F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) := by
  intro x1 x2 x3
  have heq :
      (fun t => f x1 x2 t) =
        (fun t => F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t)) := by
    funext t
    exact hComp x1 x2 t
  unfold partial3
  rw [heq]
  exact partial3_comp_coords F hF.1 x1 x2 x3

set_option maxHeartbeats 1000000 in
theorem gap4 (f F : ℝ → ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x1 x2 x3,
      f x1 x2 x3 = F (coord1 x1 x2 x3) (coord2 x1 x2 x3)
        (coord3 x1 x2 x3)) :
    ∀ x1 x2 x3,
      physicalOperator f x1 x2 x3 =
        2 * transformedLaplacian F (coord1 x1 x2 x3)
          (coord2 x1 x2 x3) (coord3 x1 x2 x3) := by
  intro x1 x2 x3
  let G : ℝ → ℝ → ℝ → ℝ :=
    fun a b c => F (coord1 a b c) (coord2 a b c) (coord3 a b c)
  have hfG : f = G := by
    funext a b c
    exact hComp a b c
  subst f
  have hG1 := partial1_comp_coords F hF.1
  have hG2 := partial2_comp_coords F hF.1
  have hG3 := partial3_comp_coords F hF.1
  have h11 : partial11 G x1 x2 x3 =
      -(-partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3)) +
        (-partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3)) +
        (-partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3) +
          partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
            (coord3 x1 x2 x3)) := by
    unfold partial11
    rw [show (fun t => partial1 G t x2 x3) =
        (fun t =>
          -partial1 F (coord1 t x2 x3) (coord2 t x2 x3) (coord3 t x2 x3) +
            partial2 F (coord1 t x2 x3) (coord2 t x2 x3) (coord3 t x2 x3) +
            partial3 F (coord1 t x2 x3) (coord2 t x2 x3)
              (coord3 t x2 x3)) by
      funext t
      exact hG1 t x2 x3]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x1 (-1) 1 1
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_const x1 (x2 + x3)).sub (hasDerivAt_id x1))
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_id x1).add_const x3).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_id x1).add_const x2).sub_const x3
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x1 (-1) 1 1
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_const x1 (x2 + x3)).sub (hasDerivAt_id x1))
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_id x1).add_const x3).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_id x1).add_const x2).sub_const x3
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x1 (-1) 1 1
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_const x1 (x2 + x3)).sub (hasDerivAt_id x1))
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_id x1).add_const x3).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_id x1).add_const x2).sub_const x3
          using 1 <;> simp [coord3])
    convert ((hA.neg.add hB).add hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  have h12 : partial12 G x1 x2 x3 =
      -(partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) := by
    unfold partial12
    rw [show (fun t => partial1 G x1 t x3) =
        (fun t =>
          -partial1 F (coord1 x1 t x3) (coord2 x1 t x3) (coord3 x1 t x3) +
            partial2 F (coord1 x1 t x3) (coord2 x1 t x3) (coord3 x1 t x3) +
            partial3 F (coord1 x1 t x3) (coord2 x1 t x3)
              (coord3 x1 t x3)) by
      funext t
      exact hG1 x1 t x3]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x2 1 (-1) 1
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x2 1 (-1) 1
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x2 1 (-1) 1
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    convert ((hA.neg.add hB).add hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  have h13 : partial13 G x1 x2 x3 =
      -(partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) := by
    unfold partial13
    rw [show (fun t => partial1 G x1 x2 t) =
        (fun t =>
          -partial1 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) +
            partial2 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) +
            partial3 F (coord1 x1 x2 t) (coord2 x1 x2 t)
              (coord3 x1 x2 t)) by
      funext t
      exact hG1 x1 x2 t]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x3 1 1 (-1)
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x3 1 1 (-1)
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x3 1 1 (-1)
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    convert ((hA.neg.add hB).add hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  have h22 : partial22 G x1 x2 x3 =
      (partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) -
      (partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) := by
    unfold partial22
    rw [show (fun t => partial2 G x1 t x3) =
        (fun t =>
          partial1 F (coord1 x1 t x3) (coord2 x1 t x3) (coord3 x1 t x3) -
            partial2 F (coord1 x1 t x3) (coord2 x1 t x3) (coord3 x1 t x3) +
            partial3 F (coord1 x1 t x3) (coord2 x1 t x3)
              (coord3 x1 t x3)) by
      funext t
      exact hG2 x1 t x3]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x2 1 (-1) 1
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x2 1 (-1) 1
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x2 1 (-1) 1
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_id x2).add_const x3).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x2 (x1 + x3)).sub (hasDerivAt_id x2))
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x2 x1).add (hasDerivAt_id x2)).sub_const x3
          using 1 <;> simp [coord3])
    convert ((hA.sub hB).add hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  have h23 : partial23 G x1 x2 x3 =
      (partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) -
      (partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) := by
    unfold partial23
    rw [show (fun t => partial2 G x1 x2 t) =
        (fun t =>
          partial1 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) -
            partial2 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) +
            partial3 F (coord1 x1 x2 t) (coord2 x1 x2 t)
              (coord3 x1 x2 t)) by
      funext t
      exact hG2 x1 x2 t]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x3 1 1 (-1)
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x3 1 1 (-1)
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x3 1 1 (-1)
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    convert ((hA.sub hB).add hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  have h33 : partial33 G x1 x2 x3 =
      (partial1 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial1 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) +
      (partial1 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial2 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) -
      (partial1 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) +
        partial2 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3) -
        partial3 (partial3 F) (coord1 x1 x2 x3) (coord2 x1 x2 x3)
          (coord3 x1 x2 x3)) := by
    unfold partial33
    rw [show (fun t => partial3 G x1 x2 t) =
        (fun t =>
          partial1 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) +
            partial2 F (coord1 x1 x2 t) (coord2 x1 x2 t) (coord3 x1 x2 t) -
            partial3 F (coord1 x1 x2 t) (coord2 x1 x2 t)
              (coord3 x1 x2 t)) by
      funext t
      exact hG3 x1 x2 t]
    have hA := hasDerivAt_comp3 (partial1 F) _ _ _ x3 1 1 (-1)
      hF.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hB := hasDerivAt_comp3 (partial2 F) _ _ _ x3 1 1 (-1)
      hF.2.2.1.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    have hC := hasDerivAt_comp3 (partial3 F) _ _ _ x3 1 1 (-1)
      hF.2.2.2.differentiableAt
      (by convert ((hasDerivAt_const x3 x2).add (hasDerivAt_id x3)).sub_const x1
          using 1 <;> simp [coord1])
      (by convert ((hasDerivAt_const x3 x1).add (hasDerivAt_id x3)).sub_const x2
          using 1 <;> simp [coord2])
      (by convert ((hasDerivAt_const x3 (x1 + x2)).sub (hasDerivAt_id x3))
          using 1 <;> simp [coord3])
    convert ((hA.add hB).sub hC).deriv using 1 <;>
      simp [id, coord1, coord2, coord3] <;> ring
  unfold physicalOperator transformedLaplacian
  rw [h11, h22, h33, h12, h13, h23]
  rw [mixed13_eq F hF (coord1 x1 x2 x3) (coord2 x1 x2 x3)
    (coord3 x1 x2 x3)]
  simp only [partial1, partial2, partial3, partial11, partial12, partial13,
    partial22, partial23, partial33]
  ring

theorem gap5 (f F : ℝ → ℝ → ℝ → ℝ)
    (hTransform : ∀ x1 x2 x3,
      physicalOperator f x1 x2 x3 =
        2 * transformedLaplacian F (coord1 x1 x2 x3)
          (coord2 x1 x2 x3) (coord3 x1 x2 x3))
    (hPDE : ∀ x1 x2 x3, physicalOperator f x1 x2 x3 = 0) :
    ∀ y1 y2 y3, transformedLaplacian F y1 y2 y3 = 0 := by
  intro y1 y2 y3
  let x1 := (y2 + y3) / 2
  let x2 := (y1 + y3) / 2
  let x3 := (y1 + y2) / 2
  have ht := hTransform x1 x2 x3
  have hp := hPDE x1 x2 x3
  have hc1 : coord1 x1 x2 x3 = y1 := by
    simp [coord1, x1, x2, x3]
    ring
  have hc2 : coord2 x1 x2 x3 = y2 := by
    simp [coord2, x1, x2, x3]
    ring
  have hc3 : coord3 x1 x2 x3 = y3 := by
    simp [coord3, x1, x2, x3]
    ring
  rw [hc1, hc2, hc3] at ht
  linarith

end

end ProofGap.Exercise3509
