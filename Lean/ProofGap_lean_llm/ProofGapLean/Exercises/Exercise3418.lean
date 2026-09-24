import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3418

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => f s v w) u

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => f u s w) v

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => f u v s) w

def differential3 (f : ℝ → ℝ → ℝ → ℝ)
    (u v w du dv dw : ℝ) : ℝ :=
  partial1 f u v w * du +
    partial2 f u v w * dv +
    partial3 f u v w * dw

def jacobian3 (f g h : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  partial1 f u v w *
      (partial2 g u v w * partial3 h u v w -
        partial3 g u v w * partial2 h u v w) -
    partial2 f u v w *
      (partial1 g u v w * partial3 h u v w -
        partial3 g u v w * partial1 h u v w) +
    partial3 f u v w *
      (partial1 g u v w * partial2 h u v w -
        partial2 g u v w * partial1 h u v w)

def replacementDet (f g h : ℝ → ℝ → ℝ → ℝ)
    (u v w dx dy dz : ℝ) : ℝ :=
  dx * (partial2 g u v w * partial3 h u v w -
      partial3 g u v w * partial2 h u v w) -
    partial2 f u v w *
      (dy * partial3 h u v w - partial3 g u v w * dz) +
    partial3 f u v w *
      (dy * partial2 h u v w - partial2 g u v w * dz)

def cofactor1 (g h : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  partial2 g u v w * partial3 h u v w -
    partial3 g u v w * partial2 h u v w

def cofactor2 (f h : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  partial3 f u v w * partial2 h u v w -
    partial2 f u v w * partial3 h u v w

def cofactor3 (f g : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  partial2 f u v w * partial3 g u v w -
    partial3 f u v w * partial2 g u v w

private theorem differential3_eq_fderiv
    (k : ℝ → ℝ → ℝ → ℝ) (a b c da db dc : ℝ)
    (hk : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2.1 p.2.2) (a, (b, c))) :
    differential3 k a b c da db dc =
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2.1 p.2.2)
        (a, (b, c))) (da, (db, dc)) := by
  let K : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => k p.1 p.2.1 p.2.2
  let L := fderiv ℝ K (a, (b, c))
  have h1 : partial1 k a b c = L (1, (0, 0)) := by
    have he : HasFDerivAt (fun s : ℝ => (s, (b, c)))
        ((1 : ℝ →L[ℝ] ℝ).prod
          ((0 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) a := by
      simpa using
        ((hasFDerivAt_id a).prodMk
          ((hasFDerivAt_const b a).prodMk (hasFDerivAt_const c a)))
    have hs := hk.hasFDerivAt.comp a he
    have hs' := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hs.fderiv
    unfold partial1 deriv
    simpa [K, L] using hs'
  have h2 : partial2 k a b c = L (0, (1, 0)) := by
    have he : HasFDerivAt (fun s : ℝ => (a, (s, c)))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) b := by
      simpa using
        ((hasFDerivAt_const a b).prodMk
          ((hasFDerivAt_id b).prodMk (hasFDerivAt_const c b)))
    have hs := hk.hasFDerivAt.comp b he
    have hs' := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hs.fderiv
    unfold partial2 deriv
    simpa [K, L] using hs'
  have h3 : partial3 k a b c = L (0, (0, 1)) := by
    have he : HasFDerivAt (fun s : ℝ => (a, (b, s)))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) c := by
      simpa using
        ((hasFDerivAt_const a c).prodMk
          ((hasFDerivAt_const b c).prodMk (hasFDerivAt_id c)))
    have hs := hk.hasFDerivAt.comp c he
    have hs' := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hs.fderiv
    unfold partial3 deriv
    simpa [K, L] using hs'
  unfold differential3
  rw [h1, h2, h3]
  change L (1, (0, 0)) * da + L (0, (1, 0)) * db +
      L (0, (0, 1)) * dc = L (da, (db, dc))
  rw [show (da, (db, dc)) =
      da • (1, (0, 0)) + db • (0, (1, 0)) + dc • (0, (0, 1)) by
        ext <;> simp]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  simp [mul_comm]

private theorem differential3_comp_fderiv
    (f U V W : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ)
    (hF : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (U x y z, (V x y z, W x y z)))
    (hU : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2) (x, (y, z)))
    (hV : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2.1 p.2.2) (x, (y, z)))
    (hW : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2.1 p.2.2) (x, (y, z))) :
    differential3 f (U x y z) (V x y z) (W x y z)
        (differential3 U x y z dx dy dz)
        (differential3 V x y z dx dy dz)
        (differential3 W x y z dx dy dz) =
      (fderiv ℝ
        (fun p : ℝ × (ℝ × ℝ) =>
          f (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
            (W p.1 p.2.1 p.2.2))
        (x, (y, z))) (dx, (dy, dz)) := by
  let F : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => f p.1 p.2.1 p.2.2
  let T : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
    fun p => (U p.1 p.2.1 p.2.2,
      (V p.1 p.2.1 p.2.2, W p.1 p.2.1 p.2.2))
  let LU := fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2)
    (x, (y, z))
  let LV := fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2.1 p.2.2)
    (x, (y, z))
  let LW := fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2.1 p.2.2)
    (x, (y, z))
  have hT : HasFDerivAt T (LU.prod (LV.prod LW)) (x, (y, z)) := by
    simpa [T, LU, LV, LW] using
      (hU.hasFDerivAt.prodMk
        (hV.hasFDerivAt.prodMk hW.hasFDerivAt))
  have hcomp := hF.hasFDerivAt.comp (x, (y, z)) hT
  rw [differential3_eq_fderiv f (U x y z) (V x y z) (W x y z)
      (differential3 U x y z dx dy dz)
      (differential3 V x y z dx dy dz)
      (differential3 W x y z dx dy dz) hF,
    differential3_eq_fderiv U x y z dx dy dz hU,
    differential3_eq_fderiv V x y z dx dy dz hV,
    differential3_eq_fderiv W x y z dx dy dz hW]
  have happ := congrArg
    (fun L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ => L (dx, (dy, dz)))
    hcomp.fderiv
  simpa [F, T, LU, LV, LW] using happ.symm

theorem gap1 (f U V W : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ)
    (hF : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (U x y z, (V x y z, W x y z)))
    (hU : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2) (x, (y, z)))
    (hV : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2.1 p.2.2) (x, (y, z)))
    (hW : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2.1 p.2.2) (x, (y, z)))
    (hX : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, (y, z)),
      p.1 = f (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
        (W p.1 p.2.1 p.2.2)) :
    dx = differential3 f (U x y z) (V x y z) (W x y z)
      (differential3 U x y z dx dy dz)
      (differential3 V x y z dx dy dz)
      (differential3 W x y z dx dy dz) := by
  rw [differential3_comp_fderiv f U V W x y z dx dy dz hF hU hV hW]
  have heq :
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.1) (x, (y, z)) =
        fderiv ℝ
          (fun p : ℝ × (ℝ × ℝ) =>
            f (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
              (W p.1 p.2.1 p.2.2))
          (x, (y, z)) :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hX
  have happ := congrArg
    (fun L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ => L (dx, (dy, dz))) heq
  rw [show fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.1) (x, (y, z)) =
      ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) by
    exact (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, (y, z)))).fderiv] at happ
  simpa using happ

theorem gap2 (g U V W : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ)
    (hG : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1 p.2.2)
      (U x y z, (V x y z, W x y z)))
    (hU : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2) (x, (y, z)))
    (hV : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2.1 p.2.2) (x, (y, z)))
    (hW : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2.1 p.2.2) (x, (y, z)))
    (hY : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, (y, z)),
      p.2.1 = g (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
        (W p.1 p.2.1 p.2.2)) :
    dy = differential3 g (U x y z) (V x y z) (W x y z)
      (differential3 U x y z dx dy dz)
      (differential3 V x y z dx dy dz)
      (differential3 W x y z dx dy dz) := by
  rw [differential3_comp_fderiv g U V W x y z dx dy dz hG hU hV hW]
  have heq :
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.2.1) (x, (y, z)) =
        fderiv ℝ
          (fun p : ℝ × (ℝ × ℝ) =>
            g (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
              (W p.1 p.2.1 p.2.2))
          (x, (y, z)) :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hY
  have hp : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (x, (y, z)) := by
    convert (hasFDerivAt_fst (𝕜 := ℝ) (p := (y, z))).comp
      (x, (y, z))
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, (y, z)))) using 1 <;>
      rfl
  have happ := congrArg
    (fun L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ => L (dx, (dy, dz))) heq
  rw [hp.fderiv] at happ
  simpa using happ

theorem gap3 (h U V W : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ)
    (hH : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => h p.1 p.2.1 p.2.2)
      (U x y z, (V x y z, W x y z)))
    (hU : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2) (x, (y, z)))
    (hV : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2.1 p.2.2) (x, (y, z)))
    (hW : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2.1 p.2.2) (x, (y, z)))
    (hZ : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, (y, z)),
      p.2.2 = h (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
        (W p.1 p.2.1 p.2.2)) :
    dz = differential3 h (U x y z) (V x y z) (W x y z)
      (differential3 U x y z dx dy dz)
      (differential3 V x y z dx dy dz)
      (differential3 W x y z dx dy dz) := by
  rw [differential3_comp_fderiv h U V W x y z dx dy dz hH hU hV hW]
  have heq :
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.2.2) (x, (y, z)) =
        fderiv ℝ
          (fun p : ℝ × (ℝ × ℝ) =>
            h (U p.1 p.2.1 p.2.2) (V p.1 p.2.1 p.2.2)
              (W p.1 p.2.1 p.2.2))
          (x, (y, z)) :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hZ
  have hp : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (x, (y, z)) := by
    convert (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, z))).comp
      (x, (y, z))
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, (y, z)))) using 1 <;>
      rfl
  have happ := congrArg
    (fun L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ => L (dx, (dy, dz))) heq
  rw [hp.fderiv] at happ
  simpa using happ

theorem gap4 (f g h : ℝ → ℝ → ℝ → ℝ)
    (u v w dx dy dz du dv dw : ℝ)
    (hJac : jacobian3 f g h u v w ≠ 0)
    (hX : dx = differential3 f u v w du dv dw)
    (hY : dy = differential3 g u v w du dv dw)
    (hZ : dz = differential3 h u v w du dv dw) :
    du = replacementDet f g h u v w dx dy dz /
      jacobian3 f g h u v w := by
  apply (eq_div_iff hJac).2
  rw [hX, hY, hZ]
  unfold differential3 replacementDet jacobian3
  ring

theorem gap5 (f g h : ℝ → ℝ → ℝ → ℝ) (u v w dx dy dz : ℝ) :
    replacementDet f g h u v w dx dy dz =
      cofactor1 g h u v w * dx +
        cofactor2 f h u v w * dy +
        cofactor3 f g u v w * dz := by
  unfold replacementDet cofactor1 cofactor2 cofactor3
  ring

theorem gap6 (f g h : ℝ → ℝ → ℝ → ℝ)
    (u v w dx dy dz du : ℝ)
    (hJac : jacobian3 f g h u v w ≠ 0)
    (h1 : du = replacementDet f g h u v w dx dy dz /
      jacobian3 f g h u v w)
    (h2 : replacementDet f g h u v w dx dy dz =
      cofactor1 g h u v w * dx +
        cofactor2 f h u v w * dy +
        cofactor3 f g u v w * dz) :
    du =
      (cofactor1 g h u v w / jacobian3 f g h u v w) * dx +
        (cofactor2 f h u v w / jacobian3 f g h u v w) * dy +
        (cofactor3 f g u v w / jacobian3 f g h u v w) * dz := by
  rw [h1, h2]
  ring

theorem gap7 (f g h : ℝ → ℝ → ℝ → ℝ)
    (U : ℝ → ℝ → ℝ → ℝ) (x y z u v w : ℝ)
    (hJac : jacobian3 f g h u v w ≠ 0)
    (hAll : ∀ dx dy dz : ℝ,
      differential3 U x y z dx dy dz =
        (cofactor1 g h u v w / jacobian3 f g h u v w) * dx +
          (cofactor2 f h u v w / jacobian3 f g h u v w) * dy +
          (cofactor3 f g u v w / jacobian3 f g h u v w) * dz) :
    partial1 U x y z =
      cofactor1 g h u v w / jacobian3 f g h u v w := by
  have hdir := hAll 1 0 0
  simpa [differential3] using hdir

theorem gap8 (f g h : ℝ → ℝ → ℝ → ℝ)
    (U : ℝ → ℝ → ℝ → ℝ) (x y z u v w : ℝ)
    (hJac : jacobian3 f g h u v w ≠ 0)
    (hAll : ∀ dx dy dz : ℝ,
      differential3 U x y z dx dy dz =
        (cofactor1 g h u v w / jacobian3 f g h u v w) * dx +
          (cofactor2 f h u v w / jacobian3 f g h u v w) * dy +
          (cofactor3 f g u v w / jacobian3 f g h u v w) * dz) :
    partial2 U x y z =
      cofactor2 f h u v w / jacobian3 f g h u v w := by
  have hdir := hAll 0 1 0
  simpa [differential3] using hdir

theorem gap9 (f g h : ℝ → ℝ → ℝ → ℝ)
    (U : ℝ → ℝ → ℝ → ℝ) (x y z u v w : ℝ)
    (hJac : jacobian3 f g h u v w ≠ 0)
    (hAll : ∀ dx dy dz : ℝ,
      differential3 U x y z dx dy dz =
        (cofactor1 g h u v w / jacobian3 f g h u v w) * dx +
          (cofactor2 f h u v w / jacobian3 f g h u v w) * dy +
          (cofactor3 f g u v w / jacobian3 f g h u v w) * dz) :
    partial3 U x y z =
      cofactor3 f g u v w / jacobian3 f g h u v w := by
  have hdir := hAll 0 0 1
  simpa [differential3] using hdir

end

end ProofGap.Exercise3418
