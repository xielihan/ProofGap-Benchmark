import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ProofGap.Exercise3471_1

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def inverseDenominator (X u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX X (u x y) (v x y) - partialY X (u x y) (v x y)

private theorem hasDerivAt_partialX
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f t y) (partialX f x y) x := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hs := hf.fun_comp' x hc
  simpa [partialX, Function.uncurry] using hs.hasDerivAt

private theorem hasDerivAt_partialY
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f x t) (partialY f x y) y := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hs := hf.fun_comp' y hc
  simpa [partialY, Function.uncurry] using hs.hasDerivAt

private theorem eventuallyEq_coordX
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (t, y)) =ᶠ[nhds x] fun t => G (t, y) := by
  have hc : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) :=
    continuousAt_id.prodMk continuousAt_const
  simpa [Function.comp_def] using h.comp_tendsto hc

private theorem eventuallyEq_coordY
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (x, t)) =ᶠ[nhds y] fun t => G (x, t) := by
  have hc : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) :=
    continuousAt_const.prodMk continuousAt_id
  simpa [Function.comp_def] using h.comp_tendsto hc

private theorem fderiv_uncurry_apply
    (F : ℝ → ℝ → ℝ) (a b da db : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a, b)) :
    fderiv ℝ (Function.uncurry F) (a, b) (da, db) =
      partialX F a b * da + partialY F a b * db := by
  have hxCurve :
      HasDerivAt (fun t : ℝ => (t, b)) (1, 0) a := by
    simpa [id] using
      (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have hyCurve :
      HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b := by
    simpa [id] using
      (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hxComp :=
    hF.hasFDerivAt.comp_hasDerivAt a hxCurve
  have hyComp :=
    hF.hasFDerivAt.comp_hasDerivAt b hyCurve
  have hx :
      partialX F a b =
        fderiv ℝ (Function.uncurry F) (a, b) (1, 0) := by
    simpa [partialX, Function.comp_def, Function.uncurry] using hxComp.deriv
  have hy :
      partialY F a b =
        fderiv ℝ (Function.uncurry F) (a, b) (0, 1) := by
    simpa [partialY, Function.comp_def, Function.uncurry] using hyComp.deriv
  let L := fderiv ℝ (Function.uncurry F) (a, b)
  calc
    L (da, db) =
        L (da • (1, 0) + db • (0, 1)) := by
      congr 1
      ext <;> simp
    _ = da • L (1, 0) + db • L (0, 1) := by
      rw [map_add, map_smul, map_smul]
    _ = partialX F a b * da + partialY F a b * db := by
      rw [← hx, ← hy]
      simp [smul_eq_mul]
      ring

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (f g : ℝ → ℝ) (t f' g' : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (f t, g t))
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => F (f s) (g s))
      (partialX F (f t) (g t) * f' + partialY F (f t) (g t) * g') t := by
  have h := hF.hasFDerivAt.comp_hasDerivAt t (hf.prodMk hg)
  rw [fderiv_uncurry_apply F (f t) (g t) f' g' hF] at h
  simpa [Function.comp_def, Function.uncurry] using h

theorem gap1 (u z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.2 - z p.1 p.2) :
    differential u x y dx dy = dy - differential z x y dx dy := by
  have hxLocal :
      (fun t : ℝ => u t y) =ᶠ[nhds x] fun t => y - z t y := by
    simpa using eventuallyEq_coordX hU
  have hyLocal :
      (fun t : ℝ => u x t) =ᶠ[nhds y] fun t => t - z x t := by
    simpa using eventuallyEq_coordY hU
  have hux : partialX u x y = -partialX z x y := by
    calc
      partialX u x y = deriv (fun t => u t y) x := rfl
      _ = deriv (fun t => y - z t y) x := hxLocal.deriv_eq
      _ = -partialX z x y := by
        convert ((hasDerivAt_const x y).sub
          (hasDerivAt_partialX z x y hzDiff)).deriv using 1 <;>
          simp
  have huy : partialY u x y = 1 - partialY z x y := by
    calc
      partialY u x y = deriv (fun t => u x t) y := rfl
      _ = deriv (fun t => t - z x t) y := hyLocal.deriv_eq
      _ = 1 - partialY z x y := by
        convert ((hasDerivAt_id y).sub
          (hasDerivAt_partialY z x y hzDiff)).deriv using 1 <;>
          simp [id]
  unfold differential
  rw [hux, huy]
  ring

theorem gap2 (v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.2 + z p.1 p.2) :
    differential v x y dx dy = dy + differential z x y dx dy := by
  have hxLocal :
      (fun t : ℝ => v t y) =ᶠ[nhds x] fun t => y + z t y := by
    simpa using eventuallyEq_coordX hV
  have hyLocal :
      (fun t : ℝ => v x t) =ᶠ[nhds y] fun t => t + z x t := by
    simpa using eventuallyEq_coordY hV
  have hvx : partialX v x y = partialX z x y := by
    calc
      partialX v x y = deriv (fun t => v t y) x := rfl
      _ = deriv (fun t => y + z t y) x := hxLocal.deriv_eq
      _ = partialX z x y := by
        convert ((hasDerivAt_const x y).add
          (hasDerivAt_partialX z x y hzDiff)).deriv using 1 <;>
          simp
  have hvy : partialY v x y = 1 + partialY z x y := by
    calc
      partialY v x y = deriv (fun t => v x t) y := rfl
      _ = deriv (fun t => t + z x t) y := hyLocal.deriv_eq
      _ = 1 + partialY z x y := by
        convert ((hasDerivAt_id y).add
          (hasDerivAt_partialY z x y hzDiff)).deriv using 1 <;>
          simp [id]
  unfold differential
  rw [hvx, hvy]
  ring

theorem gap3 (u v X : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hXDiff : DifferentiableAt ℝ (Function.uncurry X) (u x y, v x y))
    (hInverse : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      X (u p.1 p.2) (v p.1 p.2) = p.1) :
    dx =
      partialX X (u x y) (v x y) * differential u x y dx dy +
        partialY X (u x y) (v x y) * differential v x y dx dy := by
  have hxLocal :
      (fun t : ℝ => X (u t y) (v t y)) =ᶠ[nhds x] fun t => t := by
    simpa using eventuallyEq_coordX hInverse
  have hyLocal :
      (fun t : ℝ => X (u x t) (v x t)) =ᶠ[nhds y] fun _ => x := by
    simpa using eventuallyEq_coordY hInverse
  have hxChain := hasDerivAt_comp₂ X
    (fun t => u t y) (fun t => v t y) x
    (partialX u x y) (partialX v x y) hXDiff
    (hasDerivAt_partialX u x y huDiff)
    (hasDerivAt_partialX v x y hvDiff)
  have hyChain := hasDerivAt_comp₂ X
    (fun t => u x t) (fun t => v x t) y
    (partialY u x y) (partialY v x y) hXDiff
    (hasDerivAt_partialY u x y huDiff)
    (hasDerivAt_partialY v x y hvDiff)
  have hx :
      1 =
        partialX X (u x y) (v x y) * partialX u x y +
          partialY X (u x y) (v x y) * partialX v x y := by
    calc
      1 = deriv (fun t : ℝ => t) x := by simp
      _ = deriv (fun t => X (u t y) (v t y)) x := hxLocal.deriv_eq.symm
      _ = partialX X (u x y) (v x y) * partialX u x y +
          partialY X (u x y) (v x y) * partialX v x y :=
        hxChain.deriv
  have hy :
      0 =
        partialX X (u x y) (v x y) * partialY u x y +
          partialY X (u x y) (v x y) * partialY v x y := by
    calc
      0 = deriv (fun _ : ℝ => x) y := by simp
      _ = deriv (fun t => X (u x t) (v x t)) y := hyLocal.deriv_eq.symm
      _ = partialX X (u x y) (v x y) * partialY u x y +
          partialY X (u x y) (v x y) * partialY v x y :=
        hyChain.deriv
  unfold differential
  calc
    dx = 1 * dx + 0 * dy := by ring
    _ = (partialX X (u x y) (v x y) * partialX u x y +
          partialY X (u x y) (v x y) * partialX v x y) * dx +
        (partialX X (u x y) (v x y) * partialY u x y +
          partialY X (u x y) (v x y) * partialY v x y) * dy := by
      rw [← hx, ← hy]
    _ = partialX X (u x y) (v x y) *
          (partialX u x y * dx + partialY u x y * dy) +
        partialY X (u x y) (v x y) *
          (partialX v x y * dx + partialY v x y * dy) := by
      ring

theorem gap4 (u v z X : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hDu : differential u x y dx dy = dy - differential z x y dx dy)
    (hDv : differential v x y dx dy = dy + differential z x y dx dy) :
    partialX X (u x y) (v x y) * differential u x y dx dy +
        partialY X (u x y) (v x y) * differential v x y dx dy =
      partialX X (u x y) (v x y) * (dy - differential z x y dx dy) +
        partialY X (u x y) (v x y) * (dy + differential z x y dx dy) := by
  rw [hDu, hDv]

theorem gap5 (u v z X : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hChain :
      dx =
        partialX X (u x y) (v x y) * differential u x y dx dy +
          partialY X (u x y) (v x y) * differential v x y dx dy)
    (hSubstitution :
      partialX X (u x y) (v x y) * differential u x y dx dy +
          partialY X (u x y) (v x y) * differential v x y dx dy =
        partialX X (u x y) (v x y) * (dy - differential z x y dx dy) +
          partialY X (u x y) (v x y) * (dy + differential z x y dx dy)) :
    dx =
      partialX X (u x y) (v x y) * (dy - differential z x y dx dy) +
        partialY X (u x y) (v x y) * (dy + differential z x y dx dy) := by
  exact hChain.trans hSubstitution

theorem gap6 (u v z X : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hExpanded :
      dx =
        partialX X (u x y) (v x y) * (dy - differential z x y dx dy) +
          partialY X (u x y) (v x y) * (dy + differential z x y dx dy)) :
    inverseDenominator X u v x y * differential z x y dx dy =
      -dx +
        (partialX X (u x y) (v x y) +
          partialY X (u x y) (v x y)) * dy := by
  unfold inverseDenominator
  calc
    (partialX X (u x y) (v x y) -
        partialY X (u x y) (v x y)) * differential z x y dx dy =
      -(partialX X (u x y) (v x y) *
          (dy - differential z x y dx dy) +
        partialY X (u x y) (v x y) *
          (dy + differential z x y dx dy)) +
        (partialX X (u x y) (v x y) +
          partialY X (u x y) (v x y)) * dy := by
      ring
    _ = -dx +
        (partialX X (u x y) (v x y) +
          partialY X (u x y) (v x y)) * dy := by
      rw [← hExpanded]

theorem gap7 (u v z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : inverseDenominator X u v x y ≠ 0)
    (hForm : ∀ dx dy,
      inverseDenominator X u v x y * differential z x y dx dy =
        -dx +
          (partialX X (u x y) (v x y) +
            partialY X (u x y) (v x y)) * dy) :
    partialX z x y = -1 / inverseDenominator X u v x y := by
  apply (eq_div_iff hDen).2
  have h := hForm 1 0
  simpa [differential, mul_comm] using h

theorem gap8 (u v z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : inverseDenominator X u v x y ≠ 0)
    (hForm : ∀ dx dy,
      inverseDenominator X u v x y * differential z x y dx dy =
        -dx +
          (partialX X (u x y) (v x y) +
            partialY X (u x y) (v x y)) * dy) :
    partialY z x y =
      (partialX X (u x y) (v x y) +
        partialY X (u x y) (v x y)) /
          inverseDenominator X u v x y := by
  apply (eq_div_iff hDen).2
  have h := hForm 0 1
  simpa [differential, mul_comm] using h

theorem gap9 (u v z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hVNonzero : v x y ≠ 0)
    (hDen : inverseDenominator X u v x y ≠ 0)
    (hU : u x y = y - z x y)
    (hV : v x y = y + z x y)
    (hPDE : (y - z x y) * partialX z x y +
      (y + z x y) * partialY z x y = 0)
    (hZx : partialX z x y = -1 / inverseDenominator X u v x y)
    (hZy : partialY z x y =
      (partialX X (u x y) (v x y) +
        partialY X (u x y) (v x y)) /
          inverseDenominator X u v x y) :
    partialX X (u x y) (v x y) + partialY X (u x y) (v x y) =
      u x y / v x y := by
  rw [← hU, ← hV, hZx, hZy] at hPDE
  apply (eq_div_iff hVNonzero).2
  field_simp [hDen] at hPDE
  nlinarith

end

end ProofGap.Exercise3471_1
