import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3506

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def coordU (x y : ℝ) : ℝ := x * y

def coordV (x y : ℝ) : ℝ := 1 / y

def pdeExpression (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX f x y + 2 * x * y ^ 2 * partialX f x y +
    2 * (y - y ^ 3) * partialY f x y + x ^ 2 * y ^ 2 * f x y ^ 2

private theorem hasDerivAt_uncurry_comp
    (F : ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (Function.uncurry F))
    (a b : ℝ → ℝ) (a' b' x : ℝ)
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun t => F (a t) (b t))
      (a' * partialX F (a x) (b x) + b' * partialY F (a x) (b x)) x := by
  let L := fderiv ℝ (Function.uncurry F) (a x, b x)
  have hOuter : HasFDerivAt (Function.uncurry F) L (a x, b x) :=
    hF.differentiableAt.hasFDerivAt
  have hInner := ha.hasFDerivAt.prodMk hb.hasFDerivAt
  have hCompF := hOuter.comp x hInner
  have hComp : HasDerivAt (fun t => F (a t) (b t)) (L (a', b')) x := by
    simpa [Function.comp_def, Function.uncurry] using hCompF.hasDerivAt
  have hConstB : HasDerivAt (fun _ : ℝ => b x) 0 (a x) :=
    hasDerivAt_const (x := a x) (c := b x)
  have hInnerX :=
    (hasDerivAt_id (a x)).hasFDerivAt.prodMk hConstB.hasFDerivAt
  have hSectionX := hOuter.comp (a x) hInnerX
  have hX : partialX F (a x) (b x) = L (1, 0) := by
    unfold partialX
    simpa [Function.comp_def, Function.uncurry] using
      hSectionX.hasDerivAt.deriv
  have hConstA : HasDerivAt (fun _ : ℝ => a x) 0 (b x) :=
    hasDerivAt_const (x := b x) (c := a x)
  have hInnerY :=
    hConstA.hasFDerivAt.prodMk (hasDerivAt_id (b x)).hasFDerivAt
  have hSectionY := hOuter.comp (b x) hInnerY
  have hY : partialY F (a x) (b x) = L (0, 1) := by
    unfold partialY
    simpa [Function.comp_def, Function.uncurry] using
      hSectionY.hasDerivAt.deriv
  have hvec : (a', b') =
      a' • ((1, 0) : ℝ × ℝ) + b' • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hLin : L (a', b') =
      a' * partialX F (a x) (b x) + b' * partialY F (a x) (b x) := by
    rw [hvec, map_add, map_smul, map_smul, ← hX, ← hY]
    simp [smul_eq_mul]
  rw [hLin] at hComp
  exact hComp

theorem gap1 :
    ∀ x y : ℝ, y ≠ 0 → coordV x y = 1 / y := by
  intro x y hy
  rfl

theorem gap2 :
    ∀ x y : ℝ, y ≠ 0 → coordU x y = x / coordV x y := by
  intro x y hy
  unfold coordU coordV
  field_simp [hy]

theorem gap3 :
    ∀ x y : ℝ, y ≠ 0 → x / coordV x y = x * y := by
  intro x y hy
  unfold coordV
  field_simp [hy]

theorem gap4 :
    ∀ x y : ℝ, y ≠ 0 → coordU x y = x * y := by
  intro x y hy
  rfl

theorem gap5 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, y ≠ 0 → f x y = F (coordU x y) (coordV x y)) :
    ∀ x y, y ≠ 0 →
      partialX f x y =
        partialX F (coordU x y) (coordV x y) * partialX coordU x y +
          partialY F (coordU x y) (coordV x y) * partialX coordV x y := by
  intro x y hy
  have ha : HasDerivAt (fun t : ℝ => coordU t y) y x := by
    simpa [coordU] using (hasDerivAt_id x).mul_const y
  have hb : HasDerivAt (fun t : ℝ => coordV t y) 0 x := by
    simpa [coordV] using (hasDerivAt_const (x := x) (c := 1 / y))
  have hu : partialX coordU x y = y := ha.deriv
  have hv : partialX coordV x y = 0 := hb.deriv
  have heq : (fun t : ℝ => f t y) =
      (fun t : ℝ => F (coordU t y) (coordV t y)) := by
    funext t
    exact hComp t y hy
  change deriv (fun t : ℝ => f t y) x = _
  rw [heq, hu, hv]
  simpa [mul_comm] using
    (hasDerivAt_uncurry_comp F hF.1
      (fun t : ℝ => coordU t y) (fun t : ℝ => coordV t y)
      y 0 x ha hb).deriv

theorem gap6 (F : ℝ → ℝ → ℝ) :
    ∀ x y,
      partialX F (coordU x y) (coordV x y) * partialX coordU x y +
          partialY F (coordU x y) (coordV x y) * partialX coordV x y =
        y * partialX F (coordU x y) (coordV x y) := by
  intro x y
  have ha : HasDerivAt (fun t : ℝ => coordU t y) y x := by
    simpa [coordU] using (hasDerivAt_id x).mul_const y
  have hb : HasDerivAt (fun t : ℝ => coordV t y) 0 x := by
    simpa [coordV] using (hasDerivAt_const (x := x) (c := 1 / y))
  rw [show partialX coordU x y = y from ha.deriv,
    show partialX coordV x y = 0 from hb.deriv]
  ring

theorem gap7 (f F : ℝ → ℝ → ℝ)
    (hChain : ∀ x y, y ≠ 0 →
      partialX f x y =
        partialX F (coordU x y) (coordV x y) * partialX coordU x y +
          partialY F (coordU x y) (coordV x y) * partialX coordV x y) :
    ∀ x y, y ≠ 0 →
      partialX f x y = y * partialX F (coordU x y) (coordV x y) := by
  intro x y hy
  rw [hChain x y hy]
  exact gap6 F x y

theorem gap8 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, y ≠ 0 → f x y = F (coordU x y) (coordV x y)) :
    ∀ x y, y ≠ 0 →
      partialY f x y =
        partialX F (coordU x y) (coordV x y) * partialY coordU x y +
          partialY F (coordU x y) (coordV x y) * partialY coordV x y := by
  intro x y hy
  have hne : ∀ᶠ t : ℝ in nhds y, t ≠ 0 := by
    have hm : ({0}ᶜ : Set ℝ) ∈ nhds y :=
      isOpen_compl_singleton.mem_nhds (by simp [hy])
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hm
  have heq : (fun t : ℝ => f x t) =ᶠ[nhds y]
      (fun t : ℝ => F (coordU x t) (coordV x t)) :=
    hne.mono (fun t ht => hComp x t ht)
  have ha : HasDerivAt (fun t : ℝ => coordU x t) x y := by
    simpa [coordU] using (hasDerivAt_id y).const_mul x
  have hb : HasDerivAt (fun t : ℝ => coordV x t) (-1 / y ^ 2) y := by
    simpa only [coordV, one_div, id_eq] using (hasDerivAt_id y).inv hy
  have hu : partialY coordU x y = x := ha.deriv
  have hv : partialY coordV x y = -1 / y ^ 2 := hb.deriv
  change deriv (fun t : ℝ => f x t) y = _
  rw [heq.deriv_eq, hu, hv]
  simpa [mul_comm] using
    (hasDerivAt_uncurry_comp F hF.1
      (fun t : ℝ => coordU x t) (fun t : ℝ => coordV x t)
      x (-1 / y ^ 2) y ha hb).deriv

theorem gap9 (F : ℝ → ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      partialX F (coordU x y) (coordV x y) * partialY coordU x y +
          partialY F (coordU x y) (coordV x y) * partialY coordV x y =
        x * partialX F (coordU x y) (coordV x y) -
          1 / y ^ 2 * partialY F (coordU x y) (coordV x y) := by
  intro x y hy
  have ha : HasDerivAt (fun t : ℝ => coordU x t) x y := by
    simpa [coordU] using (hasDerivAt_id y).const_mul x
  have hb : HasDerivAt (fun t : ℝ => coordV x t) (-1 / y ^ 2) y := by
    simpa only [coordV, one_div, id_eq] using (hasDerivAt_id y).inv hy
  rw [show partialY coordU x y = x from ha.deriv,
    show partialY coordV x y = -1 / y ^ 2 from hb.deriv]
  ring

theorem gap10 (f F : ℝ → ℝ → ℝ)
    (hChain : ∀ x y, y ≠ 0 →
      partialY f x y =
        partialX F (coordU x y) (coordV x y) * partialY coordU x y +
          partialY F (coordU x y) (coordV x y) * partialY coordV x y) :
    ∀ x y, y ≠ 0 →
      partialY f x y =
        x * partialX F (coordU x y) (coordV x y) -
          1 / y ^ 2 * partialY F (coordU x y) (coordV x y) := by
  intro x y hy
  rw [hChain x y hy]
  exact gap9 F x y hy

theorem gap11 (f : ℝ → ℝ → ℝ) :
    ∀ x y, partialXX f x y =
      deriv (fun t => partialX f t y) x := by
  intro x y
  rfl

theorem gap12 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, y ≠ 0 → f x y = F (coordU x y) (coordV x y)) :
    ∀ x y, y ≠ 0 →
      deriv (fun t => partialX f t y) x =
        y ^ 2 * partialXX F (coordU x y) (coordV x y) := by
  intro x y hy
  have hDx := gap7 f F (gap5 f F hF hComp)
  have heq : (fun t : ℝ => partialX f t y) =
      (fun t : ℝ => y * partialX F (coordU t y) (coordV t y)) := by
    funext t
    exact hDx t y hy
  have ha : HasDerivAt (fun t : ℝ => coordU t y) y x := by
    simpa [coordU] using (hasDerivAt_id x).mul_const y
  have hb : HasDerivAt (fun t : ℝ => coordV t y) 0 x := by
    simpa [coordV] using (hasDerivAt_const (x := x) (c := 1 / y))
  have hd := hasDerivAt_uncurry_comp (partialX F) hF.2.1
    (fun t : ℝ => coordU t y) (fun t : ℝ => coordV t y)
    y 0 x ha hb
  have hd' := hd.const_mul y
  rw [heq]
  change
    deriv (fun t : ℝ => y * partialX F (coordU t y) (coordV t y)) x =
      y ^ 2 * partialX (partialX F) (coordU x y) (coordV x y)
  simpa [pow_two, mul_assoc] using hd'.deriv

theorem gap13 (f F : ℝ → ℝ → ℝ)
    (hSecond : ∀ x y, y ≠ 0 →
      deriv (fun t => partialX f t y) x =
        y ^ 2 * partialXX F (coordU x y) (coordV x y)) :
    ∀ x y, y ≠ 0 →
      partialXX f x y =
        y ^ 2 * partialXX F (coordU x y) (coordV x y) := by
  intro x y hy
  simpa [partialXX] using hSecond x y hy

theorem gap14 (f F : ℝ → ℝ → ℝ)
    (hComp : ∀ x y, y ≠ 0 → f x y = F (coordU x y) (coordV x y))
    (hDx : ∀ x y, y ≠ 0 →
      partialX f x y = y * partialX F (coordU x y) (coordV x y))
    (hDy : ∀ x y, y ≠ 0 →
      partialY f x y =
        x * partialX F (coordU x y) (coordV x y) -
          1 / y ^ 2 * partialY F (coordU x y) (coordV x y))
    (hDxx : ∀ x y, y ≠ 0 →
      partialXX f x y = y ^ 2 * partialXX F (coordU x y) (coordV x y))
    (hPDE : ∀ x y, y ≠ 0 → pdeExpression f x y = 0) :
    ∀ x y, y ≠ 0 →
      y ^ 2 * partialXX F (coordU x y) (coordV x y) +
          2 * x * y ^ 3 * partialX F (coordU x y) (coordV x y) +
          2 * x * (y - y ^ 3) * partialX F (coordU x y) (coordV x y) -
          2 * (y - y ^ 3) * (1 / y ^ 2) *
            partialY F (coordU x y) (coordV x y) +
          x ^ 2 * y ^ 2 * F (coordU x y) (coordV x y) ^ 2 = 0 := by
  intro x y hy
  have hp := hPDE x y hy
  unfold pdeExpression at hp
  rw [hDxx x y hy, hDx x y hy, hDy x y hy, hComp x y hy] at hp
  convert hp using 1 <;> ring

theorem gap15 (F : ℝ → ℝ → ℝ) (u v : ℝ)
    (hv : v ≠ 0)
    (hSubstituted :
      (1 / v) ^ 2 * partialXX F u v +
          2 * (u * v) * (1 / v) ^ 3 * partialX F u v +
          2 * (u * v) * ((1 / v) - (1 / v) ^ 3) * partialX F u v -
          2 * ((1 / v) - (1 / v) ^ 3) / (1 / v) ^ 2 * partialY F u v +
          (u * v) ^ 2 * (1 / v) ^ 2 * F u v ^ 2 = 0) :
    pdeExpression F u v = 0 := by
  have hfactor :
      (1 / v) ^ 2 * partialXX F u v +
          2 * (u * v) * (1 / v) ^ 3 * partialX F u v +
          2 * (u * v) * ((1 / v) - (1 / v) ^ 3) * partialX F u v -
          2 * ((1 / v) - (1 / v) ^ 3) / (1 / v) ^ 2 * partialY F u v +
          (u * v) ^ 2 * (1 / v) ^ 2 * F u v ^ 2 =
        (1 / v ^ 2) * pdeExpression F u v := by
    unfold pdeExpression
    field_simp [hv]
    ring
  rw [hfactor] at hSubstituted
  have hc : 1 / v ^ 2 ≠ 0 :=
    div_ne_zero one_ne_zero (pow_ne_zero 2 hv)
  exact (mul_eq_zero.mp hSubstituted).resolve_left hc

theorem gap16 (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : y ≠ 0)
    (hF : C2 F)
    (hComp : ∀ a b, b ≠ 0 →
      f a b = F (coordU a b) (coordV a b)) :
    pdeExpression f x y = 0 →
      pdeExpression F (coordU x y) (coordV x y) = 0 := by
  intro hp
  have hDx := gap7 f F (gap5 f F hF hComp)
  have hDy := gap10 f F (gap8 f F hF hComp)
  have hDxx := gap13 f F (gap12 f F hF hComp)
  have hSub :
      y ^ 2 * partialXX F (coordU x y) (coordV x y) +
          2 * x * y ^ 3 * partialX F (coordU x y) (coordV x y) +
          2 * x * (y - y ^ 3) * partialX F (coordU x y) (coordV x y) -
          2 * (y - y ^ 3) * (1 / y ^ 2) *
            partialY F (coordU x y) (coordV x y) +
          x ^ 2 * y ^ 2 * F (coordU x y) (coordV x y) ^ 2 = 0 := by
    unfold pdeExpression at hp
    rw [hDxx x y hy, hDx x y hy, hDy x y hy, hComp x y hy] at hp
    convert hp using 1 <;> ring
  have hv : coordV x y ≠ 0 := by
    simp [coordV, hy]
  apply gap15 F (coordU x y) (coordV x y) hv
  convert hSub using 1 <;> unfold coordU coordV <;> field_simp [hy] <;> ring

end

end ProofGap.Exercise3506
