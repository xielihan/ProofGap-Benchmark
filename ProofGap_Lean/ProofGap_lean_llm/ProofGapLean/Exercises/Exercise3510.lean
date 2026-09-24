import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3510

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

def C2 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial1 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial2 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial3 f p.1 p.2.1 p.2.2)

def MixedSymmetric (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Prop :=
  deriv (fun t => partial2 f t y z) x = partial12 f x y z ∧
    deriv (fun t => partial3 f t y z) x = partial13 f x y z ∧
    deriv (fun t => partial3 f x t z) y = partial23 f x y z

def euler (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * partial1 f x y z + y * partial2 f x y z + z * partial3 f x y z

def eulerSquared (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  euler (fun a b c => euler f a b c) x y z

def physicalOperator (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x ^ 2 * partial11 f x y z + y ^ 2 * partial22 f x y z +
    z ^ 2 * partial33 f x y z + 2 * x * y * partial12 f x y z +
    2 * x * z * partial13 f x y z + 2 * y * z * partial23 f x y z

def coordXi (x y z : ℝ) : ℝ := y / x

def coordEta (x y z : ℝ) : ℝ := z / x

def coordZeta (x y z : ℝ) : ℝ := y - z

private theorem euler_comp_of_coordinate_change
    (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hF : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2))
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c)) :
    x * partial1 f x y z + y * partial2 f x y z + z * partial3 f x y z =
      coordZeta x y z *
        partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) := by
  simp only [coordXi, coordEta, coordZeta]
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p => F p.1 p.2.1 p.2.2
  let p : ℝ × (ℝ × ℝ) := (y / x, (z / x, y - z))
  let L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ := fderiv ℝ G p
  have hFat : HasFDerivAt G L p := hF.differentiableAt.hasFDerivAt
  have hqx (a : ℝ) :
      HasDerivAt (fun t : ℝ => a / t) (-a / x ^ 2) x := by
    convert (hasDerivAt_const x a).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  have hlin (q : ℝ) :
      HasDerivAt (fun t : ℝ => t / x) (1 / x) q := by
    convert (hasDerivAt_id q).div_const x using 1 <;> simp [id] <;> ring
  have hcurve1 :
      HasDerivAt (fun t : ℝ => F (y / t) (z / t) (y - z))
        (L (-y / x ^ 2, (-z / x ^ 2, 0))) x := by
    have hi : HasDerivAt
        (fun t : ℝ => (y / t, (z / t, y - z)))
        (-y / x ^ 2, (-z / x ^ 2, 0)) x := by
      convert (hqx y).prodMk
        ((hqx z).prodMk (hasDerivAt_const x (y - z))) using 1 <;>
          ext t <;> simp
    simpa [G, p, Function.comp_def] using hFat.comp_hasDerivAt x hi
  have hcurve2 :
      HasDerivAt (fun t : ℝ => F (t / x) (z / x) (t - z))
        (L (1 / x, (0, 1))) y := by
    have hi : HasDerivAt
        (fun t : ℝ => (t / x, (z / x, t - z)))
        (1 / x, (0, 1)) y := by
      convert (hlin y).prodMk
        ((hasDerivAt_const y (z / x)).prodMk
          ((hasDerivAt_id y).sub_const z)) using 1 <;>
            ext t <;> simp
    simpa [G, p, Function.comp_def] using hFat.comp_hasDerivAt y hi
  have hcurve3 :
      HasDerivAt (fun t : ℝ => F (y / x) (t / x) (y - t))
        (L (0, (1 / x, -1))) z := by
    have hlast : HasDerivAt (fun t : ℝ => y - t) (-1) z := by
      convert (hasDerivAt_const z y).sub (hasDerivAt_id z) using 1 <;>
        simp <;> ring
    have hi : HasDerivAt
        (fun t : ℝ => (y / x, (t / x, y - t)))
        (0, (1 / x, -1)) z := by
      convert (hasDerivAt_const z (y / x)).prodMk
        ((hlin z).prodMk hlast) using 1 <;>
          ext t <;> simp
    simpa [G, p, Function.comp_def] using hFat.comp_hasDerivAt z hi
  have hthird :
      HasDerivAt (fun t : ℝ => F (y / x) (z / x) t)
        (L (0, (0, 1))) (y - z) := by
    have hi : HasDerivAt
        (fun t : ℝ => (y / x, (z / x, t)))
        (0, (0, 1)) (y - z) := by
      convert (hasDerivAt_const (y - z) (y / x)).prodMk
        ((hasDerivAt_const (y - z) (z / x)).prodMk
          (hasDerivAt_id (y - z))) using 1 <;>
            ext t <;> simp
    simpa [G, p, Function.comp_def] using hFat.comp_hasDerivAt (y - z) hi
  have heq1 :
      (fun t : ℝ => f t y z) =ᶠ[nhds x]
        (fun t : ℝ => F (y / t) (z / t) (y - z)) := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    simpa [coordXi, coordEta, coordZeta] using hComp t y z ht
  have heq2 :
      (fun t : ℝ => f x t z) =
        (fun t : ℝ => F (t / x) (z / x) (t - z)) := by
    funext t
    simpa [coordXi, coordEta, coordZeta] using hComp x t z hx
  have heq3 :
      (fun t : ℝ => f x y t) =
        (fun t : ℝ => F (y / x) (t / x) (y - t)) := by
    funext t
    simpa [coordXi, coordEta, coordZeta] using hComp x y t hx
  have hd1 : partial1 f x y z = L (-y / x ^ 2, (-z / x ^ 2, 0)) := by
    unfold partial1
    exact heq1.deriv_eq.trans hcurve1.deriv
  have hd2 : partial2 f x y z = L (1 / x, (0, 1)) := by
    unfold partial2
    rw [heq2]
    exact hcurve2.deriv
  have hd3 : partial3 f x y z = L (0, (1 / x, -1)) := by
    unfold partial3
    rw [heq3]
    exact hcurve3.deriv
  have hdF : partial3 F (y / x) (z / x) (y - z) = L (0, (0, 1)) := by
    unfold partial3
    exact hthird.deriv
  let e1 : ℝ × (ℝ × ℝ) := (1, (0, 0))
  let e2 : ℝ × (ℝ × ℝ) := (0, (1, 0))
  let e3 : ℝ × (ℝ × ℝ) := (0, (0, 1))
  have hv1 : (-y / x ^ 2, (-z / x ^ 2, 0)) =
      (-y / x ^ 2) • e1 + (-z / x ^ 2) • e2 := by
    ext <;> simp [e1, e2]
  have hv2 : (1 / x, (0, 1)) = (1 / x) • e1 + e3 := by
    ext <;> simp [e1, e3]
  have hv3 : (0, (1 / x, -1)) = (1 / x) • e2 - e3 := by
    ext <;> simp [e2, e3]
  have he3 : (0, (0, 1)) = e3 := by rfl
  have hd1' : partial1 f x y z =
      (-y / x ^ 2) * L e1 + (-z / x ^ 2) * L e2 := by
    rw [hd1, hv1]
    simp
  have hd2' : partial2 f x y z = (1 / x) * L e1 + L e3 := by
    rw [hd2, hv2]
    simp
  have hd3' : partial3 f x y z = (1 / x) * L e2 - L e3 := by
    rw [hd3, hv3]
    simp
  have hdF' : partial3 F (y / x) (z / x) (y - z) = L e3 := by
    rw [hdF, he3]
  rw [hd1', hd2', hd3', hdF']
  field_simp [hx]
  ring

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) :
    eulerSquared f x y z =
      x * partial1 (fun a b c => euler f a b c) x y z +
        y * partial2 (fun a b c => euler f a b c) x y z +
        z * partial3 (fun a b c => euler f a b c) x y z := by
  rfl

theorem gap2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : C2 f)
    (hMixed : MixedSymmetric f x y z) :
    eulerSquared f x y z = physicalOperator f x y z + euler f x y z := by
  have h11 : DifferentiableAt ℝ (fun t : ℝ => partial1 f t y z) x := by
    simpa only [Function.comp_apply] using
      (hf.2.1.differentiableAt.comp x
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, (y, z))) x))
  have h21 : DifferentiableAt ℝ (fun t : ℝ => partial2 f t y z) x := by
    simpa only [Function.comp_apply] using
      (hf.2.2.1.differentiableAt.comp x
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, (y, z))) x))
  have h31 : DifferentiableAt ℝ (fun t : ℝ => partial3 f t y z) x := by
    simpa only [Function.comp_apply] using
      (hf.2.2.2.differentiableAt.comp x
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, (y, z))) x))
  have h12 : DifferentiableAt ℝ (fun t : ℝ => partial1 f x t z) y := by
    simpa only [Function.comp_apply] using
      (hf.2.1.differentiableAt.comp y
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (t, z))) y))
  have h22 : DifferentiableAt ℝ (fun t : ℝ => partial2 f x t z) y := by
    simpa only [Function.comp_apply] using
      (hf.2.2.1.differentiableAt.comp y
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (t, z))) y))
  have h32 : DifferentiableAt ℝ (fun t : ℝ => partial3 f x t z) y := by
    simpa only [Function.comp_apply] using
      (hf.2.2.2.differentiableAt.comp y
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (t, z))) y))
  have h13 : DifferentiableAt ℝ (fun t : ℝ => partial1 f x y t) z := by
    simpa only [Function.comp_apply] using
      (hf.2.1.differentiableAt.comp z
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (y, t))) z))
  have h23 : DifferentiableAt ℝ (fun t : ℝ => partial2 f x y t) z := by
    simpa only [Function.comp_apply] using
      (hf.2.2.1.differentiableAt.comp z
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (y, t))) z))
  have h33 : DifferentiableAt ℝ (fun t : ℝ => partial3 f x y t) z := by
    simpa only [Function.comp_apply] using
      (hf.2.2.2.differentiableAt.comp z
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, (y, t))) z))
  have hdX :
      partial1 (fun a b c => euler f a b c) x y z =
        partial1 f x y z + x * partial11 f x y z +
          y * partial12 f x y z + z * partial13 f x y z := by
    have hA := (hasDerivAt_id x).mul h11.hasDerivAt
    have hB := (hasDerivAt_const x y).mul h21.hasDerivAt
    have hC := (hasDerivAt_const x z).mul h31.hasDerivAt
    have hsum := (hA.add hB).add hC
    change deriv
      (fun t => t * partial1 f t y z + y * partial2 f t y z +
        z * partial3 f t y z) x = _
    calc
      _ = (1 * partial1 f x y z +
              x * deriv (fun t => partial1 f t y z) x) +
            (0 * partial2 f x y z +
              y * deriv (fun t => partial2 f t y z) x) +
            (0 * partial3 f x y z +
              z * deriv (fun t => partial3 f t y z) x) := hsum.deriv
      _ = _ := by
        rw [hMixed.1, hMixed.2.1]
        simp only [partial11]
        ring
  have hdY :
      partial2 (fun a b c => euler f a b c) x y z =
        x * partial12 f x y z + partial2 f x y z +
          y * partial22 f x y z + z * partial23 f x y z := by
    have hA := (hasDerivAt_const y x).mul h12.hasDerivAt
    have hB := (hasDerivAt_id y).mul h22.hasDerivAt
    have hC := (hasDerivAt_const y z).mul h32.hasDerivAt
    have hsum := (hA.add hB).add hC
    change deriv
      (fun t => x * partial1 f x t z + t * partial2 f x t z +
        z * partial3 f x t z) y = _
    calc
      _ = (0 * partial1 f x y z +
              x * deriv (fun t => partial1 f x t z) y) +
            (1 * partial2 f x y z +
              y * deriv (fun t => partial2 f x t z) y) +
            (0 * partial3 f x y z +
              z * deriv (fun t => partial3 f x t z) y) := hsum.deriv
      _ = _ := by
        rw [hMixed.2.2]
        simp only [partial12, partial22]
        ring
  have hdZ :
      partial3 (fun a b c => euler f a b c) x y z =
        x * partial13 f x y z + y * partial23 f x y z +
          partial3 f x y z + z * partial33 f x y z := by
    have hA := (hasDerivAt_const z x).mul h13.hasDerivAt
    have hB := (hasDerivAt_const z y).mul h23.hasDerivAt
    have hC := (hasDerivAt_id z).mul h33.hasDerivAt
    have hsum := (hA.add hB).add hC
    change deriv
      (fun t => x * partial1 f x y t + y * partial2 f x y t +
        t * partial3 f x y t) z = _
    calc
      _ = (0 * partial1 f x y z +
              x * deriv (fun t => partial1 f x y t) z) +
            (0 * partial2 f x y z +
              y * deriv (fun t => partial2 f x y t) z) +
            (1 * partial3 f x y z +
              z * deriv (fun t => partial3 f x y t) z) := hsum.deriv
      _ = _ := by
        simp only [partial13, partial23, partial33]
        ring
  rw [gap1, hdX, hdY, hdZ]
  simp only [physicalOperator, euler]
  ring

theorem gap3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : C2 f)
    (hMixed : MixedSymmetric f x y z)
    (hPDE : physicalOperator f x y z = 0) :
    eulerSquared f x y z - euler f x y z = 0 := by
  rw [gap2 f x y z hf hMixed, hPDE]
  ring

theorem gap4 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) :
    euler f x y z =
      x * partial1 f x y z + y * partial2 f x y z + z * partial3 f x y z := by
  rfl

theorem gap5 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hF : C2 F)
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c)) :
    x * partial1 f x y z + y * partial2 f x y z + z * partial3 f x y z =
      coordZeta x y z *
        partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) := by
  exact euler_comp_of_coordinate_change f F x y z hx hF.1 hComp

theorem gap6 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hEuler :
      x * partial1 f x y z + y * partial2 f x y z + z * partial3 f x y z =
        coordZeta x y z *
          partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z)) :
    euler f x y z =
      coordZeta x y z *
        partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) := by
  exact hEuler

theorem gap7 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hF : C2 F)
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c)) :
    eulerSquared f x y z =
      coordZeta x y z *
        deriv (fun t => t * partial3 F (coordXi x y z) (coordEta x y z) t)
          (coordZeta x y z) := by
  let H : ℝ → ℝ → ℝ → ℝ := fun ξ η ζ => ζ * partial3 F ξ η ζ
  have hH : Differentiable ℝ
      (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2.1 p.2.2) := by
    dsimp [H]
    have hz : Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => p.2.2) := by
      fun_prop
    exact hz.mul hF.2.2.2
  have hCompH : ∀ a b c, a ≠ 0 →
      euler f a b c = H (coordXi a b c) (coordEta a b c) (coordZeta a b c) := by
    intro a b c ha
    simpa [H, euler] using
      (euler_comp_of_coordinate_change f F a b c ha hF.1 hComp)
  have h := euler_comp_of_coordinate_change
    (fun a b c => euler f a b c) H x y z hx hH hCompH
  simpa [eulerSquared, euler, H, partial3] using h

theorem gap8 (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hF : C2 F) :
    ζ * deriv (fun t => t * partial3 F ξ η t) ζ =
      ζ ^ 2 * partial33 F ξ η ζ + ζ * partial3 F ξ η ζ := by
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => partial3 F ξ η t) ζ := by
    simpa only [Function.comp_apply] using
      (hF.2.2.2.differentiableAt.comp ζ
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (ξ, (η, t))) ζ))
  have hprod : HasDerivAt (fun t : ℝ => t * partial3 F ξ η t)
      (1 * partial3 F ξ η ζ +
        ζ * deriv (fun t : ℝ => partial3 F ξ η t) ζ) ζ := by
    exact (hasDerivAt_id ζ).mul hdiff.hasDerivAt
  rw [hprod.deriv]
  simp only [partial33]
  ring

theorem gap9 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hF : C2 F)
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c)) :
    eulerSquared f x y z =
      coordZeta x y z ^ 2 *
          partial33 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) +
        coordZeta x y z *
          partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) := by
  calc
    eulerSquared f x y z =
        coordZeta x y z *
          deriv (fun t => t * partial3 F (coordXi x y z) (coordEta x y z) t)
            (coordZeta x y z) := gap7 f F x y z hx hF hComp
    _ = coordZeta x y z ^ 2 *
          partial33 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) +
        coordZeta x y z *
          partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) :=
      gap8 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) hF

theorem gap10 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hF : C2 F)
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c)) :
    eulerSquared f x y z - euler f x y z =
      coordZeta x y z ^ 2 *
        partial33 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) := by
  have hE : euler f x y z =
      coordZeta x y z *
        partial3 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) :=
    gap6 f F x y z
      (gap5 f F x y z hx hF hComp)
  rw [gap9 f F x y z hx hF hComp, hE]
  ring

theorem gap11 (f F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hx : x ≠ 0)
    (hζ : coordZeta x y z ≠ 0)
    (hf : C2 f)
    (hMixed : MixedSymmetric f x y z)
    (hF : C2 F)
    (hComp : ∀ a b c, a ≠ 0 →
      f a b c = F (coordXi a b c) (coordEta a b c) (coordZeta a b c))
    (hPDE : physicalOperator f x y z = 0) :
    partial33 F (coordXi x y z) (coordEta x y z) (coordZeta x y z) = 0 := by
  have hzero : eulerSquared f x y z - euler f x y z = 0 :=
    gap3 f x y z hf hMixed hPDE
  rw [gap10 f F x y z hx hF hComp] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hζ)

end

end ProofGap.Exercise3510
