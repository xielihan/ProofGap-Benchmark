import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3469

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def ξ (x _y _z : ℝ) : ℝ := x
def η (x y _z : ℝ) : ℝ := y - x
def ζ (x _y z : ℝ) : ℝ := z - x

def pullback (U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  U (ξ x y z) (η x y z) (ζ x y z)

private theorem hasDerivAt_const_sub_id (c x : ℝ) :
    HasDerivAt (fun t : ℝ => c - t) (-1) x := by
  convert ((hasDerivAt_const x c).sub (hasDerivAt_id x)) using 1 <;>
    norm_num

private theorem eventually_comp_aux
    {α β : Type*} {l : Filter α} {l' : Filter β}
    {p : α → Prop} {g : β → α}
    (h : ∀ᶠ a in l, p a) (hg : Filter.Tendsto g l' l) :
    ∀ᶠ b in l', p (g b) :=
  hg.eventually h

private theorem deriv_of_hasFDerivAt_aux
    {f : ℝ → ℝ} {f' : ℝ →L[ℝ] ℝ} {x : ℝ}
    (h : HasFDerivAt f f' x) :
    deriv f x = f' 1 :=
  h.hasDerivAt.deriv

theorem gap1 (u U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (huDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => u p.1 p.2.1 p.2.2) (x, y, z))
    (hUDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2)
      (ξ x y z, η x y z, ζ x y z))
    (hCompose : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, y, z),
      u p.1 p.2.1 p.2.2 = pullback U p.1 p.2.1 p.2.2) :
    partial1 u x y z =
      partial1 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ξ x y z +
        partial2 U (ξ x y z) (η x y z) (ζ x y z) * partial1 η x y z +
        partial3 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ζ x y z := by
  let F : ℝ × (ℝ × ℝ) → ℝ := fun p => U p.1 p.2.1 p.2.2
  let q : ℝ × (ℝ × ℝ) := (ξ x y z, η x y z, ζ x y z)
  let g : ℝ → ℝ × (ℝ × ℝ) := fun t => (t, y - t, z - t)
  let i : ℝ → ℝ × (ℝ × ℝ) := fun t => (t, y, z)
  have hg : HasDerivAt g ((1 : ℝ), ((-1 : ℝ), (-1 : ℝ))) x := by
    simpa [g] using
      (hasDerivAt_id x).prodMk
        ((hasDerivAt_const_sub_id y x).prodMk
          (hasDerivAt_const_sub_id z x))
  have hi : HasDerivAt i ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) x := by
    simpa [i] using
      (hasDerivAt_id x).prodMk
        ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  have hq : g x = q := by
    simp [g, q, ξ, η, ζ]
  have hF : DifferentiableAt ℝ F q := by
    simpa [F, q] using hUDiff
  have hEq : (fun t => u t y z) =ᶠ[nhds x] (fun t => F (g t)) := by
    simpa [i, F, g, pullback, ξ, η, ζ] using
      eventually_comp_aux hCompose hi.continuousAt
  have hderivEq : deriv (fun t => u t y z) x = deriv (fun t => F (g t)) x :=
    hEq.deriv_eq
  have hchain : deriv (fun t => F (g t)) x =
      fderiv ℝ F q ((1 : ℝ), ((-1 : ℝ), (-1 : ℝ))) := by
    have hFgx : DifferentiableAt ℝ F (g x) := by
      simpa [hq] using hF
    simpa [Function.comp_def, hq] using
      (deriv_of_hasFDerivAt_aux
        (hFgx.hasFDerivAt.comp x hg.hasFDerivAt))
  have hx : partial1 U (ξ x y z) (η x y z) (ζ x y z) =
      fderiv ℝ F q ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
    have hix : HasDerivAt
        (fun t : ℝ => (t, (η x y z, ζ x y z)))
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) (ξ x y z) := by
      simpa using
        (hasDerivAt_id (ξ x y z)).prodMk
          ((hasDerivAt_const (ξ x y z) (η x y z)).prodMk
            (hasDerivAt_const (ξ x y z) (ζ x y z)))
    simpa [partial1, F, q, Function.comp_def] using
      (deriv_of_hasFDerivAt_aux
        (hF.hasFDerivAt.comp (ξ x y z) hix.hasFDerivAt))
  have hy : partial2 U (ξ x y z) (η x y z) (ζ x y z) =
      fderiv ℝ F q ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    have hiy : HasDerivAt
        (fun t : ℝ => (ξ x y z, (t, ζ x y z)))
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) (η x y z) := by
      simpa using
        (hasDerivAt_const (η x y z) (ξ x y z)).prodMk
          ((hasDerivAt_id (η x y z)).prodMk
            (hasDerivAt_const (η x y z) (ζ x y z)))
    simpa [partial2, F, q, Function.comp_def] using
      (deriv_of_hasFDerivAt_aux
        (hF.hasFDerivAt.comp (η x y z) hiy.hasFDerivAt))
  have hz : partial3 U (ξ x y z) (η x y z) (ζ x y z) =
      fderiv ℝ F q ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    have hiz : HasDerivAt
        (fun t : ℝ => (ξ x y z, (η x y z, t)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (ζ x y z) := by
      simpa using
        (hasDerivAt_const (ζ x y z) (ξ x y z)).prodMk
          ((hasDerivAt_const (ζ x y z) (η x y z)).prodMk
            (hasDerivAt_id (ζ x y z)))
    simpa [partial3, F, q, Function.comp_def] using
      (deriv_of_hasFDerivAt_aux
        (hF.hasFDerivAt.comp (ζ x y z) hiz.hasFDerivAt))
  have hξ : partial1 ξ x y z = 1 := by
    simpa [partial1, ξ] using (hasDerivAt_id x).deriv
  have hη : partial1 η x y z = -1 := by
    change deriv (fun t : ℝ => y - t) x = -1
    exact (hasDerivAt_const_sub_id y x).deriv
  have hζ : partial1 ζ x y z = -1 := by
    change deriv (fun t : ℝ => z - t) x = -1
    exact (hasDerivAt_const_sub_id z x).deriv
  have hv :
      (((1 : ℝ), ((-1 : ℝ), (-1 : ℝ))) : ℝ × (ℝ × ℝ)) =
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) -
          ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) -
          ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    norm_num
  change deriv (fun t => u t y z) x = _
  rw [hderivEq, hchain, hξ, hη, hζ, hx, hy, hz]
  rw [hv, map_sub, map_sub]
  ring

theorem gap2 (U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) :
    partial1 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ξ x y z +
          partial2 U (ξ x y z) (η x y z) (ζ x y z) * partial1 η x y z +
          partial3 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ζ x y z =
      partial1 U (ξ x y z) (η x y z) (ζ x y z) -
        partial2 U (ξ x y z) (η x y z) (ζ x y z) -
        partial3 U (ξ x y z) (η x y z) (ζ x y z) := by
  have hξ : partial1 ξ x y z = 1 := by
    change deriv (fun t : ℝ => t) x = 1
    exact (hasDerivAt_id x).deriv
  have hη : partial1 η x y z = -1 := by
    change deriv (fun t : ℝ => y - t) x = -1
    exact (hasDerivAt_const_sub_id y x).deriv
  have hζ : partial1 ζ x y z = -1 := by
    change deriv (fun t : ℝ => z - t) x = -1
    exact (hasDerivAt_const_sub_id z x).deriv
  rw [hξ, hη, hζ]
  ring

theorem gap3 (u U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hChain :
      partial1 u x y z =
        partial1 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ξ x y z +
          partial2 U (ξ x y z) (η x y z) (ζ x y z) * partial1 η x y z +
          partial3 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ζ x y z)
    (hCoordinates :
      partial1 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ξ x y z +
            partial2 U (ξ x y z) (η x y z) (ζ x y z) * partial1 η x y z +
            partial3 U (ξ x y z) (η x y z) (ζ x y z) * partial1 ζ x y z =
        partial1 U (ξ x y z) (η x y z) (ζ x y z) -
          partial2 U (ξ x y z) (η x y z) (ζ x y z) -
          partial3 U (ξ x y z) (η x y z) (ζ x y z)) :
    partial1 u x y z =
      partial1 U (ξ x y z) (η x y z) (ζ x y z) -
        partial2 U (ξ x y z) (η x y z) (ζ x y z) -
        partial3 U (ξ x y z) (η x y z) (ζ x y z) := by
  exact hChain.trans hCoordinates

theorem gap4 (u U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (huDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => u p.1 p.2.1 p.2.2) (x, y, z))
    (hUDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2)
      (ξ x y z, η x y z, ζ x y z))
    (hCompose : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, y, z),
      u p.1 p.2.1 p.2.2 = pullback U p.1 p.2.1 p.2.2) :
    partial2 u x y z = partial2 U (ξ x y z) (η x y z) (ζ x y z) := by
  let F : ℝ × (ℝ × ℝ) → ℝ := fun p => U p.1 p.2.1 p.2.2
  let q : ℝ × (ℝ × ℝ) := (ξ x y z, η x y z, ζ x y z)
  let g : ℝ → ℝ × (ℝ × ℝ) := fun t => (x, t - x, z - x)
  let i : ℝ → ℝ × (ℝ × ℝ) := fun t => (x, t, z)
  have hg : HasDerivAt g ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) y := by
    simpa [g] using
      (hasDerivAt_const y x).prodMk
        (((hasDerivAt_id y).sub (hasDerivAt_const y x)).prodMk
          (hasDerivAt_const y (z - x)))
  have hi : HasDerivAt i ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) y := by
    simpa [i] using
      (hasDerivAt_const y x).prodMk
        ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have hq : g y = q := by
    simp [g, q, ξ, η, ζ]
  have hF : DifferentiableAt ℝ F q := by
    simpa [F, q] using hUDiff
  have hEq : (fun t => u x t z) =ᶠ[nhds y] (fun t => F (g t)) := by
    simpa [i, F, g, pullback, ξ, η, ζ] using
      eventually_comp_aux hCompose hi.continuousAt
  have hderivEq : deriv (fun t => u x t z) y = deriv (fun t => F (g t)) y :=
    hEq.deriv_eq
  have hchain : deriv (fun t => F (g t)) y =
      fderiv ℝ F q ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    have hFgy : DifferentiableAt ℝ F (g y) := by
      simpa [hq] using hF
    simpa [Function.comp_def, hq] using
      (deriv_of_hasFDerivAt_aux
        (hFgy.hasFDerivAt.comp y hg.hasFDerivAt))
  have hy : partial2 U (ξ x y z) (η x y z) (ζ x y z) =
      fderiv ℝ F q ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    have hiy : HasDerivAt
        (fun t : ℝ => (ξ x y z, (t, ζ x y z)))
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) (η x y z) := by
      simpa using
        (hasDerivAt_const (η x y z) (ξ x y z)).prodMk
          ((hasDerivAt_id (η x y z)).prodMk
            (hasDerivAt_const (η x y z) (ζ x y z)))
    simpa [partial2, F, q, Function.comp_def] using
      (deriv_of_hasFDerivAt_aux
        (hF.hasFDerivAt.comp (η x y z) hiy.hasFDerivAt))
  change deriv (fun t => u x t z) y = _
  rw [hderivEq, hchain, hy]

theorem gap5 (u U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (huDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => u p.1 p.2.1 p.2.2) (x, y, z))
    (hUDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => U p.1 p.2.1 p.2.2)
      (ξ x y z, η x y z, ζ x y z))
    (hCompose : ∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (x, y, z),
      u p.1 p.2.1 p.2.2 = pullback U p.1 p.2.1 p.2.2) :
    partial3 u x y z = partial3 U (ξ x y z) (η x y z) (ζ x y z) := by
  let F : ℝ × (ℝ × ℝ) → ℝ := fun p => U p.1 p.2.1 p.2.2
  let q : ℝ × (ℝ × ℝ) := (ξ x y z, η x y z, ζ x y z)
  let g : ℝ → ℝ × (ℝ × ℝ) := fun t => (x, y - x, t - x)
  let i : ℝ → ℝ × (ℝ × ℝ) := fun t => (x, y, t)
  have hg : HasDerivAt g ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z := by
    simpa [g] using
      (hasDerivAt_const z x).prodMk
        ((hasDerivAt_const z (y - x)).prodMk
          ((hasDerivAt_id z).sub (hasDerivAt_const z x)))
  have hi : HasDerivAt i ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z := by
    simpa [i] using
      (hasDerivAt_const z x).prodMk
        ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have hq : g z = q := by
    simp [g, q, ξ, η, ζ]
  have hF : DifferentiableAt ℝ F q := by
    simpa [F, q] using hUDiff
  have hEq : (fun t => u x y t) =ᶠ[nhds z] (fun t => F (g t)) := by
    simpa [i, F, g, pullback, ξ, η, ζ] using
      eventually_comp_aux hCompose hi.continuousAt
  have hderivEq : deriv (fun t => u x y t) z = deriv (fun t => F (g t)) z :=
    hEq.deriv_eq
  have hchain : deriv (fun t => F (g t)) z =
      fderiv ℝ F q ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    have hFgz : DifferentiableAt ℝ F (g z) := by
      simpa [hq] using hF
    simpa [Function.comp_def, hq] using
      (deriv_of_hasFDerivAt_aux
        (hFgz.hasFDerivAt.comp z hg.hasFDerivAt))
  have hz : partial3 U (ξ x y z) (η x y z) (ζ x y z) =
      fderiv ℝ F q ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    have hiz : HasDerivAt
        (fun t : ℝ => (ξ x y z, (η x y z, t)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (ζ x y z) := by
      simpa using
        (hasDerivAt_const (ζ x y z) (ξ x y z)).prodMk
          ((hasDerivAt_const (ζ x y z) (η x y z)).prodMk
            (hasDerivAt_id (ζ x y z)))
    simpa [partial3, F, q, Function.comp_def] using
      (deriv_of_hasFDerivAt_aux
        (hF.hasFDerivAt.comp (ζ x y z) hiz.hasFDerivAt))
  change deriv (fun t => u x y t) z = _
  rw [hderivEq, hchain, hz]

theorem gap6 (u U : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hPDE : partial1 u x y z + partial2 u x y z + partial3 u x y z = 0)
    (hX : partial1 u x y z =
      partial1 U (ξ x y z) (η x y z) (ζ x y z) -
        partial2 U (ξ x y z) (η x y z) (ζ x y z) -
        partial3 U (ξ x y z) (η x y z) (ζ x y z))
    (hY : partial2 u x y z =
      partial2 U (ξ x y z) (η x y z) (ζ x y z))
    (hZ : partial3 u x y z =
      partial3 U (ξ x y z) (η x y z) (ζ x y z)) :
    partial1 U (ξ x y z) (η x y z) (ζ x y z) = 0 := by
  rw [hX, hY, hZ] at hPDE
  linarith

end

end ProofGap.Exercise3469
