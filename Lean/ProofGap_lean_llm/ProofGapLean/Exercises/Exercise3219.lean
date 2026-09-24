import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3219

noncomputable section

def sec (t : ℝ) : ℝ :=
  1 / Real.cos t

def phase (x y : ℝ) : ℝ :=
  x ^ 2 / y

def u (x y : ℝ) : ℝ :=
  Real.tan (phase x y)

def admissible (x y : ℝ) : Prop :=
  y ≠ 0 ∧ Real.cos (phase x y) ≠ 0

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

private theorem hasDerivAt_sec_comp {g : ℝ → ℝ} {x g' : ℝ}
    (hg : HasDerivAt g g' x) (hcos : Real.cos (g x) ≠ 0) :
    HasDerivAt (fun t => sec (g t))
      (sec (g x) * Real.tan (g x) * g') x := by
  have hc : HasDerivAt (fun t => Real.cos (g t))
      (-Real.sin (g x) * g') x :=
    (Real.hasDerivAt_cos (g x)).comp x hg
  have hq := (hasDerivAt_const x (1 : ℝ)).div hc hcos
  convert hq using 1 <;>
    simp only [sec, Function.comp_apply]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos] <;>
    ring

theorem gap1 :
    ∀ x y : ℝ, admissible x y →
      partialX u x y = (2 * x / y) * sec (phase x y) ^ 2 := by
  intro x y h
  rcases h with ⟨hy, hcos⟩
  have hp : HasDerivAt (fun t : ℝ => phase t y) (2 * x / y) x := by
    convert ((hasDerivAt_id x).pow 2).div_const y using 1 <;>
      simp [phase] <;> ring
  have ht := (Real.hasDerivAt_tan hcos).comp x hp
  unfold partialX
  calc
    deriv (fun t : ℝ => u t y) x =
        1 / Real.cos (phase x y) ^ 2 * (2 * x / y) := by
      simpa only [u, Function.comp_apply] using ht.deriv
    _ = (2 * x / y) * sec (phase x y) ^ 2 := by
      simp only [sec, one_div]
      field_simp [hy, hcos]

theorem gap2 :
    ∀ x y : ℝ, admissible x y →
      partialY u x y =
        -(x ^ 2 / y ^ 2) * sec (phase x y) ^ 2 := by
  intro x y h
  rcases h with ⟨hy, hcos⟩
  have hp : HasDerivAt (fun t : ℝ => phase x t) (-(x ^ 2 / y ^ 2)) y := by
    convert (hasDerivAt_const y (x ^ 2)).div (hasDerivAt_id y) hy using 1 <;>
      simp [phase] <;> field_simp [hy] <;> ring
  have ht := (Real.hasDerivAt_tan hcos).comp y hp
  unfold partialY
  calc
    deriv (fun t : ℝ => u x t) y =
        1 / Real.cos (phase x y) ^ 2 * (-(x ^ 2 / y ^ 2)) := by
      simpa only [u, Function.comp_apply] using ht.deriv
    _ = -(x ^ 2 / y ^ 2) * sec (phase x y) ^ 2 := by
      simp only [sec, one_div]
      field_simp [hy, hcos]

theorem gap3 :
    ∀ x y : ℝ, admissible x y →
      secondXX u x y =
        (2 / y) * sec (phase x y) ^ 2 +
          (2 * x / y) * 2 * sec (phase x y) ^ 2 *
            Real.tan (phase x y) * (2 * x / y) := by
  intro x y h
  rcases h with ⟨hy, hcos⟩
  have hp : HasDerivAt (fun t : ℝ => phase t y) (2 * x / y) x := by
    convert ((hasDerivAt_id x).pow 2).div_const y using 1 <;>
      simp [phase] <;> ring
  have hs := hasDerivAt_sec_comp hp hcos
  have hl : HasDerivAt (fun t : ℝ => 2 * t / y) (2 / y) x := by
    convert ((hasDerivAt_const x 2).mul (hasDerivAt_id x)).div_const y using 1 <;>
      simp <;> ring
  have hf :
      HasDerivAt
        (fun t : ℝ => (2 * t / y) * sec (phase t y) ^ 2)
        ((2 / y) * sec (phase x y) ^ 2 +
          (2 * x / y) * 2 * sec (phase x y) ^ 2 *
            Real.tan (phase x y) * (2 * x / y)) x := by
    convert hl.mul (hs.pow 2) using 1 <;> simp <;> ring
  have hcp : ContinuousAt (fun t : ℝ => Real.cos (phase t y)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_cos (phase x y)).comp x hp).continuousAt
  have hne : ∀ᶠ t in nhds x, Real.cos (phase t y) ≠ 0 :=
    hcp.eventually_ne hcos
  have heq :
      (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
        (fun t : ℝ => (2 * t / y) * sec (phase t y) ^ 2) :=
    hne.mono (fun t ht => gap1 t y ⟨hy, ht⟩)
  unfold secondXX
  rw [heq.deriv_eq]
  exact hf.deriv

theorem gap4 :
    ∀ y x : ℝ, admissible x y →
      (2 / y) * sec (phase x y) ^ 2 +
          (2 * x / y) * 2 * sec (phase x y) ^ 2 *
            Real.tan (phase x y) * (2 * x / y) =
        (2 / y) * sec (phase x y) ^ 2 +
          (8 * x ^ 2 / y ^ 2) * sec (phase x y) ^ 3 *
            Real.sin (phase x y) := by
  intro y x h
  rcases h with ⟨hy, hcos⟩
  simp only [sec, one_div, Real.tan_eq_sin_div_cos]
  field_simp [hy, hcos]
  <;> ring

theorem gap5 :
    ∀ x y : ℝ, admissible x y →
      secondXX u x y =
        (2 / y) * sec (phase x y) ^ 2 +
          (8 * x ^ 2 / y ^ 2) * sec (phase x y) ^ 3 *
            Real.sin (phase x y) := by
  intro x y h
  calc
    secondXX u x y =
        (2 / y) * sec (phase x y) ^ 2 +
          (2 * x / y) * 2 * sec (phase x y) ^ 2 *
            Real.tan (phase x y) * (2 * x / y) := gap3 x y h
    _ = (2 / y) * sec (phase x y) ^ 2 +
          (8 * x ^ 2 / y ^ 2) * sec (phase x y) ^ 3 *
            Real.sin (phase x y) := gap4 y x h

theorem gap6 :
    ∀ x y : ℝ, admissible x y →
      secondYY u x y =
        (2 * x ^ 2 / y ^ 3) * sec (phase x y) ^ 2 +
          (2 * x ^ 4 / y ^ 4) * sec (phase x y) ^ 3 *
            Real.sin (phase x y) := by
  intro x y h
  rcases h with ⟨hy, hcos⟩
  have hp : HasDerivAt (fun t : ℝ => phase x t) (-(x ^ 2 / y ^ 2)) y := by
    convert (hasDerivAt_const y (x ^ 2)).div (hasDerivAt_id y) hy using 1 <;>
      simp [phase] <;> field_simp [hy] <;> ring
  have hs := hasDerivAt_sec_comp hp hcos
  have hb :
      HasDerivAt (fun t : ℝ => -(x ^ 2 / t ^ 2)) (2 * x ^ 2 / y ^ 3) y := by
    convert ((hasDerivAt_const y (x ^ 2)).div
      ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy)).neg using 1 <;>
      simp <;> field_simp [hy] <;> ring
  have hf :
      HasDerivAt
        (fun t : ℝ => -(x ^ 2 / t ^ 2) * sec (phase x t) ^ 2)
        ((2 * x ^ 2 / y ^ 3) * sec (phase x y) ^ 2 +
          (2 * x ^ 4 / y ^ 4) * sec (phase x y) ^ 3 *
            Real.sin (phase x y)) y := by
    convert hb.mul (hs.pow 2) using 1 <;>
      simp [sec, Real.tan_eq_sin_div_cos] <;>
      field_simp [hy, hcos] <;> ring
  have hny : ∀ᶠ t in nhds y, t ≠ 0 :=
    (hasDerivAt_id y).continuousAt.eventually_ne hy
  have hcp : ContinuousAt (fun t : ℝ => Real.cos (phase x t)) y := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_cos (phase x y)).comp y hp).continuousAt
  have hnc : ∀ᶠ t in nhds y, Real.cos (phase x t) ≠ 0 :=
    hcp.eventually_ne hcos
  have heq :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => -(x ^ 2 / t ^ 2) * sec (phase x t) ^ 2) :=
    (hny.and hnc).mono (fun t ht => gap2 x t ⟨ht.1, ht.2⟩)
  unfold secondYY
  rw [heq.deriv_eq]
  exact hf.deriv

theorem gap7 :
    ∀ x y : ℝ, admissible x y →
      mixedXY u x y =
        -(2 * x / y ^ 2) * sec (phase x y) ^ 2 -
          (4 * x ^ 3 / y ^ 3) * sec (phase x y) ^ 3 *
            Real.sin (phase x y) := by
  intro x y h
  rcases h with ⟨hy, hcos⟩
  have hp : HasDerivAt (fun t : ℝ => phase x t) (-(x ^ 2 / y ^ 2)) y := by
    convert (hasDerivAt_const y (x ^ 2)).div (hasDerivAt_id y) hy using 1 <;>
      simp [phase] <;> field_simp [hy] <;> ring
  have hs := hasDerivAt_sec_comp hp hcos
  have hb :
      HasDerivAt (fun t : ℝ => 2 * x / t) (-(2 * x / y ^ 2)) y := by
    convert (hasDerivAt_const y (2 * x)).div (hasDerivAt_id y) hy using 1 <;>
      simp <;> field_simp [hy] <;> ring
  have hf :
      HasDerivAt
        (fun t : ℝ => (2 * x / t) * sec (phase x t) ^ 2)
        (-(2 * x / y ^ 2) * sec (phase x y) ^ 2 -
          (4 * x ^ 3 / y ^ 3) * sec (phase x y) ^ 3 *
            Real.sin (phase x y)) y := by
    convert hb.mul (hs.pow 2) using 1 <;>
      simp [sec, Real.tan_eq_sin_div_cos] <;>
      field_simp [hy, hcos] <;> ring
  have hny : ∀ᶠ t in nhds y, t ≠ 0 :=
    (hasDerivAt_id y).continuousAt.eventually_ne hy
  have hcp : ContinuousAt (fun t : ℝ => Real.cos (phase x t)) y := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_cos (phase x y)).comp y hp).continuousAt
  have hnc : ∀ᶠ t in nhds y, Real.cos (phase x t) ≠ 0 :=
    hcp.eventually_ne hcos
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => (2 * x / t) * sec (phase x t) ^ 2) :=
    (hny.and hnc).mono (fun t ht => gap1 x t ⟨ht.1, ht.2⟩)
  unfold mixedXY
  rw [heq.deriv_eq]
  exact hf.deriv

end

end ProofGap.Exercise3219
