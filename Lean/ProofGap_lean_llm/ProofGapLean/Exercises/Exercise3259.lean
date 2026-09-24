import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3259

noncomputable section

def denominator (x y z : ℝ) : ℝ :=
  1 - x * y - x * z - y * z

def u (x y z : ℝ) : ℝ :=
  Real.arctan
    ((x + y + z - x * y * z) / denominator x y z)

def partialX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialXY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x t z) y

def partialXYZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialXY g x y t) z

private theorem partialX_u_eq (x y z : ℝ)
    (hden : denominator x y z ≠ 0) :
    partialX u x y z = 1 / (1 + x ^ 2) := by
  unfold partialX
  apply HasDerivAt.deriv
  have hn :
      HasDerivAt (fun t : ℝ => t + y + z - t * y * z) (1 - y * z) x := by
    convert (((hasDerivAt_id x).add_const y).add_const z).sub
      (((hasDerivAt_id x).mul_const y).mul_const z) using 1 <;> ring
  have hd :
      HasDerivAt (fun t : ℝ => denominator t y z) (-y - z) x := by
    unfold denominator
    convert (((hasDerivAt_const x 1).sub
      ((hasDerivAt_id x).mul_const y)).sub
      ((hasDerivAt_id x).mul_const z)).sub
      (hasDerivAt_const x (y * z)) using 1 <;> ring
  have hq := hn.div hd hden
  have ha :=
    (Real.hasDerivAt_arctan
      ((x + y + z - x * y * z) / denominator x y z)).comp x hq
  convert ha using 1
  have hx : 1 + x ^ 2 ≠ 0 := by positivity
  have hqpos :
      1 + ((x + y + z - x * y * z) / denominator x y z) ^ 2 ≠ 0 := by
    positivity
  unfold denominator at hden hqpos ⊢
  field_simp [hden, hx, hqpos] <;> ring

private theorem partialXY_u_eq_zero (x y z : ℝ)
    (hden : denominator x y z ≠ 0) :
    partialXY u x y z = 0 := by
  unfold partialXY
  have hc : ContinuousAt (fun t : ℝ => denominator x t z) y := by
    unfold denominator
    fun_prop
  have hne : ∀ᶠ t in nhds y, denominator x t z ≠ 0 :=
    hc.eventually_ne hden
  have heq :
      (fun t : ℝ => partialX u x t z) =ᶠ[nhds y]
        (fun _ : ℝ => 1 / (1 + x ^ 2)) :=
    hne.mono (fun t ht => partialX_u_eq x t z ht)
  rw [Filter.EventuallyEq.deriv_eq heq]
  simp

theorem gap1 :
    ∀ x y z, denominator x y z ≠ 0 →
      ∃ k : ℤ,
        u x y z =
          Real.arctan x + Real.arctan y + Real.arctan z +
            (k : ℝ) * Real.pi := by
  intro x y z hden
  let s := Real.arctan x + Real.arctan y + Real.arctan z
  let q := (x + y + z - x * y * z) / denominator x y z
  have hcx : Real.cos (Real.arctan x) ≠ 0 :=
    ne_of_gt (Real.cos_arctan_pos x)
  have hcy : Real.cos (Real.arctan y) ≠ 0 :=
    ne_of_gt (Real.cos_arctan_pos y)
  have hcz : Real.cos (Real.arctan z) ≠ 0 :=
    ne_of_gt (Real.cos_arctan_pos z)
  have hsx : Real.sin (Real.arctan x) =
      x * Real.cos (Real.arctan x) := by
    have hx := Real.tan_arctan x
    rw [Real.tan_eq_sin_div_cos] at hx
    exact (div_eq_iff hcx).mp hx
  have hsy : Real.sin (Real.arctan y) =
      y * Real.cos (Real.arctan y) := by
    have hy := Real.tan_arctan y
    rw [Real.tan_eq_sin_div_cos] at hy
    exact (div_eq_iff hcy).mp hy
  have hsz : Real.sin (Real.arctan z) =
      z * Real.cos (Real.arctan z) := by
    have hz := Real.tan_arctan z
    rw [Real.tan_eq_sin_div_cos] at hz
    exact (div_eq_iff hcz).mp hz
  have hcos :
      Real.cos s = denominator x y z *
        (Real.cos (Real.arctan x) * Real.cos (Real.arctan y) *
          Real.cos (Real.arctan z)) := by
    dsimp [s]
    simp only [Real.cos_add, Real.sin_add, hsx, hsy, hsz]
    unfold denominator
    ring
  have hsin :
      Real.sin s = (x + y + z - x * y * z) *
        (Real.cos (Real.arctan x) * Real.cos (Real.arctan y) *
          Real.cos (Real.arctan z)) := by
    dsimp [s]
    simp only [Real.sin_add, Real.cos_add, hsx, hsy, hsz]
    ring
  have hp :
      Real.cos (Real.arctan x) * Real.cos (Real.arctan y) *
          Real.cos (Real.arctan z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcx hcy) hcz
  have hcos_ne : Real.cos s ≠ 0 := by
    rw [hcos]
    exact mul_ne_zero hden hp
  have htan : Real.tan s = q := by
    dsimp [q]
    rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    field_simp [hden, hp]
  have hca : Real.cos (Real.arctan q) ≠ 0 :=
    ne_of_gt (Real.cos_arctan_pos q)
  have htaneq :
      Real.sin s / Real.cos s =
        Real.sin (Real.arctan q) / Real.cos (Real.arctan q) := by
    calc
      Real.sin s / Real.cos s = Real.tan s :=
        (Real.tan_eq_sin_div_cos s).symm
      _ = q := htan
      _ = Real.tan (Real.arctan q) := (Real.tan_arctan q).symm
      _ = Real.sin (Real.arctan q) / Real.cos (Real.arctan q) :=
        Real.tan_eq_sin_div_cos (Real.arctan q)
  have hcross :
      Real.sin s * Real.cos (Real.arctan q) =
        Real.sin (Real.arctan q) * Real.cos s :=
    (div_eq_div_iff hcos_ne hca).mp htaneq
  have hzero : Real.sin (s - Real.arctan q) = 0 := by
    rw [Real.sin_sub, hcross]
    ring
  obtain ⟨n, hn⟩ := (Real.sin_eq_zero_iff).mp hzero
  refine ⟨-n, ?_⟩
  unfold u
  change Real.arctan q = s + ((-n : ℤ) : ℝ) * Real.pi
  rw [Int.cast_neg]
  linarith [hn]

theorem gap2 :
    ∀ x y z, denominator x y z ≠ 0 →
      partialXYZ u x y z = 0 := by
  intro x y z hden
  unfold partialXYZ
  have hc : ContinuousAt (fun t : ℝ => denominator x y t) z := by
    unfold denominator
    fun_prop
  have hne : ∀ᶠ t in nhds z, denominator x y t ≠ 0 :=
    hc.eventually_ne hden
  have heq :
      (fun t : ℝ => partialXY u x y t) =ᶠ[nhds z] (fun _ : ℝ => 0) :=
    hne.mono (fun t ht => partialXY_u_eq_zero x y t ht)
  rw [Filter.EventuallyEq.deriv_eq heq]
  simp

end

end ProofGap.Exercise3259
