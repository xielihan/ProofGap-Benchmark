import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4271

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  x ^ 2 + 2 * x * y - y ^ 2

def Q (x y : ℝ) : ℝ :=
  x ^ 2 - 2 * x * y - y ^ 2

def field (z : Point) : Point :=
  (P z.1 z.2, Q z.1 z.2)

def potential (z : Point) : ℝ :=
  z.1 ^ 3 / 3 + z.1 ^ 2 * z.2 - z.1 * z.2 ^ 2 - z.2 ^ 3 / 3

def constructedPotential (z : Point) : ℝ :=
  (∫ s in (0 : ℝ)..z.1, P s z.2) +
    ∫ t in (0 : ℝ)..z.2, Q 0 t

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def IsSolution (z : Point → ℝ) : Prop :=
  ∀ p, HasCoordinateGradientAt z (field p) p

private theorem potential_gradient (p : Point) :
    HasCoordinateGradientAt potential (field p) p := by
  constructor
  · have hId := hasDerivAt_id p.1
    have hSq := hId.mul hId
    have hCube := hSq.mul hId
    have hCubic := hCube.div_const 3
    have hMixed := hSq.mul_const p.2
    have hLinear := hId.mul_const (p.2 ^ 2)
    have h := ((hCubic.add hMixed).sub hLinear).sub_const (p.2 ^ 3 / 3)
    convert h using 1 <;> simp [potential, field, P] <;> ring_nf
    funext x <;> simp <;> ring
  · have hId := hasDerivAt_id p.2
    have hSq := hId.mul hId
    have hCube := hSq.mul hId
    have hConst := hasDerivAt_const p.2 (p.1 ^ 3 / 3)
    have hLinear := hId.const_mul (p.1 ^ 2)
    have hQuad := hSq.const_mul p.1
    have hCubic := hCube.div_const 3
    have h := ((hConst.add hLinear).sub hQuad).sub hCubic
    convert h using 1 <;> simp [potential, field, Q] <;> ring_nf
    funext y <;> simp <;> ring

private theorem constructed_eq_potential (p : Point) :
    constructedPotential p = potential p := by
  rcases p with ⟨x, y⟩
  let F : ℝ → ℝ := fun s => s ^ 3 / 3 + s ^ 2 * y - s * y ^ 2
  let G : ℝ → ℝ := fun t => -(t ^ 3 / 3)
  have hF : ∀ s : ℝ, HasDerivAt F (P s y) s := by
    intro s
    have hId := hasDerivAt_id s
    have hSq := hId.mul hId
    have hCube := hSq.mul hId
    have hCubic := hCube.div_const 3
    have hMixed := hSq.mul_const y
    have hLinear := hId.mul_const (y ^ 2)
    have h := (hCubic.add hMixed).sub hLinear
    convert h using 1 <;> simp [F, P] <;> ring_nf
    funext u <;> simp <;> ring
  have hG : ∀ t : ℝ, HasDerivAt G (Q 0 t) t := by
    intro t
    have hId := hasDerivAt_id t
    have hSq := hId.mul hId
    have hCube := hSq.mul hId
    have h := hCube.div_const 3
    convert h.neg using 1 <;> simp [G, Q] <;> ring_nf
    funext u <;> simp <;> ring
  have hPcont : Continuous (fun s : ℝ => P s y) := by
    simpa [P] using
      (((continuous_id.pow 2).add
        (((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul
          continuous_id).mul
          (continuous_const : Continuous (fun _ : ℝ => y)))).sub
        ((continuous_const : Continuous (fun _ : ℝ => y)).pow 2))
  have hQcont : Continuous (fun t : ℝ => Q 0 t) := by
    simpa [Q] using (continuous_id.pow 2).neg
  have h1 :
      (∫ s in (0 : ℝ)..x, P s y) = F x - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    all_goals
      first
      | exact hPcont.intervalIntegrable _ _
      | exact hPcont.continuousOn
      | exact fun s _ => hF s
      | exact fun s => hF s
      | exact fun s _ => (hF s).hasDerivWithinAt
  have h2 :
      (∫ t in (0 : ℝ)..y, Q 0 t) = G y - G 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    all_goals
      first
      | exact hQcont.intervalIntegrable _ _
      | exact hQcont.continuousOn
      | exact fun t _ => hG t
      | exact fun t => hG t
      | exact fun t _ => (hG t).hasDerivWithinAt
  change (∫ s in (0 : ℝ)..x, P s y) + (∫ t in (0 : ℝ)..y, Q 0 t) =
    potential (x, y)
  rw [h1, h2]
  simp [F, G, potential]
  ring

private theorem solution_iff_potential_add_const (z : Point → ℝ) :
    IsSolution z ↔ ∃ C : ℝ, ∀ p, z p = potential p + C := by
  constructor
  · intro hz
    refine ⟨z (0, 0), ?_⟩
    rintro ⟨x, y⟩
    have hxzero : ∀ t : ℝ,
        HasDerivAt (fun s => z (s, y) - potential (s, y)) 0 t := by
      intro t
      convert (hz (t, y)).1.sub (potential_gradient (t, y)).1 using 1 <;>
        simp [field]
    have hyzero : ∀ t : ℝ,
        HasDerivAt (fun s => z (0, s) - potential (0, s)) 0 t := by
      intro t
      convert (hz (0, t)).2.sub (potential_gradient (0, t)).2 using 1 <;>
        simp [field]
    have hx := is_const_of_deriv_eq_zero
      (fun t => (hxzero t).differentiableAt)
      (fun t => (hxzero t).deriv) x 0
    have hy := is_const_of_deriv_eq_zero
      (fun t => (hyzero t).differentiableAt)
      (fun t => (hyzero t).deriv) y 0
    change z (x, y) - potential (x, y) =
      z (0, y) - potential (0, y) at hx
    change z (0, y) - potential (0, y) =
      z (0, 0) - potential (0, 0) at hy
    calc
      z (x, y) = potential (x, y) +
          (z (0, y) - potential (0, y)) := by
            rw [← hx]
            ring
      _ = potential (x, y) +
          (z (0, 0) - potential (0, 0)) := by rw [hy]
      _ = potential (x, y) + z (0, 0) := by simp [potential]
  · rintro ⟨C, hz⟩ p
    constructor
    · simpa only [hz, add_zero] using
        (potential_gradient p).1.add (hasDerivAt_const p.1 C)
    · simpa only [hz, add_zero] using
        (potential_gradient p).2.add (hasDerivAt_const p.2 C)

theorem gap1 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C : ℝ, ∀ p, z p = constructedPotential p + C := by
  rw [solution_iff_potential_add_const]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun p => ?_⟩
    rw [hC p, constructed_eq_potential]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun p => ?_⟩
    rw [hC p, constructed_eq_potential]

theorem gap2 (p : Point) :
    constructedPotential p = potential p := by
  exact constructed_eq_potential p

theorem gap3 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C : ℝ, ∀ p, z p = potential p + C := by
  exact solution_iff_potential_add_const z

theorem gap4 (C : ℝ) :
    IsSolution (fun p => potential p + C) := by
  rw [solution_iff_potential_add_const]
  exact ⟨C, fun p => rfl⟩

end

end ProofGap.Exercise4271
