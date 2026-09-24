import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1563

noncomputable section

def height (V r : ℝ) : ℝ := V / (Real.pi * r ^ 2)
def area (V r : ℝ) : ℝ := 2 * V / r + 2 * Real.pi * r ^ 2
def optimalRadius (V : ℝ) : ℝ := Real.cbrt (V / (2 * Real.pi))

def Feasible (V r h : ℝ) : Prop :=
  0 < r ∧ 0 < h ∧ V = Real.pi * r ^ 2 * h

def IsOptimal (V r h : ℝ) : Prop :=
  Feasible V r h ∧ ∀ r₁ h₁, Feasible V r₁ h₁ →
    2 * Real.pi * r * h + 2 * Real.pi * r ^ 2 ≤
      2 * Real.pi * r₁ * h₁ + 2 * Real.pi * r₁ ^ 2

private lemma cbrt_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.cbrt x := by
  unfold Real.cbrt
  exact Real.rpow_pos_of_pos hx _

private lemma cbrt_cube_of_pos {x : ℝ} (hx : 0 < x) :
    (Real.cbrt x) ^ 3 = x := by
  unfold Real.cbrt
  calc
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
          exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx.le _ _).symm
    _ = x := by norm_num

private lemma radius_pos (V : ℝ) (hV : 0 < V) : 0 < optimalRadius V := by
  apply cbrt_pos_of_pos
  positivity

private lemma radius_cube (V : ℝ) (hV : 0 < V) :
    (optimalRadius V) ^ 3 = V / (2 * Real.pi) := by
  apply cbrt_cube_of_pos
  positivity

private lemma deriv_area (V r : ℝ) (hr : r ≠ 0) :
    deriv (area V) r = (4 * Real.pi * r ^ 3 - 2 * V) / r ^ 2 := by
  unfold area
  have hquot : HasDerivAt (fun y : ℝ => 2 * V / y) (-2 * V / r ^ 2) r := by
    convert (hasDerivAt_const r (2 * V : ℝ)).div (hasDerivAt_id r) hr using 1 <;>
      simp [id] <;> field_simp [hr] <;> ring
  have hsquare : HasDerivAt (fun y : ℝ => 2 * Real.pi * y ^ 2)
      (4 * Real.pi * r) r := by
    convert (hasDerivAt_const r (2 * Real.pi : ℝ)).mul
      ((hasDerivAt_id r).pow 2) using 1 <;> simp [id] <;> ring
  have h := (hquot.add hsquare).deriv
  convert h using 1
  field_simp [hr]
  ring

private lemma deriv2_area (V r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (area V)) r = 4 * V / r ^ 3 + 4 * Real.pi := by
  have heq : deriv (area V) =ᶠ[nhds r]
      fun y => -2 * V / y ^ 2 + 4 * Real.pi * y := by
    filter_upwards [eventually_ne_nhds hr] with y hy
    rw [deriv_area V y hy]
    field_simp [hy]
    ring
  rw [heq.deriv_eq]
  have hquot : HasDerivAt (fun y : ℝ => -2 * V / y ^ 2)
      (4 * V / r ^ 3) r := by
    convert (hasDerivAt_const r (-2 * V : ℝ)).div
      ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr) using 1 <;>
      simp [id] <;> field_simp [hr] <;> ring
  have hlinear : HasDerivAt (fun y : ℝ => 4 * Real.pi * y)
      (4 * Real.pi) r := by
    convert (hasDerivAt_const r (4 * Real.pi : ℝ)).mul
      (hasDerivAt_id r) using 1 <;> simp [id] <;> ring
  have h := (hquot.add hlinear).deriv
  exact h

private lemma area_min (V : ℝ) (hV : 0 < V) (r : ℝ) (hr : 0 < r) :
    area V (optimalRadius V) ≤ area V r := by
  let R := optimalRadius V
  have hR : 0 < R := radius_pos V hV
  have hcube : R ^ 3 = V / (2 * Real.pi) := radius_cube V hV
  have hVeq : V = 2 * Real.pi * R ^ 3 := by
    field_simp [Real.pi_ne_zero] at hcube ⊢
    linarith
  have hnonneg : 0 ≤ 2 * Real.pi / r * ((r - R) ^ 2 * (r + 2 * R)) := by
    positivity
  have hdiff :
      area V r - area V R =
        2 * Real.pi / r * ((r - R) ^ 2 * (r + 2 * R)) := by
    unfold area
    field_simp [hr.ne', hR.ne']
    nlinarith
  linarith

theorem gap1 (V r : ℝ) :
    area V r =
      2 * Real.pi * r * height V r + 2 * Real.pi * r ^ 2 := by
  by_cases hr : r = 0
  · simp [hr, area, height]
  · unfold area height
    field_simp [hr, Real.pi_ne_zero]

theorem gap2 (V r : ℝ) (hr : r ≠ 0) :
    deriv (area V) r = (4 * Real.pi * r ^ 3 - 2 * V) / r ^ 2 := by
  exact deriv_area V r hr

theorem gap3 (V r : ℝ) (hV : 0 < V) (hr : 0 < r)
    (hcrit : deriv (area V) r = 0) :
    r = optimalRadius V := by
  rw [deriv_area V r hr.ne'] at hcrit
  have hcube : r ^ 3 = V / (2 * Real.pi) := by
    field_simp [hr.ne', Real.pi_ne_zero] at hcrit ⊢
    nlinarith
  apply (show Odd 3 by decide).pow_injective
  change r ^ 3 = (optimalRadius V) ^ 3
  rw [hcube, radius_cube V hV]

theorem gap4 (V : ℝ) (hV : 0 < V) :
    0 < deriv (deriv (area V)) (optimalRadius V) := by
  have hR := radius_pos V hV
  rw [deriv2_area V _ hR.ne']
  have hpos : 0 < 4 * V / optimalRadius V ^ 3 := by
    exact div_pos (by positivity) (pow_pos hR 3)
  linarith [Real.pi_pos]

theorem gap5 (V : ℝ) (hV : 0 < V) :
    area V (optimalRadius V) = Real.cbrt (54 * Real.pi * V ^ 2) := by
  let R := optimalRadius V
  have hR : 0 < R := radius_pos V hV
  have hcube : R ^ 3 = V / (2 * Real.pi) := radius_cube V hV
  have hVeq : V = 2 * Real.pi * R ^ 3 := by
    field_simp [Real.pi_ne_zero] at hcube ⊢
    linarith
  apply (show Odd 3 by decide).pow_injective
  change (area V R) ^ 3 = (Real.cbrt (54 * Real.pi * V ^ 2)) ^ 3
  rw [cbrt_cube_of_pos (by positivity : 0 < 54 * Real.pi * V ^ 2)]
  unfold area
  rw [hVeq]
  field_simp [hR.ne']
  ring

theorem gap6 (V : ℝ) (hV : 0 < V) :
    height V (optimalRadius V) = 2 * optimalRadius V := by
  let R := optimalRadius V
  have hR : 0 < R := radius_pos V hV
  have hcube : R ^ 3 = V / (2 * Real.pi) := radius_cube V hV
  have hVeq : V = 2 * Real.pi * R ^ 3 := by
    field_simp [Real.pi_ne_zero] at hcube ⊢
    linarith
  change V / (Real.pi * R ^ 2) = 2 * R
  rw [hVeq]
  field_simp [hR.ne', Real.pi_ne_zero]

theorem gap7 (V : ℝ) (hV : 0 < V) :
    Feasible V (optimalRadius V) (2 * optimalRadius V) := by
  have hR := radius_pos V hV
  refine ⟨hR, by positivity, ?_⟩
  have hcube := radius_cube V hV
  field_simp [Real.pi_ne_zero] at hcube ⊢
  nlinarith

theorem gap8 (V : ℝ) (hV : 0 < V) :
    IsOptimal V (optimalRadius V) (2 * optimalRadius V) := by
  refine ⟨gap7 V hV, ?_⟩
  intro r₁ h₁ hfeas
  rcases hfeas with ⟨hr₁, hh₁, hvol⟩
  have hheight : height V r₁ = h₁ := by
    unfold height
    rw [hvol]
    field_simp [hr₁.ne', Real.pi_ne_zero]
  calc
    2 * Real.pi * optimalRadius V * (2 * optimalRadius V) +
          2 * Real.pi * optimalRadius V ^ 2 =
        area V (optimalRadius V) := by rw [gap1, gap6 V hV]
    _ ≤ area V r₁ := area_min V hV r₁ hr₁
    _ = 2 * Real.pi * r₁ * h₁ + 2 * Real.pi * r₁ ^ 2 := by
      rw [gap1, hheight]

theorem gap9 (V r h : ℝ) (hV : 0 < V)
    (hpair : (r, h) = (optimalRadius V, 2 * optimalRadius V)) :
    IsOptimal V r h := by
  rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
  exact gap8 V hV

end

end ProofGap.Exercise1563
