import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2010
noncomputable section

def leftBranch : Set ℝ := Set.Ioo (-(Real.pi / 2)) 0
def rightBranch : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def branch : Set ℝ := leftBranch ∪ rightBranch
def cubeRoot (y : ℝ) :=
  Real.sign y * Real.rpow |y| (1 / 3 : ℝ)
def t (x : ℝ) := cubeRoot (Real.tan x)
def integrand (x : ℝ) := 1 / cubeRoot (Real.tan x)
def firstRational (u : ℝ) := 3 * u / (1 + u ^ 6)
def squareRational (u : ℝ) := (3 / 2 : ℝ) / (1 + (u ^ 2) ^ 3) *
  deriv (fun v : ℝ => v ^ 2) u
def primitiveT (u : ℝ) :=
  (1 / 4 : ℝ) * Real.log ((u ^ 2 + 1) ^ 2 / (u ^ 4 - u ^ 2 + 1)) +
    Real.sqrt 3 / 2 * Real.arctan ((2 * u ^ 2 - 1) / Real.sqrt 3)
def primitive (x : ℝ) := primitiveT (t x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def BranchwiseTranslates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ Cleft Cright,
    (∀ x ∈ leftBranch, F x = p x + Cleft) ∧
    (∀ x ∈ rightBranch, F x = p x + Cright)}

private theorem cubeRoot_cubed (y : ℝ) : cubeRoot y ^ 3 = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · norm_num [cubeRoot]
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hpow :
        Real.rpow (-y) (1 / 3 : ℝ) ^ 3 = -y := by
      simpa [one_div] using
        (Real.rpow_inv_natCast_pow (x := -y) (n := 3)
          (le_of_lt (neg_pos.mpr hy)) (by norm_num))
    rw [cubeRoot, Real.sign_of_neg hy, abs_of_neg hy]
    norm_num
    change (-Real.rpow (-y) (1 / 3 : ℝ)) ^ 3 = y
    calc
      (-Real.rpow (-y) (1 / 3 : ℝ)) ^ 3 =
          -(Real.rpow (-y) (1 / 3 : ℝ) ^ 3) := by ring
      _ = -(-y) := by rw [hpow]
      _ = y := by ring
  · simpa [cubeRoot, Real.sign_of_pos hy, abs_of_pos hy, one_div] using
      (Real.rpow_inv_natCast_pow (x := y) (n := 3) hy.le
        (by norm_num))

private theorem hasDerivAt_rpow_third_of_pos {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
      (Real.rpow y (1 / 3 : ℝ) / (3 * y)) y := by
  have h :=
    Real.hasDerivAt_rpow_const (x := y) (p := (1 / 3 : ℝ))
      (Or.inl hy.ne')
  convert h using 1
  rw [Real.rpow_sub hy]
  simp only [Real.rpow_one]
  field_simp [hy.ne']
  exact Real.rpow_eq_pow y (1 / 3 : ℝ)

private theorem hasDerivAt_cubeRoot {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt cubeRoot (cubeRoot y / (3 * y)) y := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hpos := hasDerivAt_rpow_third_of_pos (neg_pos.mpr hy)
    have hcomp := hpos.comp y (hasDerivAt_id y).neg
    have hneg := hcomp.neg
    have heq :
        cubeRoot =ᶠ[nhds y]
          ((-(fun z : ℝ => Real.rpow z (1 / 3 : ℝ))) ∘ Neg.neg) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      have hz' : z < 0 := hz
      simp [cubeRoot, Function.comp_def, Real.sign_of_neg hz', abs_of_neg hz']
    have hfinal := hneg.congr_of_eventuallyEq heq
    convert hfinal using 1
    simp [cubeRoot, Real.sign_of_neg hy, abs_of_neg hy]
    field_simp [hy.ne]
  · have hpos := hasDerivAt_rpow_third_of_pos hy
    have heq :
        cubeRoot =ᶠ[nhds y]
          (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      have hz' : 0 < z := hz
      simp [cubeRoot, Real.sign_of_pos hz', abs_of_pos hz']
    have hfinal := hpos.congr_of_eventuallyEq heq
    simpa [cubeRoot, Real.sign_of_pos hy, abs_of_pos hy] using hfinal

private theorem t_cubed (x : ℝ) : t x ^ 3 = Real.tan x := by
  unfold t
  exact cubeRoot_cubed (Real.tan x)

private theorem t_hasDerivAt (x : ℝ) (hcos : Real.cos x ≠ 0)
    (htan : Real.tan x ≠ 0) :
    HasDerivAt t
      (t x / (3 * Real.tan x) * (1 / Real.cos x ^ 2)) x := by
  have h :=
    (hasDerivAt_cubeRoot htan).comp x (Real.hasDerivAt_tan hcos)
  simpa [t, Function.comp_def] using h

private theorem branch_mem_mainInterval {x : ℝ} (hx : x ∈ branch) :
    x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rcases hx with hx | hx
  · change -(Real.pi / 2) < x ∧ x < 0 at hx
    exact ⟨hx.1, by linarith [Real.pi_pos]⟩
  · change 0 < x ∧ x < Real.pi / 2 at hx
    exact ⟨by linarith [Real.pi_pos], hx.2⟩

private theorem branch_cos_ne {x : ℝ} (hx : x ∈ branch) :
    Real.cos x ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo (branch_mem_mainInterval hx)).ne'

private theorem branch_tan_ne {x : ℝ} (hx : x ∈ branch) :
    Real.tan x ≠ 0 := by
  rcases hx with hx | hx
  · change -(Real.pi / 2) < x ∧ x < 0 at hx
    exact (Real.tan_neg_of_neg_of_pi_div_two_lt hx.2 hx.1).ne
  · change 0 < x ∧ x < Real.pi / 2 at hx
    exact (Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2).ne'

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    x = Real.arctan (t x ^ 3) := by
  rw [t_cubed]
  exact (Real.arctan_tan
    (branch_mem_mainInterval hx).1 (branch_mem_mainInterval hx).2).symm
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun u : ℝ => Real.arctan (u ^ 3))
      (3 * t x ^ 2 / (1 + t x ^ 6)) (t x) := by
  have h :
      HasDerivAt (fun u : ℝ => Real.arctan (u ^ 3))
        (1 / (1 + (t x ^ 3) ^ 2) * (3 * t x ^ 2)) (t x) := by
    simpa using (((hasDerivAt_id (t x)).pow 3).arctan)
  convert h using 1
  ring
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    integrand x = firstRational (t x) * deriv t x := by
  have hcos := branch_cos_ne hx
  have htan := branch_tan_ne hx
  have ht3 := t_cubed x
  have htne : t x ≠ 0 := by
    intro ht
    apply htan
    rw [← ht3, ht]
    norm_num
  have htrig := Real.one_add_tan_sq_mul_cos_sq_eq_one hcos
  rw [(t_hasDerivAt x hcos htan).deriv]
  unfold integrand firstRational
  change
    1 / t x =
      3 * t x / (1 + t x ^ 6) *
        (t x / (3 * Real.tan x) *
          (1 / Real.cos x ^ 2))
  rw [show t x ^ 6 = (t x ^ 3) ^ 2 by ring, ht3]
  have hden : 1 + Real.tan x ^ 2 ≠ 0 := by positivity
  field_simp [htne, htan, hcos, hden]
  calc
    Real.tan x * (1 + Real.tan x ^ 2) * Real.cos x ^ 2 =
        Real.tan x * ((1 + Real.tan x ^ 2) * Real.cos x ^ 2) := by ring
    _ = Real.tan x := by rw [htrig]; ring
    _ = t x ^ 3 := ht3.symm
theorem gap4 (u : ℝ) : firstRational u = squareRational u := by
  have hderiv : deriv (fun v : ℝ => v ^ 2) u = 2 * u := by
    simpa using ((hasDerivAt_id u).pow 2).deriv
  unfold firstRational squareRational
  rw [hderiv]
  ring
theorem gap5 (u : ℝ) : HasDerivAt primitiveT (firstRational u) u := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 3 ≠ 0 := hspos.ne'
  have hssq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hupos : 0 < u ^ 2 + 1 := by
    nlinarith [sq_nonneg u]
  have hApos : 0 < (u ^ 2 + 1) ^ 2 := sq_pos_of_pos hupos
  have hBpos : 0 < u ^ 4 - u ^ 2 + 1 := by
    nlinarith [sq_nonneg (u ^ 2 - (1 / 2 : ℝ))]
  have hDpos : 0 < 1 + u ^ 6 := by positivity
  have hfactor :
      (u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1) = 1 + u ^ 6 := by
    ring
  have hA :
      HasDerivAt (fun v : ℝ => (v ^ 2 + 1) ^ 2)
        (4 * u * (u ^ 2 + 1)) u := by
    convert (((hasDerivAt_id u).pow 2).add_const 1).pow 2 using 1 <;>
      simp <;> ring
  have hB :
      HasDerivAt (fun v : ℝ => v ^ 4 - v ^ 2 + 1)
        (4 * u ^ 3 - 2 * u) u := by
    convert (((hasDerivAt_id u).pow 4).sub
      ((hasDerivAt_id u).pow 2)).add_const 1 using 1 <;>
      simp <;> ring
  have hR := hA.div hB hBpos.ne'
  have hRpos :
      0 < (u ^ 2 + 1) ^ 2 / (u ^ 4 - u ^ 2 + 1) :=
    div_pos hApos hBpos
  have hLogRaw := (Real.hasDerivAt_log hRpos.ne').comp u hR
  have hLog :
      HasDerivAt
        (fun v : ℝ =>
          Real.log ((v ^ 2 + 1) ^ 2 / (v ^ 4 - v ^ 2 + 1)))
        (6 * u * (1 - u ^ 2) /
          ((u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1))) u := by
    convert hLogRaw using 1
    field_simp [hupos.ne', hApos.ne', hBpos.ne']
    <;> ring
  have hQ :
      HasDerivAt (fun v : ℝ => (2 * v ^ 2 - 1) / Real.sqrt 3)
        (4 * u / Real.sqrt 3) u := by
    convert ((((hasDerivAt_id u).pow 2).const_mul 2).sub_const 1).div_const
      (Real.sqrt 3) using 1 <;>
      simp <;> ring
  have hQdenpos :
      0 < 1 + ((2 * u ^ 2 - 1) / Real.sqrt 3) ^ 2 := by
    positivity
  have hAtanDen :
      (Real.sqrt 3) ^ 2 *
          (1 + ((2 * u ^ 2 - 1) / Real.sqrt 3) ^ 2) =
        4 * (u ^ 4 - u ^ 2 + 1) := by
    calc
      (Real.sqrt 3) ^ 2 *
            (1 + ((2 * u ^ 2 - 1) / Real.sqrt 3) ^ 2) =
          (Real.sqrt 3) ^ 2 + (2 * u ^ 2 - 1) ^ 2 := by
        field_simp [hsne]
        <;> ring
      _ = 4 * (u ^ 4 - u ^ 2 + 1) := by
        rw [hssq]
        ring
  have hAtanRaw := hQ.arctan
  have hAtan :
      HasDerivAt
        (fun v : ℝ => Real.arctan ((2 * v ^ 2 - 1) / Real.sqrt 3))
        (Real.sqrt 3 * u / (u ^ 4 - u ^ 2 + 1)) u := by
    convert hAtanRaw using 1
    symm
    calc
      1 / (1 + ((2 * u ^ 2 - 1) / Real.sqrt 3) ^ 2) *
            (4 * u / Real.sqrt 3) =
          4 * u * Real.sqrt 3 /
            ((Real.sqrt 3) ^ 2 *
              (1 + ((2 * u ^ 2 - 1) / Real.sqrt 3) ^ 2)) := by
        field_simp [hsne, hQdenpos.ne']
        <;> ring
      _ = 4 * u * Real.sqrt 3 /
            (4 * (u ^ 4 - u ^ 2 + 1)) := by
        rw [hAtanDen]
      _ = Real.sqrt 3 * u / (u ^ 4 - u ^ 2 + 1) := by
        field_simp [hBpos.ne']
        <;> ring
  have hFinal :
      HasDerivAt primitiveT
        ((1 / 4 : ℝ) *
            (6 * u * (1 - u ^ 2) /
              ((u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1))) +
          Real.sqrt 3 / 2 *
            (Real.sqrt 3 * u / (u ^ 4 - u ^ 2 + 1))) u := by
    simpa only [primitiveT] using
      (hLog.const_mul (1 / 4 : ℝ)).add
        (hAtan.const_mul (Real.sqrt 3 / 2))
  have hcoeff :
      (1 / 4 : ℝ) *
            (6 * u * (1 - u ^ 2) /
              ((u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1))) +
          Real.sqrt 3 / 2 *
            (Real.sqrt 3 * u / (u ^ 4 - u ^ 2 + 1)) =
        firstRational u := by
    unfold firstRational
    calc
      (1 / 4 : ℝ) *
              (6 * u * (1 - u ^ 2) /
                ((u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1))) +
            Real.sqrt 3 / 2 *
              (Real.sqrt 3 * u / (u ^ 4 - u ^ 2 + 1)) =
          (3 * u * (1 - u ^ 2) +
              (Real.sqrt 3) ^ 2 * u * (u ^ 2 + 1)) /
            (2 * (u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1)) := by
        field_simp [hsne, hupos.ne', hBpos.ne']
        <;> ring
      _ = (3 * u * (1 - u ^ 2) +
              3 * u * (u ^ 2 + 1)) /
            (2 * (u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1)) := by
        rw [hssq]
      _ = 3 * u /
            ((u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1)) := by
        field_simp [hupos.ne', hBpos.ne']
        <;> ring
      _ = 3 * u / (1 + u ^ 6) := by rw [hfactor]
  rw [hcoeff] at hFinal
  exact hFinal

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hcos := branch_cos_ne hx
  have htan := branch_tan_ne hx
  have ht := t_hasDerivAt x hcos htan
  have hcomp := (gap5 (t x)).comp x ht
  unfold primitive
  convert hcomp using 1
  rw [← ht.deriv]
  exact gap3 x hx

theorem gap6 : Family integrand = BranchwiseTranslates primitive := by
  have hopenL : IsOpen leftBranch := by
    simpa [leftBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (-(Real.pi / 2)) (0 : ℝ)))
  have hopenR : IsOpen rightBranch := by
    simpa [rightBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  have hpreL : IsPreconnected leftBranch := by
    simpa [leftBranch] using
      (convex_Ioo (-(Real.pi / 2)) (0 : ℝ)).isPreconnected
  have hpreR : IsPreconnected rightBranch := by
    simpa [rightBranch] using
      (convex_Ioo (0 : ℝ) (Real.pi / 2)).isPreconnected
  have hxL : -(Real.pi / 4) ∈ leftBranch := by
    change -(Real.pi / 2) < -(Real.pi / 4) ∧ -(Real.pi / 4) < 0
    constructor <;> nlinarith [Real.pi_pos]
  have hxR : Real.pi / 4 ∈ rightBranch := by
    change 0 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ Cleft Cright,
        (∀ x ∈ leftBranch, F x = primitive x + Cleft) ∧
        ∀ x ∈ rightBranch, F x = primitive x + Cright
  constructor
  · intro hF
    let q : ℝ → ℝ := fun x => F x - primitive x
    have hzeroL : ∀ x ∈ leftBranch, HasDerivAt q 0 x := by
      intro x hx
      dsimp [q]
      convert (hF x (Or.inl hx)).sub
        (primitive_hasDerivAt x (Or.inl hx)) using 1
      ring
    have hzeroR : ∀ x ∈ rightBranch, HasDerivAt q 0 x := by
      intro x hx
      dsimp [q]
      convert (hF x (Or.inr hx)).sub
        (primitive_hasDerivAt x (Or.inr hx)) using 1
      ring
    have hdiffL : DifferentiableOn ℝ q leftBranch := by
      intro x hx
      exact (hzeroL x hx).differentiableAt.differentiableWithinAt
    have hdiffR : DifferentiableOn ℝ q rightBranch := by
      intro x hx
      exact (hzeroR x hx).differentiableAt.differentiableWithinAt
    have hderivL : ∀ x ∈ leftBranch, deriv q x = 0 :=
      fun x hx => (hzeroL x hx).deriv
    have hderivR : ∀ x ∈ rightBranch, deriv q x = 0 :=
      fun x hx => (hzeroR x hx).deriv
    refine
      ⟨F (-(Real.pi / 4)) - primitive (-(Real.pi / 4)),
        F (Real.pi / 4) - primitive (Real.pi / 4), ?_, ?_⟩
    · intro x hx
      have heq : q x = q (-(Real.pi / 4)) :=
        hopenL.is_const_of_deriv_eq_zero hpreL hdiffL hderivL hx hxL
      dsimp [q] at heq
      linarith
    · intro x hx
      have heq : q x = q (Real.pi / 4) :=
        hopenR.is_const_of_deriv_eq_zero hpreR hdiffR hderivR hx hxR
      dsimp [q] at heq
      linarith
  · rintro ⟨Cleft, Cright, hleft, hright⟩
    intro x hx
    rcases hx with hx | hx
    · apply
        ((primitive_hasDerivAt x (Or.inl hx)).add_const Cleft).congr_of_eventuallyEq
      filter_upwards [hopenL.mem_nhds hx] with y hy
      exact hleft y hy
    · apply
        ((primitive_hasDerivAt x (Or.inr hx)).add_const Cright).congr_of_eventuallyEq
      filter_upwards [hopenR.mem_nhds hx] with y hy
      exact hright y hy

end
end ProofGap.Exercise2010
