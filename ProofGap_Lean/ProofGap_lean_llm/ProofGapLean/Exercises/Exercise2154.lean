import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2154

noncomputable section

def branch : Set ℝ := Set.Ioo (-1) 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def s (x : ℝ) := Real.sqrt (1 - x ^ 2)
def integrand (x : ℝ) := x ^ 3 * Real.arccos x / s x
def InitialFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (x ^ 2 * Real.arccos x * deriv s x) x) ∧
    ∀ x ∈ branch, F x = -G x}
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => s x * (2 * x * Real.arccos x - x ^ 2 / s x)),
    ∀ x ∈ branch, F x = -x ^ 2 * s x * Real.arccos x + G x}
def SecondReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.arccos x * deriv (fun y : ℝ => s y ^ 3) x) x) ∧
    ∃ H ∈ AntiderivativesOn (fun x => x ^ 2),
    ∀ x ∈ branch,
      F x = -x ^ 2 * s x * Real.arccos x - 2 / 3 * G x - H x}
def ThirdReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (fun x => s x ^ 3 / s x),
    ∀ x ∈ branch,
      F x = -x ^ 2 * s x * Real.arccos x -
        2 / 3 * s x ^ 3 * Real.arccos x -
        2 / 3 * G x - 1 / 3 * x ^ 3}
def primitiveLong (x : ℝ) :=
  -x ^ 2 * s x * Real.arccos x -
    2 / 3 * s x ^ 3 * Real.arccos x -
    2 / 3 * x + 2 / 9 * x ^ 3 - 1 / 3 * x ^ 3
def primitive (x : ℝ) :=
  -(6 * x + x ^ 3) / 9 -
    (2 + x ^ 2) / 3 * s x * Real.arccos x

private theorem branch_inner_pos {x : ℝ} (hx : x ∈ branch) : 0 < 1 - x ^ 2 := by
  change -1 < x ∧ x < 1 at hx
  nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

private theorem s_ne_zero {x : ℝ} (hx : x ∈ branch) : s x ≠ 0 := by
  unfold s
  exact ne_of_gt (Real.sqrt_pos.2 (branch_inner_pos hx))

private theorem s_sq {x : ℝ} (hx : x ∈ branch) : s x ^ 2 = 1 - x ^ 2 := by
  unfold s
  exact Real.sq_sqrt (le_of_lt (branch_inner_pos hx))

private theorem hasDerivAt_s (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt s (-x / s x) x := by
  have hi : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      ((hasDerivAt_id x).pow 2) using 1 <;> simp [id] <;> ring_nf
  have hs := (Real.hasDerivAt_sqrt
    (ne_of_gt (branch_inner_pos hx))).comp x hi
  unfold s
  convert hs using 1
  field_simp [s_ne_zero hx]

private theorem deriv_s (x : ℝ) (hx : x ∈ branch) :
    deriv s x = -x / s x :=
  (hasDerivAt_s x hx).deriv

private theorem hasDerivAt_arccos_branch (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt Real.arccos (-1 / s x) x := by
  simpa [s, div_eq_mul_inv] using Real.hasDerivAt_arccos
    (ne_of_gt hx.1) (ne_of_lt hx.2)

private theorem hasDerivAt_s_cube (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => s y ^ 3) (-3 * x * s x) x := by
  have hd := (hasDerivAt_s x hx).pow 3
  convert hd using 1
  norm_num
  field_simp [s_ne_zero hx] <;> ring

private theorem deriv_s_cube (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => s y ^ 3) x = -3 * x * s x :=
  (hasDerivAt_s_cube x hx).deriv

private theorem hasDerivAt_cube_third (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
  convert ((hasDerivAt_id x).pow 3).div_const 3 using 1 <;>
    simp [id] <;> ring_nf

private theorem hasDerivAt_first_term (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => -y ^ 2 * s y * Real.arccos y)
      (integrand x - s x * (2 * x * Real.arccos x - x ^ 2 / s x)) x := by
  have hd := ((((hasDerivAt_id x).pow 2).mul (hasDerivAt_s x hx)).mul
    (hasDerivAt_arccos_branch x hx)).neg
  convert hd using 1
  · funext y
    change -(y ^ 2) * s y * Real.arccos y =
      -(y ^ 2 * s y * Real.arccos y)
    ring
  · simp [integrand, id]
    field_simp [s_ne_zero hx]
    ring

private theorem hasDerivAt_cube_arccos (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => s y ^ 3 * Real.arccos y)
      (Real.arccos x * deriv (fun y : ℝ => s y ^ 3) x - s x ^ 3 / s x) x := by
  have hd := (hasDerivAt_s_cube x hx).mul (hasDerivAt_arccos_branch x hx)
  convert hd using 1
  rw [deriv_s_cube x hx]
  field_simp [s_ne_zero hx] <;> ring

private theorem hasDerivAt_congr_branch {F P : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ branch) (hEq : ∀ y ∈ branch, F y = P y)
    (hP : HasDerivAt P d x) : HasDerivAt F d x := by
  apply hP.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hEq y hy

private theorem antiderivative_diff_constant {f p F : ℝ → ℝ}
    (hF : ∀ x ∈ branch, HasDerivAt F (f x) x)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C := by
  let D : ℝ → ℝ := fun x => F x - p x
  have hdiff : DifferentiableOn ℝ D branch := by
    intro x hx
    exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ branch, deriv D x = 0 := by
    intro x hx
    simpa [D] using ((hF x hx).sub (hp x hx)).deriv
  have h0 : (0 : ℝ) ∈ branch := by
    constructor <;> norm_num
  refine ⟨D 0, ?_⟩
  intro x hx
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero
    isPreconnected_Ioo hdiff hzero hx h0
  dsimp [D] at heq ⊢
  linarith

private theorem antiderivatives_eq_primitive_of_hasDerivAt {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    exact antiderivative_diff_constant hF hp
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    exact hasDerivAt_congr_branch hx hEq ((hp x hx).add_const C)

private theorem hasDerivAt_primitiveLong (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveLong (integrand x) x := by
  have hB := hasDerivAt_first_term x hx
  have hP := hasDerivAt_cube_arccos x hx
  have h1 := hB.sub (hP.const_mul (2 / 3))
  have h2 := h1.sub ((hasDerivAt_id x).const_mul (2 / 3))
  have h3 := h2.add ((hasDerivAt_cube_third x).const_mul (2 / 3))
  have hd := h3.sub (hasDerivAt_cube_third x)
  unfold primitiveLong
  convert hd using 1
  · funext y
    simp [id] <;> ring
  · rw [deriv_s_cube x hx]
    field_simp [s_ne_zero hx]
    ring_nf
    nlinarith [s_sq hx]

private theorem primitiveLong_eq_primitive (x : ℝ) (hx : x ∈ branch) :
    primitiveLong x = primitive x := by
  have hs : s x ^ 3 = s x * (1 - x ^ 2) := by
    calc
      s x ^ 3 = s x * s x ^ 2 := by ring
      _ = s x * (1 - x ^ 2) := by rw [s_sq hx]
  unfold primitiveLong primitive
  rw [hs]
  ring

theorem gap1 :
    AntiderivativesOn integrand = InitialFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change F ∈ InitialFamily
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).neg using 1
      rw [deriv_s x hx]
      simp only [integrand]
      ring
    · intro x hx
      simp
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hd : HasDerivAt (fun y => -G y) (integrand x) x := by
      convert (hG x hx).neg using 1
      rw [deriv_s x hx]
      simp only [integrand]
      ring
    exact hasDerivAt_congr_branch hx hFG hd
theorem gap2 :
    AntiderivativesOn integrand = FirstReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change F ∈ FirstReductionFamily
    let G : ℝ → ℝ := fun y => F y - (-y ^ 2 * s y * Real.arccos y)
    refine ⟨G, ?_, ?_⟩
    · change ∀ x ∈ branch, HasDerivAt G
        (s x * (2 * x * Real.arccos x - x ^ 2 / s x)) x
      intro x hx
      dsimp [G]
      convert (hF x hx).sub (hasDerivAt_first_term x hx) using 1 <;> ring
    · intro x hx
      dsimp [G]
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hd := (hasDerivAt_first_term x hx).add (hG x hx)
    have hd' : HasDerivAt
        (fun y => -y ^ 2 * s y * Real.arccos y + G y)
        (integrand x) x := by
      convert hd using 1 <;> ring
    exact hasDerivAt_congr_branch hx hFG hd'
theorem gap3 :
    AntiderivativesOn integrand = SecondReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change F ∈ SecondReductionFamily
    let H : ℝ → ℝ := fun y => y ^ 3 / 3
    let G : ℝ → ℝ := fun y =>
      (-3 / 2) * (F y - (-y ^ 2 * s y * Real.arccos y) + H y)
    refine ⟨G, ?_, H, ?_, ?_⟩
    · intro x hx
      have hH : HasDerivAt H (x ^ 2) x := by
        simpa [H] using hasDerivAt_cube_third x
      dsimp [G]
      have hd := ((hF x hx).sub (hasDerivAt_first_term x hx)).add hH
      convert hd.const_mul (-3 / 2) using 1
      rw [deriv_s_cube x hx]
      field_simp [s_ne_zero hx] <;> ring
    · change ∀ x ∈ branch, HasDerivAt H (x ^ 2) x
      intro x hx
      simpa [H] using hasDerivAt_cube_third x
    · intro x hx
      dsimp [G, H]
      ring
  · rintro ⟨G, hG, H, hH, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hd := ((hasDerivAt_first_term x hx).sub
      ((hG x hx).const_mul (2 / 3))).sub (hH x hx)
    have hd' : HasDerivAt
        (fun y => -y ^ 2 * s y * Real.arccos y - 2 / 3 * G y - H y)
        (integrand x) x := by
      convert hd using 1
      rw [deriv_s_cube x hx]
      field_simp [s_ne_zero hx] <;> ring
    exact hasDerivAt_congr_branch hx hFG hd'
theorem gap4 :
    AntiderivativesOn integrand = ThirdReductionFamily := by
  ext F
  constructor
  · intro hF
    have hsecond : F ∈ SecondReductionFamily := by
      rw [← gap3]
      exact hF
    rcases hsecond with ⟨G, hG, H, hH, hrep⟩
    change F ∈ ThirdReductionFamily
    let L : ℝ → ℝ := fun y =>
      G y - s y ^ 3 * Real.arccos y + 3 / 2 * H y - 1 / 2 * y ^ 3
    refine ⟨L, ?_, ?_⟩
    · change ∀ x ∈ branch, HasDerivAt L (s x ^ 3 / s x) x
      intro x hx
      dsimp [L]
      have hd := (((hG x hx).sub (hasDerivAt_cube_arccos x hx)).add
        ((hH x hx).const_mul (3 / 2))).sub
        (((hasDerivAt_id x).pow 3).const_mul (1 / 2))
      convert hd using 1 <;> simp [id] <;> ring_nf
    · intro x hx
      dsimp [L]
      rw [hrep x hx]
      ring
  · rintro ⟨L, hL, hrep⟩
    let G : ℝ → ℝ := fun y => s y ^ 3 * Real.arccos y + L y
    let H : ℝ → ℝ := fun y => y ^ 3 / 3
    have hsecond : F ∈ SecondReductionFamily := by
      refine ⟨G, ?_, H, ?_, ?_⟩
      · intro x hx
        dsimp [G]
        have hd := (hasDerivAt_cube_arccos x hx).add (hL x hx)
        convert hd using 1 <;> ring
      · change ∀ x ∈ branch, HasDerivAt H (x ^ 2) x
        intro x hx
        simpa [H] using hasDerivAt_cube_third x
      · intro x hx
        dsimp [G, H]
        rw [hrep x hx]
        ring
    rw [gap3]
    exact hsecond
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := by
  exact antiderivatives_eq_primitive_of_hasDerivAt hasDerivAt_primitiveLong
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap5]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = primitiveLong x + C := hC x hx
      _ = primitive x + C := by rw [primitiveLong_eq_primitive x hx]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hC x hx
      _ = primitiveLong x + C := by rw [primitiveLong_eq_primitive x hx]

end
end ProofGap.Exercise2154
