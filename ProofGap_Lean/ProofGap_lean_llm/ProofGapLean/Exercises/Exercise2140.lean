import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2140

noncomputable section

def branch : Set ℝ := Set.Ioo 1 2
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def q (x : ℝ) := -x ^ 2 + 3 * x - 2
def integrand (x : ℝ) := (2 * x + 3) * Real.arccos (2 * x - 3)
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (Real.arccos (2 * x - 3) *
          deriv (fun y : ℝ => y ^ 2 + 3 * y) x) x) ∧
    ∀ x ∈ branch, F x = G x}
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => (x ^ 2 + 3 * x) / Real.sqrt (q x)),
    ∀ x ∈ branch,
      F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) + G x}
def ExpandedFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn (fun x => Real.sqrt (q x)),
    ∃ B ∈ AntiderivativesOn
      (fun x => (-2 * x + 3) / Real.sqrt (q x)),
    ∃ D ∈ AntiderivativesOn (fun x => 1 / Real.sqrt (q x)),
    ∀ x ∈ branch,
      F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) -
        A x - 3 * B x + 7 * D x}
def ShiftedFamily : Set (ℝ → ℝ) :=
  {F | ∃ A : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt A
          (Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2) *
            deriv (fun y : ℝ => y - 3 / 2) x) x) ∧
    ∃ D : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt D
          (deriv (fun y : ℝ => y - 3 / 2) x /
            Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2)) x) ∧
    ∀ x ∈ branch,
      F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) -
        A x - 6 * Real.sqrt (q x) + 7 * D x}
def primitiveLong (x : ℝ) :=
  (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) -
    (2 * x - 3) / 4 * Real.sqrt (q x) -
    1 / 8 * Real.arcsin (2 * x - 3) -
    6 * Real.sqrt (q x) - 7 * Real.arccos (2 * x - 3)
def primitiveFinal (x : ℝ) :=
  (x ^ 2 + 3 * x - 55 / 8) * Real.arccos (2 * x - 3) -
    (2 * x + 21) / 4 * Real.sqrt (q x)

private theorem local_q_pos {x : ℝ} (hx : x ∈ branch) : 0 < q x := by
  change 1 < x ∧ x < 2 at hx
  have hmul : 0 < (x - 1) * (2 - x) :=
    mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  unfold q
  nlinarith [hmul]

private theorem local_sqrt_ne {x : ℝ} (hx : x ∈ branch) :
    Real.sqrt (q x) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (local_q_pos hx))

private theorem local_hasDerivAt_poly (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 + 3 * y) (2 * x + 3) x := by
  convert ((hasDerivAt_id x).pow 2).add
    ((hasDerivAt_id x).const_mul 3) using 1 <;>
    simp [id] <;> ring

private theorem local_deriv_poly (x : ℝ) :
    deriv (fun y : ℝ => y ^ 2 + 3 * y) x = 2 * x + 3 :=
  (local_hasDerivAt_poly x).deriv

private theorem local_hasDerivAt_u (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y - 3) 2 x := by
  convert ((hasDerivAt_id x).const_mul 2).sub_const 3 using 1 <;>
    simp [id] <;> ring

private theorem local_hasDerivAt_q (x : ℝ) :
    HasDerivAt q (-2 * x + 3) x := by
  unfold q
  convert (((hasDerivAt_id x).pow 2).neg.add
    ((hasDerivAt_id x).const_mul 3)).sub_const 2 using 1 <;>
    simp [id] <;> ring

private theorem local_sqrt_radical (x : ℝ) :
    Real.sqrt (1 - (2 * x - 3) ^ 2) = 2 * Real.sqrt (q x) := by
  have hrad : 1 - (2 * x - 3) ^ 2 = 4 * q x := by
    unfold q
    ring
  rw [hrad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hsqrt4]

private theorem local_hasDerivAt_acos (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.arccos (2 * y - 3))
      (-1 / Real.sqrt (q x)) x := by
  have hx' : 1 < x ∧ x < 2 := hx
  have hu_neg : 2 * x - 3 ≠ -1 := by nlinarith
  have hu_pos : 2 * x - 3 ≠ 1 := by nlinarith
  have h := (Real.hasDerivAt_arccos hu_neg hu_pos).comp x
    (local_hasDerivAt_u x)
  rw [local_sqrt_radical] at h
  have hs : Real.sqrt (q x) ≠ 0 := local_sqrt_ne hx
  convert h using 1
  field_simp

private theorem local_hasDerivAt_sqrtq (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.sqrt (q y))
      ((-2 * x + 3) / (2 * Real.sqrt (q x))) x := by
  have hq0 : q x ≠ 0 := ne_of_gt (local_q_pos hx)
  have h := (Real.hasDerivAt_sqrt hq0).comp x (local_hasDerivAt_q x)
  convert h using 1
  field_simp

private theorem local_hasDerivAt_product (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3))
      (integrand x - (x ^ 2 + 3 * x) / Real.sqrt (q x)) x := by
  have h := (local_hasDerivAt_poly x).mul (local_hasDerivAt_acos x hx)
  convert h using 1 <;> simp [integrand] <;> ring

private theorem local_hasDerivAt_B (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => 2 * Real.sqrt (q y))
      ((-2 * x + 3) / Real.sqrt (q x)) x := by
  have h := (local_hasDerivAt_sqrtq x hx).const_mul 2
  convert h using 1
  field_simp [local_sqrt_ne hx]

private theorem local_hasDerivAt_D (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => -Real.arccos (2 * y - 3))
      (1 / Real.sqrt (q x)) x := by
  convert (local_hasDerivAt_acos x hx).neg using 1
  ring

private theorem local_coeff_identity (x : ℝ) (hx : x ∈ branch) :
    integrand x - (x ^ 2 + 3 * x) / Real.sqrt (q x) -
          Real.sqrt (q x) -
          3 * ((-2 * x + 3) / Real.sqrt (q x)) +
          7 * (1 / Real.sqrt (q x)) = integrand x := by
  have hs0 : Real.sqrt (q x) ≠ 0 := local_sqrt_ne hx
  have hs2 : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt (local_q_pos hx))
  field_simp [hs0]
  rw [hs2]
  unfold q
  ring

private theorem local_hasDerivAt_reduction {G : ℝ → ℝ} {x : ℝ}
    (hG : HasDerivAt G ((x ^ 2 + 3 * x) / Real.sqrt (q x)) x)
    (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) + G y)
      (integrand x) x := by
  convert (local_hasDerivAt_product x hx).add hG using 1 <;> ring

private theorem local_hasDerivAt_remainder {F : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt F (integrand x) x) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        F y - (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3))
      ((x ^ 2 + 3 * x) / Real.sqrt (q x)) x := by
  convert hF.sub (local_hasDerivAt_product x hx) using 1 <;> ring

private theorem local_hasDerivAt_expanded {A B D : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (Real.sqrt (q x)) x)
    (hB : HasDerivAt B ((-2 * x + 3) / Real.sqrt (q x)) x)
    (hD : HasDerivAt D (1 / Real.sqrt (q x)) x)
    (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) -
          A y - 3 * B y + 7 * D y)
      (integrand x) x := by
  have h := (((local_hasDerivAt_product x hx).sub hA).sub
    (hB.const_mul 3)).add (hD.const_mul 7)
  convert h using 1
  exact (local_coeff_identity x hx).symm

private theorem local_hasDerivAt_shifted {A D : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (Real.sqrt (q x)) x)
    (hD : HasDerivAt D (1 / Real.sqrt (q x)) x)
    (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) -
          A y - 6 * Real.sqrt (q y) + 7 * D y)
      (integrand x) x := by
  have h := (((local_hasDerivAt_product x hx).sub hA).sub
    ((local_hasDerivAt_sqrtq x hx).const_mul 6)).add
    (hD.const_mul 7)
  convert h using 1
  have hs0 : Real.sqrt (q x) ≠ 0 := local_sqrt_ne hx
  have hs2 : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt (local_q_pos hx))
  field_simp [hs0]
  rw [hs2]
  unfold q
  ring

private theorem local_hasDerivAt_adjustedA {F : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt F (integrand x) x) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) -
          6 * Real.sqrt (q y) - 7 * Real.arccos (2 * y - 3) - F y)
      (Real.sqrt (q x)) x := by
  have h := (((local_hasDerivAt_product x hx).sub
    ((local_hasDerivAt_sqrtq x hx).const_mul 6)).sub
    ((local_hasDerivAt_acos x hx).const_mul 7)).sub hF
  convert h using 1
  have hs0 : Real.sqrt (q x) ≠ 0 := local_sqrt_ne hx
  have hs2 : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt (local_q_pos hx))
  field_simp [hs0]
  rw [hs2]
  unfold q
  ring

private theorem local_deriv_shift (x : ℝ) :
    deriv (fun y : ℝ => y - 3 / 2) x = 1 := by
  convert ((hasDerivAt_id x).sub_const (3 / 2)).deriv using 1 <;>
    simp [id] <;> ring

private theorem local_shift_radical (x : ℝ) :
    (1 / 2 : ℝ) ^ 2 - (x - 3 / 2) ^ 2 = q x := by
  unfold q
  ring

private theorem local_to_shifted_A {A : ℝ → ℝ} (x : ℝ)
    (hA : HasDerivAt A (Real.sqrt (q x)) x) :
    HasDerivAt A
      (Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2) *
        deriv (fun y : ℝ => y - 3 / 2) x) x := by
  simpa only [local_deriv_shift, local_shift_radical, mul_one] using hA

private theorem local_from_shifted_A {A : ℝ → ℝ} (x : ℝ)
    (hA : HasDerivAt A
      (Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2) *
        deriv (fun y : ℝ => y - 3 / 2) x) x) :
    HasDerivAt A (Real.sqrt (q x)) x := by
  simpa only [local_deriv_shift, local_shift_radical, mul_one] using hA

private theorem local_to_shifted_D {D : ℝ → ℝ} (x : ℝ)
    (hD : HasDerivAt D (1 / Real.sqrt (q x)) x) :
    HasDerivAt D
      (deriv (fun y : ℝ => y - 3 / 2) x /
        Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2)) x := by
  simpa only [local_deriv_shift, local_shift_radical] using hD

private theorem local_from_shifted_D {D : ℝ → ℝ} (x : ℝ)
    (hD : HasDerivAt D
      (deriv (fun y : ℝ => y - 3 / 2) x /
        Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2)) x) :
    HasDerivAt D (1 / Real.sqrt (q x)) x := by
  simpa only [local_deriv_shift, local_shift_radical] using hD

private theorem local_hasDerivAt_congr_branch {F G : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ branch) (hFG : ∀ y ∈ branch, F y = G y)
    (hG : HasDerivAt G d x) : HasDerivAt F d x := by
  have heq : F =ᶠ[nhds x] G := by
    change 1 < x ∧ x < 2 at hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hFG y hy
  exact heq.hasDerivAt_iff.mpr hG

private theorem local_hasDerivAt_coeff (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 + 3 * y - 55 / 8)
      (2 * x + 3) x := by
  convert (local_hasDerivAt_poly x).sub_const (55 / 8) using 1 <;>
    ring

private theorem local_hasDerivAt_linearFinal (x : ℝ) :
    HasDerivAt (fun y : ℝ => (2 * y + 21) / 4) (1 / 2) x := by
  convert (((hasDerivAt_id x).const_mul (1 / 2)).add_const
    (21 / 4)) using 1 <;> simp [id] <;> ring

private theorem local_hasDerivAt_primitiveFinal (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveFinal (integrand x) x := by
  have h := (local_hasDerivAt_coeff x).mul
      (local_hasDerivAt_acos x hx) |>.sub
    ((local_hasDerivAt_linearFinal x).mul
      (local_hasDerivAt_sqrtq x hx))
  unfold primitiveFinal
  convert h using 1
  have hs0 : Real.sqrt (q x) ≠ 0 := local_sqrt_ne hx
  have hs2 : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt (local_q_pos hx))
  field_simp [hs0]
  rw [hs2]
  unfold integrand q
  ring

private theorem local_antiderivatives_eq_primitive {p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (integrand x) x) :
    AntiderivativesOn integrand = PrimitiveFamily p := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - p y
    have hH : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      dsimp [H]
      convert (hF x hx).sub (hp x hx) using 1
      ring
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      exact (hH x hx).deriv
    refine ⟨H (3 / 2), ?_⟩
    intro x hx
    have hm : (3 / 2 : ℝ) ∈ branch := by
      change 1 < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < 2
      norm_num
    have hc : H x = H (3 / 2) :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hx hm
    dsimp [H] at hc ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    apply local_hasDerivAt_congr_branch hx hFC
    exact (hp x hx).add_const C

private theorem local_primitiveLong_eq (x : ℝ) :
    primitiveLong x = primitiveFinal x - Real.pi / 16 := by
  unfold primitiveLong primitiveFinal
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

private theorem local_primitiveFamily_eq_of_const {p r : ℝ → ℝ} {c : ℝ}
    (h : ∀ x, p x = r x + c) :
    PrimitiveFamily p = PrimitiveFamily r := by
  ext F
  change
    (∃ C : ℝ, ∀ x ∈ branch, F x = p x + C) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = r x + C
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨c + C, ?_⟩
    intro x hx
    rw [hC x hx, h x]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - c, ?_⟩
    intro x hx
    rw [hC x hx, h x]
    ring

theorem gap1 :
    AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ G : ℝ → ℝ,
        (∀ x ∈ branch,
          HasDerivAt G
            (Real.arccos (2 * x - 3) *
              deriv (fun y : ℝ => y ^ 2 + 3 * y) x) x) ∧
        ∀ x ∈ branch, F x = G x
  constructor
  · intro hF
    refine ⟨F, ?_, fun _ _ => rfl⟩
    intro x hx
    simpa [integrand, local_deriv_poly, mul_comm] using hF x hx
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    apply local_hasDerivAt_congr_branch hx hFG
    simpa [integrand, local_deriv_poly, mul_comm] using hG x hx
theorem gap2 :
    AntiderivativesOn integrand = ReductionFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ G ∈ AntiderivativesOn
        (fun x => (x ^ 2 + 3 * x) / Real.sqrt (q x)),
        ∀ x ∈ branch,
          F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) + G x
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y =>
      F y - (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3)
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      exact local_hasDerivAt_remainder (hF x hx) hx
    · intro x hx
      dsimp [G]
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    apply local_hasDerivAt_congr_branch hx hFG
    exact local_hasDerivAt_reduction (hG x hx) hx
theorem gap3 :
    AntiderivativesOn integrand = ExpandedFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ A ∈ AntiderivativesOn (fun x => Real.sqrt (q x)),
      ∃ B ∈ AntiderivativesOn
        (fun x => (-2 * x + 3) / Real.sqrt (q x)),
      ∃ D ∈ AntiderivativesOn (fun x => 1 / Real.sqrt (q x)),
      ∀ x ∈ branch,
        F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) -
          A x - 3 * B x + 7 * D x
  constructor
  · intro hF
    let A : ℝ → ℝ := fun y =>
      (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) -
        6 * Real.sqrt (q y) - 7 * Real.arccos (2 * y - 3) - F y
    let B : ℝ → ℝ := fun y => 2 * Real.sqrt (q y)
    let D : ℝ → ℝ := fun y => -Real.arccos (2 * y - 3)
    refine ⟨A, ?_, B, ?_, D, ?_, ?_⟩
    · intro x hx
      exact local_hasDerivAt_adjustedA (hF x hx) hx
    · intro x hx
      exact local_hasDerivAt_B x hx
    · intro x hx
      exact local_hasDerivAt_D x hx
    · intro x hx
      dsimp [A, B, D]
      ring
  · rintro ⟨A, hA, B, hB, D, hD, hF⟩
    intro x hx
    apply local_hasDerivAt_congr_branch hx hF
    exact local_hasDerivAt_expanded (hA x hx) (hB x hx) (hD x hx) hx
theorem gap4 :
    AntiderivativesOn integrand = ShiftedFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ A : ℝ → ℝ,
        (∀ x ∈ branch,
          HasDerivAt A
            (Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2) *
              deriv (fun y : ℝ => y - 3 / 2) x) x) ∧
        ∃ D : ℝ → ℝ,
          (∀ x ∈ branch,
            HasDerivAt D
              (deriv (fun y : ℝ => y - 3 / 2) x /
                Real.sqrt ((1 / 2) ^ 2 - (x - 3 / 2) ^ 2)) x) ∧
          ∀ x ∈ branch,
            F x = (x ^ 2 + 3 * x) * Real.arccos (2 * x - 3) -
              A x - 6 * Real.sqrt (q x) + 7 * D x
  constructor
  · intro hF
    let A : ℝ → ℝ := fun y =>
      (y ^ 2 + 3 * y) * Real.arccos (2 * y - 3) -
        6 * Real.sqrt (q y) - 7 * Real.arccos (2 * y - 3) - F y
    let D : ℝ → ℝ := fun y => -Real.arccos (2 * y - 3)
    refine ⟨A, ?_, D, ?_, ?_⟩
    · intro x hx
      exact local_to_shifted_A x (local_hasDerivAt_adjustedA (hF x hx) hx)
    · intro x hx
      exact local_to_shifted_D x (local_hasDerivAt_D x hx)
    · intro x hx
      dsimp [A, D]
      ring
  · rintro ⟨A, hA, D, hD, hF⟩
    intro x hx
    have hA' : HasDerivAt A (Real.sqrt (q x)) x :=
      local_from_shifted_A x (hA x hx)
    have hD' : HasDerivAt D (1 / Real.sqrt (q x)) x :=
      local_from_shifted_D x (hD x hx)
    apply local_hasDerivAt_congr_branch hx hF
    exact local_hasDerivAt_shifted hA' hD' hx
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := by
  calc
    AntiderivativesOn integrand = PrimitiveFamily primitiveFinal :=
      local_antiderivatives_eq_primitive local_hasDerivAt_primitiveFinal
    _ = PrimitiveFamily primitiveLong := by
      apply local_primitiveFamily_eq_of_const (c := Real.pi / 16)
      intro x
      rw [local_primitiveLong_eq x]
      ring
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveFinal := by
  exact local_antiderivatives_eq_primitive local_hasDerivAt_primitiveFinal

end
end ProofGap.Exercise2140
