import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1887

noncomputable section

def integrand (x : ℝ) : ℝ :=
  1 / ((1 + x) * (1 + x ^ 2) * (1 + x ^ 3))
def domain : Set ℝ := {x | x ≠ -1}
def primitive (x : ℝ) : ℝ :=
  (1 / 6 : ℝ) * Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)) -
    1 / (6 * (x + 1)) +
    (1 / 2 : ℝ) * Real.arctan x -
    1 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * x - 1) / Real.sqrt 3)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D E F : ℝ) : Prop :=
  ∀ x, 1 =
    A * (x + 1) * (x ^ 2 + 1) * (x ^ 2 - x + 1) +
      B * (x ^ 2 + 1) * (x ^ 2 - x + 1) +
      (C * x + D) * (x + 1) ^ 2 * (x ^ 2 - x + 1) +
      (E * x + F) * (x + 1) ^ 2 * (x ^ 2 + 1)

private theorem coeff_values (A B C D E F : ℝ)
    (h : CoeffIdentity A B C D E F) :
    A = 1 / 3 ∧ B = 1 / 6 ∧ C = 0 ∧ D = 1 / 2 ∧
      E = -(1 / 3 : ℝ) ∧ F = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  have h3 := h 3
  norm_num at h0 h1 hm1 h2 hm2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem gap1 :
    ∃ A B C D E F : ℝ, CoeffIdentity A B C D E F := by
  refine ⟨1 / 3, 1 / 6, 0, 1 / 2, -(1 / 3), 0, ?_⟩
  intro x
  ring

theorem gap2 (A B C D E F x : ℝ) (h : CoeffIdentity A B C D E F) :
    1 =
      A * (x + 1) * (x ^ 2 + 1) * (x ^ 2 - x + 1) +
        B * (x ^ 2 + 1) * (x ^ 2 - x + 1) +
        (C * x + D) * (x + 1) ^ 2 * (x ^ 2 - x + 1) +
        (E * x + F) * (x + 1) ^ 2 * (x ^ 2 + 1) := by
  exact h x

theorem gap3 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    A + C + E = 0 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap4 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    B + C + D + 2 * E + F = 0 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap5 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    A - B + D + 2 * E + 2 * F = 0 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap6 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    A + 2 * B + C + 2 * E + 2 * F = 0 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap7 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    B + C + D + E + 2 * F = 1 / 3 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap8 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    A + B + D + E = 2 / 3 := by
  rcases coeff_values A B C D E F h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  norm_num

theorem gap9 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    A = 1 / 3 := by
  exact (coeff_values A B C D E F h).1

theorem gap10 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    B = 1 / 6 := by
  exact (coeff_values A B C D E F h).2.1

theorem gap11 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    C = 0 := by
  exact (coeff_values A B C D E F h).2.2.1

theorem gap12 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    D = 1 / 2 := by
  exact (coeff_values A B C D E F h).2.2.2.1

theorem gap13 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    E = -(1 / 3 : ℝ) := by
  exact (coeff_values A B C D E F h).2.2.2.2.1

theorem gap14 (A B C D E F : ℝ) (h : CoeffIdentity A B C D E F) :
    F = 0 := by
  exact (coeff_values A B C D E F h).2.2.2.2.2

theorem gap15 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      1 / (3 * (x + 1)) + 1 / (6 * (x + 1) ^ 2) +
        1 / (2 * (x ^ 2 + 1)) -
        x / (3 * (x ^ 2 - x + 1)) := by
  have hx1 : x + 1 ≠ 0 := by
    intro hz
    apply hx
    linarith
  have hx2 : x ^ 2 + 1 ≠ 0 := by positivity
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  unfold integrand
  rw [show 1 + x = x + 1 by ring]
  rw [show 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) by ring]
  have hq' : 1 - x + x ^ 2 ≠ 0 := by nlinarith
  rw [show x ^ 2 - x + 1 = 1 - x + x ^ 2 by ring]
  field_simp [hx1, hx2, hq']
  ring

private def expandedPrimitive (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.log |x + 1| -
    (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1) -
    (1 / 6 : ℝ) * (x + 1)⁻¹ +
    (1 / 2 : ℝ) * Real.arctan x -
    1 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * x - 1) / Real.sqrt 3)

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using
    (isOpen_ne : IsOpen {x : ℝ | x ≠ (-1 : ℝ)})

private theorem primitive_eq_expanded {x : ℝ} (hx : x ∈ domain) :
    primitive x = expandedPrimitive x := by
  have hx1 : x + 1 ≠ 0 := by
    intro hz
    apply hx
    linarith
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  have hlog :
      Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)) =
        2 * Real.log |x + 1| - Real.log (x ^ 2 - x + 1) := by
    rw [Real.log_div (pow_ne_zero 2 hx1) hq, Real.log_pow]
    simp only [Real.log_abs]
    norm_num
  unfold primitive expandedPrimitive
  rw [hlog]
  field_simp [hx1]
  ring

private theorem expandedPrimitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (integrand x) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro hz
    apply hx
    linarith
  have hx2 : x ^ 2 + 1 ≠ 0 := by positivity
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hl1 :
      HasDerivAt (fun y : ℝ => Real.log |y + 1|) (1 / (x + 1)) x := by
    have hraw :=
      (Real.hasDerivAt_log hx1).comp x ((hasDerivAt_id x).add_const 1)
    simpa only [Function.comp_def, Real.log_abs, id_eq, mul_one, one_div] using hraw
  have hquad :
      HasDerivAt (fun y : ℝ => y ^ 2 - y + 1) (2 * x - 1) x := by
    convert
      (((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).add_const 1
        using 1 <;>
      simp only [id_eq] <;>
      ring
  have hlq :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 2 - y + 1))
        ((2 * x - 1) / (x ^ 2 - x + 1)) x := by
    have hraw := (Real.hasDerivAt_log hq).comp x hquad
    convert hraw using 1 <;> ring
  have hinv :=
    (((hasDerivAt_id x).add_const 1).inv hx1).const_mul (-(1 / 6 : ℝ))
  have hatan := Real.hasDerivAt_arctan x
  have harg :
      HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    convert
      (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const
        (Real.sqrt 3) using 1 <;>
      ring
  have hatanArg :=
    (Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 3)).comp x harg
  have hargden :
      1 + ((2 * x - 1) / Real.sqrt 3) ^ 2 =
        4 * (x ^ 2 - x + 1) / 3 := by
    field_simp [hs3]
    rw [sqrt_three_sq]
    ring
  have hatancoef :
      1 / (3 * Real.sqrt 3) *
          (1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2) *
            (2 / Real.sqrt 3)) =
        1 / (6 * (x ^ 2 - x + 1)) := by
    rw [hargden]
    field_simp [hs3, hq]
    rw [sqrt_three_sq]
    ring
  have hraw :=
    ((((hl1.const_mul (1 / 3 : ℝ)).sub
      (hlq.const_mul (1 / 6 : ℝ))).add hinv).add
      (hatan.const_mul (1 / 2 : ℝ))).sub
      (hatanArg.const_mul (1 / (3 * Real.sqrt 3)))
  unfold expandedPrimitive
  convert hraw using 1
  · funext y
    simp [Function.comp_def]
    ring
  · simp only [id_eq]
    rw [hatancoef]
    unfold integrand
    rw [show 1 + x = x + 1 by ring]
    rw [show 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) by ring]
    have hq' : 1 - x + x ^ 2 ≠ 0 := by nlinarith
    rw [show x ^ 2 - x + 1 = 1 - x + x ^ 2 by ring]
    field_simp [hx1, hx2, hq']
    ring

theorem gap16 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have heq : primitive =ᶠ[nhds x] expandedPrimitive := by
    filter_upwards [domain_isOpen.mem_nhds hx] with y hy
    exact primitive_eq_expanded hy
  exact (expandedPrimitive_hasDerivAt hx).congr_of_eventuallyEq heq

theorem gap17 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : IsAntiderivativeOn primitive integrand s := by
    intro x hx
    exact gap16 x (hdom hx)
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hempty : s.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hempty
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        IsOpen.is_const_of_deriv_eq_zero hopen hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hempty ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    apply ((hprimitive x hx).add_const C).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1887
