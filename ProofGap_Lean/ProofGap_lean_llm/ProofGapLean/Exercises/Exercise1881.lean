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

namespace ProofGap.Exercise1881

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x ^ 3 + 1)
def domain : Set ℝ := {x | x ≠ -1}
def primitive (x : ℝ) : ℝ :=
  (1 / 6 : ℝ) * Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)) +
    1 / Real.sqrt 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C : ℝ) : Prop :=
  ∀ x, 1 = A * (x ^ 2 - x + 1) + (B * x + C) * (x + 1)

theorem gap1 :
    ∃ A B C : ℝ, CoeffIdentity A B C := by
  refine ⟨1 / 3, -(1 / 3), 2 / 3, ?_⟩
  intro x
  ring

theorem gap2 (A B C x : ℝ) (h : CoeffIdentity A B C) :
    1 = A * (x ^ 2 - x + 1) + (B * x + C) * (x + 1) := by
  exact h x

theorem gap3 (A B C : ℝ) (h : CoeffIdentity A B C) :
    A + B = 0 := by
  have hm := h (-1)
  have hz := h 0
  have ho := h 1
  norm_num at hm hz ho
  nlinarith

theorem gap4 (A B C : ℝ) (h : CoeffIdentity A B C) :
    -A + B + C = 0 := by
  have hm := h (-1)
  have hz := h 0
  have ho := h 1
  norm_num at hm hz ho
  nlinarith

theorem gap5 (A B C : ℝ) (h : CoeffIdentity A B C) :
    A + C = 1 := by
  simpa using (h 0).symm

theorem gap6 (A B C : ℝ) (h : CoeffIdentity A B C) :
    A = 1 / 3 := by
  have hm := h (-1)
  norm_num at hm ⊢
  linarith

theorem gap7 (A B C : ℝ) (h : CoeffIdentity A B C) :
    B = -(1 / 3 : ℝ) := by
  have hAB := gap3 A B C h
  have hA := gap6 A B C h
  linarith

theorem gap8 (A B C : ℝ) (h : CoeffIdentity A B C) :
    C = 2 / 3 := by
  have hAC := gap5 A B C h
  have hA := gap6 A B C h
  norm_num at hA ⊢
  linarith

theorem gap9 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      1 / (3 * (x + 1)) - (x - 2) / (3 * (x ^ 2 - x + 1)) := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  have hq' : 1 - x + x ^ 2 ≠ 0 := by nlinarith
  unfold integrand
  have hfactor : x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by ring
  rw [hfactor]
  have hpf :
      1 / ((x + 1) * (x ^ 2 - x + 1)) =
        (1 / 3 : ℝ) / (x + 1) +
          ((-(1 / 3 : ℝ)) * x + 2 / 3) / (x ^ 2 - x + 1) := by
    field_simp [hx1, hq]
    ring_nf
    field_simp [hq']
    ring
  rw [hpf]
  field_simp [hx1, hq]
  ring_nf

private def expandedPrimitive (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.log |x + 1| -
    (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1) +
    1 / Real.sqrt 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3)

private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using
    (isOpen_ne : IsOpen {x : ℝ | x ≠ (-1 : ℝ)})

private theorem primitive_eq_expanded {x : ℝ} (hx : x ∈ domain) :
    primitive x = expandedPrimitive x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  have hq' : 1 - x + x ^ 2 ≠ 0 := by nlinarith
  have hlog :
      Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)) =
        2 * Real.log |x + 1| - Real.log (x ^ 2 - x + 1) := by
    rw [Real.log_div (pow_ne_zero 2 hx1) hq, Real.log_pow]
    simp only [Real.log_abs]
    norm_num
  unfold primitive expandedPrimitive
  rw [hlog]
  ring

private theorem expandedPrimitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (integrand x) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hqpos : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
  have hq' : 1 - x + x ^ 2 ≠ 0 := by nlinarith
  have hsne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
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
  have harg :
      HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    convert
      (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const
        (Real.sqrt 3) using 1 <;>
      ring
  have hatan :=
    (Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 3)).comp x harg
  have hargden :
      1 + ((2 * x - 1) / Real.sqrt 3) ^ 2 =
        4 * (x ^ 2 - x + 1) / 3 := by
    field_simp [hsne]
    rw [sqrt_three_sq]
    ring
  have hatancoef :
      1 / Real.sqrt 3 *
          (1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2) *
            (2 / Real.sqrt 3)) =
        1 / (2 * (x ^ 2 - x + 1)) := by
    rw [hargden]
    field_simp [hsne, hq]
    rw [sqrt_three_sq]
    ring
  have hraw :=
    ((hl1.const_mul (1 / 3 : ℝ)).sub
      (hlq.const_mul (1 / 6 : ℝ))).add
      (hatan.const_mul (1 / Real.sqrt 3))
  unfold expandedPrimitive
  convert hraw using 1
  rw [hatancoef]
  unfold integrand
  rw [show x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) by ring]
  field_simp [hx1, hq]
  ring_nf
  field_simp [hq']
  ring

theorem gap10 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have heq : primitive =ᶠ[nhds x] expandedPrimitive := by
    filter_upwards [domain_isOpen.mem_nhds hx] with y hy
    exact primitive_eq_expanded hy
  exact (expandedPrimitive_hasDerivAt hx).congr_of_eventuallyEq heq

theorem gap11 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : IsAntiderivativeOn primitive integrand s := by
    intro x hx
    exact gap10 x (hdom hx)
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

end ProofGap.Exercise1881
