import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1891

noncomputable section

def q₁ (x : ℝ) : ℝ := (x - 1) * (x + 1) ^ 2
def q₂ (x : ℝ) : ℝ := (x - 1) * (x + 1)
def integrand (x : ℝ) : ℝ := x / ((x - 1) ^ 2 * (x + 1) ^ 3)
def domain : Set ℝ := {x | x ≠ -1 ∧ x ≠ 1}
def primitive (x : ℝ) : ℝ :=
  -(x ^ 2 + x + 2) / (8 * (x - 1) * (x + 1) ^ 2) +
    (1 / 16 : ℝ) * Real.log |(x + 1) / (x - 1)|
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D E : ℝ) : Prop :=
  ∀ x, x =
    (2 * A * x + B) * (x - 1) * (x + 1) -
      (3 * x - 1) * (A * x ^ 2 + B * x + C) +
      (D * x + E) * (x - 1) * (x + 1) ^ 2

private theorem coeffIdentity_values (A B C D E : ℝ)
    (h : CoeffIdentity A B C D E) :
    A = -(1 / 8 : ℝ) ∧ B = -(1 / 8 : ℝ) ∧ C = -(1 / 4 : ℝ) ∧
      D = 0 ∧ E = -(1 / 8 : ℝ) := by
  have hm2 := h (-2)
  have hm1 := h (-1)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [CoeffIdentity] at hm2 hm1 h0 h1 h2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem gap1 (x : ℝ) :
    q₁ x = x ^ 3 + x ^ 2 - x - 1 := by
  unfold q₁
  ring

theorem gap2 (x : ℝ) :
    q₂ x = x ^ 2 - 1 := by
  unfold q₂
  ring

theorem gap3 :
    ∃ A B C D E : ℝ, CoeffIdentity A B C D E := by
  refine ⟨-(1 / 8 : ℝ), -(1 / 8 : ℝ), -(1 / 4 : ℝ), 0, -(1 / 8 : ℝ), ?_⟩
  unfold CoeffIdentity
  intro x
  ring

theorem gap4 (A B C D E x : ℝ) (h : CoeffIdentity A B C D E) :
    x =
      (2 * A * x + B) * (x - 1) * (x + 1) -
        (3 * x - 1) * (A * x ^ 2 + B * x + C) +
        (D * x + E) * (x - 1) * (x + 1) ^ 2 := by
  exact h x

theorem gap5 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    D = 0 := by
  exact (coeffIdentity_values A B C D E h).2.2.2.1

theorem gap6 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    -A + D + E = 0 := by
  rcases coeffIdentity_values A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  rw [hA, hD, hE]
  norm_num

theorem gap7 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    A - 2 * B - D + E = 0 := by
  rcases coeffIdentity_values A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  rw [hA, hB, hD, hE]
  norm_num

theorem gap8 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    -2 * A + B - 3 * C - D - E = 1 := by
  rcases coeffIdentity_values A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  rw [hA, hB, hC, hD, hE]
  norm_num

theorem gap9 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    -B + C - E = 0 := by
  rcases coeffIdentity_values A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  rw [hB, hC, hE]
  norm_num

theorem gap10 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    A = -(1 / 8 : ℝ) := by
  exact (coeffIdentity_values A B C D E h).1

theorem gap11 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    B = -(1 / 8 : ℝ) := by
  exact (coeffIdentity_values A B C D E h).2.1

theorem gap12 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    C = -(1 / 4 : ℝ) := by
  exact (coeffIdentity_values A B C D E h).2.2.1

theorem gap13 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    D = 0 := by
  exact gap5 A B C D E h

theorem gap14 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    E = -(1 / 8 : ℝ) := by
  exact (coeffIdentity_values A B C D E h).2.2.2.2

theorem gap15 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change x ≠ -1 ∧ x ≠ 1 at hx
  rcases hx with ⟨hxm, hxp⟩
  have hxsub : x - 1 ≠ 0 := by
    intro hzero
    apply hxp
    linarith
  have hxadd : x + 1 ≠ 0 := by
    intro hzero
    apply hxm
    linarith
  have hden0 : 8 * (x - 1) * (x + 1) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hxsub) (pow_ne_zero 2 hxadd)
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hplus : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    hid.add_const 1
  have hminus : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    hid.sub_const 1
  have hnum :
      HasDerivAt (fun y : ℝ => y ^ 2 + y + 2) (2 * x + 1) x := by
    convert ((hid.pow 2).add hid).add_const 2 using 1 <;> ring
  have hleft :
      HasDerivAt (fun y : ℝ => 8 * (y - 1)) 8 x := by
    convert hminus.const_mul 8 using 1 <;> ring
  have hsq :
      HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
    convert hplus.pow 2 using 1 <;> ring
  have hden :
      HasDerivAt
        (fun y : ℝ => 8 * (y - 1) * (y + 1) ^ 2)
        (8 * (x + 1) ^ 2 + 16 * (x - 1) * (x + 1)) x := by
    convert hleft.mul hsq using 1 <;> ring
  have hrat :
      HasDerivAt
        (fun y : ℝ => -(y ^ 2 + y + 2) / (8 * (y - 1) * (y + 1) ^ 2))
        ((-(2 * x + 1) * (8 * (x - 1) * (x + 1) ^ 2) -
            (-(x ^ 2 + x + 2)) *
              (8 * (x + 1) ^ 2 + 16 * (x - 1) * (x + 1))) /
          (8 * (x - 1) * (x + 1) ^ 2) ^ 2) x := by
    convert hnum.neg.div hden hden0 using 1 <;> ring
  have hquot :
      HasDerivAt (fun y : ℝ => (y + 1) / (y - 1))
        (-2 / (x - 1) ^ 2) x := by
    convert hplus.div hminus hxsub using 1 <;> ring
  have hquot0 : (x + 1) / (x - 1) ≠ 0 := div_ne_zero hxadd hxsub
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log |(y + 1) / (y - 1)|)
        (((x + 1) / (x - 1))⁻¹ * (-2 / (x - 1) ^ 2)) x := by
    have hraw := (Real.hasDerivAt_log hquot0).comp x hquot
    simpa only [Real.log_abs, Function.comp_def] using hraw
  have hscaled :
      HasDerivAt
        (fun y : ℝ => (1 / 16 : ℝ) * Real.log |(y + 1) / (y - 1)|)
        ((1 / 16 : ℝ) *
          (((x + 1) / (x - 1))⁻¹ * (-2 / (x - 1) ^ 2))) x := by
    convert (hasDerivAt_const x (1 / 16 : ℝ)).mul hlog using 1 <;> ring
  unfold primitive integrand
  convert hrat.add hscaled using 1
  field_simp [hxsub, hxadd] <;> ring

theorem gap16 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change (∀ x ∈ s, HasDerivAt F (integrand x) x) at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    by_cases hsne : s.Nonempty
    · rcases hsne with ⟨x₀, hx₀⟩
      have hzero :
          ∀ x ∈ s, HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
        intro x hx
        simpa using (hF x hx).sub (gap15 x (hdom hx))
      have hdiff :
          DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) s := by
        intro x hx
        exact (hzero x hx).differentiableAt.differentiableWithinAt
      have hderiv :
          ∀ x ∈ s, deriv (fun y : ℝ => F y - primitive y) x = 0 := by
        intro x hx
        exact (hzero x hx).deriv
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hsne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    change ∀ x ∈ s, HasDerivAt F (integrand x) x
    intro x hx
    have hbase :
        HasDerivAt (fun y : ℝ => primitive y + C) (integrand x) x :=
      (gap15 x (hdom hx)).add_const C
    have hevent : F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) := by
      apply Filter.mem_of_superset (hopen.mem_nhds hx)
      intro y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1891
