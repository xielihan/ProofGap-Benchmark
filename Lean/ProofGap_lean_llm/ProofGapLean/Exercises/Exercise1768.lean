import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1768

noncomputable section

def subst (x : ℝ) : ℝ := 2 - x
def integrand (x : ℝ) : ℝ := x ^ 2 / Real.sqrt (subst x)
def intermediate (x : ℝ) : ℝ :=
  -8 * Real.sqrt (subst x) +
    (8 / 3 : ℝ) * (Real.sqrt (subst x)) ^ 3 -
    (2 / 5 : ℝ) * (Real.sqrt (subst x)) ^ 5
def primitive (x : ℝ) : ℝ :=
  -(2 / 15 : ℝ) * (32 + 8 * x + 3 * x ^ 2) * Real.sqrt (subst x)
def domain : Set ℝ := Set.Iio 2
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem antiderivatives_differ_by_constant
    {f F P : ℝ → ℝ} {s : Set ℝ}
    (hsopen : IsOpen s) (hs : Convex ℝ s) (hne : s.Nonempty)
    (hF : ∀ x ∈ s, HasDerivAt F (f x) x)
    (hP : ∀ x ∈ s, HasDerivAt P (f x) x) :
    ∃ C, ∀ x ∈ s, F x = P x + C := by
  rcases hne with ⟨x₀, hx₀⟩
  refine ⟨F x₀ - P x₀, ?_⟩
  intro x hx
  have hdiff : DifferentiableOn ℝ (fun z => F z - P z) s := by
    intro y hy
    exact ((hF y hy).sub (hP y hy)).differentiableAt.differentiableWithinAt
  have hzero : ∀ y ∈ s, deriv (fun z => F z - P z) y = 0 := by
    intro y hy
    simpa using ((hF y hy).sub (hP y hy)).deriv
  have heq : F x - P x = F x₀ - P x₀ :=
    hsopen.is_const_of_deriv_eq_zero hs.isPreconnected hdiff hzero hx hx₀
  linarith

theorem gap1 (x : ℝ) :
    x = 2 - subst x := by
  simp [subst]

theorem gap2 (x : ℝ) :
    deriv subst x = -1 := by
  have h : HasDerivAt subst (-1) x := by
    simpa [subst] using
      (hasDerivAt_const (x := x) (c := (2 : ℝ))).sub (hasDerivAt_id x)
  exact h.deriv

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      -((2 - subst x) ^ 2 / Real.sqrt (subst x)) * deriv subst x := by
  rw [gap2, ← gap1 x]
  simp [integrand]

theorem gap4 (x : ℝ) (hx : x ∈ domain) :
    (2 - subst x) ^ 2 / Real.sqrt (subst x) =
      4 / Real.sqrt (subst x) - 4 * Real.sqrt (subst x) +
        (Real.sqrt (subst x)) ^ 3 := by
  have hs : 0 < subst x := by
    have hlt : x < 2 := by simpa [domain] using hx
    simp [subst]
    linarith
  have hy0 : Real.sqrt (subst x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hy2 : (Real.sqrt (subst x)) ^ 2 = subst x :=
    Real.sq_sqrt (le_of_lt hs)
  have hy4 : (Real.sqrt (subst x)) ^ 4 = (subst x) ^ 2 := by
    calc
      (Real.sqrt (subst x)) ^ 4 = ((Real.sqrt (subst x)) ^ 2) ^ 2 := by ring
      _ = (subst x) ^ 2 := by rw [hy2]
  field_simp [hy0]
  nlinarith [hy2, hy4]

theorem gap5 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  have hs : 0 < subst x := by
    have hlt : x < 2 := by simpa [domain] using hx
    simp [subst]
    linarith
  have hy0 : Real.sqrt (subst x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hsub : HasDerivAt subst (-1) x := by
    simpa [subst] using
      (hasDerivAt_const (x := x) (c := (2 : ℝ))).sub (hasDerivAt_id x)
  have hsqrt :
      HasDerivAt (fun y => Real.sqrt (subst y))
        (-1 / (2 * Real.sqrt (subst x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hs)).comp x hsub using 1 <;> ring
  have hraw :=
    ((hsqrt.const_mul (-8)).add
      ((hsqrt.pow 3).const_mul (8 / 3))).sub
      ((hsqrt.pow 5).const_mul (2 / 5))
  have hcalc :
      HasDerivAt intermediate
        (4 / Real.sqrt (subst x) - 4 * Real.sqrt (subst x) +
          (Real.sqrt (subst x)) ^ 3) x := by
    convert hraw using 1
    field_simp [hy0]
    ring
  have hint :
      integrand x =
        4 / Real.sqrt (subst x) - 4 * Real.sqrt (subst x) +
          (Real.sqrt (subst x)) ^ 3 := by
    calc
      integrand x = (2 - subst x) ^ 2 / Real.sqrt (subst x) := by
        rw [gap3 x hx, gap2]
        ring
      _ = 4 / Real.sqrt (subst x) - 4 * Real.sqrt (subst x) +
          (Real.sqrt (subst x)) ^ 3 := gap4 x hx
  simpa only [hint] using hcalc

theorem gap6 (x : ℝ) (hx : x ∈ domain) :
    intermediate x = primitive x := by
  have hs : 0 ≤ subst x := by
    have hlt : x < 2 := by simpa [domain] using hx
    simp [subst]
    linarith
  unfold intermediate primitive
  set y : ℝ := Real.sqrt (subst x) with hy
  have hy2 : y ^ 2 = subst x := by
    simpa [hy] using Real.sq_sqrt hs
  have hx' : x = 2 - y ^ 2 := by
    calc
      x = 2 - subst x := gap1 x
      _ = 2 - y ^ 2 := by rw [hy2]
  rw [hx']
  ring

theorem gap7 :
    Family integrand domain = Translates primitive domain := by
  have hopen : IsOpen domain := by
    simpa [domain] using (isOpen_Iio : IsOpen (Set.Iio (2 : ℝ)))
  have hp : ∀ x ∈ domain, HasDerivAt primitive (integrand x) x := by
    intro x hx
    have heq : Filter.EventuallyEq (nhds x) intermediate primitive :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => gap6 y hy)
    exact (gap5 x hx).congr_of_eventuallyEq heq.symm
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    apply antiderivatives_differ_by_constant
    · exact hopen
    · simpa [domain] using (convex_Iio (2 : ℝ))
    · exact ⟨0, by simp [domain]⟩
    · exact hF
    · exact hp
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have heq : Filter.EventuallyEq (nhds x) (fun y => primitive y + C) F :=
      Filter.mem_of_superset (hopen.mem_nhds hx)
        (fun y hy => (hC y hy).symm)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq.symm

end

end ProofGap.Exercise1768
