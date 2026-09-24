import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1769

noncomputable section

def subst (x : ℝ) : ℝ := 1 - x ^ 2
def integrand (x : ℝ) : ℝ := x ^ 5 / Real.sqrt (subst x)
def intermediate (x : ℝ) : ℝ :=
  -Real.sqrt (subst x) + (2 / 3 : ℝ) * (Real.sqrt (subst x)) ^ 3 -
    (1 / 5 : ℝ) * (Real.sqrt (subst x)) ^ 5
def primitive (x : ℝ) : ℝ :=
  -(1 / 15 : ℝ) * (8 + 4 * x ^ 2 + 3 * x ^ 4) * Real.sqrt (subst x)
def domain : Set ℝ := Set.Ioo (-1) 1
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem substitution_pos {x : ℝ} (hx : x ∈ domain) : 0 < subst x := by
  change -1 < x ∧ x < 1 at hx
  have hleft : 0 < 1 - x := sub_pos.mpr hx.2
  have hright : 0 < 1 + x := by linarith [hx.1]
  have hproduct : 0 < (1 - x) * (1 + x) := mul_pos hleft hright
  unfold subst
  nlinarith

private theorem hasDerivAt_substitution (x : ℝ) :
    HasDerivAt subst (-2 * x) x := by
  simpa [subst] using
    (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)

private theorem zero_derivative_constant_on_domain
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ domain, HasDerivAt f 0 x) :
    ∀ x ∈ domain, f x = f 0 := by
  have hdiff : DifferentiableOn ℝ f domain := by
    intro x hx
    exact (hf x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ domain, deriv f x = 0 := by
    intro x hx
    exact (hf x hx).deriv
  have hzero : (0 : ℝ) ∈ domain := by
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    constructor <;> linarith
  intro x hx
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hderiv
      (x := x) (y := 0) hx hzero

theorem gap1 (x : ℝ) :
    x ^ 2 = 1 - subst x := by
  unfold subst
  ring

theorem gap2 (x : ℝ) :
    x ^ 5 = (1 / 2 : ℝ) * (x ^ 2) ^ 2 * deriv (fun y : ℝ => y ^ 2) x := by
  have hderiv : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    simpa using ((hasDerivAt_id x).pow 2).deriv
  rw [hderiv]
  ring

theorem gap3 (x : ℝ) :
    (1 / 2 : ℝ) * (x ^ 2) ^ 2 * deriv (fun y : ℝ => y ^ 2) x =
      -(1 / 2 : ℝ) * (1 - subst x) ^ 2 * deriv subst x := by
  have hpow : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    simpa using ((hasDerivAt_id x).pow 2).deriv
  have hsubst : deriv subst x = -2 * x :=
    (hasDerivAt_substitution x).deriv
  rw [hpow, hsubst]
  unfold subst
  ring

theorem gap4 (x : ℝ) :
    x ^ 5 = -(1 / 2 : ℝ) * (1 - subst x) ^ 2 * deriv subst x := by
  calc
    x ^ 5 = (1 / 2 : ℝ) * (x ^ 2) ^ 2 * deriv (fun y : ℝ => y ^ 2) x := gap2 x
    _ = -(1 / 2 : ℝ) * (1 - subst x) ^ 2 * deriv subst x := gap3 x

theorem gap5 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      -(1 / 2 : ℝ) * (1 - subst x) ^ 2 / Real.sqrt (subst x) *
        deriv subst x := by
  unfold integrand
  rw [gap4 x]
  ring

theorem gap6 (x : ℝ) (hx : x ∈ domain) :
    (1 - subst x) ^ 2 / Real.sqrt (subst x) =
      1 / Real.sqrt (subst x) - 2 * Real.sqrt (subst x) +
        (Real.sqrt (subst x)) ^ 3 := by
  let s : ℝ := Real.sqrt (subst x)
  have hu : 0 < subst x := substitution_pos hx
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact ne_of_gt (Real.sqrt_pos.2 hu)
  have hs2 : s ^ 2 = subst x := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hu)
  change (1 - subst x) ^ 2 / s = 1 / s - 2 * s + s ^ 3
  calc
    (1 - subst x) ^ 2 / s = (1 - s ^ 2) ^ 2 / s := by rw [hs2]
    _ = 1 / s - 2 * s + s ^ 3 := by
      field_simp [hs0]
      ring

theorem gap7 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  let s : ℝ := Real.sqrt (subst x)
  let d : ℝ := (1 / (2 * s)) * (-2 * x)
  have hu : 0 < subst x := substitution_pos hx
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact ne_of_gt (Real.sqrt_pos.2 hu)
  have hs2 : s ^ 2 = subst x := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hu)
  have hx2 : x ^ 2 = 1 - s ^ 2 := by
    rw [hs2]
    exact gap1 x
  have hroot : HasDerivAt (fun y : ℝ => Real.sqrt (subst y)) d x := by
    dsimp [d, s]
    exact
      (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x
        (hasDerivAt_substitution x)
  have hinter :
      HasDerivAt intermediate
        (-d + (2 / 3 : ℝ) * (3 * s ^ 2 * d) -
          (1 / 5 : ℝ) * (5 * s ^ 4 * d)) x := by
    convert
      (hroot.neg.add ((hroot.pow 3).const_mul (2 / 3 : ℝ))).sub
        ((hroot.pow 5).const_mul (1 / 5 : ℝ)) using 1
    all_goals first | rfl | (funext y; rfl) | ring
  have heq :
      -d + (2 / 3 : ℝ) * (3 * s ^ 2 * d) -
          (1 / 5 : ℝ) * (5 * s ^ 4 * d) = integrand x := by
    calc
      -d + (2 / 3 : ℝ) * (3 * s ^ 2 * d) -
          (1 / 5 : ℝ) * (5 * s ^ 4 * d) =
          x * (1 - s ^ 2) ^ 2 / s := by
            simp only [d]
            field_simp [hs0]
            ring
      _ = x ^ 5 / s := by
        rw [← hx2]
        ring
      _ = integrand x := by
        simp [integrand, s]
  rw [heq] at hinter
  exact hinter

theorem gap8 (x : ℝ) (hx : x ∈ domain) :
    intermediate x = primitive x := by
  let s : ℝ := Real.sqrt (subst x)
  have hu : 0 < subst x := substitution_pos hx
  have hs2 : s ^ 2 = subst x := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hu)
  have hx2 : x ^ 2 = 1 - s ^ 2 := by
    calc
      x ^ 2 = 1 - subst x := gap1 x
      _ = 1 - s ^ 2 := by rw [hs2]
  have hx4 : x ^ 4 = (1 - s ^ 2) ^ 2 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (1 - s ^ 2) ^ 2 := by rw [hx2]
  change
    -s + (2 / 3 : ℝ) * s ^ 3 - (1 / 5 : ℝ) * s ^ 5 =
      -(1 / 15 : ℝ) * (8 + 4 * x ^ 2 + 3 * x ^ 4) * s
  rw [hx2, hx4]
  ring

theorem gap9 :
    Family integrand domain = Translates primitive domain := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    have hzero :
        ∀ x ∈ domain,
          HasDerivAt (fun y : ℝ => F y - intermediate y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (gap7 x hx)
    have hconst := zero_derivative_constant_on_domain
      (fun y : ℝ => F y - intermediate y) hzero
    refine ⟨F 0 - intermediate 0, ?_⟩
    intro x hx
    have hc := hconst x hx
    rw [← gap8 x hx]
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hmem : ∀ᶠ y in nhds x, y ∈ domain := hopen.mem_nhds hx
    have hev : F =ᶠ[nhds x] (fun y : ℝ => intermediate y + C) :=
      hmem.mono (fun y hy => by
        calc
          F y = primitive y + C := hC y hy
          _ = intermediate y + C := by rw [gap8 y hy])
    have hadd :
        HasDerivAt (fun y : ℝ => intermediate y + C) (integrand x + 0) x := by
      exact (gap7 x hx).add (hasDerivAt_const x C)
    have hFderiv : HasDerivAt F (integrand x + 0) x :=
      hadd.congr_of_eventuallyEq hev
    simpa only [add_zero] using hFderiv

end

end ProofGap.Exercise1769
