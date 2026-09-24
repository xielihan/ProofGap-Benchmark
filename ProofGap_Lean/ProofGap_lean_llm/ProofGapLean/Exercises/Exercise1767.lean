import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1767

noncomputable section

def subst (x : ℝ) : ℝ := 1 - 5 * x ^ 2
def integrand (x : ℝ) : ℝ := x ^ 3 * subst x ^ 10
def intermediate (x : ℝ) : ℝ :=
  -(1 / 550 : ℝ) * subst x ^ 11 + (1 / 600 : ℝ) * subst x ^ 12
def primitive (x : ℝ) : ℝ :=
  -(1 + 55 * x ^ 2) / 6600 * subst x ^ 11
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem hasDerivAt_succ_pow
    (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) :
    ∀ n : ℕ, HasDerivAt (fun y => f y ^ (n + 1))
      (((n : ℝ) + 1) * f x ^ n * f') x := by
  intro n
  induction n with
  | zero =>
      simpa using hf
  | succ n ih =>
      convert ih.mul hf using 1 <;> simp [pow_succ] <;> ring

private theorem hasDerivAt_square (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  convert
    (hasDerivAt_succ_pow (fun y : ℝ => y) 1 x (hasDerivAt_id x) 1) using 1 <;>
    ring

private theorem hasDerivAt_subst (x : ℝ) :
    HasDerivAt subst (-10 * x) x := by
  unfold subst
  convert
    (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_square x).const_mul 5) using 1 <;>
    ring

private theorem eq_at_zero_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 := by
  have hdiff : Differentiable ℝ f := fun y => (hf y).differentiableAt
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg hdiff (fun y => by rw [(hf y).deriv])
  have hanti : Antitone f :=
    antitone_of_deriv_nonpos hdiff (fun y => by rw [(hf y).deriv])
  rcases le_total x 0 with hx | hx
  · exact le_antisymm (hmono hx) (hanti hx)
  · exact le_antisymm (hanti hx) (hmono hx)

theorem gap1 (x : ℝ) :
    x ^ 2 = (1 / 5 : ℝ) * (1 - subst x) := by
  unfold subst
  ring

theorem gap2 (x : ℝ) :
    x ^ 3 = (1 / 2 : ℝ) * x ^ 2 * deriv (fun y : ℝ => y ^ 2) x := by
  rw [(hasDerivAt_square x).deriv]
  ring

theorem gap3 (x : ℝ) :
    (1 / 2 : ℝ) * x ^ 2 * deriv (fun y : ℝ => y ^ 2) x =
      (1 / 10 : ℝ) * (1 - subst x) * (-1 / 5) * deriv subst x := by
  rw [(hasDerivAt_square x).deriv, (hasDerivAt_subst x).deriv]
  unfold subst
  ring

theorem gap4 (x : ℝ) :
    (1 / 10 : ℝ) * (1 - subst x) * (-1 / 5) * deriv subst x =
      -(1 / 50 : ℝ) * (1 - subst x) * deriv subst x := by
  ring

theorem gap5 (x : ℝ) :
    integrand x =
      -(1 / 50 : ℝ) * (subst x ^ 10 - subst x ^ 11) * deriv subst x := by
  unfold integrand
  rw [gap2 x, gap3 x, gap4 x]
  ring

theorem gap6 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have h11 :
      HasDerivAt (fun y => subst y ^ 11)
        (11 * subst x ^ 10 * (-10 * x)) x := by
    convert
      (hasDerivAt_succ_pow subst (-10 * x) x (hasDerivAt_subst x) 10) using 1 <;>
      ring
  have h12 :
      HasDerivAt (fun y => subst y ^ 12)
        (12 * subst x ^ 11 * (-10 * x)) x := by
    convert
      (hasDerivAt_succ_pow subst (-10 * x) x (hasDerivAt_subst x) 11) using 1 <;>
      ring
  have hi :
      HasDerivAt intermediate
        (-(1 / 550 : ℝ) * (11 * subst x ^ 10 * (-10 * x)) +
          (1 / 600 : ℝ) * (12 * subst x ^ 11 * (-10 * x))) x := by
    unfold intermediate
    convert
      (h11.const_mul (-(1 / 550 : ℝ))).add
        (h12.const_mul (1 / 600 : ℝ)) using 1 <;>
      ring
  convert hi using 1
  unfold integrand subst
  ring

theorem gap7 (x : ℝ) :
    intermediate x =
      -(1 / 550 : ℝ) * subst x ^ 11 + (1 / 600 : ℝ) * subst x ^ 12 := by
  rfl

theorem gap8 (x : ℝ) :
    intermediate x = primitive x := by
  unfold intermediate primitive subst
  ring

theorem gap9 :
    Family integrand = Translates primitive := by
  apply Set.ext
  intro F
  change IsAntiderivative F integrand ↔ ∃ C, ∀ x, F x = primitive x + C
  have hIP : intermediate = primitive := funext gap8
  have hP : IsAntiderivative primitive integrand := by
    intro x
    rw [← hIP]
    exact gap6 x
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hG : ∀ y, HasDerivAt G 0 y := by
      intro y
      dsimp [G]
      convert (hF y).sub (hP y) using 1 <;> ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := eq_at_zero_of_hasDerivAt_zero G hG x
    dsimp [G] at hc
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hC⟩
    intro x
    have hsum :
        HasDerivAt (primitive + fun _ => C) (integrand x) x := by
      simpa using (hP x).add (hasDerivAt_const x C)
    have hfun : (primitive + fun _ => C) = F := by
      funext y
      simpa using (hC y).symm
    exact hfun ▸ hsum

end

end ProofGap.Exercise1767
