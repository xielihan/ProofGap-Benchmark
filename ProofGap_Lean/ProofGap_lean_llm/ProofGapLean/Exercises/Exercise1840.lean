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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1840

noncomputable section

def branch : Set ℝ := Set.univ
def denominator (x : ℝ) := x ^ 2 + x + 1
def integrand (x : ℝ) := (x + 1) / denominator x
def rewrittenIntegrand (x : ℝ) :=
  ((1 / 2 : ℝ) * (2 * x + 1) + 1 / 2) / denominator x
def logIntegrand (x : ℝ) := (2 * x + 1) / denominator x
def atanIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => t + 1 / 2) x /
    ((x + 1 / 2) ^ 2 + (Real.sqrt 3 / 2) ^ 2)
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * Real.log (denominator x) +
    1 / Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn logIntegrand,
    ∃ H ∈ AntiderivativesOn atanIntegrand,
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem denominator_pos (x : ℝ) : 0 < denominator x := by
  unfold denominator
  nlinarith [sq_nonneg (x + 1 / 2)]

private theorem denominator_hasDerivAt (x : ℝ) :
    HasDerivAt denominator (2 * x + 1) x := by
  unfold denominator
  convert
    (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1
      using 1 <;>
    simp only [id_eq] <;>
    ring

private theorem log_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.log (denominator y)) (logIntegrand x) x := by
  have hdne : denominator x ≠ 0 := ne_of_gt (denominator_pos x)
  have hraw :=
    (Real.hasDerivAt_log hdne).comp x (denominator_hasDerivAt x)
  unfold logIntegrand
  convert hraw using 1
  ring

private theorem atanIntegrand_eq (x : ℝ) :
    atanIntegrand x = 1 / denominator x := by
  have haff : HasDerivAt (fun t : ℝ => t + 1 / 2) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 / 2)
  rw [atanIntegrand, haff.deriv]
  unfold denominator
  congr 1
  rw [div_pow, sqrt_three_sq]
  ring

private theorem rewritten_split (x : ℝ) :
    rewrittenIntegrand x =
      (1 / 2 : ℝ) * logIntegrand x +
        (1 / 2 : ℝ) * atanIntegrand x := by
  rw [atanIntegrand_eq]
  unfold rewrittenIntegrand logIntegrand
  have hdne : denominator x ≠ 0 := ne_of_gt (denominator_pos x)
  field_simp [hdne]

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hsne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hdne : denominator x ≠ 0 := ne_of_gt (denominator_pos x)
  have hinner : HasDerivAt
      (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
      (2 / Real.sqrt 3) x := by
    convert
      (((hasDerivAt_id x).const_mul 2).add_const 1).div_const
        (Real.sqrt 3) using 1 <;>
      ring
  have hatan :=
    (Real.hasDerivAt_arctan ((2 * x + 1) / Real.sqrt 3)).comp x hinner
  have hargden :
      1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 =
        4 * denominator x / 3 := by
    unfold denominator
    field_simp [hsne]
    rw [sqrt_three_sq]
    ring
  have hraw :=
    ((log_hasDerivAt x).const_mul (1 / 2 : ℝ)).add
      (hatan.const_mul (1 / Real.sqrt 3))
  unfold primitive integrand
  convert hraw using 1
  unfold logIntegrand
  rw [hargden]
  field_simp [hsne, hdne]
  rw [sqrt_three_sq]
  ring

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn rewrittenIntegrand := by
  have hfun : integrand = rewrittenIntegrand := by
    funext x
    unfold integrand rewrittenIntegrand
    ring
  rw [hfun]
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand = SplitFamily := by
  ext F
  simp only [AntiderivativesOn, SplitFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => Real.log (denominator x)
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      exact log_hasDerivAt x
    · let H : ℝ → ℝ := fun x => 2 * F x - G x
      refine ⟨H, ?_, ?_⟩
      · intro x hx
        have hraw :=
          ((hF x hx).const_mul 2).sub (log_hasDerivAt x)
        have hcoef :
            2 * rewrittenIntegrand x - logIntegrand x =
              atanIntegrand x := by
          rw [rewritten_split]
          ring
        rw [← hcoef]
        simpa [H, G] using hraw
      · intro x hx
        dsimp [H, G]
        ring
  · rintro ⟨G, hG, H, hH, hF⟩
    have hfun :
        F = fun x => (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * H x := by
      funext x
      exact hF x (Set.mem_univ x)
    rw [hfun]
    intro x hx
    have hraw :=
      ((hG x hx).const_mul (1 / 2 : ℝ)).add
        ((hH x hx).const_mul (1 / 2 : ℝ))
    rw [rewritten_split]
    exact hraw
theorem gap3 :
    AntiderivativesOn integrand = SplitFamily := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using
        (hF x (Set.mem_univ x)).sub (primitive_hasDerivAt x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun x => (hzero x).deriv)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc : F x - primitive x = F 0 - primitive 0 :=
      hconst x 0
    linarith
  · rintro ⟨C, hFC⟩
    have hfun : F = fun x => primitive x + C := by
      funext x
      exact hFC x (Set.mem_univ x)
    rw [hfun]
    intro x hx
    exact (primitive_hasDerivAt x).add_const C

end
end ProofGap.Exercise1840
