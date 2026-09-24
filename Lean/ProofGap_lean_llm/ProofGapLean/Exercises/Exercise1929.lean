import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1929

noncomputable section

def root6 (x : ℝ) := Real.rpow x (1 / 6 : ℝ)
def cubeRoot (x : ℝ) := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def xOf (t : ℝ) := t ^ 6 - 1
def nonnegativeBranch : Set ℝ := {t | 0 ≤ t}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ t ∈ s, HasDerivWithinAt F (f t) s t}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ t ∈ s, F t = p t + C}
def sourceIntegrand (t : ℝ) :=
  (1 - Real.sqrt (xOf t + 1)) /
    (1 + cubeRoot (xOf t + 1)) * deriv xOf t
def transformed₁ (t : ℝ) :=
  t ^ 5 * (1 - t ^ 3) / (1 + t ^ 2)
def transformed₂ (t : ℝ) :=
  -t ^ 6 + t ^ 4 + t ^ 3 - t ^ 2 - t + 1 +
    (t - 1) / (1 + t ^ 2)
def ScaledFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn nonnegativeBranch p,
    ∀ t ∈ nonnegativeBranch, F t = 6 * G t}
def primitive (t : ℝ) :=
  -6 / 7 * t ^ 7 + 6 / 5 * t ^ 5 + 3 / 2 * t ^ 4 -
    2 * t ^ 3 - 3 * t ^ 2 + 6 * t +
    3 * Real.log (1 + t ^ 2) - 6 * Real.arctan t

theorem gap1 (t : ℝ) :
    xOf t = t ^ 6 - 1 := by
  rfl
theorem gap2 (t : ℝ) :
    HasDerivAt xOf (6 * t ^ 5) t := by
  have h :=
    ((((((hasDerivAt_id t).mul (hasDerivAt_id t)).mul
      (hasDerivAt_id t)).mul (hasDerivAt_id t)).mul
      (hasDerivAt_id t)).mul (hasDerivAt_id t)).sub_const 1
  change HasDerivAt
    (fun x : ℝ => x * x * x * x * x * x - 1) _ t at h
  have hfun :
      (fun x : ℝ => x * x * x * x * x * x - 1) = xOf := by
    funext x
    simp only [xOf]
    ring
  rw [hfun] at h
  convert h using 1 <;> simp <;> ring

private theorem sqrt_xOf_add_one (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (xOf t + 1) = t ^ 3 := by
  rw [show xOf t + 1 = t ^ 6 by simp [xOf]]
  rw [show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (pow_nonneg ht 3)

private theorem cubeRoot_xOf_add_one (t : ℝ) (ht : 0 ≤ t) :
    cubeRoot (xOf t + 1) = t ^ 2 := by
  rw [show xOf t + 1 = t ^ 6 by simp [xOf]]
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [cubeRoot]
  · unfold cubeRoot
    rw [Real.sign_of_pos (pow_pos ht 6), abs_of_pos (pow_pos ht 6), one_mul]
    rw [show t ^ 6 = (t ^ 2) ^ 3 by ring]
    simpa [one_div] using
      (Real.pow_rpow_inv_natCast (x := t ^ 2) (n := 3)
        (sq_nonneg t) (by norm_num))

private theorem sourceIntegrand_eq (t : ℝ) (ht : t ∈ nonnegativeBranch) :
    sourceIntegrand t = 6 * transformed₁ t := by
  have ht' : 0 ≤ t := ht
  unfold sourceIntegrand transformed₁
  rw [sqrt_xOf_add_one t ht', cubeRoot_xOf_add_one t ht', (gap2 t).deriv]
  ring

private theorem transformed_eq (t : ℝ) :
    transformed₁ t = transformed₂ t := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  unfold transformed₁ transformed₂
  field_simp [hden]
  ring

private theorem primitive_hasDerivAt (t : ℝ) :
    HasDerivAt primitive (6 * transformed₂ t) t := by
  have h2 := (hasDerivAt_id t).pow 2
  have h3 := (hasDerivAt_id t).pow 3
  have h4 := (hasDerivAt_id t).pow 4
  have h5 := (hasDerivAt_id t).pow 5
  have h7 := (hasDerivAt_id t).pow 7
  have harg :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).add h2 using 1 <;>
      simp only [id_eq] <;> ring
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
        ((2 * t) / (1 + t ^ 2)) t := by
    have hden : 1 + t ^ 2 ≠ 0 := by positivity
    convert (Real.hasDerivAt_log hden).comp t harg using 1 <;> ring
  have hraw :=
    (((((((h7.const_mul (-6 / 7 : ℝ)).add
      (h5.const_mul (6 / 5 : ℝ))).add
      (h4.const_mul (3 / 2 : ℝ))).sub
      (h3.const_mul 2)).sub
      (h2.const_mul 3)).add
      ((hasDerivAt_id t).const_mul 6)).add
      (hlog.const_mul 3)).sub
      ((Real.hasDerivAt_arctan t).const_mul 6)
  unfold primitive transformed₂
  convert hraw using 1
  simp only [id_eq]
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

theorem gap3 :
    AntiderivativesOn nonnegativeBranch sourceIntegrand =
      ScaledFamily transformed₁ := by
  ext F
  change
    (∀ t ∈ nonnegativeBranch,
        HasDerivWithinAt F (sourceIntegrand t) nonnegativeBranch t) ↔
      ∃ G,
        (∀ t ∈ nonnegativeBranch,
          HasDerivWithinAt G (transformed₁ t) nonnegativeBranch t) ∧
        ∀ t ∈ nonnegativeBranch, F t = 6 * G t
  constructor
  · intro hF
    refine ⟨fun t => (1 / 6 : ℝ) * F t, ?_, ?_⟩
    · intro t ht
      have hd := (hF t ht).const_mul (1 / 6 : ℝ)
      rw [sourceIntegrand_eq t ht] at hd
      convert hd using 1 <;> ring
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have hd := (hG t ht).const_mul 6
    have hd' :
        HasDerivWithinAt (fun y => 6 * G y) (sourceIntegrand t)
          nonnegativeBranch t := by
      convert hd using 1
      rw [sourceIntegrand_eq t ht]
    exact hd'.congr_of_mem (fun y hy => hFG y hy) ht
theorem gap4 :
    AntiderivativesOn nonnegativeBranch sourceIntegrand =
      ScaledFamily transformed₂ := by
  calc
    AntiderivativesOn nonnegativeBranch sourceIntegrand =
        ScaledFamily transformed₁ := gap3
    _ = ScaledFamily transformed₂ := by
      rw [show transformed₁ = transformed₂ by
        funext t
        exact transformed_eq t]
theorem gap5 :
    AntiderivativesOn nonnegativeBranch sourceIntegrand =
      PrimitiveFamilyOn nonnegativeBranch primitive := by
  have hprimitive : ∀ t ∈ nonnegativeBranch,
      HasDerivWithinAt primitive (sourceIntegrand t) nonnegativeBranch t := by
    intro t ht
    have hd :=
      (primitive_hasDerivAt t).hasDerivWithinAt (s := nonnegativeBranch)
    convert hd using 1
    rw [sourceIntegrand_eq t ht, transformed_eq t]
  apply Set.ext
  intro F
  change
    (∀ t ∈ nonnegativeBranch,
        HasDerivWithinAt F (sourceIntegrand t) nonnegativeBranch t) ↔
      ∃ C : ℝ, ∀ t ∈ nonnegativeBranch, F t = primitive t + C
  constructor
  · intro hF
    let q : ℝ → ℝ := fun t => F t - primitive t
    have hzero : ∀ t ∈ nonnegativeBranch,
        HasDerivWithinAt q 0 nonnegativeBranch t := by
      intro t ht
      dsimp [q]
      convert (hF t ht).sub (hprimitive t ht) using 1
      ring
    have hdiff : DifferentiableOn ℝ q nonnegativeBranch := by
      intro t ht
      exact (hzero t ht).differentiableWithinAt
    have hunique : UniqueDiffOn ℝ nonnegativeBranch := by
      simpa [nonnegativeBranch] using uniqueDiffOn_Ici (0 : ℝ)
    have hfderiv : ∀ t ∈ nonnegativeBranch,
        fderivWithin ℝ q nonnegativeBranch t = 0 := by
      intro t ht
      have heq :=
        (hzero t ht).hasFDerivWithinAt.fderivWithin (hunique t ht)
      simpa using heq
    have hconv : Convex ℝ nonnegativeBranch := by
      simpa [nonnegativeBranch] using convex_Ici (0 : ℝ)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro t ht
    have hconst : q t = q 0 :=
      hconv.is_const_of_fderivWithin_eq_zero hdiff hfderiv ht
        (by simp [nonnegativeBranch])
    dsimp [q] at hconst
    linarith
  · rintro ⟨C, hC⟩
    intro t ht
    exact ((hprimitive t ht).add_const C).congr_of_mem
      (fun y hy => hC y hy) ht
theorem gap6 (t : ℝ) (ht : 0 ≤ t) :
    t = root6 (xOf t + 1) := by
  rw [show xOf t + 1 = t ^ 6 by simp [xOf]]
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [root6]
  · symm
    rw [root6]
    calc
      (t ^ 6).rpow (1 / 6 : ℝ) =
          Real.exp (Real.log (t ^ 6) * (1 / 6 : ℝ)) :=
        Real.rpow_def_of_pos (pow_pos ht 6) _
      _ = Real.exp (Real.log t) := by
        rw [Real.log_pow]
        congr 1
        ring
      _ = t := Real.exp_log ht

end
end ProofGap.Exercise1929
