import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2033
noncomputable section

def tanBranch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def integrand (a b x : ℝ) :=
  1 / (a * Real.sin x + b * Real.cos x) ^ 2
def transformed (a b x : ℝ) :=
  1 / a * (1 / (a * Real.tan x + b) ^ 2) *
    deriv (fun y : ℝ => a * Real.tan y + b) x
def primitiveT (a b x : ℝ) := -1 / (a * (a * Real.tan x + b))
def primitive (a b x : ℝ) :=
  -Real.cos x / (a * (a * Real.sin x + b * Real.cos x))
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ U ⊆ tanBranch ∧
    (∀ x ∈ U, a * Real.sin x + b * Real.cos x ≠ 0)

theorem gap1 (a b x : ℝ) (ha : a ≠ 0) (hx : x ∈ tanBranch)
    (hden : a * Real.sin x + b * Real.cos x ≠ 0) :
    integrand a b x = transformed a b x := by
  have hcos : Real.cos x ≠ 0 := by
    apply ne_of_gt
    exact Real.cos_pos_of_mem_Ioo (by simpa [tanBranch] using hx)
  have hinner : a * Real.tan x + b ≠ 0 := by
    intro hz
    apply hden
    calc
      a * Real.sin x + b * Real.cos x =
          (a * Real.tan x + b) * Real.cos x := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcos]
            <;> ring
      _ = 0 := by rw [hz, zero_mul]
  have hinner' : a * (Real.sin x / Real.cos x) + b ≠ 0 := by
    simpa [Real.tan_eq_sin_div_cos] using hinner
  have hd : HasDerivAt (fun y : ℝ => a * Real.tan y + b)
      (a * (1 / Real.cos x ^ 2)) x := by
    simpa using ((Real.hasDerivAt_tan hcos).const_mul a).const_add b
  unfold integrand transformed
  rw [hd.deriv, Real.tan_eq_sin_div_cos]
  field_simp [ha, hcos, hden, hinner']
  <;> ring
theorem gap2 (U : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (hU : Regular U a b) :
    Family U (integrand a b) = Translates U (primitiveT a b) := by
  rcases hU with ⟨hopen, hconn, hbranch, hden⟩
  have hp : ∀ x ∈ U,
      HasDerivAt (primitiveT a b) (integrand a b x) x := by
    intro x hx
    have hxbranch : x ∈ tanBranch := hbranch hx
    have hcos : Real.cos x ≠ 0 := by
      apply ne_of_gt
      exact Real.cos_pos_of_mem_Ioo (by simpa [tanBranch] using hxbranch)
    have hinner : a * Real.tan x + b ≠ 0 := by
      intro hz
      apply hden x hx
      calc
        a * Real.sin x + b * Real.cos x =
            (a * Real.tan x + b) * Real.cos x := by
              rw [Real.tan_eq_sin_div_cos]
              field_simp [hcos]
              <;> ring
        _ = 0 := by rw [hz, zero_mul]
    have hd : HasDerivAt (fun y : ℝ => a * Real.tan y + b)
        (a * (1 / Real.cos x ^ 2)) x := by
      simpa using ((Real.hasDerivAt_tan hcos).const_mul a).const_add b
    have had : HasDerivAt
        (fun y : ℝ => a * (a * Real.tan y + b))
        (a * (a * (1 / Real.cos x ^ 2))) x :=
      hd.const_mul a
    have hadne : a * (a * Real.tan x + b) ≠ 0 :=
      mul_ne_zero ha hinner
    have hpt0 : HasDerivAt (primitiveT a b)
        ((a * (a * (1 / Real.cos x ^ 2))) /
          (a * (a * Real.tan x + b)) ^ 2) x := by
      simpa [primitiveT] using
        (hasDerivAt_const x (-1 : ℝ)).div had hadne
    have hcoef :
        (a * (a * (1 / Real.cos x ^ 2))) /
            (a * (a * Real.tan x + b)) ^ 2 =
          transformed a b x := by
      unfold transformed
      rw [hd.deriv]
      field_simp [ha, hcos, hinner]
      <;> ring
    have hpt : HasDerivAt (primitiveT a b) (transformed a b x) x := by
      rw [← hcoef]
      exact hpt0
    rw [gap1 a b x ha hxbranch (hden x hx)]
    exact hpt
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hdiff : DifferentiableOn ℝ
          (fun y => F y - primitiveT a b y) U := by
        intro x hx
        exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
      have hzero : ∀ x ∈ U,
          deriv (fun y => F y - primitiveT a b y) x = 0 := by
        intro x hx
        simpa using ((hF x hx).sub (hp x hx)).deriv
      refine ⟨F x₀ - primitiveT a b x₀, ?_⟩
      intro x hx
      have heq :
          F x - primitiveT a b x =
            F x₀ - primitiveT a b x₀ :=
        hopen.is_const_of_deriv_eq_zero hconn hdiff hzero hx hx₀
      calc
        F x = primitiveT a b x + (F x - primitiveT a b x) := by ring
        _ = primitiveT a b x + (F x₀ - primitiveT a b x₀) := by rw [heq]
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have hwithin : HasDerivWithinAt F (integrand a b x) U x := by
      apply ((hp x hx).const_add C).hasDerivWithinAt.congr
      · intro y hy
        simpa [add_comm] using hC y hy
      · simpa [add_comm] using hC x hx
    exact hwithin.hasDerivAt (hopen.mem_nhds hx)
theorem gap3 (U : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (hU : Regular U a b) :
    Family U (integrand a b) = Translates U (primitive a b) := by
  rw [gap2 U a b ha hU]
  rcases hU with ⟨_, _, hbranch, hden⟩
  have hp_eq : ∀ x ∈ U, primitive a b x = primitiveT a b x := by
    intro x hx
    have hxbranch : x ∈ tanBranch := hbranch hx
    have hcos : Real.cos x ≠ 0 := by
      apply ne_of_gt
      exact Real.cos_pos_of_mem_Ioo (by simpa [tanBranch] using hxbranch)
    have hinner : a * Real.tan x + b ≠ 0 := by
      intro hz
      apply hden x hx
      calc
        a * Real.sin x + b * Real.cos x =
            (a * Real.tan x + b) * Real.cos x := by
              rw [Real.tan_eq_sin_div_cos]
              field_simp [hcos]
              <;> ring
        _ = 0 := by rw [hz, zero_mul]
    have hinner' : a * (Real.sin x / Real.cos x) + b ≠ 0 := by
      simpa [Real.tan_eq_sin_div_cos] using hinner
    unfold primitive primitiveT
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ha, hcos, hinner', hden x hx]
    <;> ring
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hC x hx, hp_eq x hx]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hC x hx, ← hp_eq x hx]

end
end ProofGap.Exercise2033
