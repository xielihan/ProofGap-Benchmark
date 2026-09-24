import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2142

noncomputable section

def branch : Set ℝ := Set.Ioo 0 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def integrand (x : ℝ) :=
  Real.arcsin x / x ^ 2 * ((1 + x ^ 2) / Real.sqrt (1 - x ^ 2))
def split₁ (x : ℝ) :=
  Real.arcsin x / (x ^ 2 * Real.sqrt (1 - x ^ 2))
def split₂ (x : ℝ) :=
  Real.arcsin x / Real.sqrt (1 - x ^ 2)
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn split₁,
    ∃ B ∈ AntiderivativesOn split₂,
    ∀ x ∈ branch, F x = A x + B x}
def FirstSubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ A : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt A
          (Real.arcsin x * deriv (fun y : ℝ => y) x /
            (x ^ 3 * Real.sqrt (x⁻¹ ^ 2 - 1))) x) ∧
    ∃ B : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt B
          (Real.arcsin x * deriv Real.arcsin x) x) ∧
    ∀ x ∈ branch, F x = Real.sign x * A x + B x}
def SecondSubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ A : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt A
          (Real.arcsin x *
            deriv (fun y : ℝ => Real.sqrt (y⁻¹ ^ 2 - 1)) x) x) ∧
    ∀ x ∈ branch,
      F x = -Real.sign x * A x + 1 / 2 * Real.arcsin x ^ 2}
def AbsoluteValueFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (fun x => 1 / |x|),
    ∀ x ∈ branch,
      F x = -Real.sign x *
          (Real.sqrt (1 - x ^ 2) / |x| * Real.arcsin x - G x) +
        1 / 2 * Real.arcsin x ^ 2}
def LogReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (fun x => 1 / x),
    ∀ x ∈ branch,
      F x = -Real.sqrt (1 - x ^ 2) / x * Real.arcsin x +
        G x + 1 / 2 * Real.arcsin x ^ 2}
def primitive (x : ℝ) :=
  -Real.sqrt (1 - x ^ 2) / x * Real.arcsin x +
    Real.log |x| + 1 / 2 * Real.arcsin x ^ 2

private lemma branch_aux (x : ℝ) (hx : x ∈ branch) :
    0 < 1 - x ^ 2 := by
  rcases hx with ⟨hx0, hx1⟩
  nlinarith [sq_nonneg (1 - x)]

private lemma hasDerivAt_congr_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact hfg y hy

private lemma hasDerivAt_asin_sq (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => 1 / 2 * Real.arcsin y ^ 2) (split₂ x) x := by
  have hxm : -1 < x := lt_trans (by norm_num) hx.1
  have hd := (Real.hasDerivAt_arcsin (ne_of_gt hxm) (ne_of_lt hx.2)).pow 2
  unfold split₂
  convert hd.const_mul (1 / 2) using 1 <;>
    simp [div_eq_mul_inv] <;> ring

private lemma integrand_eq_split (x : ℝ) (hx : x ∈ branch) :
    integrand x = split₁ x + split₂ x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (branch_aux x hx))
  unfold integrand split₁ split₂
  field_simp [hx0, hs] <;> ring

private lemma first_substitution_one (x : ℝ) (hx : x ∈ branch) :
    Real.arcsin x * deriv (fun y : ℝ => y) x /
        (x ^ 3 * Real.sqrt (x⁻¹ ^ 2 - 1)) = split₁ x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hi := branch_aux x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hi)
  have hu : x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by
    field_simp [hx0] <;> ring
  have hsqrt : Real.sqrt (x⁻¹ ^ 2 - 1) = Real.sqrt (1 - x ^ 2) / x := by
    rw [hu, Real.sqrt_div (le_of_lt hi)]
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hx.1]
  have hid : deriv (fun y : ℝ => y) x = 1 := (hasDerivAt_id x).deriv
  rw [hid, hsqrt]
  unfold split₁
  field_simp [hx0, hs] <;> ring

private lemma first_substitution_two (x : ℝ) (hx : x ∈ branch) :
    Real.arcsin x * deriv Real.arcsin x = split₂ x := by
  have hxm : -1 < x := lt_trans (by norm_num) hx.1
  rw [(Real.hasDerivAt_arcsin (ne_of_gt hxm) (ne_of_lt hx.2)).deriv]
  unfold split₂
  ring

private lemma hasDerivAt_sqrt_quot (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2) / y)
      (-1 / (x ^ 2 * Real.sqrt (1 - x ^ 2))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hi := branch_aux x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hi)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hi)).comp x hinner using 1 <;>
      simp [Function.comp_def] <;> ring
  have hd := hsqrt.div (hasDerivAt_id x) hx0
  have hd' : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2) / y)
      (((-x / Real.sqrt (1 - x ^ 2)) * x - Real.sqrt (1 - x ^ 2)) / x ^ 2) x := by
    simpa only [id_eq, mul_one] using hd
  convert hd' using 1
  field_simp [hx0, hs]
  nlinarith [Real.sq_sqrt (le_of_lt hi)]

private lemma hasDerivAt_sqrt_quot_mul_asin (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ => Real.sqrt (1 - y ^ 2) / y * Real.arcsin y)
      (-split₁ x + 1 / x) x := by
  have hxm : -1 < x := lt_trans (by norm_num) hx.1
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (branch_aux x hx))
  have hd := (hasDerivAt_sqrt_quot x hx).mul
    (Real.hasDerivAt_arcsin (ne_of_gt hxm) (ne_of_lt hx.2))
  convert hd using 1
  unfold split₁
  field_simp [hx0, hs] <;> ring

private lemma hasDerivAt_second_sqrt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y⁻¹ ^ 2 - 1))
      (-1 / (x ^ 2 * Real.sqrt (1 - x ^ 2))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hi := branch_aux x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hi)
  have hu_eq : x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by
    field_simp [hx0] <;> ring
  have hu : 0 < x⁻¹ ^ 2 - 1 := by
    rw [hu_eq]
    positivity
  have hsqrt : Real.sqrt (x⁻¹ ^ 2 - 1) = Real.sqrt (1 - x ^ 2) / x := by
    rw [hu_eq, Real.sqrt_div (le_of_lt hi)]
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hx.1]
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-1 / x ^ 2) x := by
    simpa only [id_eq] using (hasDerivAt_id x).inv hx0
  have hinner : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2 - 1) (-2 / x ^ 3) x := by
    convert (hinv.pow 2).sub_const 1 using 1 <;> try simp only [pow_one]
    field_simp [hx0] <;> ring
    simp [hx0]
  have hd := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hinner
  convert hd using 1 <;> try simp only [Function.comp_apply]
  rw [hsqrt]
  field_simp [hx0, hs] <;> ring

private lemma second_substitution_coefficient (x : ℝ) (hx : x ∈ branch) :
    Real.arcsin x *
        deriv (fun y : ℝ => Real.sqrt (y⁻¹ ^ 2 - 1)) x = -split₁ x := by
  rw [(hasDerivAt_second_sqrt x hx).deriv]
  unfold split₁
  ring

private lemma hasDerivAt_log_abs (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  refine hasDerivAt_congr_branch
    (f := fun y : ℝ => Real.log |y|) (g := Real.log) hx ?_ ?_
  · intro y hy
    simp [abs_of_pos hy.1]
  · simpa [one_div] using Real.hasDerivAt_log hx0

private lemma antiderivative_inv_eq_log_add_const
    (G : ℝ → ℝ)
    (hG : G ∈ AntiderivativesOn (fun x => 1 / x)) :
    ∃ C : ℝ, ∀ x ∈ branch, G x = Real.log |x| + C := by
  let H : ℝ → ℝ := fun x => G x - Real.log |x|
  have hdiff : DifferentiableOn ℝ H (Set.Ioo 0 1) := by
    intro x hx
    have hxb : x ∈ branch := by simpa [branch] using hx
    exact ((hG x hxb).sub (hasDerivAt_log_abs x hxb)).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv H x = 0 := by
    intro x hx
    have hxb : x ∈ branch := by simpa [branch] using hx
    change deriv (fun y => G y - Real.log |y|) x = 0
    simpa using ((hG x hxb).sub (hasDerivAt_log_abs x hxb)).deriv
  have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      H x = H y := by
    intro x hx y hy
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hx hy
  refine ⟨H (1 / 2), ?_⟩
  intro x hx
  have hxi : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [branch] using hx
  have hb : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by
    constructor <;> norm_num
  have heq := hconst x hxi (1 / 2) hb
  dsimp [H] at heq ⊢
  linarith

private lemma antiderivatives_eq_second :
    AntiderivativesOn integrand = SecondSubstitutionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    refine ⟨fun x => -F x + 1 / 2 * Real.arcsin x ^ 2, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).neg.add (hasDerivAt_asin_sq x hx)
      convert hd using 1
      rw [second_substitution_coefficient x hx, integrand_eq_split x hx]
      ring
    · intro x hx
      simp [Real.sign_of_pos hx.1]
  · rintro ⟨A, hA, hF⟩
    intro x hx
    have hd := (hA x hx).neg.add (hasDerivAt_asin_sq x hx)
    have hd' : HasDerivAt
        (fun y => -A y + 1 / 2 * Real.arcsin y ^ 2) (integrand x) x := by
      convert hd using 1
      rw [second_substitution_coefficient x hx, integrand_eq_split x hx]
      ring
    apply hasDerivAt_congr_branch hx ?_ hd'
    intro y hy
    calc
      F y = -Real.sign y * A y + 1 / 2 * Real.arcsin y ^ 2 := hF y hy
      _ = -A y + 1 / 2 * Real.arcsin y ^ 2 := by
        simp [Real.sign_of_pos hy.1]

theorem gap1 :
    AntiderivativesOn integrand = SplitFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    refine ⟨fun x => F x - 1 / 2 * Real.arcsin x ^ 2, ?_,
      fun x => 1 / 2 * Real.arcsin x ^ 2, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).sub (hasDerivAt_asin_sq x hx) using 1
      rw [integrand_eq_split x hx]
      ring
    · intro x hx
      exact hasDerivAt_asin_sq x hx
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    intro x hx
    have hd := (hA x hx).add (hB x hx)
    rw [← integrand_eq_split x hx] at hd
    apply hasDerivAt_congr_branch hx hF hd
theorem gap2 :
    AntiderivativesOn integrand = FirstSubstitutionFamily := by
  rw [gap1]
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, hF⟩
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro x hx
      rw [first_substitution_one x hx]
      exact hA x hx
    · intro x hx
      rw [first_substitution_two x hx]
      exact hB x hx
    · intro x hx
      simpa [Real.sign_of_pos hx.1] using hF x hx
  · rintro ⟨A, hA, B, hB, hF⟩
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro x hx
      rw [← first_substitution_one x hx]
      exact hA x hx
    · intro x hx
      rw [← first_substitution_two x hx]
      exact hB x hx
    · intro x hx
      simpa [Real.sign_of_pos hx.1] using hF x hx
theorem gap3 :
    FirstSubstitutionFamily = SecondSubstitutionFamily := by
  exact gap2.symm.trans antiderivatives_eq_second
theorem gap4 :
    AntiderivativesOn integrand = SecondSubstitutionFamily := by
  exact antiderivatives_eq_second
theorem gap5 :
    AntiderivativesOn integrand = AbsoluteValueFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    refine ⟨fun x => F x +
        Real.sqrt (1 - x ^ 2) / x * Real.arcsin x -
          1 / 2 * Real.arcsin x ^ 2, ?_, ?_⟩
    · intro x hx
      have hd := ((hF x hx).add (hasDerivAt_sqrt_quot_mul_asin x hx)).sub
        (hasDerivAt_asin_sq x hx)
      convert hd using 1
      rw [integrand_eq_split x hx]
      simp [abs_of_pos hx.1] <;> ring
    · intro x hx
      simp [Real.sign_of_pos hx.1, abs_of_pos hx.1] <;> ring
  · rintro ⟨G, hG, hF⟩
    intro x hx
    have hd := ((hasDerivAt_sqrt_quot_mul_asin x hx).sub (hG x hx)).neg.add
      (hasDerivAt_asin_sq x hx)
    have hd' : HasDerivAt
        (fun y => -(Real.sqrt (1 - y ^ 2) / y * Real.arcsin y - G y) +
          1 / 2 * Real.arcsin y ^ 2) (integrand x) x := by
      convert hd using 1
      rw [integrand_eq_split x hx]
      simp [abs_of_pos hx.1] <;> ring
    apply hasDerivAt_congr_branch hx ?_ hd'
    intro y hy
    calc
      F y = -Real.sign y *
          (Real.sqrt (1 - y ^ 2) / |y| * Real.arcsin y - G y) +
          1 / 2 * Real.arcsin y ^ 2 := hF y hy
      _ = -(Real.sqrt (1 - y ^ 2) / y * Real.arcsin y - G y) +
          1 / 2 * Real.arcsin y ^ 2 := by
        rw [Real.sign_of_pos hy.1, abs_of_pos hy.1] <;> ring
theorem gap6 :
    AbsoluteValueFamily = LogReductionFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hF⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      simpa [abs_of_pos hx.1] using hG x hx
    · intro x hx
      calc
        F x = -Real.sign x *
            (Real.sqrt (1 - x ^ 2) / |x| * Real.arcsin x - G x) +
            1 / 2 * Real.arcsin x ^ 2 := hF x hx
        _ = -Real.sqrt (1 - x ^ 2) / x * Real.arcsin x + G x +
            1 / 2 * Real.arcsin x ^ 2 := by
          rw [Real.sign_of_pos hx.1, abs_of_pos hx.1] <;> ring
  · rintro ⟨G, hG, hF⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      simpa [abs_of_pos hx.1] using hG x hx
    · intro x hx
      calc
        F x = -Real.sqrt (1 - x ^ 2) / x * Real.arcsin x + G x +
            1 / 2 * Real.arcsin x ^ 2 := hF x hx
        _ = -Real.sign x *
            (Real.sqrt (1 - x ^ 2) / |x| * Real.arcsin x - G x) +
            1 / 2 * Real.arcsin x ^ 2 := by
          rw [Real.sign_of_pos hx.1, abs_of_pos hx.1] <;> ring
theorem gap7 :
    AntiderivativesOn integrand = LogReductionFamily := by
  rw [gap5, gap6]
theorem gap8 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap7]
  ext F
  constructor
  · rintro ⟨G, hG, hF⟩
    obtain ⟨C, hC⟩ := antiderivative_inv_eq_log_add_const G hG
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hC x hx]
    simp only [primitive]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨fun x => Real.log |x| + C, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_log_abs x hx).add_const C
    · intro x hx
      rw [hF x hx]
      simp only [primitive]
      ring

end
end ProofGap.Exercise2142
