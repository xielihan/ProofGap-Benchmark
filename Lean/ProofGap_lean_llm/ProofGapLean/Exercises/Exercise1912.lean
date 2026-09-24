import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1912

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def power (n : ℤ) (x : ℝ) : ℝ := x ^ n
def integrand (n : ℤ) (x : ℝ) : ℝ :=
  x ^ (3 * n - 1) / (x ^ (2 * n) + 1) ^ 2
def productRewrite (n : ℤ) (x : ℝ) : ℝ :=
  x ^ (2 * n) * x ^ (n - 1) / (x ^ (2 * n) + 1) ^ 2
def substitutedIntegrand (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) *
    (x ^ (2 * n) / (x ^ (2 * n) + 1) ^ 2) *
    deriv (power n) x
def numeratorRewrite (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) *
    ((x ^ (2 * n) + 1 - 1) / (x ^ (2 * n) + 1) ^ 2) *
    deriv (power n) x
def splitIntegrand (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) *
    (1 / (x ^ (2 * n) + 1) - 1 / (x ^ (2 * n) + 1) ^ 2) *
    deriv (power n) x
def primitiveRaw (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) * Real.arctan (x ^ n) -
    1 / (n : ℝ) *
      (x ^ n / (2 * (x ^ (2 * n) + 1)) +
        (1 / 2 : ℝ) * Real.arctan (x ^ n))
def primitiveNonzero (n : ℤ) (x : ℝ) : ℝ :=
  1 / (2 * (n : ℝ)) *
    (Real.arctan (x ^ n) - x ^ n / (x ^ (2 * n) + 1))
def zeroIntegrand (x : ℝ) : ℝ := 1 / (4 * x)
def primitiveZero (x : ℝ) : ℝ := (1 / 4 : ℝ) * Real.log |x|
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem family_congr_on_branch {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ branch, f x = g x) : Family f = Family g := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [hfg x hx] using hF x hx
  · intro hF x hx
    simpa [hfg x hx] using hF x hx

private theorem translates_congr_on_branch {p q : ℝ → ℝ}
    (hpq : ∀ x ∈ branch, p x = q x) :
    Translates p = Translates q := by
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hpq x hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hpq x hx]

private theorem hasDerivAt_power (n : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (power n) ((n : ℝ) * x ^ (n - 1)) x := by
  unfold power
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          simpa using (hasDerivAt_id x).pow 0
      | succ k =>
          simpa using (hasDerivAt_id x).pow (k + 1)
  | negSucc k =>
      have hd := ((hasDerivAt_id x).pow (k + 1)).inv
        (pow_ne_zero (k + 1) hx)
      convert hd using 1 <;> simp <;> field_simp [hx] <;> ring

private theorem family_eq_translates_of_derivative (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - p y
    have hH : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using (hF x hx).sub (hp x hx)
    have hopen : IsOpen branch := by
      change IsOpen (Set.Ioi (0 : ℝ))
      exact isOpen_Ioi
    have hconv : Convex ℝ branch := by
      change Convex ℝ (Set.Ioi (0 : ℝ))
      exact convex_Ioi (0 : ℝ)
    have hpre : IsPreconnected branch := hconv.isPreconnected
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      exact (hH x hx).deriv
    have hconst : ∀ x ∈ branch, ∀ y ∈ branch, H x = H y := by
      intro x hx y hy
      exact hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hy
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have h1 : (1 : ℝ) ∈ branch := by
      norm_num [branch]
    have hEq : H x = H 1 := hconst x hx 1 h1
    dsimp [H] at hEq
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => C + p y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simpa [add_comm] using hF y hy
    exact ((hp x hx).const_add C).congr_of_eventuallyEq heq

theorem gap1 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (productRewrite n) := by
  apply family_congr_on_branch
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold integrand productRewrite
  congr 1
  rw [← zpow_add₀ hx0]
  congr 1
  ring

theorem gap2 (n : ℤ) (hn : n ≠ 0) :
    Family (productRewrite n) = Family (substitutedIntegrand n) := by
  apply family_congr_on_branch
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hd := hasDerivAt_power n hx0
  have hden : x ^ (2 * n) + 1 ≠ 0 := by
    have hp : 0 < x ^ (2 * n) := zpow_pos hx _
    linarith
  unfold productRewrite substitutedIntegrand
  rw [hd.deriv]
  field_simp [hnR, hden]

theorem gap3 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (substitutedIntegrand n) := by
  exact (gap1 n hn).trans (gap2 n hn)

theorem gap4 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (numeratorRewrite n) := by
  rw [gap3 n hn]
  apply family_congr_on_branch
  intro x hx
  unfold substitutedIntegrand numeratorRewrite
  ring

theorem gap5 (n : ℤ) (hn : n ≠ 0) :
    Family (numeratorRewrite n) = Family (splitIntegrand n) := by
  apply family_congr_on_branch
  intro x hx
  have hden : x ^ (2 * n) + 1 ≠ 0 := by
    have hp : 0 < x ^ (2 * n) := zpow_pos hx _
    linarith
  unfold numeratorRewrite splitIntegrand
  field_simp [hden]

theorem gap6 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (splitIntegrand n) := by
  exact (gap4 n hn).trans (gap5 n hn)

theorem gap7 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Translates (primitiveRaw n) := by
  apply family_eq_translates_of_derivative
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have ht := hasDerivAt_power n hx0
  have ht2 := hasDerivAt_power (2 * n) hx0
  have ha : HasDerivAt (fun y : ℝ => Real.arctan (y ^ n))
      (((n : ℝ) * x ^ (n - 1)) / (1 + (x ^ n) ^ 2)) x := by
    simpa [div_eq_mul_inv, mul_comm] using ht.arctan
  have hd : HasDerivAt (fun y : ℝ => 2 * (y ^ (2 * n) + 1))
      (2 * (((2 * n : ℤ) : ℝ) * x ^ (2 * n - 1))) x := by
    simpa using (ht2.add_const 1).const_mul 2
  have hden : 2 * (x ^ (2 * n) + 1) ≠ 0 := by
    have hp : 0 < x ^ (2 * n) := zpow_pos hx _
    positivity
  have hq := ht.div hd hden
  have hp := (ha.const_mul (1 / (n : ℝ))).sub
    ((hq.add (ha.const_mul (1 / 2 : ℝ))).const_mul (1 / (n : ℝ)))
  have hsq : (x ^ n) ^ 2 = x ^ (2 * n) := by
    rw [pow_two, ← zpow_add₀ hx0]
    congr 1
    ring
  have hsq' : (x ^ n) ^ 2 = x ^ (n * 2) := by
    rw [pow_two, ← zpow_add₀ hx0]
    congr 1
    ring
  have hshift : x ^ (2 * n - 1) = x ^ (n - 1) * x ^ n := by
    rw [← zpow_add₀ hx0]
    congr 1
    ring
  have hnum : x ^ (3 * n - 1) = x ^ (n - 1) * x ^ (2 * n) := by
    rw [← zpow_add₀ hx0]
    congr 1
    ring
  unfold primitiveRaw at hp
  convert hp using 1
  simp only [integrand, power, hsq, hshift, hnum, Int.cast_mul, Int.cast_ofNat]
  have hD : x ^ (2 * n) + 1 ≠ 0 := by
    have hz : 0 < x ^ (2 * n) := zpow_pos hx _
    linarith
  have hD' : 1 + x ^ (n * 2) ≠ 0 := by
    have hz : 0 < x ^ (n * 2) := zpow_pos hx _
    linarith
  have hD'' : x ^ (n * 2) + 1 ≠ 0 := by
    have hz : 0 < x ^ (n * 2) := zpow_pos hx _
    linarith
  field_simp [power, hnR, hD, hD', hD'', hsq'] <;> ring
  rw [hsq']
  field_simp [hD']
  ring

theorem gap8 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Translates (primitiveNonzero n) := by
  rw [gap7 n hn]
  apply translates_congr_on_branch
  intro x hx
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hden : x ^ (2 * n) + 1 ≠ 0 := by
    have hp : 0 < x ^ (2 * n) := zpow_pos hx _
    linarith
  unfold primitiveRaw primitiveNonzero
  field_simp [hnR, hden]
  ring

theorem gap9 (n : ℤ) (hn : n = 0) :
    Family (integrand n) = Family zeroIntegrand := by
  subst n
  apply family_congr_on_branch
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold integrand zeroIntegrand
  norm_num
  field_simp [hx0]

theorem gap10 (n : ℤ) (hn : n = 0) :
    Family zeroIntegrand = Translates primitiveZero := by
  apply family_eq_translates_of_derivative
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have heq : primitiveZero =ᶠ[nhds x]
      (fun y : ℝ => (1 / 4 : ℝ) * Real.log y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change (0 : ℝ) < y at hy
    simp [primitiveZero, abs_of_pos hy]
  have hd : HasDerivAt (fun y : ℝ => (1 / 4 : ℝ) * Real.log y)
      ((1 / 4 : ℝ) * x⁻¹) x := by
    simpa using (Real.hasDerivAt_log hx0).const_mul (1 / 4 : ℝ)
  have hp : HasDerivAt primitiveZero ((1 / 4 : ℝ) * x⁻¹) x :=
    hd.congr_of_eventuallyEq heq
  convert hp using 1
  unfold zeroIntegrand
  field_simp [hx0]

theorem gap11 (n : ℤ) (hn : n = 0) :
    Family (integrand n) = Translates primitiveZero := by
  exact (gap9 n hn).trans (gap10 n hn)

end

end ProofGap.Exercise1912
