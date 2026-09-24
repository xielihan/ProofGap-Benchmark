import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1911

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def power (n : ℤ) (x : ℝ) : ℝ := x ^ n
def integrand (n : ℤ) (x : ℝ) : ℝ :=
  x ^ (2 * n - 1) / (x ^ n + 1)
def productRewrite (n : ℤ) (x : ℝ) : ℝ :=
  x ^ n * x ^ (n - 1) / (x ^ n + 1)
def substitutedIntegrand (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) * (x ^ n / (x ^ n + 1)) * deriv (power n) x
def decomposedIntegrand (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) * (1 - 1 / (x ^ n + 1)) * deriv (power n) x
def primitiveNonzero (n : ℤ) (x : ℝ) : ℝ :=
  1 / (n : ℝ) * (x ^ n - Real.log |x ^ n + 1|)
def zeroIntegrand (x : ℝ) : ℝ := 1 / (2 * x)
def primitiveZero (x : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log |x|
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem family_congr_on_branch {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ branch, f x = g x) : Family f = Family g := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [hfg x hx] using hF x hx
  · intro hF x hx
    simpa only [hfg x hx] using hF x hx

private theorem hasDerivAt_power (n : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (power n) ((n : ℝ) * x ^ (n - 1)) x := by
  unfold power
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ)))
      | succ k =>
          simpa [Nat.cast_add, Nat.cast_one] using
            ((hasDerivAt_id x).pow (k + 1))
  | negSucc k =>
      have hk : x ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hx
      have hbase :
          HasDerivAt (fun y : ℝ => (y ^ (k + 1))⁻¹)
            (-(((k + 1 : ℕ) : ℝ) * x ^ k) / (x ^ (k + 1)) ^ 2) x := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (((hasDerivAt_id x).pow (k + 1)).inv hk)
      have hcoef :
          -(((k + 1 : ℕ) : ℝ) * x ^ k) / (x ^ (k + 1)) ^ 2 =
            ((Int.negSucc k : ℤ) : ℝ) *
              x ^ ((Int.negSucc k : ℤ) - 1) := by
        simp [zpow_negSucc]
        field_simp [hx]
        ring
      rw [hcoef] at hbase
      simpa [zpow_negSucc] using hbase

private theorem family_eq_translates_of_hasDeriv (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let q : ℝ → ℝ := fun x => F x - p x
    have hq : ∀ x ∈ branch, HasDerivAt q 0 x := by
      intro x hx
      simpa only [q, sub_self] using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ q branch := by
      intro x hx
      exact (hq x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv q x = 0 := by
      intro x hx
      exact (hq x hx).deriv
    have hopen : IsOpen branch := by
      simpa only [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hconv : Convex ℝ branch := by
      simpa only [branch] using
        (convex_Ioi (0 : ℝ) : Convex ℝ (Set.Ioi (0 : ℝ)))
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have hqx : q x = q 1 :=
      hopen.is_const_of_deriv_eq_zero hconv.isPreconnected hdiff hzero
        hx (by simp [branch])
    dsimp [q] at hqx
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hopen : IsOpen branch := by
      simpa only [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have heq : F =ᶠ[nhds x] (fun y => p y + C) := by
      apply Filter.mem_of_superset (hopen.mem_nhds hx)
      intro y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (productRewrite n) := by
  apply family_congr_on_branch
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold integrand productRewrite
  rw [show 2 * n - 1 = n + (n - 1) by ring, zpow_add₀ hx0]

theorem gap2 (n : ℤ) (hn : n ≠ 0) :
    Family (productRewrite n) = Family (substitutedIntegrand n) := by
  apply family_congr_on_branch
  intro x hx
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hden : x ^ n + 1 ≠ 0 :=
    ne_of_gt (add_pos (zpow_pos hx n) zero_lt_one)
  have hd : deriv (power n) x = (n : ℝ) * x ^ (n - 1) :=
    (hasDerivAt_power n (ne_of_gt hx)).deriv
  unfold productRewrite substitutedIntegrand
  rw [hd]
  field_simp [hnR, hden] <;> ring

theorem gap3 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (substitutedIntegrand n) := by
  calc
    Family (integrand n) = Family (productRewrite n) := gap1 n hn
    _ = Family (substitutedIntegrand n) := gap2 n hn

theorem gap4 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Family (decomposedIntegrand n) := by
  calc
    Family (integrand n) = Family (substitutedIntegrand n) := gap3 n hn
    _ = Family (decomposedIntegrand n) := by
      apply family_congr_on_branch
      intro x hx
      have hden : x ^ n + 1 ≠ 0 :=
        ne_of_gt (add_pos (zpow_pos hx n) zero_lt_one)
      have hfrac : x ^ n / (x ^ n + 1) = 1 - 1 / (x ^ n + 1) := by
        field_simp [hden] <;> ring
      unfold substitutedIntegrand decomposedIntegrand
      rw [hfrac]

theorem gap5 (n : ℤ) (hn : n ≠ 0) :
    Family (decomposedIntegrand n) = Translates (primitiveNonzero n) := by
  apply family_eq_translates_of_hasDeriv
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hden : power n x + 1 ≠ 0 := by
    unfold power
    exact ne_of_gt (add_pos (zpow_pos hx n) zero_lt_one)
  have hden' : x ^ n + 1 ≠ 0 := by
    simpa only [power] using hden
  have hpow : HasDerivAt (power n) ((n : ℝ) * x ^ (n - 1)) x :=
    hasDerivAt_power n hx0
  have hlog :
      HasDerivAt (fun y => Real.log (power n y + 1))
        (((n : ℝ) * x ^ (n - 1)) / (power n x + 1)) x :=
    (hpow.add_const 1).log hden
  have hscaled := (hpow.sub hlog).const_mul (1 / (n : ℝ))
  have hp0 :
      HasDerivAt
        (fun y => 1 / (n : ℝ) *
          (power n y - Real.log (power n y + 1)))
        (1 / (n : ℝ) *
          ((n : ℝ) * x ^ (n - 1) -
            ((n : ℝ) * x ^ (n - 1)) / (x ^ n + 1))) x := by
    simpa only [Pi.sub_apply, power] using hscaled
  have hfun :
      (fun y => 1 / (n : ℝ) *
        (power n y - Real.log (power n y + 1))) =
        primitiveNonzero n := by
    funext y
    unfold primitiveNonzero power
    rw [Real.log_abs]
  have hd : deriv (power n) x = (n : ℝ) * x ^ (n - 1) := hpow.deriv
  have hcoef :
      1 / (n : ℝ) *
          ((n : ℝ) * x ^ (n - 1) -
            ((n : ℝ) * x ^ (n - 1)) / (x ^ n + 1)) =
        decomposedIntegrand n x := by
    unfold decomposedIntegrand
    rw [hd]
    field_simp [hnR, hden'] <;> ring
  rw [← hcoef, ← hfun]
  exact hp0

theorem gap6 (n : ℤ) (hn : n ≠ 0) :
    Family (integrand n) = Translates (primitiveNonzero n) := by
  calc
    Family (integrand n) = Family (decomposedIntegrand n) := gap4 n hn
    _ = Translates (primitiveNonzero n) := gap5 n hn

theorem gap7 (n : ℤ) (hn : n = 0) :
    Family (integrand n) = Family zeroIntegrand := by
  subst n
  apply family_congr_on_branch
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold integrand zeroIntegrand
  norm_num [zpow_neg_one] <;> field_simp [hx0] <;> ring

theorem gap8 (n : ℤ) (hn : n = 0) :
    Family zeroIntegrand = Translates primitiveZero := by
  apply family_eq_translates_of_hasDeriv
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt (fun y : ℝ => Real.log |y|) x⁻¹ x := by
    simpa only [Real.log_abs] using (Real.hasDerivAt_log hx0)
  have hscaled := hlog.const_mul (1 / 2 : ℝ)
  have hp0 : HasDerivAt primitiveZero ((1 / 2 : ℝ) * x⁻¹) x := by
    simpa only [primitiveZero] using hscaled
  have hcoef : (1 / 2 : ℝ) * x⁻¹ = zeroIntegrand x := by
    unfold zeroIntegrand
    field_simp [hx0] <;> ring
  rw [← hcoef]
  exact hp0

theorem gap9 (n : ℤ) (hn : n = 0) :
    Family (integrand n) = Translates primitiveZero := by
  calc
    Family (integrand n) = Family zeroIntegrand := gap7 n hn
    _ = Translates primitiveZero := gap8 n hn

end

end ProofGap.Exercise1911
