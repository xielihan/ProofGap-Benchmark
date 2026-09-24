import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2011
noncomputable section

def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = p x + C}
def I (n : ℕ) := Family (fun x => Real.sin x ^ n)
def K (n : ℕ) := Family (fun x => Real.cos x ^ n)
def SinParts (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ I (n - 2), ∃ C, ∀ x,
    F x = -Real.cos x * Real.sin x ^ (n - 1) / n +
      ((n - 1 : ℕ) : ℝ) / n * G x + C}
def CosParts (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ K (n - 2), ∃ C, ∀ x,
    F x = Real.sin x * Real.cos x ^ (n - 1) / n +
      ((n - 1 : ℕ) : ℝ) / n * G x + C}
def sinPrimitive6 (x : ℝ) :=
  -Real.cos x * Real.sin x ^ 5 / 6 -
    5 * Real.cos x * Real.sin x ^ 3 / 24 -
    5 * Real.cos x * Real.sin x / 16 + 5 / 16 * x
def cosPrimitive8 (x : ℝ) :=
  1 / 8 * Real.sin x * Real.cos x ^ 7 +
    7 / 48 * Real.sin x * Real.cos x ^ 5 +
    35 / 192 * Real.sin x * Real.cos x ^ 3 +
    35 / 128 * Real.sin x * Real.cos x + 35 / 128 * x

private theorem family_eq_translates_of_hasDerivAt
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hD : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x).sub (hp x) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun y => F y - p y) :=
      fun x => (hD x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - p y) x = 0 :=
      fun x => (hD x).deriv
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hc : F x - p x = F 0 - p 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => p x + C := funext hC
    rw [hfun]
    intro x
    exact (hp x).add_const C

private theorem sin_reduction_aux (k : ℕ) :
    I (k + 2) = SinParts (k + 2) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (Real.sin x ^ (k + 2)) x at hF
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    let G : ℝ → ℝ := fun x =>
      ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        (F x - (-Real.cos x * Real.sin x ^ (k + 1) /
          ((k + 2 : ℕ) : ℝ)))
    have hG : G ∈ I k := by
      change ∀ x, HasDerivAt G (Real.sin x ^ k) x
      intro x
      have hA :=
        (((Real.hasDerivAt_cos x).neg.mul
          ((Real.hasDerivAt_sin x).pow (k + 1))).div_const
            ((k + 2 : ℕ) : ℝ))
      have hD := ((hF x).sub hA).const_mul
        (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
      have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      change HasDerivAt G (Real.sin x ^ k) x
      dsimp [G]
      convert hD using 1
      simp only [neg_neg, pow_succ, Nat.add_sub_cancel, Pi.mul_apply,
        Pi.neg_apply]
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      ring_nf
      rw [hcos]
      norm_num [Pi.pow_apply, Nat.cast_add] <;> ring
    have hs : ∃ G ∈ I k, ∃ C, ∀ x,
        F x = -Real.cos x * Real.sin x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C := by
      refine ⟨G, hG, 0, ?_⟩
      intro x
      dsimp [G]
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      ring
    simpa [SinParts] using hs
  · intro hS
    have hs : ∃ G ∈ I k, ∃ C, ∀ x,
        F x = -Real.cos x * Real.sin x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C := by
      simpa [SinParts] using hS
    rcases hs with ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt G (Real.sin x ^ k) x at hG
    change ∀ x, HasDerivAt F (Real.sin x ^ (k + 2)) x
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hfun : F = fun x =>
        -Real.cos x * Real.sin x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C :=
      funext hEq
    rw [hfun]
    intro x
    have hA :=
      (((Real.hasDerivAt_cos x).neg.mul
        ((Real.hasDerivAt_sin x).pow (k + 1))).div_const
          ((k + 2 : ℕ) : ℝ))
    have hD :=
      (hA.add ((hG x).const_mul
        (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))).add_const C
    have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    convert hD using 1
    simp only [neg_neg, pow_succ, Nat.add_sub_cancel, Pi.mul_apply,
      Pi.neg_apply]
    field_simp [ne_of_gt hk2]
    ring_nf
    rw [hcos]
    norm_num [Pi.pow_apply, Nat.cast_add] <;> ring

private theorem cos_reduction_aux (k : ℕ) :
    K (k + 2) = CosParts (k + 2) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (Real.cos x ^ (k + 2)) x at hF
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    let G : ℝ → ℝ := fun x =>
      ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        (F x - (Real.sin x * Real.cos x ^ (k + 1) /
          ((k + 2 : ℕ) : ℝ)))
    have hG : G ∈ K k := by
      change ∀ x, HasDerivAt G (Real.cos x ^ k) x
      intro x
      have hA :=
        (((Real.hasDerivAt_sin x).mul
          ((Real.hasDerivAt_cos x).pow (k + 1))).div_const
            ((k + 2 : ℕ) : ℝ))
      have hD := ((hF x).sub hA).const_mul
        (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
      have hsin : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      change HasDerivAt G (Real.cos x ^ k) x
      dsimp [G]
      convert hD using 1
      simp only [pow_succ, Nat.add_sub_cancel, Pi.mul_apply]
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      ring_nf
      rw [hsin]
      norm_num [Pi.pow_apply, Nat.cast_add] <;> ring
    have hs : ∃ G ∈ K k, ∃ C, ∀ x,
        F x = Real.sin x * Real.cos x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C := by
      refine ⟨G, hG, 0, ?_⟩
      intro x
      dsimp [G]
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      ring
    simpa [CosParts] using hs
  · intro hS
    have hs : ∃ G ∈ K k, ∃ C, ∀ x,
        F x = Real.sin x * Real.cos x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C := by
      simpa [CosParts] using hS
    rcases hs with ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt G (Real.cos x ^ k) x at hG
    change ∀ x, HasDerivAt F (Real.cos x ^ (k + 2)) x
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hfun : F = fun x =>
        Real.sin x * Real.cos x ^ (k + 1) /
            ((k + 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * G x + C :=
      funext hEq
    rw [hfun]
    intro x
    have hA :=
      (((Real.hasDerivAt_sin x).mul
        ((Real.hasDerivAt_cos x).pow (k + 1))).div_const
          ((k + 2 : ℕ) : ℝ))
    have hD :=
      (hA.add ((hG x).const_mul
        (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))).add_const C
    have hsin : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    convert hD using 1
    simp only [pow_succ, Nat.add_sub_cancel, Pi.mul_apply]
    field_simp [ne_of_gt hk2]
    ring_nf
    rw [hsin]
    norm_num [Pi.pow_apply, Nat.cast_add] <;> ring

private theorem hasDerivAt_sinPrimitive6 (x : ℝ) :
    HasDerivAt sinPrimitive6 (Real.sin x ^ 6) x := by
  unfold sinPrimitive6
  have h1 :=
    (((Real.hasDerivAt_cos x).neg.mul
      ((Real.hasDerivAt_sin x).pow 5)).div_const (6 : ℝ))
  have h2 :=
    ((((Real.hasDerivAt_cos x).const_mul (5 : ℝ)).mul
      ((Real.hasDerivAt_sin x).pow 3)).div_const (24 : ℝ))
  have h3 :=
    ((((Real.hasDerivAt_cos x).const_mul (5 : ℝ)).mul
      (Real.hasDerivAt_sin x)).div_const (16 : ℝ))
  have h4 := (hasDerivAt_id x).const_mul (5 / 16 : ℝ)
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  convert (((h1.sub h2).sub h3).add h4) using 1
  norm_num [pow_succ]
  ring_nf
  rw [hcos]
  ring

private theorem hasDerivAt_cosPrimitive8 (x : ℝ) :
    HasDerivAt cosPrimitive8 (Real.cos x ^ 8) x := by
  unfold cosPrimitive8
  have h1 :=
    (((Real.hasDerivAt_sin x).const_mul (1 / 8 : ℝ)).mul
      ((Real.hasDerivAt_cos x).pow 7))
  have h2 :=
    (((Real.hasDerivAt_sin x).const_mul (7 / 48 : ℝ)).mul
      ((Real.hasDerivAt_cos x).pow 5))
  have h3 :=
    (((Real.hasDerivAt_sin x).const_mul (35 / 192 : ℝ)).mul
      ((Real.hasDerivAt_cos x).pow 3))
  have h4 :=
    (((Real.hasDerivAt_sin x).const_mul (35 / 128 : ℝ)).mul
      (Real.hasDerivAt_cos x))
  have h5 := (hasDerivAt_id x).const_mul (35 / 128 : ℝ)
  have hsin : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  convert ((((h1.add h2).add h3).add h4).add h5) using 1
  norm_num [pow_succ]
  ring_nf
  rw [hsin]
  ring

theorem gap1 (n : ℕ) : I n = Family (fun x => Real.sin x ^ n) := by
  rfl
theorem gap2 (n : ℕ) (hn : 2 ≤ n) : I n = SinParts n := by
  have h : n = (n - 2) + 2 := by omega
  rw [h]
  exact sin_reduction_aux (n - 2)
theorem gap3 (n : ℕ) (hn : 2 ≤ n) : I n = SinParts n := by
  exact gap2 n hn
theorem gap4 (n : ℕ) (hn : 2 ≤ n) : I n = SinParts n := by
  exact gap2 n hn
theorem gap5 (n : ℕ) (hn : 2 ≤ n) : I n = SinParts n := by
  exact gap2 n hn
theorem gap6 (n : ℕ) (hn : 2 ≤ n) : I n = SinParts n := by
  exact gap2 n hn
theorem gap7 : I 0 = Family (fun _ => 1) := by
  rfl
theorem gap8 : Family (fun _ => (1 : ℝ)) = Translates id := by
  apply family_eq_translates_of_hasDerivAt
  intro x
  simpa using hasDerivAt_id x
theorem gap9 : I 0 = Translates id := by
  exact gap7.trans gap8
theorem gap10 : I 6 = Family (fun x => Real.sin x ^ 6) := by
  rfl
theorem gap11 : I 6 = Translates sinPrimitive6 := by
  calc
    I 6 = Family (fun x => Real.sin x ^ 6) := gap10
    _ = Translates sinPrimitive6 :=
      family_eq_translates_of_hasDerivAt
        (fun x => Real.sin x ^ 6) sinPrimitive6 hasDerivAt_sinPrimitive6
theorem gap12 : I 6 = Translates sinPrimitive6 := by
  exact gap11
theorem gap13 (n : ℕ) : K n = Family (fun x => Real.cos x ^ n) := by
  rfl
theorem gap14 (n : ℕ) (hn : 2 ≤ n) : K n = CosParts n := by
  have h : n = (n - 2) + 2 := by omega
  rw [h]
  exact cos_reduction_aux (n - 2)
theorem gap15 (n : ℕ) (hn : 2 ≤ n) : K n = CosParts n := by
  exact gap14 n hn
theorem gap16 (n : ℕ) (hn : 2 ≤ n) : K n = CosParts n := by
  exact gap14 n hn
theorem gap17 (n : ℕ) (hn : 2 ≤ n) : K n = CosParts n := by
  exact gap14 n hn
theorem gap18 (n : ℕ) (hn : 2 ≤ n) : K n = CosParts n := by
  exact gap14 n hn
theorem gap19 : K 0 = Translates id := by
  calc
    K 0 = Family (fun _ => (1 : ℝ)) := by rfl
    _ = Translates id := gap8
theorem gap20 : K 8 = Family (fun x => Real.cos x ^ 8) := by
  rfl
theorem gap21 : K 8 = Translates cosPrimitive8 := by
  calc
    K 8 = Family (fun x => Real.cos x ^ 8) := gap20
    _ = Translates cosPrimitive8 :=
      family_eq_translates_of_hasDerivAt
        (fun x => Real.cos x ^ 8) cosPrimitive8 hasDerivAt_cosPrimitive8
theorem gap22 : K 8 = Translates cosPrimitive8 := by
  exact gap21

end
end ProofGap.Exercise2011
