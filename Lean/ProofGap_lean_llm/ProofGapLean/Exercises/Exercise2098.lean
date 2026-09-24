import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2098
noncomputable section

def U : Set ℝ := Set.Ioi 0
def f (n : ℕ) (x : ℝ) := Real.log x ^ n
def Family (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Step1 (n : ℕ) := {F : ℝ → ℝ |
  ∃ G ∈ Family (f (n - 1)), ∃ C, ∀ x ∈ U,
    F x = x * Real.log x ^ n - (n : ℝ) * G x + C}
def Step2 (n : ℕ) := {F : ℝ → ℝ |
  ∃ G ∈ Family (f (n - 2)), ∃ C, ∀ x ∈ U,
    F x = x * Real.log x ^ n -
      (n : ℝ) * x * Real.log x ^ (n - 1) +
      (n : ℝ) * ((n : ℝ) - 1) * G x + C}
def primitive (n : ℕ) (x : ℝ) :=
  x * ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
      (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k)
def FiniteExpansion (n : ℕ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = primitive n x + C}

private theorem hasDerivAt_congr_on_U
    {F P : ℝ → ℝ} {d x : ℝ} (hx : x ∈ U)
    (hP : HasDerivAt P d x) (hEq : ∀ y ∈ U, F y = P y) :
    HasDerivAt F d x := by
  have hx0 : 0 < x := hx
  have heq : F =ᶠ[nhds x] P := by
    apply Filter.mem_of_superset (Ioi_mem_nhds hx0)
    intro y hy
    exact hEq y hy
  exact hP.congr_of_eventuallyEq heq

private theorem primitive_succ (n : ℕ) (x : ℝ) :
    primitive (n + 1) x =
      x * Real.log x ^ (n + 1) - (n + 1 : ℝ) * primitive n x := by
  have hsum :
      (∑ k ∈ Finset.range (n + 2),
        (-1 : ℝ) ^ k * (Nat.factorial (n + 1) : ℝ) /
          (Nat.factorial (n + 1 - k) : ℝ) * Real.log x ^ (n + 1 - k)) =
      Real.log x ^ (n + 1) - (n + 1 : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
            (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_mul]
    rw [div_self (by positivity : (Nat.factorial (n + 1) : ℝ) ≠ 0), one_mul]
    calc
      (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (k + 1) * (Nat.factorial (n + 1) : ℝ) /
            (Nat.factorial (n + 1 - (k + 1)) : ℝ) *
              Real.log x ^ (n + 1 - (k + 1))) + Real.log x ^ (n + 1) =
        Real.log x ^ (n + 1) +
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (k + 1) * (Nat.factorial (n + 1) : ℝ) /
              (Nat.factorial (n + 1 - (k + 1)) : ℝ) *
                Real.log x ^ (n + 1 - (k + 1)) := by
          rw [add_comm]
      _ = Real.log x ^ (n + 1) +
          ∑ k ∈ Finset.range (n + 1),
            (-(n + 1 : ℝ)) *
              ((-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
                (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hsub : n + 1 - (k + 1) = n - k := by omega
          rw [hsub, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one, pow_succ]
          ring
      _ = Real.log x ^ (n + 1) + (-(n + 1 : ℝ)) *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
              (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k) := by
          rw [Finset.mul_sum]
      _ = Real.log x ^ (n + 1) - (n + 1 : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
              (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k) := by
          ring
  unfold primitive
  rw [hsum]
  ring

private theorem hasDerivAt_primitive (n : ℕ) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (primitive n) (f n x) x := by
  induction n with
  | zero =>
      have hprim : primitive 0 = id := by
        funext y
        simp [primitive]
      simpa [f, hprim] using hasDerivAt_id x
  | succ n ih =>
      have hx0 : 0 < x := hx
      have hfun : primitive (n + 1) = fun y =>
          y * Real.log y ^ (n + 1) - (n + 1 : ℝ) * primitive n y := by
        funext y
        exact primitive_succ n y
      rw [hfun]
      have hp := (hasDerivAt_id x).mul
        ((Real.hasDerivAt_log hx0.ne').pow (n + 1))
      have hd := hp.sub (ih.const_mul (n + 1 : ℝ))
      convert hd using 1
      simp [f] <;> field_simp [hx0.ne'] <;> ring

private theorem family_eq_finiteExpansion (n : ℕ) :
    Family (f n) = FiniteExpansion n := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f n x) x at hF
    change ∃ C, ∀ x ∈ U, F x = primitive n x + C
    let D : ℝ → ℝ := fun x => F x - primitive n x
    have hdiff : DifferentiableOn ℝ D U := by
      intro x hx
      exact ((hF x hx).sub (hasDerivAt_primitive n hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv D x = 0 := by
      intro x hx
      simpa [D] using ((hF x hx).sub (hasDerivAt_primitive n hx)).deriv
    have hopen : IsOpen U := by
      simpa [U] using isOpen_Ioi
    have hpre : IsPreconnected U := by
      simpa [U] using isPreconnected_Ioi
    have h1 : (1 : ℝ) ∈ U := by norm_num [U]
    refine ⟨F 1 - primitive n 1, ?_⟩
    intro x hx
    have heq := hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx h1
    dsimp [D] at heq
    linarith
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (f n x) x
    intro x hx
    apply hasDerivAt_congr_on_U hx ((hasDerivAt_primitive n hx).add_const C)
    intro y hy
    exact hEq y hy

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    Family (f n) = Step1 n := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f n x) x at hF
    change ∃ G ∈ Family (f (n - 1)), ∃ C, ∀ x ∈ U,
      F x = x * Real.log x ^ n - (n : ℝ) * G x + C
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    let G : ℝ → ℝ := fun y =>
      (y * Real.log y ^ n - F y) / (n : ℝ)
    have hG : G ∈ Family (f (n - 1)) := by
      intro x hx
      have hx0 : 0 < x := hx
      have hp := (hasDerivAt_id x).mul
        ((Real.hasDerivAt_log hx0.ne').pow n)
      have hd := (hp.sub (hF x hx)).div_const (n : ℝ)
      change HasDerivAt G (f (n - 1) x) x
      convert hd using 1
      simp [f] <;> field_simp [hn0, hx0.ne'] <;> ring
    refine ⟨G, hG, 0, ?_⟩
    intro x hx
    dsimp [G]
    field_simp [hn0] <;> ring
  · rintro ⟨G, hG, C, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (f n x) x
    intro x hx
    have hx0 : 0 < x := hx
    have hp := (hasDerivAt_id x).mul
      ((Real.hasDerivAt_log hx0.ne').pow n)
    have hd := hp.sub ((hG x hx).const_mul (n : ℝ))
    have hd0 : HasDerivAt
        (fun y => y * Real.log y ^ n - (n : ℝ) * G y)
        (f n x) x := by
      convert hd using 1
      simp [f] <;> field_simp [hx0.ne'] <;> ring
    have hd' : HasDerivAt
        (fun y => y * Real.log y ^ n - (n : ℝ) * G y + C)
        (f n x) x := hd0.add_const C
    apply hasDerivAt_congr_on_U hx hd'
    intro y hy
    exact hEq y hy
theorem gap2 (n : ℕ) (hn : 2 ≤ n) :
    Step1 n = Step2 n := by
  ext F
  constructor
  · rintro ⟨G, hG, C, hF⟩
    have hn1 : 1 ≤ n - 1 := by omega
    have hGstep : G ∈ Step1 (n - 1) := by
      rw [← gap1 (n - 1) hn1]
      exact hG
    rcases hGstep with ⟨H, hH, D, hG⟩
    have hH' : H ∈ Family (f (n - 2)) := by
      simpa [Nat.sub_sub] using hH
    refine ⟨H, hH', C - (n : ℝ) * D, ?_⟩
    intro x hx
    rw [hF x hx, hG x hx]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
    ring
  · rintro ⟨H, hH, C, hF⟩
    have hn1 : 1 ≤ n - 1 := by omega
    have hH' : H ∈ Family (f ((n - 1) - 1)) := by
      simpa [Nat.sub_sub] using hH
    let G : ℝ → ℝ := fun x =>
      x * Real.log x ^ (n - 1) - ((n : ℝ) - 1) * H x
    have hGstep : G ∈ Step1 (n - 1) := by
      refine ⟨H, hH', 0, ?_⟩
      intro x hx
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      dsimp [G]
      rw [hcast]
      ring
    have hG : G ∈ Family (f (n - 1)) := by
      rw [gap1 (n - 1) hn1]
      exact hGstep
    refine ⟨G, hG, C, ?_⟩
    intro x hx
    rw [hF x hx]
    dsimp [G]
    ring
theorem gap3 (n : ℕ) (hn : 2 ≤ n) :
    Step2 n = FiniteExpansion n := by
  calc
    Step2 n = Step1 n := (gap2 n hn).symm
    _ = Family (f n) := (gap1 n (by omega)).symm
    _ = FiniteExpansion n := family_eq_finiteExpansion n
theorem gap4 (n : ℕ) :
    Family (f n) = FiniteExpansion n := by
  exact family_eq_finiteExpansion n
theorem gap5 (n : ℕ) :
    Family (f n) =
      {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x =
        x * ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) /
            (Nat.factorial (n - k) : ℝ) * Real.log x ^ (n - k) + C} := by
  simpa [FiniteExpansion, primitive] using gap4 n

end
end ProofGap.Exercise2098
