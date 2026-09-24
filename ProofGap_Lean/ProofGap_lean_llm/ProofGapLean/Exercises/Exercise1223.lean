import ProofGapLean.Prelude.Core
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1223

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := (x - a) ^ n * φ x

def fallingFactorial (n j : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)

def leibnizExpansion (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    (Nat.choose (n - 1) j : ℝ) * fallingFactorial n j *
      (x - a) ^ (n - j) * iterDeriv (n - 1 - j) φ x

def quotientExpansion (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  leibnizExpansion a n φ x / (x - a)

private theorem fallingFactorial_eq_descFactorial
    (n j : ℕ) (hj : j ≤ n) :
    fallingFactorial n j = (n.descFactorial j : ℝ) := by
  unfold fallingFactorial
  apply (div_eq_iff ?_).2
  · rw [mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial hj).symm
  · positivity

private theorem iteratedDeriv_sub_pow (a x : ℝ) (n j : ℕ) :
    iteratedDeriv j (fun z : ℝ => (z - a) ^ n) x =
      (n.descFactorial j : ℝ) * (x - a) ^ (n - j) := by
  have h := congrFun
    (iteratedDeriv_comp_sub_const j (fun z : ℝ => z ^ n) a) x
  simpa only [iteratedDeriv_pow] using h

private theorem iteratedDeriv_sub_pow_at_center (a : ℝ) (n j : ℕ) :
    iteratedDeriv j (fun z : ℝ => (z - a) ^ n) a =
      if j = n then (Nat.factorial n : ℝ) else 0 := by
  rw [iteratedDeriv_sub_pow]
  by_cases hj : j = n
  · subst j
    simp [Nat.descFactorial_self]
  · by_cases hjlt : j < n
    · have hpos : 0 < n - j := by omega
      simp [hj, hpos.ne']
    · have hnj : n < j := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnj]
      simp [hj]

private theorem iterDeriv_f_center
    (a : ℝ) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ContDiffAt ℝ n φ a) :
    iterDeriv n (f a n φ) a =
      (Nat.factorial n : ℝ) * φ a := by
  have hp : ContDiffAt ℝ n (fun z : ℝ => (z - a) ^ n) a := by
    fun_prop
  have h := iteratedDeriv_fun_mul hp hφ
  have hf : f a n φ =
      fun z : ℝ => (z - a) ^ n * φ z := by rfl
  rw [hf]
  unfold iterDeriv
  rw [← iteratedDeriv_eq_iterate]
  rw [h]
  simp_rw [iteratedDeriv_sub_pow_at_center]
  simp

theorem gap1 (a x : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ x) :
    iterDeriv (n - 1) (f a n φ) x = leibnizExpansion a n φ x := by
  have hp : ContDiffAt ℝ (n - 1 : ℕ) (fun z : ℝ => (z - a) ^ n) x := by
    fun_prop
  have hφ' : ContDiffAt ℝ (n - 1 : ℕ) φ x := by
    apply hφ.of_le
    gcongr
    exact Nat.sub_le n 1
  have h := iteratedDeriv_fun_mul hp hφ'
  unfold f leibnizExpansion
  unfold iterDeriv
  rw [← iteratedDeriv_eq_iterate]
  rw [Nat.sub_add_cancel hn] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by
    simp only [Finset.mem_range] at hj
    omega
  rw [iteratedDeriv_sub_pow,
    ← fallingFactorial_eq_descFactorial n j hjn]
  simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
  ring

theorem gap2 (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ a) :
    iterDeriv (n - 1) (f a n φ) a = 0 := by
  rw [gap1 a a n φ hn hφ]
  unfold leibnizExpansion
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hpos : 0 < n - j := by omega
  simp [hpos.ne']

theorem gap3 (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ a) :
    Filter.Tendsto
        (fun x => (iterDeriv (n - 1) (f a n φ) x -
            iterDeriv (n - 1) (f a n φ) a) / (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhds (iterDeriv n (f a n φ) a)) := by
  have hF : ContDiffAt ℝ n (f a n φ) a := by
    unfold f
    fun_prop
  have hIF :
      DifferentiableAt ℝ
        (iteratedFDeriv ℝ (n - 1) (f a n φ)) a := by
    apply hF.differentiableAt_iteratedFDeriv
    apply WithTop.coe_lt_coe.mpr
    exact ENat.coe_lt_coe.mpr (by omega)
  have hd :
      DifferentiableAt ℝ
        (iteratedDeriv (n - 1) (f a n φ)) a := by
    rw [iteratedDeriv_eq_equiv_comp]
    fun_prop
  have hnext :
      deriv (iteratedDeriv (n - 1) (f a n φ)) a =
        iteratedDeriv n (f a n φ) a := by
    have hs := congrFun
      (iteratedDeriv_succ (n := n - 1) (f := f a n φ)) a
    rw [Nat.sub_add_cancel hn] at hs
    exact hs.symm
  have hh :
      HasDerivAt (iteratedDeriv (n - 1) (f a n φ))
        (iteratedDeriv n (f a n φ) a) a := by
    rw [← hnext]
    exact hd.hasDerivAt
  simpa only [iterDeriv, ← iteratedDeriv_eq_iterate, slope,
    smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
    using hh.tendsto_slope

theorem gap4 (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ a) :
    Filter.Tendsto (quotientExpansion a n φ)
      (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhds ((Nat.factorial n : ℝ) * φ a)) := by
  have ht := gap3 a n φ hn hφ
  rw [iterDeriv_f_center a n φ hφ] at ht
  have hev :
      ∀ᶠ x : ℝ in nhdsWithin a ({a} : Set ℝ)ᶜ,
        ContDiffAt ℝ n φ x :=
    (hφ.eventually (by simp)).filter_mono nhdsWithin_le_nhds
  have heq :
      quotientExpansion a n φ =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        (fun x => (iterDeriv (n - 1) (f a n φ) x -
            iterDeriv (n - 1) (f a n φ) a) / (x - a)) := by
    filter_upwards [hev] with x hx
    unfold quotientExpansion
    rw [← gap1 a x n φ hn hx, gap2 a n φ hn hφ]
    simp
  exact ht.congr' heq.symm

theorem gap5 (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ a) :
    iterDeriv n (f a n φ) a = (Nat.factorial n : ℝ) * φ a := by
  exact iterDeriv_f_center a n φ hφ

theorem gap6 (a : ℝ) (n : ℕ) (φ : ℝ → ℝ) (hn : 1 ≤ n)
    (hφ : ContDiffAt ℝ n φ a) :
    iterDeriv n (f a n φ) a = (Nat.factorial n : ℝ) * φ a := by
  exact gap5 a n φ hn hφ

end

end ProofGap.Exercise1223
