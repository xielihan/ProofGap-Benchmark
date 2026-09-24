import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2867

noncomputable section

def logLinearTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1)

def logQuadraticTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * (n + 1)) / (n + 1)

def sparseQuadraticTerm (x : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  if Even m then
    2 * (-1 : ℝ) ^ (m / 2 - 1) * x ^ m / m
  else
    0

def combinedLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  logLinearTerm x n + sparseQuadraticTerm x n

private theorem hasSum_logLinearTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (logLinearTerm x) (Real.log (1 + x)) := by
  have hneg : |-x| < 1 := by simpa using hx
  have hseries :
      HasSum (fun n : ℕ => - ((-x) ^ (n + 1) / (n + 1)))
        (Real.log (1 + x)) := by
    simpa using (Real.hasSum_pow_div_log_of_abs_lt_one hneg).neg
  have hterms :
      (fun n : ℕ => - ((-x) ^ (n + 1) / (n + 1))) =
        logLinearTerm x := by
    funext n
    unfold logLinearTerm
    rw [neg_pow, pow_succ]
    ring
  exact hterms ▸ hseries

private theorem hasSum_logQuadraticTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (logQuadraticTerm x) (Real.log (1 + x ^ 2)) := by
  have hx2 : |x ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg x]
  have hterms : logLinearTerm (x ^ 2) = logQuadraticTerm x := by
    funext n
    unfold logLinearTerm logQuadraticTerm
    rw [pow_mul]
  exact hterms ▸ hasSum_logLinearTerm hx2

private theorem sparseQuadraticTerm_odd (x : ℝ) (k : ℕ) :
    sparseQuadraticTerm x (2 * k + 1) = logQuadraticTerm x k := by
  have hm : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  have he : Even (2 * (k + 1)) := by
    refine ⟨k + 1, ?_⟩
    omega
  simp [sparseQuadraticTerm, logQuadraticTerm, hm, he]
  field_simp

private theorem sparseQuadraticTerm_even (x : ℝ) (k : ℕ) :
    sparseQuadraticTerm x (2 * k) = 0 := by
  have hnot : ¬Even (2 * k + 1) := by
    intro h
    rcases h with ⟨j, hj⟩
    omega
  simp [sparseQuadraticTerm, hnot]

private def parityEquiv : ℕ ⊕ ℕ ≃ ℕ where
  toFun z :=
    match z with
    | Sum.inl k => 2 * k
    | Sum.inr k => 2 * k + 1
  invFun n :=
    if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)
  left_inv := by
    intro z
    rcases z with k | k
    · change
        (if (2 * k) % 2 = 0 then
          (Sum.inl ((2 * k) / 2) : ℕ ⊕ ℕ)
        else
          Sum.inr ((2 * k) / 2)) = Sum.inl k
      have hmod : (2 * k) % 2 = 0 := by omega
      have hdiv : (2 * k) / 2 = k := by omega
      rw [if_pos hmod, hdiv]
    · change
        (if (2 * k + 1) % 2 = 0 then
          (Sum.inl ((2 * k + 1) / 2) : ℕ ⊕ ℕ)
        else
          Sum.inr ((2 * k + 1) / 2)) = Sum.inr k
      have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * k + 1) / 2 = k := by omega
      rw [if_neg hmod, hdiv]
  right_inv := by
    intro n
    change
      (match
        (if n % 2 = 0 then
          (Sum.inl (n / 2) : ℕ ⊕ ℕ)
        else
          Sum.inr (n / 2))
      with
      | Sum.inl k => 2 * k
      | Sum.inr k => 2 * k + 1) = n
    by_cases hmod : n % 2 = 0
    · rw [if_pos hmod]
      calc
        2 * (n / 2) = n % 2 + 2 * (n / 2) := by
          simp only [hmod, zero_add]
        _ = n := Nat.mod_add_div n 2
    · rw [if_neg hmod]
      have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
      have hone : n % 2 = 1 := by omega
      calc
        2 * (n / 2) + 1 = n % 2 + 2 * (n / 2) := by
          simpa only [hone] using
            (Nat.add_comm (2 * (n / 2)) 1)
        _ = n := Nat.mod_add_div n 2

private theorem parityEquiv_inl (k : ℕ) :
    parityEquiv (Sum.inl k) = 2 * k := rfl

private theorem parityEquiv_inr (k : ℕ) :
    parityEquiv (Sum.inr k) = 2 * k + 1 := rfl

private theorem hasSum_sumQuadraticTerm {x : ℝ} (hx : |x| < 1) :
    HasSum
      (Sum.elim (fun _ : ℕ => (0 : ℝ)) (logQuadraticTerm x))
      (Real.log (1 + x ^ 2)) := by
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have hq : HasSum (logQuadraticTerm x) (Real.log (1 + x ^ 2)) :=
    hasSum_logQuadraticTerm hx
  have hp0raw :
      HasSum
        (Sum.elim (fun _ : ℕ => (0 : ℝ)) (logQuadraticTerm x))
        (0 + Real.log (1 + x ^ 2)) :=
    hz.sum hq
  exact (zero_add (Real.log (1 + x ^ 2))) ▸ hp0raw

private theorem hasSum_sparseQuadraticTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (sparseQuadraticTerm x) (Real.log (1 + x ^ 2)) := by
  have hterms :
      Sum.elim (fun _ : ℕ => (0 : ℝ)) (logQuadraticTerm x) =
        (fun z : ℕ ⊕ ℕ => sparseQuadraticTerm x (parityEquiv z)) := by
    funext z
    rcases z with k | k
    · rw [parityEquiv_inl]
      exact (sparseQuadraticTerm_even x k).symm
    · rw [parityEquiv_inr]
      exact (sparseQuadraticTerm_odd x k).symm
  have hp :
      HasSum ((sparseQuadraticTerm x) ∘ parityEquiv)
        (Real.log (1 + x ^ 2)) := by
    change
      HasSum
        (fun z : ℕ ⊕ ℕ => sparseQuadraticTerm x (parityEquiv z))
        (Real.log (1 + x ^ 2))
    exact hterms ▸ (hasSum_sumQuadraticTerm hx)
  exact parityEquiv.hasSum_iff.mp hp

theorem gap1 :
    ∀ x : ℝ,
      Real.log (1 + x + x ^ 2 + x ^ 3) =
        Real.log ((1 + x) * (1 + x ^ 2)) := by
  intro x
  congr 1
  ring

theorem gap2
    (hfactor :
      ∀ x : ℝ,
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          Real.log ((1 + x) * (1 + x ^ 2))) :
    ∀ x : ℝ, -1 < x →
      Real.log ((1 + x) * (1 + x ^ 2)) =
        Real.log (1 + x) + Real.log (1 + x ^ 2) := by
  intro x hx
  rw [Real.log_mul]
  · linarith
  · nlinarith [sq_nonneg x]

theorem gap3
    (hfactor :
      ∀ x : ℝ,
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          Real.log ((1 + x) * (1 + x ^ 2)))
    (hlogProduct :
      ∀ x : ℝ, -1 < x →
        Real.log ((1 + x) * (1 + x ^ 2)) =
          Real.log (1 + x) + Real.log (1 + x ^ 2)) :
    ∀ x : ℝ, -1 < x →
      Real.log (1 + x + x ^ 2 + x ^ 3) =
        Real.log (1 + x) + Real.log (1 + x ^ 2) := by
  intro x hx
  rw [hfactor x, hlogProduct x hx]

theorem gap4
    (hlogs :
      ∀ x : ℝ, -1 < x →
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          Real.log (1 + x) + Real.log (1 + x ^ 2)) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (1 + x) = ∑' n, logLinearTerm x n := by
  intro x hx
  exact (hasSum_logLinearTerm hx).tsum_eq.symm

theorem gap5
    (hlinear :
      ∀ x : ℝ, |x| < 1 →
        Real.log (1 + x) = ∑' n, logLinearTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (1 + x ^ 2) = ∑' n, logQuadraticTerm x n := by
  intro x hx
  exact (hasSum_logQuadraticTerm hx).tsum_eq.symm

theorem gap6
    (hlogs :
      ∀ x : ℝ, -1 < x →
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          Real.log (1 + x) + Real.log (1 + x ^ 2))
    (hlinear :
      ∀ x : ℝ, |x| < 1 →
        Real.log (1 + x) = ∑' n, logLinearTerm x n)
    (hquadratic :
      ∀ x : ℝ, |x| < 1 →
        Real.log (1 + x ^ 2) = ∑' n, logQuadraticTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (1 + x + x ^ 2 + x ^ 3) =
        (∑' n, logLinearTerm x n) + (∑' n, logQuadraticTerm x n) := by
  intro x hx
  have hneg : -1 < x := (abs_lt.mp hx).1
  rw [hlogs x hneg, hlinear x hx, hquadratic x hx]

theorem gap7
    (hsum :
      ∀ x : ℝ, |x| < 1 →
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          (∑' n, logLinearTerm x n) + (∑' n, logQuadraticTerm x n)) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (1 + x + x ^ 2 + x ^ 3) =
        (∑' n, logLinearTerm x n) + (∑' n, sparseQuadraticTerm x n) := by
  intro x hx
  calc
    Real.log (1 + x + x ^ 2 + x ^ 3) =
        (∑' n, logLinearTerm x n) + (∑' n, logQuadraticTerm x n) :=
      hsum x hx
    _ = (∑' n, logLinearTerm x n) + Real.log (1 + x ^ 2) := by
      rw [(hasSum_logQuadraticTerm hx).tsum_eq]
    _ = (∑' n, logLinearTerm x n) + (∑' n, sparseQuadraticTerm x n) := by
      rw [(hasSum_sparseQuadraticTerm hx).tsum_eq]

theorem gap8
    (hsparse :
      ∀ x : ℝ, |x| < 1 →
        Real.log (1 + x + x ^ 2 + x ^ 3) =
          (∑' n, logLinearTerm x n) + (∑' n, sparseQuadraticTerm x n)) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (1 + x + x ^ 2 + x ^ 3) =
        ∑' n, combinedLogTerm x n := by
  intro x hx
  calc
    Real.log (1 + x + x ^ 2 + x ^ 3) =
        (∑' n, logLinearTerm x n) + (∑' n, sparseQuadraticTerm x n) :=
      hsparse x hx
    _ = ∑' n, combinedLogTerm x n := by
      have hl : Summable (logLinearTerm x) :=
        (hasSum_logLinearTerm hx).summable
      have hs : Summable (sparseQuadraticTerm x) :=
        (hasSum_sparseQuadraticTerm hx).summable
      simpa only [combinedLogTerm] using
        (hl.hasSum.add hs.hasSum).tsum_eq.symm

end

end ProofGap.Exercise2867
