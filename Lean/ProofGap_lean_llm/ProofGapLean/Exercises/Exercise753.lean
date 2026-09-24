import ProofGapLean.Prelude.Sequences
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise753

/-- Source: `proof_gap/exercise_753/1.txt`. -/
private theorem tendsto_add_const_atTop753 (p : ℝ) :
    Filter.Tendsto (fun x : ℝ => x + p) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  refine Filter.eventually_atTop.2 ⟨b - p, ?_⟩
  intro x hx
  linarith

private theorem tendsto_add_nat_mul_atTop753 (x q : ℝ) (hq : 0 < q) :
    Filter.Tendsto (fun N : ℕ => x + (N : ℝ) * q)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - x) / q)
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
  have hmul : (N : ℝ) * q ≤ (n : ℝ) * q :=
    mul_le_mul_of_nonneg_right hcast (le_of_lt hq)
  have hstrict : b - x < (N : ℝ) * q :=
    (div_lt_iff₀ hq).mp hN
  calc
    b ≤ x + (N : ℝ) * q := by linarith
    _ ≤ x + (n : ℝ) * q := add_le_add_right hmul x

theorem gap1 (φ : ℝ → ℝ) (p : ℝ) (hφ : Function.Periodic φ p) :
    ∀ x, φ (x + p) = φ x := by
  exact hφ

/-- Source: `proof_gap/exercise_753/2.txt`. -/
theorem gap2 (φ ψ : ℝ → ℝ) (p : ℝ)
    (hlim : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x => φ (x + p) - ψ (x + p))
      Filter.atTop (nhds 0) := by
  simpa only [Function.comp_apply] using
    hlim.comp (tendsto_add_const_atTop753 p)

/-- Source: `proof_gap/exercise_753/3.txt`. -/
theorem gap3 (φ ψ : ℝ → ℝ) (p : ℝ) (hφ : Function.Periodic φ p)
    (hlim : Filter.Tendsto (fun x => φ (x + p) - ψ (x + p))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x => φ x - ψ (x + p))
      Filter.atTop (nhds 0) := by
  have heq :
      (fun x => φ (x + p) - ψ (x + p)) =
        (fun x => φ x - ψ (x + p)) := by
    funext x
    rw [hφ x]
  rw [← heq]
  exact hlim

/-- Source: `proof_gap/exercise_753/4.txt`; replace arithmetic on unspecified
limit values by the corresponding `Tendsto` statement. -/
theorem gap4 (φ ψ : ℝ → ℝ) (p : ℝ)
    (h₁ : Filter.Tendsto (fun x => φ x - ψ (x + p))
      Filter.atTop (nhds 0))
    (h₂ : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x => ψ x - ψ (x + p))
      Filter.atTop (nhds (0 - 0)) := by
  have heq :
      (fun x => ψ x - ψ (x + p)) =
        (fun x => (φ x - ψ (x + p)) - (φ x - ψ x)) := by
    funext x
    ring
  rw [heq]
  exact h₁.sub h₂

/-- Source: `proof_gap/exercise_753/5.txt`. -/
theorem gap5 : (0 : ℝ) - 0 = 0 := by
  simp

/-- Source: `proof_gap/exercise_753/6.txt`. -/
theorem gap6 (φ ψ : ℝ → ℝ) (p : ℝ)
    (h₁ : Filter.Tendsto (fun x => φ x - ψ (x + p))
      Filter.atTop (nhds 0))
    (h₂ : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x => ψ x - ψ (x + p))
      Filter.atTop (nhds 0) := by
  simpa using gap4 φ ψ p h₁ h₂

/-- Source: `proof_gap/exercise_753/7.txt`; bind one fixed counterexample and
use the sequence `x₀+Nq` rather than one `x` equal to all of its terms. -/
theorem gap7 (ψ : ℝ → ℝ) (p q x₀ : ℝ)
    (hq : Function.Periodic ψ q) :
    ∀ N : ℕ,
      |ψ (x₀ + N * q) - ψ (x₀ + N * q + p)| =
        |ψ x₀ - ψ (x₀ + p)| := by
  intro N
  have hN : Function.Periodic ψ ((N : ℝ) * q) := by
    simpa only [nsmul_eq_mul] using hq.nsmul N
  rw [hN x₀]
  rw [show x₀ + (N : ℝ) * q + p =
      (x₀ + p) + (N : ℝ) * q by ring]
  rw [hN (x₀ + p)]

/-- Source: `proof_gap/exercise_753/8.txt`; express the eventual smallness at
the periodic sequence explicitly. -/
theorem gap8 (ψ : ℝ → ℝ) (p q x₀ : ℝ)
    (hq0 : 0 < q)
    (hlim : Filter.Tendsto (fun x => ψ x - ψ (x + p))
      Filter.atTop (nhds 0)) (hneq : ψ x₀ ≠ ψ (x₀ + p)) :
    ∃ N : ℕ,
      |ψ (x₀ + N * q) - ψ (x₀ + N * q + p)| <
        |ψ x₀ - ψ (x₀ + p)| := by
  have hc : 0 < |ψ x₀ - ψ (x₀ + p)| :=
    abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hs : Filter.Tendsto
      (fun N : ℕ =>
        ψ (x₀ + (N : ℝ) * q) - ψ (x₀ + (N : ℝ) * q + p))
      Filter.atTop (nhds 0) :=
    hlim.comp (tendsto_add_nat_mul_atTop753 x₀ q hq0)
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      dist (ψ (x₀ + (N : ℝ) * q) -
        ψ (x₀ + (N : ℝ) * q + p)) 0 <
        |ψ x₀ - ψ (x₀ + p)| :=
    (Metric.tendsto_nhds.1 hs) _ hc
  rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hN N le_rfl

/-- Source: `proof_gap/exercise_753/9.txt`; add positivity of the known period,
needed for `x₀+Nq → +∞`. -/
theorem gap9 (ψ : ℝ → ℝ) (p q : ℝ) (hq0 : 0 < q)
    (hq : Function.Periodic ψ q)
    (hlim : Filter.Tendsto (fun x => ψ x - ψ (x + p))
      Filter.atTop (nhds 0)) :
    (∃ x₀, ψ x₀ ≠ ψ (x₀ + p)) → False := by
  rintro ⟨x₀, hneq⟩
  obtain ⟨N, hlt⟩ := gap8 ψ p q x₀ hq0 hlim hneq
  have heq := gap7 ψ p q x₀ hq N
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

/-- Source: `proof_gap/exercise_753/10.txt`. -/
theorem gap10 (ψ : ℝ → ℝ) (p q : ℝ) (hq0 : 0 < q)
    (hq : Function.Periodic ψ q)
    (hlim : Filter.Tendsto (fun x => ψ x - ψ (x + p))
      Filter.atTop (nhds 0)) :
    Function.Periodic ψ p := by
  intro x
  by_contra h
  exact gap9 ψ p q hq0 hq hlim ⟨x, Ne.symm h⟩

/-- Source: `proof_gap/exercise_753/11.txt`; replace the ill-scoped existential
`x` by the periodic sequence. -/
theorem gap11 (φ ψ : ℝ → ℝ) (p x₁ : ℝ)
    (hφ : Function.Periodic φ p) (hψ : Function.Periodic ψ p) :
    ∀ N : ℕ,
      |φ (x₁ + N * p) - ψ (x₁ + N * p)| = |φ x₁ - ψ x₁| := by
  intro N
  have hφN : Function.Periodic φ ((N : ℝ) * p) := by
    simpa only [nsmul_eq_mul] using hφ.nsmul N
  have hψN : Function.Periodic ψ ((N : ℝ) * p) := by
    simpa only [nsmul_eq_mul] using hψ.nsmul N
  rw [hφN x₁, hψN x₁]

/-- Source: `proof_gap/exercise_753/12.txt`. -/
theorem gap12 (φ ψ : ℝ → ℝ) (p x₁ : ℝ) (hp : 0 < p)
    (hlim : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) (hneq : φ x₁ ≠ ψ x₁) :
    ∃ N : ℕ,
      |φ (x₁ + N * p) - ψ (x₁ + N * p)| < |φ x₁ - ψ x₁| := by
  have hc : 0 < |φ x₁ - ψ x₁| :=
    abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hs : Filter.Tendsto
      (fun N : ℕ =>
        φ (x₁ + (N : ℝ) * p) - ψ (x₁ + (N : ℝ) * p))
      Filter.atTop (nhds 0) :=
    hlim.comp (tendsto_add_nat_mul_atTop753 x₁ p hp)
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      dist (φ (x₁ + (N : ℝ) * p) -
        ψ (x₁ + (N : ℝ) * p)) 0 < |φ x₁ - ψ x₁| :=
    (Metric.tendsto_nhds.1 hs) _ hc
  rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hN N le_rfl

/-- Source: `proof_gap/exercise_753/13.txt`; add positivity of the common
period. -/
theorem gap13 (φ ψ : ℝ → ℝ) (p : ℝ) (hp : 0 < p)
    (hφ : Function.Periodic φ p) (hψ : Function.Periodic ψ p)
    (hlim : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    (∃ x₁, φ x₁ ≠ ψ x₁) → False := by
  rintro ⟨x₁, hneq⟩
  obtain ⟨N, hlt⟩ := gap12 φ ψ p x₁ hp hlim hneq
  have heq := gap11 φ ψ p x₁ hφ hψ N
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

/-- Source: `proof_gap/exercise_753/14.txt`. -/
theorem gap14 (φ ψ : ℝ → ℝ) (p : ℝ) (hp : 0 < p)
    (hφ : Function.Periodic φ p) (hψ : Function.Periodic ψ p)
    (hlim : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    ∀ x, φ x = ψ x := by
  intro x
  by_contra hneq
  exact gap13 φ ψ p hp hφ hψ hlim ⟨x, hneq⟩

/-- Source: `proof_gap/exercise_753/15.txt`. -/
theorem gap15 (φ ψ : ℝ → ℝ) (p : ℝ) (hp : 0 < p)
    (hφ : Function.Periodic φ p) (hψ : Function.Periodic ψ p)
    (hlim : Filter.Tendsto (fun x => φ x - ψ x)
      Filter.atTop (nhds 0)) :
    ∀ x, φ x = ψ x := by
  exact gap14 φ ψ p hp hφ hψ hlim

end ProofGap.Exercise753
