import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2710

noncomputable section

def term (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ (n / 2) * y ^ ((n + 1) / 2)

def evenPart (x y : ℝ) (n : ℕ) : ℝ :=
  if Even n then term x y n else 0

def oddPart (x y : ℝ) (n : ℕ) : ℝ :=
  if Odd n then term x y n else 0

private theorem hasSum_term_of_hasSum (x y a : ℝ)
    (ha : HasSum (fun k : ℕ => (x * y) ^ k) a) :
    HasSum (fun n : ℕ => term x y n) (a + y * a) := by
  have heq :
      (fun k : ℕ => term x y (2 * k)) =
        fun k : ℕ => (x * y) ^ k := by
    funext k
    have h₁ : (2 * k) / 2 = k := by omega
    have h₂ : (2 * k + 1) / 2 = k := by omega
    simp [term, h₁, h₂, mul_pow]
  have he : HasSum (fun k : ℕ => term x y (2 * k)) a := by
    rw [heq]
    exact ha
  have hoq :
      (fun k : ℕ => term x y (2 * k + 1)) =
        fun k : ℕ => y * (x * y) ^ k := by
    funext k
    have h₁ : (2 * k + 1) / 2 = k := by omega
    have h₂ : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
    simp only [term, h₁, h₂, mul_pow, pow_succ]
    ring
  have ho : HasSum (fun k : ℕ => term x y (2 * k + 1)) (y * a) := by
    rw [hoq]
    exact ha.mul_left y
  exact he.even_add_odd ho

theorem gap1 (x y : ℝ) (hxy : |x * y| < 1) :
    ∑' n : ℕ, term x y n =
      (∑' n : ℕ, evenPart x y n) + ∑' n : ℕ, oddPart x y n := by
  classical
  have hg : Summable (fun k : ℕ => (x * y) ^ k) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using hxy)
  rcases hg with ⟨a, ha⟩
  have hs : Summable (fun n : ℕ => term x y n) :=
    (hasSum_term_of_hasSum x y a ha).summable
  have heq :
      {n : ℕ | Even n}.indicator (fun n => term x y n) =
        fun n => evenPart x y n := by
    funext n
    by_cases hn : Even n <;> simp [evenPart, hn]
  have hoq :
      {n : ℕ | Odd n}.indicator (fun n => term x y n) =
        fun n => oddPart x y n := by
    funext n
    by_cases hn : Odd n <;> simp [oddPart, hn]
  have he : Summable (fun n : ℕ => evenPart x y n) := by
    rw [← heq]
    exact hs.indicator {n : ℕ | Even n}
  have ho : Summable (fun n : ℕ => oddPart x y n) := by
    rw [← hoq]
    exact hs.indicator {n : ℕ | Odd n}
  have hpoint : ∀ n : ℕ,
      term x y n = evenPart x y n + oddPart x y n := by
    intro n
    rcases Nat.even_or_odd n with hn | hn
    · have hn' : ¬ Odd n := by
        rintro ⟨k, hk⟩
        rcases hn with ⟨l, hl⟩
        omega
      simp [evenPart, oddPart, hn, hn']
    · have hn' : ¬ Even n := by
        rintro ⟨k, hk⟩
        rcases hn with ⟨l, hl⟩
        omega
      simp [evenPart, oddPart, hn, hn']
  calc
    ∑' n : ℕ, term x y n =
        ∑' n : ℕ, (evenPart x y n + oddPart x y n) :=
      tsum_congr hpoint
    _ = (∑' n : ℕ, evenPart x y n) + ∑' n : ℕ, oddPart x y n :=
      he.tsum_add ho

theorem gap2 (x y : ℝ) (hxy : |x * y| < 1) :
    ∑' n : ℕ, term x y n =
      (∑' k : ℕ, x ^ k * y ^ k) +
        ∑' k : ℕ, x ^ k * y ^ (k + 1) := by
  have hg : Summable (fun k : ℕ => (x * y) ^ k) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using hxy)
  rcases hg with ⟨a, ha⟩
  have ht : HasSum (fun n : ℕ => term x y n) (a + y * a) :=
    hasSum_term_of_hasSum x y a ha
  have heq :
      (fun k : ℕ => (x * y) ^ k) =
        fun k : ℕ => x ^ k * y ^ k := by
    funext k
    rw [mul_pow]
  have he : HasSum (fun k : ℕ => x ^ k * y ^ k) a := by
    rw [← heq]
    exact ha
  have hoq :
      (fun k : ℕ => y * (x * y) ^ k) =
        fun k : ℕ => x ^ k * y ^ (k + 1) := by
    funext k
    rw [mul_pow, pow_succ]
    ring
  have ho : HasSum (fun k : ℕ => x ^ k * y ^ (k + 1)) (y * a) := by
    rw [← hoq]
    exact ha.mul_left y
  calc
    ∑' n : ℕ, term x y n = a + y * a := ht.tsum_eq
    _ = (∑' k : ℕ, x ^ k * y ^ k) +
          ∑' k : ℕ, x ^ k * y ^ (k + 1) := by
      rw [he.tsum_eq, ho.tsum_eq]

theorem gap3 (x y : ℝ) (hxy : |x * y| < 1) :
    Summable (fun k : ℕ => |(x * y) ^ k|) := by
  have hs : Summable (fun k : ℕ => |x * y| ^ k) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (x * y))]
      exact hxy)
  simpa [abs_pow] using hs

theorem gap4 (x y : ℝ) (hxy : |x * y| < 1) :
    Summable (fun k : ℕ => |y * (x * y) ^ k|) := by
  have hs : Summable (fun k : ℕ => |y| * |(x * y) ^ k|) :=
    (gap3 x y hxy).mul_left |y|
  simpa [abs_mul] using hs

theorem gap5 (x y : ℝ) (hxy : |x * y| < 1) :
    ∑' n : ℕ, term x y n =
      (∑' k : ℕ, (x * y) ^ k) +
        y * ∑' k : ℕ, (x * y) ^ k := by
  have he :
      (∑' k : ℕ, x ^ k * y ^ k) = ∑' k : ℕ, (x * y) ^ k := by
    apply tsum_congr
    intro k
    rw [mul_pow]
  have ho :
      (∑' k : ℕ, x ^ k * y ^ (k + 1)) =
        ∑' k : ℕ, y * (x * y) ^ k := by
    apply tsum_congr
    intro k
    rw [mul_pow, pow_succ]
    ring
  rw [gap2 x y hxy, he, ho, tsum_mul_left]

theorem gap6 (x y : ℝ) (hxy : |x * y| < 1) :
    (∑' k : ℕ, (x * y) ^ k) +
        y * ∑' k : ℕ, (x * y) ^ k =
      (1 + y) * ∑' k : ℕ, (x * y) ^ k := by
  ring

theorem gap7 (x y : ℝ) (hxy : |x * y| < 1) :
    (1 + y) * ∑' k : ℕ, (x * y) ^ k =
      (1 + y) / (1 - x * y) := by
  have hnorm : ‖x * y‖ < 1 := by
    simpa [Real.norm_eq_abs] using hxy
  rw [tsum_geometric_of_norm_lt_one hnorm]
  simp [div_eq_mul_inv]

theorem gap8 (x y : ℝ) (hxy : |x * y| < 1) :
    ∑' n : ℕ, term x y n = (1 + y) / (1 - x * y) := by
  calc
    ∑' n : ℕ, term x y n =
        (∑' k : ℕ, (x * y) ^ k) +
          y * ∑' k : ℕ, (x * y) ^ k := gap5 x y hxy
    _ = (1 + y) * ∑' k : ℕ, (x * y) ^ k := gap6 x y hxy
    _ = (1 + y) / (1 - x * y) := gap7 x y hxy

end

end ProofGap.Exercise2710
