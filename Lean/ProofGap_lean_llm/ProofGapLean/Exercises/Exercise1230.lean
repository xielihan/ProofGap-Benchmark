import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ProofGap.Exercise1230

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x ^ 2)

def coefficient (n k : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) /
    ((Nat.factorial k : ℝ) * (Nat.factorial (n - 2 * k) : ℝ))

def compositionSum (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    coefficient n k * (2 * x) ^ (n - 2 * k) *
      iterDeriv (n - k) f (x ^ 2)

def RepresentsNear (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  ∀ᶠ t in nhds x, iterDeriv n (y f) t = compositionSum f n t

theorem gap1 (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (x ^ 2)) :
    deriv (y f) x = 2 * x * deriv f (x ^ 2) := by
  have hs : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hc : HasDerivAt (fun t : ℝ => f (t ^ 2))
      (deriv f (x ^ 2) * (2 * x)) x :=
    HasDerivAt.comp x hf.hasDerivAt hs
  unfold y
  simpa only [Function.comp_apply, mul_comm] using hc.deriv

theorem gap2 (f : ℝ → ℝ) (m : ℕ) (x : ℝ)
    (hrep : RepresentsNear f m x) :
    iterDeriv (m + 1) (y f) x = deriv (iterDeriv m (y f)) x := by
  simp [iterDeriv, Function.iterate_succ_apply']

theorem gap3 (f : ℝ → ℝ) (m : ℕ) (x : ℝ)
    (hrep : RepresentsNear f m x) :
    deriv (iterDeriv m (y f)) x = deriv (compositionSum f m) x := by
  exact Filter.EventuallyEq.deriv_eq hrep

private theorem coeff_rec (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 * k ≤ m) :
    coefficient (m + 1) k =
      coefficient m k +
        2 * (m - 2 * (k - 1) : ℕ) * coefficient m (k - 1) := by
  rcases k with _ | r
  · omega
  · generalize ha : m - 2 * (r + 1) = a
    have hm : m = a + 2 * (r + 1) := by omega
    subst m
    have h0 : a + 2 * (r + 1) + 1 - 2 * (r + 1) = a + 1 := by omega
    have h1 : a + 2 * (r + 1) - 2 * (r + 1) = a := by omega
    have h2 : a + 2 * (r + 1) - 2 * r = a + 2 := by omega
    simp only [coefficient, Nat.succ_sub_one]
    rw [h0, h1, h2]
    norm_num [Nat.factorial_succ]
    field_simp
    push_cast
    ring

private theorem coeff_top (r : ℕ) :
    coefficient (2 * r + 2) (r + 1) =
      2 * coefficient (2 * r + 1) r := by
  have h0 : 2 * r + 2 - 2 * (r + 1) = 0 := by omega
  have h1 : 2 * r + 1 - 2 * r = 1 := by omega
  simp only [coefficient]
  rw [h0, h1]
  norm_num [Nat.factorial_succ]
  field_simp
  push_cast
  ring

private lemma contDiffAt_iterDeriv (f : ℝ → ℝ) (x : ℝ) (n k : ℕ)
    (hf : ContDiffAt ℝ (n + k) f x) :
    ContDiffAt ℝ n (iterDeriv k f) x := by
  induction k generalizing f with
  | zero =>
      simpa [iterDeriv] using hf
  | succ k ih =>
      have hf' : ContDiffAt ℝ ((n + k) + 1) f x := by
        convert hf using 1 <;> omega
      have hderiv : ContDiffAt ℝ (n + k) (deriv f) x :=
        hf'.derivWithin (m := n + k) (le_refl _)
      simpa [iterDeriv, Function.iterate_succ_apply] using
        ih (f := deriv f) hderiv

private theorem deriv_compositionSum_expansion
    (f : ℝ → ℝ) (m : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ (m + 1) f (x ^ 2)) :
    deriv (compositionSum f m) x =
      ∑ k ∈ Finset.range (m / 2 + 1),
        (coefficient m k * (2 * (m - 2 * k : ℕ)) *
            (2 * x) ^ (m - 2 * k - 1) *
            iterDeriv (m - k) f (x ^ 2) +
          coefficient m k * (2 * x) ^ (m - 2 * k) *
            (2 * x * iterDeriv (m - k + 1) f (x ^ 2))) := by
  have hsum : HasDerivAt (compositionSum f m)
      (∑ k ∈ Finset.range (m / 2 + 1),
        (coefficient m k * (2 * (m - 2 * k : ℕ)) *
            (2 * x) ^ (m - 2 * k - 1) *
            iterDeriv (m - k) f (x ^ 2) +
          coefficient m k * (2 * x) ^ (m - 2 * k) *
            (2 * x * iterDeriv (m - k + 1) f (x ^ 2)))) x := by
    unfold compositionSum
    apply HasDerivAt.fun_sum
    intro k hk
    have hkm : k ≤ m := by
      have hk' := Finset.mem_range.mp hk
      omega
    have hfkcd : ContDiffAt ℝ 1 (iterDeriv (m - k) f) (x ^ 2) := by
      apply contDiffAt_iterDeriv f (x ^ 2) 1 (m - k)
      apply hf.of_le
      have hn : 1 + (m - k) ≤ m + 1 := by omega
      have hen : ((1 + (m - k) : ℕ) : ℕ∞) ≤ (m + 1 : ℕ) :=
        ENat.coe_le_coe.mpr hn
      have hwt := WithTop.coe_le_coe.mpr hen
      simpa only [ENat.coe_add, ENat.coe_one, Nat.cast_one,
        WithTop.coe_add, WithTop.coe_one] using hwt
    have hfkd : DifferentiableAt ℝ (iterDeriv (m - k) f) (x ^ 2) :=
      hfkcd.differentiableAt (by norm_num)
    have hs : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
    have hcomp : HasDerivAt
        (fun t : ℝ => iterDeriv (m - k) f (t ^ 2))
        (2 * x * iterDeriv (m - k + 1) f (x ^ 2)) x := by
      have hc : HasDerivAt
          (fun t : ℝ => iterDeriv (m - k) f (t ^ 2))
          (deriv (iterDeriv (m - k) f) (x ^ 2) * (2 * x)) x :=
        HasDerivAt.comp x hfkd.hasDerivAt hs
      convert hc using 1 <;>
        simp [iterDeriv, Function.iterate_succ_apply'] <;> ring
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      convert (hasDerivAt_id x).const_mul 2 using 1 <;> simp [id]
    have hp := hlin.pow (m - 2 * k)
    convert (hp.mul hcomp).const_mul (coefficient m k) using 1 <;>
      simp [id] <;> ring
  exact hsum.deriv

private theorem sum_recurrence (m : ℕ) (u : ℝ) (D : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m / 2 + 1),
      (coefficient m k * (2 * (m - 2 * k : ℕ)) *
          u ^ (m - 2 * k - 1) * D (m - k) +
        coefficient m k * u ^ (m - 2 * k) *
          (u * D (m - k + 1)))) =
      ∑ k ∈ Finset.range ((m + 1) / 2 + 1),
        coefficient (m + 1) k * u ^ (m + 1 - 2 * k) *
          D (m + 1 - k) := by
  rcases m.even_or_odd' with ⟨r, hr | hr⟩
  · subst m
    let A : ℕ → ℝ := fun k =>
      coefficient (2 * r) k * (2 * (2 * r - 2 * k : ℕ)) *
        u ^ (2 * r - 2 * k - 1) * D (2 * r - k)
    let B : ℕ → ℝ := fun k =>
      coefficient (2 * r) k * u ^ (2 * r - 2 * k) *
        (u * D (2 * r - k + 1))
    let T : ℕ → ℝ := fun k =>
      coefficient (2 * r + 1) k * u ^ (2 * r + 1 - 2 * k) *
        D (2 * r + 1 - k)
    have hbase : B 0 = T 0 := by
      dsimp [B, T]
      simp only [coefficient, Nat.sub_zero, Nat.mul_zero]
      rw [pow_succ]
      field_simp
    have hcombine (j : ℕ) (hj : j ∈ Finset.range r) :
        B (j + 1) + A j = T (j + 1) := by
      have hjr : j < r := Finset.mem_range.mp hj
      dsimp [A, B, T]
      rw [coeff_rec (2 * r) (j + 1) (by omega) (by omega)]
      have he₁ : 2 * r - 2 * (j + 1) + 1 =
          2 * r + 1 - 2 * (j + 1) := by omega
      have he₂ : 2 * r - (j + 1) + 1 =
          2 * r + 1 - (j + 1) := by omega
      have he₃ : 2 * r - 2 * j - 1 =
          2 * r + 1 - 2 * (j + 1) := by omega
      have he₄ : 2 * r - j = 2 * r + 1 - (j + 1) := by omega
      have hp : u ^ (2 * r - 2 * (j + 1)) * u =
          u ^ (2 * r + 1 - 2 * (j + 1)) := by
        rw [← pow_succ, he₁]
      rw [he₂, he₃, he₄]
      rw [show 2 * r - 2 * ((j + 1) - 1) = 2 * r - 2 * j by omega]
      rw [show 2 * (2 * r - 2 * j : ℕ) =
        (2 : ℝ) * (2 * r - 2 * j : ℕ) by norm_num]
      push_cast
      rw [← hp]
      ring
    have hlast : A r = 0 := by
      simp [A]
    have hdiv : 2 * r / 2 = r := by omega
    have hdiv1 : (2 * r + 1) / 2 = r := by omega
    change (∑ k ∈ Finset.range (2 * r / 2 + 1), (A k + B k)) =
      ∑ k ∈ Finset.range ((2 * r + 1) / 2 + 1), T k
    rw [hdiv, hdiv1, Finset.sum_add_distrib]
    calc
      (∑ k ∈ Finset.range (r + 1), A k) +
          ∑ k ∈ Finset.range (r + 1), B k =
        (∑ k ∈ Finset.range r, A k) +
          (∑ j ∈ Finset.range r, B (j + 1)) + B 0 := by
            rw [Finset.sum_range_succ, hlast, add_zero,
              Finset.sum_range_succ']
            ring
      _ = B 0 + ∑ j ∈ Finset.range r, (B (j + 1) + A j) := by
            rw [Finset.sum_add_distrib]
            ring
      _ = T 0 + ∑ j ∈ Finset.range r, T (j + 1) := by
            rw [hbase]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            exact hcombine j hj
      _ = ∑ k ∈ Finset.range (r + 1), T k := by
            rw [Finset.sum_range_succ']
            ring
  · subst m
    let A : ℕ → ℝ := fun k =>
      coefficient (2 * r + 1) k *
        (2 * (2 * r + 1 - 2 * k : ℕ)) *
        u ^ (2 * r + 1 - 2 * k - 1) * D (2 * r + 1 - k)
    let B : ℕ → ℝ := fun k =>
      coefficient (2 * r + 1) k * u ^ (2 * r + 1 - 2 * k) *
        (u * D (2 * r + 1 - k + 1))
    let T : ℕ → ℝ := fun k =>
      coefficient (2 * r + 2) k * u ^ (2 * r + 2 - 2 * k) *
        D (2 * r + 2 - k)
    have hbase : B 0 = T 0 := by
      dsimp [B, T]
      simp only [coefficient, Nat.sub_zero, Nat.mul_zero]
      rw [pow_succ]
      field_simp
      rw [← pow_add]
      ring
    have hcombine (j : ℕ) (hj : j ∈ Finset.range r) :
        B (j + 1) + A j = T (j + 1) := by
      have hjr : j < r := Finset.mem_range.mp hj
      dsimp [A, B, T]
      rw [coeff_rec (2 * r + 1) (j + 1) (by omega) (by omega)]
      have he₁ : 2 * r + 1 - 2 * (j + 1) + 1 =
          2 * r + 2 - 2 * (j + 1) := by omega
      have he₂ : 2 * r + 1 - (j + 1) + 1 =
          2 * r + 2 - (j + 1) := by omega
      have he₃ : 2 * r + 1 - 2 * j - 1 =
          2 * r + 2 - 2 * (j + 1) := by omega
      have he₄ : 2 * r + 1 - j =
          2 * r + 2 - (j + 1) := by omega
      have hp : u ^ (2 * r + 1 - 2 * (j + 1)) * u =
          u ^ (2 * r + 2 - 2 * (j + 1)) := by
        rw [← pow_succ, he₁]
      rw [he₂, he₃, he₄]
      rw [show 2 * r + 1 - 2 * ((j + 1) - 1) =
        2 * r + 1 - 2 * j by omega]
      rw [show 2 * (2 * r + 1 - 2 * j : ℕ) =
        (2 : ℝ) * (2 * r + 1 - 2 * j : ℕ) by norm_num]
      push_cast
      rw [← hp]
      ring
    have htop : A r = T (r + 1) := by
      dsimp [A, T]
      rw [coeff_top r]
      have h₁ : 2 * r + 1 - 2 * r = 1 := by omega
      have h₂ : 2 * r + 1 - 2 * r - 1 = 0 := by omega
      have h₃ : 2 * r + 1 - r = r + 1 := by omega
      have h₄ : 2 * r + 2 - 2 * (r + 1) = 0 := by omega
      have h₅ : 2 * r + 2 - (r + 1) = r + 1 := by omega
      rw [h₂, h₃, h₄, h₅, h₁]
      norm_num only [Nat.cast_one, one_mul, pow_zero]
      ring
    have hdiv : (2 * r + 1) / 2 = r := by omega
    have hdiv1 : (2 * r + 2) / 2 = r + 1 := by omega
    change (∑ k ∈ Finset.range ((2 * r + 1) / 2 + 1),
        (A k + B k)) =
      ∑ k ∈ Finset.range ((2 * r + 2) / 2 + 1), T k
    rw [hdiv, hdiv1, Finset.sum_add_distrib]
    calc
      (∑ k ∈ Finset.range (r + 1), A k) +
          ∑ k ∈ Finset.range (r + 1), B k =
        ((∑ j ∈ Finset.range r, A j) + A r) +
          ((∑ j ∈ Finset.range r, B (j + 1)) + B 0) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ']
      _ = B 0 + (∑ j ∈ Finset.range r, (B (j + 1) + A j)) +
          A r := by
            rw [Finset.sum_add_distrib]
            ring
      _ = T 0 + (∑ j ∈ Finset.range r, T (j + 1)) +
          T (r + 1) := by
            rw [hbase, htop]
            congr 2
            apply Finset.sum_congr rfl
            intro j hj
            exact hcombine j hj
      _ = ∑ k ∈ Finset.range (r + 2), T k := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ']
            ring

theorem gap4 (f : ℝ → ℝ) (m : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ (m + 1) f (x ^ 2)) :
    deriv (compositionSum f m) x = compositionSum f (m + 1) x := by
  rw [deriv_compositionSum_expansion f m x hf]
  unfold compositionSum
  exact sum_recurrence m (2 * x)
    (fun q => iterDeriv q f (x ^ 2))

theorem gap5 (f : ℝ → ℝ) (m : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ (m + 1) f (x ^ 2))
    (hrep : RepresentsNear f m x) :
    iterDeriv (m + 1) (y f) x = compositionSum f (m + 1) x := by
  rw [gap2 f m x hrep, gap3 f m x hrep, gap4 f m x hf]

theorem gap6 (f : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ n f (x ^ 2)) :
    iterDeriv n (y f) x = compositionSum f n x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y, compositionSum, coefficient]
  | succ m ih =>
      have hrep : RepresentsNear f m x := by
        unfold RepresentsNear
        have hevent_at :
            ∀ᶠ u in nhds (x ^ 2), ContDiffAt ℝ (m + 1) f u :=
          hf.eventually (by simp)
        have htend :
            Filter.Tendsto (fun t : ℝ => t ^ 2) (nhds x) (nhds (x ^ 2)) :=
          (continuous_pow 2).continuousAt
        have hevent := htend.eventually hevent_at
        filter_upwards [hevent] with t hft
        have hfm : ContDiffAt ℝ m f (t ^ 2) := by
          apply hft.of_le
          have hn : (m : ℕ∞) ≤ (m + 1 : ℕ) :=
            ENat.coe_le_coe.mpr (Nat.le_succ m)
          exact WithTop.coe_le_coe.mpr hn
        exact ih t hfm
      exact gap5 f m x hf hrep

theorem gap7 (f : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ n f (x ^ 2)) :
    iterDeriv n (y f) x = compositionSum f n x := by
  exact gap6 f n x hf

end

end ProofGap.Exercise1230
