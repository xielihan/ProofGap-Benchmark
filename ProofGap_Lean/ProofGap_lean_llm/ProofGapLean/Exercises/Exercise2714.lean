import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2714

noncomputable section

open Filter
open scoped BigOperators Interval

def aTerm (α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) / Real.rpow n α

def bTerm (β : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) / Real.rpow n β

def coefficient (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, aTerm α i * bTerm β (n - i + 1)

def amplitude (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    1 / (Real.rpow i α * Real.rpow (n - i + 1) β)

def firstHalf (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2),
    1 / (Real.rpow i α * Real.rpow (n - i + 1) β)

def secondHalf (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (n / 2 + 1) n,
    1 / (Real.rpow i α * Real.rpow (n - i + 1) β)

def partialA (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, aTerm α i

def partialB (β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, bTerm β i

def cauchyPartial (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 n, coefficient α β s

def delta (α β : ℝ) (n : ℕ) : ℝ :=
  partialA α n * partialB β n - cauchyPartial α β n

theorem gap1 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ n : ℕ,
      coefficient α β n =
        ∑ i ∈ Finset.Icc 1 n,
          aTerm α i * bTerm β (n - i + 1) := by
  intro n
  rfl

theorem gap2 (α β : ℝ) :
    ∀ n : ℕ,
      coefficient α β n =
        (-1 : ℝ) ^ (n - 1) * amplitude α β n := by
  intro n
  rw [coefficient, amplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Icc] at hi
  simp only [aTerm, bTerm]
  have hsub : n - i + 1 - 1 = n - i := by omega
  rw [hsub]
  have hexp : i - 1 + (n - i) = n - 1 := by omega
  rw [← hexp, pow_add]
  have hcast : ((n - i + 1 : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hi.2]
  rw [hcast]
  ring

theorem gap3 (α β : ℝ) :
    ∃ d : ℕ → ℝ,
      (∀ n, d n = amplitude α β n) ∧
      ∀ n, coefficient α β n = (-1 : ℝ) ^ (n - 1) * d n := by
  exact ⟨amplitude α β, fun _ => rfl, gap2 α β⟩

theorem gap4 (α β : ℝ) :
    ∀ n : ℕ,
      coefficient α β n = (-1 : ℝ) ^ (n - 1) * amplitude α β n := by
  exact gap2 α β

theorem gap5 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ∀ n : ℕ,
      amplitude α β n ≥ firstHalf α β n := by
  intro n
  unfold amplitude firstHalf
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, hi.2.trans (Nat.div_le_self n 2)⟩
  · intro i hi _
    simp only [Finset.mem_Icc] at hi
    have hi₀ : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    have hni : (0 : ℝ) ≤ (n : ℝ) - (i : ℝ) + 1 := by linarith
    exact one_div_nonneg.mpr
      (mul_nonneg (Real.rpow_nonneg hi₀ _) (Real.rpow_nonneg hni _))

theorem gap6 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ∀ n : ℕ, 2 ≤ n →
      amplitude α β n ≥
        1 / Real.rpow ((n - n / 2 : ℕ) : ℝ) α *
          (∑ j ∈ Finset.Icc (n / 2 + 1) n,
            1 / Real.rpow j β) := by
  classical
  intro n hn
  let m : ℕ := n / 2
  let s : Finset ℕ := Finset.Icc (m + 1) n
  let t : Finset ℕ := Finset.Icc 1 (n - m)
  let f : ℕ → ℝ := fun j =>
    1 / (Real.rpow ((n - j + 1 : ℕ) : ℝ) α * Real.rpow (j : ℝ) β)
  let g : ℕ → ℝ := fun i =>
    1 / (Real.rpow (i : ℝ) α * Real.rpow ((n : ℝ) - (i : ℝ) + 1) β)
  have hreindex : (∑ j ∈ s, f j) = ∑ i ∈ t, g i := by
    apply Finset.sum_nbij' (fun j => n - j + 1) (fun i => n - i + 1)
    · intro j hj
      simp only [s, t, Finset.mem_Icc] at hj ⊢
      omega
    · intro i hi
      simp only [s, t, Finset.mem_Icc] at hi ⊢
      omega
    · intro j hj
      simp only [s, Finset.mem_Icc] at hj
      omega
    · intro i hi
      simp only [t, Finset.mem_Icc] at hi
      omega
    · intro j hj
      simp only [s, Finset.mem_Icc] at hj
      have hnat : n - (n - j + 1) + 1 = j := by omega
      have hreal : (n : ℝ) - ((n - j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        have hle : n - j + 1 ≤ n := by omega
        calc
          (n : ℝ) - ((n - j + 1 : ℕ) : ℝ) + 1 =
              ((n - (n - j + 1) : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub hle]
          _ = ((n - (n - j + 1) + 1 : ℕ) : ℝ) := by norm_num
          _ = (j : ℝ) := by rw [hnat]
      simp only [f, g]
      rw [hreal]
  have hsubset : t ⊆ Finset.Icc 1 n := by
    intro i hi
    simp only [t, Finset.mem_Icc] at hi ⊢
    omega
  have hsum_subset : (∑ i ∈ t, g i) ≤ ∑ i ∈ Finset.Icc 1 n, g i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro i hi _
    simp only [Finset.mem_Icc] at hi
    have hi₀ : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    have hni : (0 : ℝ) ≤ (n : ℝ) - (i : ℝ) + 1 := by linarith
    exact one_div_nonneg.mpr
      (mul_nonneg (Real.rpow_nonneg hi₀ _) (Real.rpow_nonneg hni _))
  have hterm : ∀ j ∈ s,
      1 / Real.rpow ((n - m : ℕ) : ℝ) α * (1 / Real.rpow (j : ℝ) β) ≤ f j := by
    intro j hj
    simp only [s, Finset.mem_Icc] at hj
    have hmap_pos : 0 < n - j + 1 := by omega
    have hmap_le : n - j + 1 ≤ n - m := by omega
    have hpow : Real.rpow ((n - j + 1 : ℕ) : ℝ) α ≤
        Real.rpow ((n - m : ℕ) : ℝ) α := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast hmap_le
      · exact hα.le
    have hinv : 1 / Real.rpow ((n - m : ℕ) : ℝ) α ≤
        1 / Real.rpow ((n - j + 1 : ℕ) : ℝ) α := by
      apply one_div_le_one_div_of_le
      · exact Real.rpow_pos_of_pos (by positivity) _
      · exact hpow
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hjnonneg : 0 ≤ 1 / Real.rpow (j : ℝ) β :=
      one_div_nonneg.mpr (Real.rpow_nonneg hjpos.le _)
    calc
      1 / Real.rpow ((n - m : ℕ) : ℝ) α * (1 / Real.rpow (j : ℝ) β) ≤
          1 / Real.rpow ((n - j + 1 : ℕ) : ℝ) α *
            (1 / Real.rpow (j : ℝ) β) := mul_le_mul_of_nonneg_right hinv hjnonneg
      _ = f j := by simp only [f]; ring
  calc
    1 / Real.rpow ((n - n / 2 : ℕ) : ℝ) α *
        (∑ j ∈ Finset.Icc (n / 2 + 1) n, 1 / Real.rpow j β) =
        ∑ j ∈ s,
          1 / Real.rpow ((n - m : ℕ) : ℝ) α * (1 / Real.rpow (j : ℝ) β) := by
            simp only [m, s, Finset.mul_sum]
    _ ≤ ∑ j ∈ s, f j := Finset.sum_le_sum fun j hj => hterm j hj
    _ = ∑ i ∈ t, g i := hreindex
    _ ≤ ∑ i ∈ Finset.Icc 1 n, g i := hsum_subset
    _ = amplitude α β n := by rfl

theorem gap7 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ∀ n : ℕ, 2 ≤ n →
      (∑ j ∈ Finset.Icc (n / 2 + 1) n,
          1 / Real.rpow j β) ≥
        ∫ t in (((n / 2 + 1 : ℕ) : ℝ))..((n : ℝ) + 1),
          1 / Real.rpow t β := by
  intro n hn
  let a : ℕ := n / 2 + 1
  let b : ℕ := n + 1
  have hab' : a ≤ b := by dsimp [a, b]; omega
  have hanti : AntitoneOn (fun t : ℝ => 1 / Real.rpow t β)
      (Set.Icc (a : ℝ) (b : ℝ)) := by
    intro x hx y hy hxy
    apply one_div_le_one_div_of_le
    · exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hx.1) _
    · apply Real.rpow_le_rpow
      · exact (lt_of_lt_of_le (by positivity) hx.1).le
      · exact hxy
      · exact hβ.le
  have h := hanti.integral_le_sum_Ico hab'
  have hset : Finset.Ico a b = Finset.Icc (n / 2 + 1) n := by
    ext j
    simp [a, b]
  rw [hset] at h
  simpa [a, b, Nat.cast_add, Nat.cast_one] using h

theorem gap8 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ∀ n : ℕ, 2 ≤ n →
      amplitude α β n ≥
        1 / Real.rpow ((n - n / 2 : ℕ) : ℝ) α *
          ∫ t in (((n / 2 + 1 : ℕ) : ℝ))..((n : ℝ) + 1),
            1 / Real.rpow t β := by
  intro n hn
  have hdiff : 0 < n - n / 2 := by omega
  have hfactor : 0 ≤ 1 / Real.rpow ((n - n / 2 : ℕ) : ℝ) α := by
    exact one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
  exact (mul_le_mul_of_nonneg_left (gap7 α β hα hβ hab n hn) hfactor).trans
    (gap6 α β hα hβ hab n hn)

private theorem amplitude_lower_rpow (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ n : ℕ, 1 ≤ n →
      Real.rpow n (1 - (α + β)) ≤ amplitude α β n := by
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hterm : ∀ i ∈ Finset.Icc 1 n,
      1 / Real.rpow (n : ℝ) (α + β) ≤
        1 / (Real.rpow (i : ℝ) α * Real.rpow ((n : ℝ) - (i : ℝ) + 1) β) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi.1
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    have hsecondpos : (0 : ℝ) < (n : ℝ) - (i : ℝ) + 1 := by linarith
    have hsecondle : (n : ℝ) - (i : ℝ) + 1 ≤ (n : ℝ) := by
      have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
      linarith
    have hpowi : Real.rpow (i : ℝ) α ≤ Real.rpow (n : ℝ) α := by
      apply Real.rpow_le_rpow hipos.le hin hα.le
    have hpows : Real.rpow ((n : ℝ) - (i : ℝ) + 1) β ≤
        Real.rpow (n : ℝ) β := by
      apply Real.rpow_le_rpow hsecondpos.le hsecondle hβ.le
    have hmul : Real.rpow (i : ℝ) α *
        Real.rpow ((n : ℝ) - (i : ℝ) + 1) β ≤
        Real.rpow (n : ℝ) (α + β) := by
      have hnadd : Real.rpow (n : ℝ) (α + β) =
          Real.rpow (n : ℝ) α * Real.rpow (n : ℝ) β := by
        simp only [Real.rpow_eq_pow]
        exact Real.rpow_add hnpos α β
      rw [hnadd]
      exact mul_le_mul hpowi hpows (Real.rpow_nonneg hsecondpos.le _)
        (Real.rpow_nonneg hnpos.le _)
    apply one_div_le_one_div_of_le
    · exact mul_pos (Real.rpow_pos_of_pos hipos _) (Real.rpow_pos_of_pos hsecondpos _)
    · exact hmul
  have hsum := Finset.sum_le_sum hterm
  have hcard : (Finset.Icc 1 n).card = n := by simp [Nat.card_Icc, hn]
  have hleft : Real.rpow (n : ℝ) (1 - (α + β)) =
      (n : ℝ) * (1 / Real.rpow (n : ℝ) (α + β)) := by
    rw [Real.rpow_eq_pow, Real.rpow_sub hnpos, Real.rpow_one, ← Real.rpow_eq_pow]
    ring
  calc
    Real.rpow (n : ℝ) (1 - (α + β)) =
        (n : ℝ) * (1 / Real.rpow (n : ℝ) (α + β)) := hleft
    _ = ∑ i ∈ Finset.Icc 1 n, 1 / Real.rpow (n : ℝ) (α + β) := by
      simp [hcard]
    _ ≤ amplitude α β n := by simpa [amplitude] using hsum

theorem gap9 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ∃ N : ℕ, ∀ n ≥ N,
      amplitude α β n ≥
        Real.rpow 2 α / (2 * (1 - β)) *
          (1 - 1 / Real.rpow 2 (1 - β)) *
          Real.rpow n (1 - (α + β)) := by
  let e : ℝ := 1 - β
  let A : ℝ := Real.rpow 2 α
  let B : ℝ := Real.rpow 2 e
  have hepos : 0 < e := by dsimp [e]; linarith
  have hele : e ≤ 1 := by dsimp [e]; linarith
  have hae : α ≤ e := by dsimp [e]; linarith
  have hA : A ≤ B := by
    simp only [A, B, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hae
  have hBpos : 0 < B := by
    simp only [B]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hB1 : 1 ≤ B := by
    simp only [B, Real.rpow_eq_pow]
    exact Real.one_le_rpow (by norm_num) hepos.le
  have hBernoulli : B ≤ 1 + e := by
    simp only [B, Real.rpow_eq_pow]
    convert rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num) hepos.le hele using 1 <;>
      norm_num
  have hdiff : B - 1 ≤ e := by linarith
  have hprod₁ : A * (B - 1) ≤ B * (B - 1) :=
    mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hB1)
  have hprod₂ : B * (B - 1) ≤ B * e :=
    mul_le_mul_of_nonneg_left hdiff hBpos.le
  have hconst : A / (2 * e) * (1 - 1 / B) ≤ 1 := by
    have he0 : e ≠ 0 := hepos.ne'
    have hB0 : B ≠ 0 := hBpos.ne'
    have hrearrange : A / (2 * e) * (1 - 1 / B) = A * (B - 1) / (2 * e * B) := by
      field_simp
    rw [hrearrange, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hepos) hBpos)]
    nlinarith [hprod₁, hprod₂]
  refine ⟨1, ?_⟩
  intro n hn
  have hlower := amplitude_lower_rpow α β hα hβ n hn
  have hrnonneg : 0 ≤ Real.rpow (n : ℝ) (1 - (α + β)) :=
    Real.rpow_nonneg (by positivity) _
  have hscaled : A / (2 * e) * (1 - 1 / B) *
      Real.rpow (n : ℝ) (1 - (α + β)) ≤
      Real.rpow (n : ℝ) (1 - (α + β)) := by
    simpa using mul_le_mul_of_nonneg_right hconst hrnonneg
  exact (by simpa [A, B, e] using hscaled.trans hlower)

theorem gap10 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ¬ Tendsto (amplitude α β) atTop (nhds 0) := by
  intro hlim
  have hsmall : ∀ᶠ n in atTop, amplitude α β n < (1 : ℝ) / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨n, hsmall, hn⟩ := (hsmall.and (eventually_ge_atTop (1 : ℕ))).exists
  have hlower := amplitude_lower_rpow α β hα hβ n hn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : (0 : ℝ) ≤ 1 - (α + β) := by linarith
  have hone : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 - (α + β)) := by
    rw [Real.rpow_eq_pow]
    exact Real.one_le_rpow hnreal hexp
  linarith

theorem gap11 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : α + β ≤ 1) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => coefficient α β (n + 1)) := by
  intro hs
  unfold ProofGap.SeriesConverges at hs
  rcases hs with ⟨l, hl⟩
  have hpartial : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, coefficient α β (k + 1))
      atTop (nhds l) := by
    simpa [HasSum] using hl
  have hshift : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), coefficient α β (k + 1))
      atTop (nhds l) := (tendsto_add_atTop_iff_nat 1).2 hpartial
  have hcoeff : Tendsto (fun n : ℕ => coefficient α β (n + 1)) atTop (nhds 0) := by
    have hdiff := hshift.sub hpartial
    convert hdiff using 1
    · ext n
      simp [Finset.sum_range_succ]
    · ring
  have hamp_nonneg : ∀ n : ℕ, 0 ≤ amplitude α β n := by
    intro n
    unfold amplitude
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi₀ : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    have hni : (0 : ℝ) ≤ (n : ℝ) - (i : ℝ) + 1 := by linarith
    exact one_div_nonneg.mpr
      (mul_nonneg (Real.rpow_nonneg hi₀ _) (Real.rpow_nonneg hni _))
  have habs : ∀ n : ℕ,
      |coefficient α β (n + 1)| = amplitude α β (n + 1) := by
    intro n
    rw [gap4 α β (n + 1)]
    simp [abs_mul, abs_pow, hamp_nonneg]
  have hampShift : Tendsto (fun n : ℕ => amplitude α β (n + 1)) atTop (nhds 0) := by
    have ha := hcoeff.abs
    simpa only [abs_zero, habs] using ha
  exact gap10 α β hα hβ hab ((tendsto_add_atTop_iff_nat 1).1 hampShift)

theorem gap12 (α β : ℝ) :
    ∀ n : ℕ,
      amplitude α β n = firstHalf α β n + secondHalf α β n := by
  classical
  intro n
  unfold amplitude firstHalf secondHalf
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_Icc] at hi₁ hi₂
    omega

theorem gap13 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    Asymptotics.IsBigO atTop (firstHalf α β)
      (fun n : ℕ =>
        1 / Real.rpow n β + Real.rpow n (1 - (α + β)) +
          Real.rpow n ((1 - (α + β)) / 2)) := by
  have hfirst_bound : ∀ n : ℕ, 2 ≤ n →
      firstHalf α β n ≤
        (1 / Real.rpow ((n : ℝ) / 2) β) *
          (∑ i ∈ Finset.Icc 1 (n / 2), 1 / Real.rpow (i : ℝ) α) := by
    intro n hn
    unfold firstHalf
    calc
      (∑ i ∈ Finset.Icc 1 (n / 2),
          1 / (Real.rpow (i : ℝ) α * Real.rpow ((n : ℝ) - (i : ℝ) + 1) β)) ≤
          ∑ i ∈ Finset.Icc 1 (n / 2),
            (1 / Real.rpow ((n : ℝ) / 2) β) *
              (1 / Real.rpow (i : ℝ) α) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_Icc] at hi
        have hi2 : 2 * i ≤ n := by omega
        have hi2r : (2 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi2
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hhalfpos : (0 : ℝ) < (n : ℝ) / 2 := by positivity
        have hsecondpos : (0 : ℝ) < (n : ℝ) - (i : ℝ) + 1 := by linarith
        have hbase : (n : ℝ) / 2 ≤ (n : ℝ) - (i : ℝ) + 1 := by linarith
        have hpow : Real.rpow ((n : ℝ) / 2) β ≤
            Real.rpow ((n : ℝ) - (i : ℝ) + 1) β := by
          apply Real.rpow_le_rpow hhalfpos.le hbase hβ.le
        have hinv : 1 / Real.rpow ((n : ℝ) - (i : ℝ) + 1) β ≤
            1 / Real.rpow ((n : ℝ) / 2) β := by
          apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hhalfpos _) hpow
        have hinonneg : 0 ≤ 1 / Real.rpow (i : ℝ) α := by
          exact one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
        calc
          1 / (Real.rpow (i : ℝ) α *
              Real.rpow ((n : ℝ) - (i : ℝ) + 1) β) =
              (1 / Real.rpow (i : ℝ) α) *
                (1 / Real.rpow ((n : ℝ) - (i : ℝ) + 1) β) := by ring
          _ ≤ (1 / Real.rpow (i : ℝ) α) *
              (1 / Real.rpow ((n : ℝ) / 2) β) :=
            mul_le_mul_of_nonneg_left hinv hinonneg
          _ = (1 / Real.rpow ((n : ℝ) / 2) β) *
              (1 / Real.rpow (i : ℝ) α) := by ring
      _ = (1 / Real.rpow ((n : ℝ) / 2) β) *
          (∑ i ∈ Finset.Icc 1 (n / 2), 1 / Real.rpow (i : ℝ) α) := by
        rw [Finset.mul_sum]
  have hhalf_rewrite : ∀ n : ℕ, 1 ≤ n →
      1 / Real.rpow ((n : ℝ) / 2) β =
        Real.rpow 2 β * (1 / Real.rpow (n : ℝ) β) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn0 : Real.rpow (n : ℝ) β ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    have h20 : Real.rpow 2 β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow hnpos.le (by norm_num) β]
    field_simp
  by_cases ha : 1 < α
  · have hs : Summable (fun i : ℕ => 1 / Real.rpow (i : ℝ) α) :=
      Real.summable_one_div_nat_rpow.mpr ha
    let Cα : ℝ := ∑' i : ℕ, 1 / Real.rpow (i : ℝ) α
    let C : ℝ := Real.rpow 2 β * Cα
    have hCα : 0 ≤ Cα := by
      exact tsum_nonneg fun i => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCα
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hpartial : (∑ i ∈ Finset.Icc 1 (n / 2),
        1 / Real.rpow (i : ℝ) α) ≤ Cα := by
      exact hs.sum_le_tsum _ (fun i _ => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
    have hfn : 0 ≤ firstHalf α β n := by
      unfold firstHalf
      apply Finset.sum_nonneg
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hin : (i : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hi.2.trans (Nat.div_le_self n 2)
      exact one_div_nonneg.mpr (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by linarith) _))
    have hmain : firstHalf α β n ≤ C * (1 / Real.rpow (n : ℝ) β) := by
      calc
        firstHalf α β n ≤ (1 / Real.rpow ((n : ℝ) / 2) β) * Cα :=
          (hfirst_bound n hn).trans (mul_le_mul_of_nonneg_left hpartial
            (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)))
        _ = C * (1 / Real.rpow (n : ℝ) β) := by rw [hhalf_rewrite n (by omega)]; ring
    have hg₀ : 0 ≤ 1 / Real.rpow (n : ℝ) β +
        Real.rpow (n : ℝ) (1 - (α + β)) +
        Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
      exact add_nonneg (add_nonneg
        (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
    have hbase_le : 1 / Real.rpow (n : ℝ) β ≤
        1 / Real.rpow (n : ℝ) β + Real.rpow (n : ℝ) (1 - (α + β)) +
          Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
      have hfullnonneg : 0 ≤ Real.rpow (n : ℝ) (1 - (α + β)) :=
        Real.rpow_nonneg (by positivity) _
      have hhalfnonneg : 0 ≤ Real.rpow (n : ℝ) ((1 - (α + β)) / 2) :=
        Real.rpow_nonneg (by positivity) _
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hfn, Real.norm_eq_abs, abs_of_nonneg hg₀]
    exact hmain.trans (mul_le_mul_of_nonneg_left hbase_le hC)
  · have ha1 : α ≤ 1 := le_of_not_gt ha
    let q : ℝ := (1 + α + β) / 2
    have hq1 : 1 < q := by dsimp [q]; linarith
    have hqa : 0 ≤ q - α := by dsimp [q]; linarith
    have hs : Summable (fun i : ℕ => 1 / Real.rpow (i : ℝ) q) :=
      Real.summable_one_div_nat_rpow.mpr hq1
    let Cq : ℝ := ∑' i : ℕ, 1 / Real.rpow (i : ℝ) q
    let C : ℝ := Real.rpow 2 β * Cq
    have hCq : 0 ≤ Cq := by
      exact tsum_nonneg fun i => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCq
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hpartial : (∑ i ∈ Finset.Icc 1 (n / 2),
        1 / Real.rpow (i : ℝ) α) ≤ Real.rpow (n : ℝ) (q - α) * Cq := by
      calc
        (∑ i ∈ Finset.Icc 1 (n / 2), 1 / Real.rpow (i : ℝ) α) ≤
            ∑ i ∈ Finset.Icc 1 (n / 2),
              Real.rpow (n : ℝ) (q - α) * (1 / Real.rpow (i : ℝ) q) := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Finset.mem_Icc] at hi
          have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi.1
          have hin : (i : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hi.2.trans (Nat.div_le_self n 2)
          have hpow : Real.rpow (i : ℝ) (q - α) ≤
              Real.rpow (n : ℝ) (q - α) :=
            Real.rpow_le_rpow hipos.le hin hqa
          have hnonneg : 0 ≤ 1 / Real.rpow (i : ℝ) q :=
            one_div_nonneg.mpr (Real.rpow_nonneg hipos.le _)
          have hid : 1 / Real.rpow (i : ℝ) α =
              Real.rpow (i : ℝ) (q - α) * (1 / Real.rpow (i : ℝ) q) := by
            have hiα : Real.rpow (i : ℝ) α ≠ 0 := (Real.rpow_pos_of_pos hipos _).ne'
            have hiq : Real.rpow (i : ℝ) q ≠ 0 := (Real.rpow_pos_of_pos hipos _).ne'
            have hidiff : Real.rpow (i : ℝ) (q - α) ≠ 0 :=
              (Real.rpow_pos_of_pos hipos _).ne'
            have hadd : Real.rpow (i : ℝ) q = Real.rpow (i : ℝ) (q - α) *
                Real.rpow (i : ℝ) α := by
              simp only [Real.rpow_eq_pow]
              convert Real.rpow_add hipos (q - α) α using 1 <;> ring
            rw [hadd]
            field_simp [hidiff]
          rw [hid]
          exact mul_le_mul_of_nonneg_right hpow hnonneg
        _ = Real.rpow (n : ℝ) (q - α) *
            (∑ i ∈ Finset.Icc 1 (n / 2), 1 / Real.rpow (i : ℝ) q) := by
          rw [Finset.mul_sum]
        _ ≤ Real.rpow (n : ℝ) (q - α) * Cq := by
          apply mul_le_mul_of_nonneg_left
          · exact hs.sum_le_tsum _ (fun i _ => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
          · exact Real.rpow_nonneg hnpos.le _
    have hfn : 0 ≤ firstHalf α β n := by
      unfold firstHalf
      apply Finset.sum_nonneg
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hin : (i : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hi.2.trans (Nat.div_le_self n 2)
      exact one_div_nonneg.mpr (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by linarith) _))
    have hexp : q - α - β = (1 - (α + β)) / 2 := by dsimp [q]; ring
    have hmain : firstHalf α β n ≤ C *
        Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
      calc
        firstHalf α β n ≤ (1 / Real.rpow ((n : ℝ) / 2) β) *
            (Real.rpow (n : ℝ) (q - α) * Cq) :=
          (hfirst_bound n hn).trans (mul_le_mul_of_nonneg_left hpartial
            (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)))
        _ = C * Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
          rw [hhalf_rewrite n (by omega)]
          have hsub : Real.rpow (n : ℝ) (q - α) /
              Real.rpow (n : ℝ) β = Real.rpow (n : ℝ) (q - α - β) := by
            simp only [Real.rpow_eq_pow]
            exact (Real.rpow_sub hnpos (q - α) β).symm
          rw [← hexp, ← hsub]
          simp only [C]
          ring
    have hg₀ : 0 ≤ 1 / Real.rpow (n : ℝ) β +
        Real.rpow (n : ℝ) (1 - (α + β)) +
        Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
      exact add_nonneg (add_nonneg
        (one_div_nonneg.mpr (Real.rpow_nonneg hnpos.le _)) (Real.rpow_nonneg hnpos.le _))
        (Real.rpow_nonneg hnpos.le _)
    have hhalf_le : Real.rpow (n : ℝ) ((1 - (α + β)) / 2) ≤
        1 / Real.rpow (n : ℝ) β + Real.rpow (n : ℝ) (1 - (α + β)) +
          Real.rpow (n : ℝ) ((1 - (α + β)) / 2) := by
      exact le_add_of_nonneg_left (add_nonneg
        (one_div_nonneg.mpr (Real.rpow_nonneg hnpos.le _)) (Real.rpow_nonneg hnpos.le _))
    rw [Real.norm_eq_abs, abs_of_nonneg hfn, Real.norm_eq_abs, abs_of_nonneg hg₀]
    exact hmain.trans (mul_le_mul_of_nonneg_left hhalf_le hC)

private theorem secondHalf_le_swap_add (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ n : ℕ, 2 ≤ n →
      secondHalf α β n ≤ firstHalf β α n +
        Real.rpow 2 α * (1 / Real.rpow (n : ℝ) α) := by
  classical
  intro n hn
  let m : ℕ := n / 2
  let s : Finset ℕ := Finset.Icc (m + 1) n
  let t : Finset ℕ := Finset.Icc 1 (n - m)
  let f : ℕ → ℝ := fun j =>
    1 / (Real.rpow ((n - j + 1 : ℕ) : ℝ) α * Real.rpow (j : ℝ) β)
  let g : ℕ → ℝ := fun i =>
    1 / (Real.rpow (i : ℝ) α *
      Real.rpow ((n : ℝ) - (i : ℝ) + 1) β)
  have hreindex : (∑ i ∈ s, g i) = ∑ j ∈ t, f j := by
    apply Finset.sum_nbij' (fun i => n - i + 1) (fun j => n - j + 1)
    · intro i hi
      simp only [s, t, Finset.mem_Icc] at hi ⊢
      omega
    · intro j hj
      simp only [s, t, Finset.mem_Icc] at hj ⊢
      omega
    · intro i hi
      simp only [s, Finset.mem_Icc] at hi
      omega
    · intro j hj
      simp only [t, Finset.mem_Icc] at hj
      omega
    · intro i hi
      simp only [s, Finset.mem_Icc] at hi
      have hle : n - i + 1 ≤ n := by omega
      have hinv : n - (n - i + 1) + 1 = i := by omega
      have hcast : ((n - i + 1 : ℕ) : ℝ) =
          (n : ℝ) - (i : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hi.2]
      simp only [g, f]
      rw [hinv, hcast]
  have hsubset : t ⊆ Finset.Icc 1 (m + 1) := by
    intro j hj
    simp only [t, Finset.mem_Icc] at hj ⊢
    dsimp [m] at hj ⊢
    omega
  have hsum_subset : (∑ j ∈ t, f j) ≤ ∑ j ∈ Finset.Icc 1 (m + 1), f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hj hnot
    simp only [Finset.mem_Icc] at hj
    simp only [f]
    exact one_div_nonneg.mpr (mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _))
  have hset : Finset.Icc 1 (m + 1) =
      insert (m + 1) (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit : (∑ j ∈ Finset.Icc 1 (m + 1), f j) =
      (∑ j ∈ Finset.Icc 1 m, f j) + f (m + 1) := by
    rw [hset]
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.sum_insert hnot]
    ring
  have hfirst : (∑ j ∈ Finset.Icc 1 m, f j) = firstHalf β α n := by
    unfold firstHalf
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjn : j ≤ n := by
      exact hj.2.trans (Nat.div_le_self n 2)
    have hcast : ((n - j + 1 : ℕ) : ℝ) =
        (n : ℝ) - (j : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn]
    simp only [f, m]
    rw [hcast]
    ring
  have hm1le : m + 1 ≤ n := by
    dsimp [m]
    omega
  have hnmpos : 0 < n - m := by omega
  have hnat : n - (m + 1) + 1 = n - m := by omega
  have hone : 1 ≤ Real.rpow ((m + 1 : ℕ) : ℝ) β := by
    apply Real.one_le_rpow
    · exact_mod_cast (show 1 ≤ m + 1 by omega)
    · exact hβ.le
  have hleftpos : 0 < Real.rpow ((n - m : ℕ) : ℝ) α :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnmpos) _
  have hprod : Real.rpow ((n - m : ℕ) : ℝ) α ≤
      Real.rpow ((n - m : ℕ) : ℝ) α *
        Real.rpow ((m + 1 : ℕ) : ℝ) β := by
    calc
      Real.rpow ((n - m : ℕ) : ℝ) α =
          Real.rpow ((n - m : ℕ) : ℝ) α * 1 := by ring
      _ ≤ Real.rpow ((n - m : ℕ) : ℝ) α *
          Real.rpow ((m + 1 : ℕ) : ℝ) β :=
        mul_le_mul_of_nonneg_left hone hleftpos.le
  have hinv₁ : 1 / (Real.rpow ((n - m : ℕ) : ℝ) α *
      Real.rpow ((m + 1 : ℕ) : ℝ) β) ≤
      1 / Real.rpow ((n - m : ℕ) : ℝ) α := by
    exact one_div_le_one_div_of_le hleftpos hprod
  have hnle : n ≤ 2 * (n - m) := by
    dsimp [m]
    omega
  have hnler : (n : ℝ) ≤ 2 * ((n - m : ℕ) : ℝ) := by exact_mod_cast hnle
  have hhalfbase : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hhalfpos : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  have hpow : Real.rpow ((n : ℝ) / 2) α ≤
      Real.rpow ((n - m : ℕ) : ℝ) α :=
    Real.rpow_le_rpow hhalfpos.le hhalfbase hα.le
  have hinv₂ : 1 / Real.rpow ((n - m : ℕ) : ℝ) α ≤
      1 / Real.rpow ((n : ℝ) / 2) α := by
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hhalfpos _) hpow
  have hhalf_rewrite : 1 / Real.rpow ((n : ℝ) / 2) α =
      Real.rpow 2 α * (1 / Real.rpow (n : ℝ) α) := by
    have hn0 : Real.rpow (n : ℝ) α ≠ 0 :=
      (Real.rpow_pos_of_pos hnpos _).ne'
    have h20 : Real.rpow 2 α ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow hnpos.le (by norm_num) α]
    field_simp
  have hextra : f (m + 1) ≤
      Real.rpow 2 α * (1 / Real.rpow (n : ℝ) α) := by
    calc
      f (m + 1) = 1 / (Real.rpow ((n - m : ℕ) : ℝ) α *
          Real.rpow ((m + 1 : ℕ) : ℝ) β) := by
            simp only [f, hnat]
      _ ≤ 1 / Real.rpow ((n - m : ℕ) : ℝ) α := hinv₁
      _ ≤ 1 / Real.rpow ((n : ℝ) / 2) α := hinv₂
      _ = Real.rpow 2 α * (1 / Real.rpow (n : ℝ) α) := hhalf_rewrite
  calc
    secondHalf α β n = ∑ i ∈ s, g i := by rfl
    _ = ∑ j ∈ t, f j := hreindex
    _ ≤ ∑ j ∈ Finset.Icc 1 (m + 1), f j := hsum_subset
    _ = (∑ j ∈ Finset.Icc 1 m, f j) + f (m + 1) := hsplit
    _ = firstHalf β α n + f (m + 1) := by rw [hfirst]
    _ ≤ firstHalf β α n +
        Real.rpow 2 α * (1 / Real.rpow (n : ℝ) α) :=
      add_le_add le_rfl hextra

theorem gap14 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    Asymptotics.IsBigO atTop (secondHalf α β)
      (fun n : ℕ =>
        1 / Real.rpow n α + Real.rpow n (1 - (α + β)) +
          Real.rpow n ((1 - (α + β)) / 2)) := by
  let G : ℕ → ℝ := fun n =>
    1 / Real.rpow (n : ℝ) α + Real.rpow (n : ℝ) (1 - (α + β)) +
      Real.rpow (n : ℝ) ((1 - (α + β)) / 2)
  have hfirst : Asymptotics.IsBigO atTop (firstHalf β α) G := by
    simpa only [G, add_comm β α] using gap13 β α hβ hα (by linarith)
  rw [Asymptotics.isBigO_iff] at hfirst ⊢
  rcases hfirst with ⟨c, hc⟩
  refine ⟨|c| + Real.rpow 2 α, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (2 : ℕ)] with n hc hn
  let A : ℝ := 1 / Real.rpow (n : ℝ) α
  let E : ℝ := Real.rpow (n : ℝ) (1 - (α + β))
  let H : ℝ := Real.rpow (n : ℝ) ((1 - (α + β)) / 2)
  have hA : 0 ≤ A := one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
  have hE : 0 ≤ E := Real.rpow_nonneg (by positivity) _
  have hH : 0 ≤ H := Real.rpow_nonneg (by positivity) _
  have hG : 0 ≤ A + E + H := by positivity
  have hF : 0 ≤ firstHalf β α n := by
    unfold firstHalf
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hin : (i : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hi.2.trans (Nat.div_le_self n 2)
    exact one_div_nonneg.mpr (mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by linarith) _))
  have hS : 0 ≤ secondHalf α β n := by
    unfold secondHalf
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    exact one_div_nonneg.mpr (mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by linarith) _))
  have hc' : firstHalf β α n ≤ |c| * (A + E + H) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hF] at hc
    rw [Real.norm_eq_abs, abs_of_nonneg hG] at hc
    calc
      firstHalf β α n ≤ c * (A + E + H) := by
        simpa only [G, A, E, H] using hc
      _ ≤ |c| * (A + E + H) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) hG
  have hAle : A ≤ A + E + H := by linarith
  have hbound := secondHalf_le_swap_add α β hα hβ n hn
  rw [Real.norm_eq_abs, abs_of_nonneg hS, Real.norm_eq_abs, abs_of_nonneg hG]
  calc
    secondHalf α β n ≤ firstHalf β α n + Real.rpow 2 α * A := by
      simpa only [A] using hbound
    _ ≤ |c| * (A + E + H) + Real.rpow 2 α * (A + E + H) :=
      add_le_add hc' (mul_le_mul_of_nonneg_left hAle (Real.rpow_nonneg (by norm_num) _))
    _ = (|c| + Real.rpow 2 α) * (A + E + H) := by ring

theorem gap15 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    Asymptotics.IsBigO atTop (amplitude α β)
      (fun n : ℕ =>
        1 / Real.rpow n α + 1 / Real.rpow n β +
          Real.rpow n (1 - (α + β)) +
          Real.rpow n ((1 - (α + β)) / 2)) := by
  have hfirst := gap13 α β hα hβ hab
  have hsecond := gap14 α β hα hβ hab
  rw [Asymptotics.isBigO_iff] at hfirst hsecond ⊢
  rcases hfirst with ⟨c₁, hc₁⟩
  rcases hsecond with ⟨c₂, hc₂⟩
  refine ⟨|c₁| + |c₂|, ?_⟩
  filter_upwards [hc₁, hc₂, eventually_ge_atTop (1 : ℕ)] with n hc₁ hc₂ hn
  have hn₀ : (0 : ℝ) ≤ (n : ℝ) := by positivity
  let A : ℝ := 1 / Real.rpow (n : ℝ) α
  let B : ℝ := 1 / Real.rpow (n : ℝ) β
  let E : ℝ := Real.rpow (n : ℝ) (1 - (α + β))
  let H : ℝ := Real.rpow (n : ℝ) ((1 - (α + β)) / 2)
  have hA : 0 ≤ A := one_div_nonneg.mpr (Real.rpow_nonneg hn₀ _)
  have hB : 0 ≤ B := one_div_nonneg.mpr (Real.rpow_nonneg hn₀ _)
  have hE : 0 ≤ E := Real.rpow_nonneg hn₀ _
  have hH : 0 ≤ H := Real.rpow_nonneg hn₀ _
  have hF : 0 ≤ firstHalf α β n := by
    unfold firstHalf
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hin : (i : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hi.2.trans (Nat.div_le_self n 2)
    exact one_div_nonneg.mpr (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by linarith) _))
  have hS : 0 ≤ secondHalf α β n := by
    unfold secondHalf
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.2
    exact one_div_nonneg.mpr (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by linarith) _))
  have hc₁' : firstHalf α β n ≤ |c₁| * (A + B + E + H) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hF] at hc₁
    have hG₁ : 0 ≤ B + E + H := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hG₁] at hc₁
    calc
      firstHalf α β n ≤ c₁ * (B + E + H) := by simpa [A, B, E, H] using hc₁
      _ ≤ |c₁| * (B + E + H) :=
        mul_le_mul_of_nonneg_right (le_abs_self c₁) hG₁
      _ ≤ |c₁| * (A + B + E + H) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg c₁)
        linarith
  have hc₂' : secondHalf α β n ≤ |c₂| * (A + B + E + H) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hS] at hc₂
    have hG₂ : 0 ≤ A + E + H := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hG₂] at hc₂
    calc
      secondHalf α β n ≤ c₂ * (A + E + H) := by simpa [A, B, E, H] using hc₂
      _ ≤ |c₂| * (A + E + H) :=
        mul_le_mul_of_nonneg_right (le_abs_self c₂) hG₂
      _ ≤ |c₂| * (A + B + E + H) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg c₂)
        linarith
  have hamp : amplitude α β n = firstHalf α β n + secondHalf α β n := gap12 α β n
  have hG : 0 ≤ A + B + E + H := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hamp]; positivity), Real.norm_eq_abs,
    abs_of_nonneg hG, hamp]
  simpa [A, B, E, H, add_mul] using add_le_add hc₁' hc₂'

theorem gap16 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    Tendsto (amplitude α β) atTop (nhds 0) := by
  have hinv : ∀ (γ : ℝ), 0 < γ →
      Tendsto (fun n : ℕ => 1 / Real.rpow (n : ℝ) γ) atTop (nhds 0) := by
    intro γ hγ
    have h := (tendsto_rpow_neg_atTop hγ).comp
      (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
    convert h using 1
    ext n
    simp only [Function.comp_apply, one_div]
    rw [Real.rpow_eq_pow, Real.rpow_neg (by positivity)]
  let p : ℝ := α + β - 1
  have hp : 0 < p := by dsimp [p]; linarith
  have hfull : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 - (α + β)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hp).comp
      (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
    convert h using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_eq_pow]
    congr 1
    dsimp [p]
    ring
  have hhalf : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) ((1 - (α + β)) / 2))
      atTop (nhds 0) := by
    have hp2 : 0 < p / 2 := by positivity
    have h := (tendsto_rpow_neg_atTop hp2).comp
      (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
    convert h using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_eq_pow]
    congr 1
    dsimp [p]
    ring
  let G : ℕ → ℝ := fun n =>
    1 / Real.rpow n α + 1 / Real.rpow n β +
      Real.rpow n (1 - (α + β)) + Real.rpow n ((1 - (α + β)) / 2)
  have hG : Tendsto G atTop (nhds 0) := by
    dsimp [G]
    convert (((hinv α hα).add (hinv β hβ)).add hfull).add hhalf using 1 <;> ring
  have hO := gap15 α β hα hβ hab
  rw [Asymptotics.isBigO_iff] at hO
  rcases hO with ⟨c, hc⟩
  apply squeeze_zero_norm' hc
  simpa [G] using hG.norm.const_mul c

theorem gap17 (α β : ℝ) :
    ∀ n : ℕ,
      delta α β n =
        ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n,
            if n + 1 < i + j then aTerm α i * bTerm β j else 0 := by
  classical
  intro n
  let s : Finset ℕ := Finset.Icc 1 n
  let square : Finset (ℕ × ℕ) := s.product s
  let low : Finset (ℕ × ℕ) :=
    square.filter (fun p => p.1 + p.2 ≤ n + 1)
  let source : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun k => Finset.Icc 1 k)
  let term : ℕ × ℕ → ℝ := fun p => aTerm α p.1 * bTerm β p.2
  have hprod : partialA α n * partialB β n = ∑ p ∈ square, term p := by
    calc
      partialA α n * partialB β n =
          ∑ i ∈ s, ∑ j ∈ s, aTerm α i * bTerm β j := by
            simp only [partialA, partialB, s]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ p ∈ square, term p := by
        simpa only [square, term] using
          (Finset.sum_product' s s (fun i j => aTerm α i * bTerm β j)).symm
  have hcauchy : cauchyPartial α β n = ∑ p ∈ low, term p := by
    calc
      cauchyPartial α β n =
          ∑ x ∈ source,
            aTerm α x.2 * bTerm β (x.1 - x.2 + 1) := by
              simp only [cauchyPartial, coefficient, source]
              rw [Finset.sum_sigma']
      _ = ∑ p ∈ low, term p := by
        apply Finset.sum_bij
          (fun x _ => (x.2, x.1 - x.2 + 1))
        · rintro ⟨k, i⟩ hx
          have hx' : k ∈ Finset.Icc 1 n ∧ i ∈ Finset.Icc 1 k := by
            simpa only [source, Finset.mem_sigma] using hx
          simp only [Finset.mem_Icc] at hx'
          rcases hx' with ⟨⟨hk1, hkn⟩, hi1, hik⟩
          have hj1 : 1 ≤ k - i + 1 := by omega
          have hjn : k - i + 1 ≤ n := by omega
          have hsum : i + (k - i + 1) ≤ n + 1 := by omega
          have hmem : (i, k - i + 1) ∈ low := by
            apply Finset.mem_filter.mpr
            constructor
            · apply Finset.mem_product.mpr
              exact ⟨Finset.mem_Icc.mpr ⟨hi1, hik.trans hkn⟩,
                Finset.mem_Icc.mpr ⟨hj1, hjn⟩⟩
            · exact hsum
          simpa only using hmem
        · rintro ⟨k₁, i₁⟩ h₁ ⟨k₂, i₂⟩ h₂ heq
          change (i₁, k₁ - i₁ + 1) = (i₂, k₂ - i₂ + 1) at heq
          have hi : i₁ = i₂ := congrArg Prod.fst heq
          have hj : k₁ - i₁ + 1 = k₂ - i₂ + 1 := congrArg Prod.snd heq
          simp only [source, Finset.mem_sigma, Finset.mem_Icc] at h₁ h₂
          have hk : k₁ = k₂ := by omega
          subst k₂
          subst i₂
          rfl
        · rintro ⟨i, j⟩ hp
          have hp' := Finset.mem_filter.mp hp
          have hsquare := Finset.mem_product.mp hp'.1
          have hi := Finset.mem_Icc.mp hsquare.1
          have hj := Finset.mem_Icc.mp hsquare.2
          rcases hi with ⟨hi1, hin⟩
          rcases hj with ⟨hj1, hjn⟩
          have hij := hp'.2
          refine ⟨⟨i + j - 1, i⟩, ?_, ?_⟩
          · simp only [source, Finset.mem_sigma, Finset.mem_Icc]
            omega
          · simp only
            congr <;> omega
        · rintro ⟨k, i⟩ hx
          rfl
  have hlow :
      (∑ p ∈ square,
        if p.1 + p.2 ≤ n + 1 then term p else 0) =
        ∑ p ∈ low, term p := by
    simp only [low, Finset.sum_filter]
  have hsplit :
      (∑ p ∈ square, term p) =
        (∑ p ∈ low, term p) +
          ∑ p ∈ square,
            if n + 1 < p.1 + p.2 then term p else 0 := by
    calc
      (∑ p ∈ square, term p) =
          ∑ p ∈ square,
            ((if p.1 + p.2 ≤ n + 1 then term p else 0) +
              if n + 1 < p.1 + p.2 then term p else 0) := by
                apply Finset.sum_congr rfl
                intro p hp
                by_cases h : p.1 + p.2 ≤ n + 1
                · simp [h, not_lt_of_ge h]
                · have h' : n + 1 < p.1 + p.2 := Nat.lt_of_not_ge h
                  simp [h, h']
      _ = (∑ p ∈ square,
            if p.1 + p.2 ≤ n + 1 then term p else 0) +
          ∑ p ∈ square,
            if n + 1 < p.1 + p.2 then term p else 0 := by
              rw [Finset.sum_add_distrib]
      _ = (∑ p ∈ low, term p) +
          ∑ p ∈ square,
            if n + 1 < p.1 + p.2 then term p else 0 := by rw [hlow]
  calc
    delta α β n =
        (∑ p ∈ square, term p) - (∑ p ∈ low, term p) := by
          simp only [delta, hprod, hcauchy]
    _ = ∑ p ∈ square,
          if n + 1 < p.1 + p.2 then term p else 0 := by
            rw [hsplit]
            ring
    _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n,
            if n + 1 < i + j then aTerm α i * bTerm β j else 0 := by
              simpa only [square, s, term] using
                Finset.sum_product s s
                  (fun p => if n + 1 < p.1 + p.2 then term p else 0)

private theorem abs_sum_range_alternating_le
    (u : ℕ → ℝ) (hu : Antitone u) (hu0 : ∀ r, 0 ≤ u r) (k : ℕ) :
    |∑ r ∈ Finset.range k, (-1 : ℝ) ^ r * u r| ≤ u 0 := by
  cases k with
  | zero => simp [hu0 0]
  | succ k =>
      let v : ℕ → ℝ := fun r => if r < k + 1 then u r else 0
      have hv : Antitone v := by
        intro i j hij
        by_cases hj : j < k + 1
        · have hi : i < k + 1 := lt_of_le_of_lt hij hj
          simpa only [v, if_pos hi, if_pos hj] using hu hij
        · by_cases hi : i < k + 1
          · simpa only [v, if_pos hi, if_neg hj] using hu0 i
          · simp only [v, if_neg hi, if_neg hj]
            exact le_rfl
      have hvs : Summable v := by
        apply summable_of_ne_finset_zero (s := Finset.range (k + 1))
        intro r hr
        have hr' : ¬ r < k + 1 := by simpa only [Finset.mem_range] using hr
        simp only [v, if_neg hr']
      have hb := alternating_series_error_bound v hv hvs 0
      have htsum :
          (∑' r : ℕ, (-1 : ℝ) ^ r * v r) =
            ∑ r ∈ Finset.range (k + 1), (-1 : ℝ) ^ r * u r := by
        rw [tsum_eq_sum (s := Finset.range (k + 1))]
        · apply Finset.sum_congr rfl
          intro r hr
          have hr' : r < k + 1 := Finset.mem_range.mp hr
          simp only [v, if_pos hr']
        · intro r hr
          have hr' : ¬ r < k + 1 := by simpa only [Finset.mem_range] using hr
          simp only [v, if_neg hr', mul_zero]
      rw [htsum] at hb
      simpa only [Finset.sum_range_zero, sub_zero, v, Nat.zero_lt_succ, if_pos] using hb

private theorem abs_sum_Icc_bTerm_le (β : ℝ) (hβ : 0 < β)
    (p q : ℕ) (hp : 1 ≤ p) :
    |∑ j ∈ Finset.Icc p q, bTerm β j| ≤ 1 / Real.rpow p β := by
  by_cases hpq : p ≤ q
  · let u : ℕ → ℝ := fun r => 1 / Real.rpow (p + r : ℕ) β
    have hu : Antitone u := by
      intro i j hij
      apply one_div_le_one_div_of_le
      · exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < p + i by omega)) _
      · apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast Nat.add_le_add_left hij p
        · exact hβ.le
    have hu0 : ∀ r, 0 ≤ u r := by
      intro r
      exact one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hb := abs_sum_range_alternating_le u hu hu0 (q - p + 1)
    have hreindex :
        (∑ j ∈ Finset.Icc p q, bTerm β j) =
          ∑ r ∈ Finset.range (q - p + 1), bTerm β (p + r) := by
      symm
      apply Finset.sum_bij (fun r _ => p + r)
      · intro r hr
        simp only [Finset.mem_range] at hr
        simp only [Finset.mem_Icc]
        omega
      · intro r₁ h₁ r₂ h₂ heq
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        refine ⟨j - p, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro r hr
        rfl
    have hfactor :
        (∑ r ∈ Finset.range (q - p + 1), bTerm β (p + r)) =
          (-1 : ℝ) ^ (p - 1) *
            ∑ r ∈ Finset.range (q - p + 1), (-1 : ℝ) ^ r * u r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hexp : p + r - 1 = (p - 1) + r := by omega
      simp only [bTerm, u, hexp, pow_add]
      ring
    rw [hreindex, hfactor, abs_mul]
    simpa only [abs_pow, abs_neg, abs_one, one_pow, one_mul, u, Nat.add_zero] using hb
  · have hqp : q < p := Nat.lt_of_not_ge hpq
    rw [Finset.Icc_eq_empty_of_lt hqp]
    simp only [Finset.sum_empty, abs_zero]
    exact one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)

theorem gap18 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ∃ N : ℕ, ∀ n ≥ N,
      |delta α β n| ≤ amplitude α β (n + 1) := by
  refine ⟨1, ?_⟩
  intro n hn
  rw [gap17 α β n]
  calc
    |∑ i ∈ Finset.Icc 1 n,
        ∑ j ∈ Finset.Icc 1 n,
          if n + 1 < i + j then aTerm α i * bTerm β j else 0| ≤
        ∑ i ∈ Finset.Icc 1 n,
          |∑ j ∈ Finset.Icc 1 n,
            if n + 1 < i + j then aTerm α i * bTerm β j else 0| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 n,
        1 / (Real.rpow (i : ℝ) α *
          Real.rpow ((n - i + 2 : ℕ) : ℝ) β) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_Icc] at hi
      let p : ℕ := n - i + 2
      have hp : 1 ≤ p := by dsimp [p]; omega
      have hrow :
          (∑ j ∈ Finset.Icc 1 n,
              if n + 1 < i + j then aTerm α i * bTerm β j else 0) =
            aTerm α i * ∑ j ∈ Finset.Icc p n, bTerm β j := by
        calc
          (∑ j ∈ Finset.Icc 1 n,
              if n + 1 < i + j then aTerm α i * bTerm β j else 0) =
              ∑ j ∈ (Finset.Icc 1 n).filter (fun j => p ≤ j),
                aTerm α i * bTerm β j := by
                  rw [Finset.sum_filter]
                  apply Finset.sum_congr rfl
                  intro j hj
                  by_cases hcond : p ≤ j
                  · have hlt : n + 1 < i + j := by dsimp [p] at hcond; omega
                    simp [hcond, hlt]
                  · have hnlt : ¬ n + 1 < i + j := by dsimp [p] at hcond; omega
                    simp [hcond, hnlt]
          _ = ∑ j ∈ Finset.Icc p n, aTerm α i * bTerm β j := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_Icc]
            omega
          _ = aTerm α i * ∑ j ∈ Finset.Icc p n, bTerm β j := by
            rw [Finset.mul_sum]
      have htail := abs_sum_Icc_bTerm_le β hβ p n hp
      have haabs : |aTerm α i| = 1 / Real.rpow (i : ℝ) α := by
        simp only [aTerm, abs_div, abs_pow, abs_neg, abs_one, one_pow]
        have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi.1
        have hpowpos : 0 < Real.rpow (i : ℝ) α :=
          Real.rpow_pos_of_pos hipos _
        exact congrArg (fun x : ℝ => 1 / x) (abs_of_pos hpowpos)
      rw [hrow, abs_mul, haabs]
      calc
        1 / Real.rpow (i : ℝ) α * |∑ j ∈ Finset.Icc p n, bTerm β j| ≤
            1 / Real.rpow (i : ℝ) α * (1 / Real.rpow (p : ℝ) β) :=
          mul_le_mul_of_nonneg_left htail
            (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
        _ = 1 / (Real.rpow (i : ℝ) α *
            Real.rpow ((n - i + 2 : ℕ) : ℝ) β) := by
          simp only [p]
          ring
    _ ≤ amplitude α β (n + 1) := by
      unfold amplitude
      calc
        (∑ i ∈ Finset.Icc 1 n,
            1 / (Real.rpow (i : ℝ) α *
              Real.rpow ((n - i + 2 : ℕ) : ℝ) β)) =
            ∑ i ∈ Finset.Icc 1 n,
              1 / (Real.rpow (i : ℝ) α *
                Real.rpow (((n + 1 : ℕ) : ℝ) - (i : ℝ) + 1) β) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  simp only [Finset.mem_Icc] at hi
                  have hin : i ≤ n := hi.2
                  congr 3
                  norm_num
                  rw [Nat.cast_sub hin]
                  ring
        _ ≤ ∑ i ∈ Finset.Icc 1 (n + 1),
              1 / (Real.rpow (i : ℝ) α *
                Real.rpow (((n + 1 : ℕ) : ℝ) - (i : ℝ) + 1) β) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            omega
          · intro i hi hnot
            simp only [Finset.mem_Icc] at hi
            have hin : (i : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hi.2
            exact one_div_nonneg.mpr (mul_nonneg
              (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg (by linarith) _))

theorem gap19 (α β : ℝ) :
    ∀ n : ℕ,
      (∑ i ∈ Finset.Icc 1 (n + 1),
        1 / (Real.rpow i α * Real.rpow (n + 2 - i) β)) =
          amplitude α β (n + 1) := by
  intro n
  unfold amplitude
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Icc] at hi
  congr 3
  norm_num
  ring

theorem gap20 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ∃ N : ℕ, ∀ n ≥ N,
      |delta α β n| ≤ amplitude α β (n + 1) := by
  exact gap18 α β hα hβ hab

theorem gap21 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    Tendsto (delta α β) atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := gap18 α β hα hβ hab
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [Real.norm_eq_abs] using hN n hn
  · exact (tendsto_add_atTop_iff_nat 1).2 (gap16 α β hα hβ hab)

theorem gap22 (α β : ℝ) :
    ∀ n : ℕ,
      cauchyPartial α β n =
        partialA α n * partialB β n - delta α β n := by
  intro n
  unfold delta
  ring

private theorem sum_range_shift_eq_Icc (f : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range n, f (k + 1)) =
        ∑ i ∈ Finset.Icc 1 n, f i := by
  intro n
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k₁ h₁ k₂ h₂ heq
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    refine ⟨i - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

private theorem aTerm_seriesConverges (α : ℝ) (hα : 0 < α) :
    ProofGap.SeriesConverges (fun n : ℕ => aTerm α (n + 1)) := by
  have hanti : Antitone (fun n : ℕ => 1 / Real.rpow (n + 1) α) := by
    intro n m hnm
    apply one_div_le_one_div_of_le
    · exact Real.rpow_pos_of_pos (by positivity) _
    · apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast Nat.add_le_add_right hnm 1
      · exact hα.le
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1 / Real.rpow (n + 1) α) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop hα |>.comp hbase
    convert h using 1
    ext n
    simp only [Function.comp_apply, one_div]
    rw [Real.rpow_eq_pow]
    rw [Real.rpow_neg (by positivity)]
  rcases hanti.tendsto_alternating_series_of_tendsto_zero hzero with ⟨l, hl⟩
  unfold ProofGap.SeriesConverges
  refine ⟨l, ?_⟩
  simpa [HasSum, aTerm, div_eq_mul_inv] using hl

theorem gap23 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ∃ A B : ℝ,
      Tendsto (partialA α) atTop (nhds A) ∧
      Tendsto (partialB β) atTop (nhds B) ∧
      Tendsto
        (fun n : ℕ => partialA α n * partialB β n - delta α β n)
        atTop (nhds (A * B)) := by
  rcases aTerm_seriesConverges α hα with ⟨A, hA⟩
  have hbseries : ProofGap.SeriesConverges
      (fun n : ℕ => bTerm β (n + 1)) := by
    simpa only [aTerm, bTerm] using aTerm_seriesConverges β hβ
  rcases hbseries with ⟨B, hB⟩
  have hArange : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, aTerm α (k + 1))
      atTop (nhds A) := by
    simpa [HasSum] using hA
  have hBrange : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, bTerm β (k + 1))
      atTop (nhds B) := by
    simpa [HasSum] using hB
  have hApartial : Tendsto (partialA α) atTop (nhds A) := by
    apply hArange.congr'
    filter_upwards with n
    simpa only [partialA] using sum_range_shift_eq_Icc (aTerm α) n
  have hBpartial : Tendsto (partialB β) atTop (nhds B) := by
    apply hBrange.congr'
    filter_upwards with n
    simpa only [partialB] using sum_range_shift_eq_Icc (bTerm β) n
  refine ⟨A, B, hApartial, hBpartial, ?_⟩
  have hfinal := (hApartial.mul hBpartial).sub (gap21 α β hα hβ hab)
  convert hfinal using 1 <;> ring

theorem gap24 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ∃ A B : ℝ,
      Tendsto (cauchyPartial α β) atTop (nhds (A * B)) := by
  rcases gap23 α β hα hβ hab with ⟨A, B, hA, hB, hconv⟩
  refine ⟨A, B, ?_⟩
  apply hconv.congr'
  filter_upwards with n
  exact (gap22 α β n).symm

theorem gap25 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ProofGap.SeriesConverges (fun n : ℕ => aTerm α (n + 1)) := by
  have hanti : Antitone (fun n : ℕ => 1 / Real.rpow (n + 1) α) := by
    intro n m hnm
    apply one_div_le_one_div_of_le
    · exact Real.rpow_pos_of_pos (by positivity) _
    · apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast Nat.add_le_add_right hnm 1
      · exact hα.le
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1 / Real.rpow (n + 1) α) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop hα |>.comp hbase
    convert h using 1
    ext n
    simp only [Function.comp_apply, one_div]
    rw [Real.rpow_eq_pow]
    rw [Real.rpow_neg (by positivity)]
  rcases hanti.tendsto_alternating_series_of_tendsto_zero hzero with ⟨l, hl⟩
  unfold ProofGap.SeriesConverges
  refine ⟨l, ?_⟩
  simpa [HasSum, aTerm, div_eq_mul_inv] using hl

theorem gap26 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ProofGap.SeriesConverges (fun n : ℕ => bTerm β (n + 1)) := by
  exact gap25 β α hβ hα (by linarith)

theorem gap27 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hab : 1 < α + β) :
    ProofGap.SeriesConverges (fun n : ℕ => coefficient α β (n + 1)) := by
  rcases gap24 α β hα hβ hab with ⟨A, B, hconv⟩
  have hrange : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, coefficient α β (k + 1))
      atTop (nhds (A * B)) := by
    apply hconv.congr'
    filter_upwards with n
    simpa only [cauchyPartial] using
      (sum_range_shift_eq_Icc (coefficient α β) n).symm
  unfold ProofGap.SeriesConverges
  refine ⟨A * B, ?_⟩
  simpa [HasSum] using hrange

theorem gap28 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (1 < α + β →
      ProofGap.SeriesConverges (fun n : ℕ => coefficient α β (n + 1))) ∧
    (α + β ≤ 1 →
      ¬ ProofGap.SeriesConverges (fun n : ℕ => coefficient α β (n + 1))) := by
  exact ⟨gap27 α β hα hβ, gap11 α β hα hβ⟩

end

end ProofGap.Exercise2714
