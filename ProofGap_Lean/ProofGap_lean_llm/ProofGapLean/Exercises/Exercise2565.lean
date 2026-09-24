import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2565

noncomputable section

def arithmeticTerm (a₁ d : ℝ) (n : ℕ) : ℝ :=
  a₁ + ((n : ℝ) - 1) * d

def reciprocalTerm (a₁ d : ℝ) (n : ℕ) : ℝ :=
  1 / arithmeticTerm a₁ d n

def comparisonTerm (d : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * d)

def TailNotSummable (u : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ¬ Summable (fun k : ℕ => u (k + n₀))

private theorem add_fixed_right_injective (n : ℕ) :
    Function.Injective (fun k : ℕ => k + n) := by
  intro x y hxy
  exact Nat.add_right_cancel hxy

theorem gap1
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n) :
    ∀ n, a n = a₁ + ((n : ℝ) - 1) * d := by
  intro n
  simpa [arithmeticTerm] using ha n

theorem gap2
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      |a₁| < ((n₀ : ℝ) - 1) * d := by
  intro hd
  obtain ⟨n, hn⟩ := exists_nat_gt (|a₁| / d)
  have hn' : |a₁| < (n : ℝ) * d := (div_lt_iff₀ hd).mp hn
  refine ⟨n + 2, by omega, ?_⟩
  norm_num [Nat.cast_add]
  nlinarith

theorem gap3
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hthreshold : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      |a₁| < ((n₀ : ℝ) - 1) * d) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      arithmeticTerm a₁ d n < 2 * ((n : ℝ) - 1) * d := by
  intro hd
  obtain ⟨n₀, hn₀, hthreshold₀⟩ := hthreshold hd
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn
  have hcast : (n₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hmono : 0 ≤ ((n : ℝ) - (n₀ : ℝ)) * d :=
    mul_nonneg (sub_nonneg.mpr hcast) hd.le
  have ha_le : a₁ ≤ |a₁| := le_abs_self a₁
  simp only [arithmeticTerm]
  nlinarith

theorem gap4
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hthreshold : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      |a₁| < ((n₀ : ℝ) - 1) * d)
    (hbound : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      arithmeticTerm a₁ d n < 2 * ((n : ℝ) - 1) * d) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      reciprocalTerm a₁ d n >
        1 / (2 * ((n : ℝ) - 1) * d) := by
  intro hd
  obtain ⟨nt, hnt2, ht⟩ := hthreshold hd
  obtain ⟨nb, hnb2, hb⟩ := hbound hd
  refine ⟨max nt nb, hnt2.trans (Nat.le_max_left nt nb), ?_⟩
  intro n hn
  have hntn : nt ≤ n := (Nat.le_max_left nt nb).trans hn
  have hnbn : nb ≤ n := (Nat.le_max_right nt nb).trans hn
  have hcast : (nt : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hntn
  have hmono : 0 ≤ ((n : ℝ) - (nt : ℝ)) * d :=
    mul_nonneg (sub_nonneg.mpr hcast) hd.le
  have harithpos : 0 < arithmeticTerm a₁ d n := by
    rw [arithmeticTerm]
    nlinarith [neg_abs_le a₁]
  have hupper := hb n hnbn
  simpa [reciprocalTerm] using
    (one_div_lt_one_div_of_lt harithpos hupper)

theorem gap5
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hreciprocal : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      reciprocalTerm a₁ d n >
        1 / (2 * ((n : ℝ) - 1) * d)) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      1 / (2 * ((n : ℝ) - 1) * d) > comparisonTerm d n := by
  intro hd
  refine ⟨2, le_rfl, ?_⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hden : 0 < 2 * ((n : ℝ) - 1) * d := by
    have : 0 < (n : ℝ) - 1 := by nlinarith
    exact mul_pos (mul_pos (by norm_num) this) hd
  have hlt : 2 * ((n : ℝ) - 1) * d < 2 * (n : ℝ) * d := by
    nlinarith
  simpa [comparisonTerm] using
    (one_div_lt_one_div_of_lt hden hlt)

theorem gap6
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hcompare : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      1 / (2 * ((n : ℝ) - 1) * d) > comparisonTerm d n) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      comparisonTerm d n > 0 := by
  intro hd
  refine ⟨2, le_rfl, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hden : 0 < 2 * (n : ℝ) * d :=
    mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hnpos)) hd
  simpa [comparisonTerm] using (one_div_pos.mpr hden)

theorem gap7
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hreciprocal : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      reciprocalTerm a₁ d n >
        1 / (2 * ((n : ℝ) - 1) * d))
    (hcompare : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      1 / (2 * ((n : ℝ) - 1) * d) > comparisonTerm d n)
    (hpositive : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      comparisonTerm d n > 0) :
    d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      reciprocalTerm a₁ d n > 0 := by
  intro hd
  obtain ⟨nr, hnr2, hr⟩ := hreciprocal hd
  obtain ⟨nc, hnc2, hc⟩ := hcompare hd
  obtain ⟨np, hnp2, hp⟩ := hpositive hd
  let N := max nr (max nc np)
  have hnrN : nr ≤ N := Nat.le_max_left nr (max nc np)
  have hncN : nc ≤ N :=
    (Nat.le_max_left nc np).trans (Nat.le_max_right nr (max nc np))
  have hnpN : np ≤ N :=
    (Nat.le_max_right nc np).trans (Nat.le_max_right nr (max nc np))
  refine ⟨N, hnr2.trans hnrN, ?_⟩
  intro n hn
  have hnrn : nr ≤ n := hnrN.trans hn
  have hncn : nc ≤ n := hncN.trans hn
  have hnpn : np ≤ n := hnpN.trans hn
  linarith [hr n hnrn, hc n hncn, hp n hnpn]

theorem gap8
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n) :
    d > 0 → ∀ n₀ : ℕ, TailNotSummable (comparisonTerm d) n₀ := by
  intro hd n₀
  unfold TailNotSummable
  intro hs
  have hscaled :
      Summable (fun k : ℕ => (2 * d) * comparisonTerm d (k + n₀)) :=
    hs.mul_left (2 * d)
  have hh : Summable (fun k : ℕ => 1 / (((k + n₀ : ℕ) : ℝ))) := by
    convert hscaled using 1
    funext k
    by_cases hk : k + n₀ = 0
    · simp [hk, comparisonTerm]
    · have hkR : (((k + n₀ : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk
      simp only [comparisonTerm]
      field_simp [hd.ne', hkR] <;> ring
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff n₀).mp hh
  let f : ℕ → ℝ := fun k => 1 / (((k + 1 : ℕ) : ℝ))
  have hf : Summable f := by
    change Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)))
    exact (summable_nat_add_iff 1).mpr hall
  let S : ℕ → ℝ := fun n => (Finset.range n).sum f
  let L : ℝ := tsum f
  have ht : Tendsto S atTop (nhds L) := by
    simpa [S, L] using hf.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp ht) (1 / 8) (by norm_num)
  let m : ℕ := max N 1
  have hmN : N ≤ m := by
    dsimp [m]
    exact Nat.le_max_left N 1
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hnear_m : dist (S m) L < 1 / 8 := hN m hmN
  have hNmm : N ≤ m + m := by omega
  have hnear_mm : dist (S (m + m)) L < 1 / 8 :=
    hN (m + m) hNmm
  have hdist : dist (S (m + m)) (S m) < 1 / 4 := by
    calc
      dist (S (m + m)) (S m) ≤
          dist (S (m + m)) L + dist L (S m) :=
        dist_triangle (S (m + m)) L (S m)
      _ = dist (S (m + m)) L + dist (S m) L := by
        rw [dist_comm L (S m)]
      _ < 1 / 8 + 1 / 8 := add_lt_add hnear_mm hnear_m
      _ = 1 / 4 := by norm_num
  have hsum_eq :
      S (m + m) =
        S m + (Finset.range m).sum (fun k => f (m + k)) := by
    simpa [S] using (Finset.sum_range_add f m m)
  have hterm : ∀ k ∈ Finset.range m,
      1 / (2 * (m : ℝ)) ≤ f (m + k) := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hnat : m + k + 1 ≤ 2 * m := by omega
    have hpos : 0 < (((m + k + 1 : ℕ) : ℝ)) :=
      Nat.cast_pos.mpr (by omega)
    have hcast :
        (((m + k + 1 : ℕ) : ℝ)) ≤ (((2 * m : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hnat
    have hle :
        (((m + k + 1 : ℕ) : ℝ)) ≤ 2 * (m : ℝ) := by
      simpa using hcast
    change 1 / (2 * (m : ℝ)) ≤
      1 / (((m + k + 1 : ℕ) : ℝ))
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (one_div_lt_one_div_of_lt hpos hlt).le
    · simpa [heq]
  have hblock :
      (Finset.range m).sum
          (fun _k => (1 / (2 * (m : ℝ)) : ℝ)) ≤
        (Finset.range m).sum (fun k => f (m + k)) := by
    exact Finset.sum_le_sum hterm
  have hmR : (m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmpos)
  have hhalf :
      (1 / 2 : ℝ) ≤
        (Finset.range m).sum (fun k => f (m + k)) := by
    calc
      (1 / 2 : ℝ) =
          (m : ℝ) * (1 / (2 * (m : ℝ))) := by
        field_simp [hmR]
      _ = (Finset.range m).sum
          (fun _k => (1 / (2 * (m : ℝ)) : ℝ)) := by
        simp
      _ ≤ (Finset.range m).sum (fun k => f (m + k)) := hblock
  have hdiff_lower :
      (1 / 2 : ℝ) ≤ S (m + m) - S m := by
    rw [hsum_eq]
    linarith [hhalf]
  have habs : |S (m + m) - S m| < 1 / 4 := by
    simpa [Real.dist_eq] using hdist
  linarith [hdiff_lower, le_abs_self (S (m + m) - S m), habs]

theorem gap9
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hreciprocal : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      reciprocalTerm a₁ d n >
        1 / (2 * ((n : ℝ) - 1) * d))
    (hcompare : d > 0 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
      1 / (2 * ((n : ℝ) - 1) * d) > comparisonTerm d n)
    (hcomparisonDiv : d > 0 → ∀ n₀ : ℕ,
      TailNotSummable (comparisonTerm d) n₀) :
    d > 0 → ∃ n₀ : ℕ,
      TailNotSummable (reciprocalTerm a₁ d) n₀ := by
  intro hd
  obtain ⟨nr, hnr2, hr⟩ := hreciprocal hd
  obtain ⟨nc, hnc2, hc⟩ := hcompare hd
  let N := max nr nc
  have hnrN : nr ≤ N := Nat.le_max_left nr nc
  have hncN : nc ≤ N := Nat.le_max_right nr nc
  refine ⟨N, ?_⟩
  unfold TailNotSummable
  intro hs
  have hnonneg : ∀ k : ℕ, 0 ≤ comparisonTerm d (k + N) := by
    intro k
    have hkpos : 0 < k + N := by omega
    have hden : 0 < 2 * ((k + N : ℕ) : ℝ) * d :=
      mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hkpos)) hd
    exact (one_div_pos.mpr hden).le
  have hle : ∀ k : ℕ,
      comparisonTerm d (k + N) ≤ reciprocalTerm a₁ d (k + N) := by
    intro k
    have hNk : N ≤ k + N := by omega
    have hnrk : nr ≤ k + N := hnrN.trans hNk
    have hnck : nc ≤ k + N := hncN.trans hNk
    exact (hc (k + N) hnck).le.trans (hr (k + N) hnrk).le
  have hcomp : Summable (fun k : ℕ => comparisonTerm d (k + N)) :=
    Summable.of_nonneg_of_le hnonneg hle hs
  exact hcomparisonDiv hd N hcomp

theorem gap10
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (htail : d > 0 → ∃ n₀ : ℕ,
      TailNotSummable (reciprocalTerm a₁ d) n₀) :
    d > 0 → ¬ Summable (reciprocalTerm a₁ d) := by
  intro hd hs
  obtain ⟨n₀, hn₀⟩ := htail hd
  apply hn₀
  exact hs.comp_injective (add_fixed_right_injective n₀)

theorem gap11
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hnonzero : ∀ n : ℕ, 1 ≤ n → a n ≠ 0) :
    d = 0 → a₁ ≠ 0 := by
  intro hd
  have h := hnonzero 1 (by omega)
  simpa [ha 1, arithmeticTerm, hd] using h

theorem gap12
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hconst : d = 0 → a₁ ≠ 0) :
    d = 0 → ¬ Summable (fun _ : ℕ => (1 / a₁ : ℝ)) := by
  intro hd hs
  have ha₁ : a₁ ≠ 0 := hconst hd
  have hz : Tendsto (fun _ : ℕ => (1 / a₁ : ℝ)) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hc : Tendsto (fun _ : ℕ => (1 / a₁ : ℝ)) atTop (nhds (1 / a₁)) :=
    tendsto_const_nhds
  have heq : (1 / a₁ : ℝ) = 0 := tendsto_nhds_unique hc hz
  exact (one_div_ne_zero ha₁) heq

theorem gap13
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n) :
    d < 0 → ¬ Summable (reciprocalTerm a₁ d) := by
  intro hd hs
  let b : ℕ → ℝ := fun n => arithmeticTerm (-a₁) (-d) n
  have hb : ∀ n, b n = arithmeticTerm (-a₁) (-d) n := by
    intro n
    rfl
  have hthreshold := gap2 b (-a₁) (-d) hb
  have hbound := gap3 b (-a₁) (-d) hb hthreshold
  have hrec := gap4 b (-a₁) (-d) hb hthreshold hbound
  have hcompare := gap5 b (-a₁) (-d) hb hrec
  have hcomparisonDiv := gap8 b (-a₁) (-d) hb
  have htail := gap9 b (-a₁) (-d) hb hrec hcompare hcomparisonDiv
  have hnonsum : ¬ Summable (reciprocalTerm (-a₁) (-d)) :=
    gap10 b (-a₁) (-d) hb htail (by linarith)
  have heq : reciprocalTerm (-a₁) (-d) =
      fun n => -reciprocalTerm a₁ d n := by
    funext n
    have hden : arithmeticTerm (-a₁) (-d) n =
        -arithmeticTerm a₁ d n := by
      unfold arithmeticTerm
      ring
    simpa [reciprocalTerm, hden]
  apply hnonsum
  rw [heq]
  exact hs.neg

theorem gap14
    (a : ℕ → ℝ) (a₁ d : ℝ)
    (ha : ∀ n, a n = arithmeticTerm a₁ d n)
    (hdegenerate : a₁ ≠ 0 ∨ d ≠ 0)
    (hpos : d > 0 → ¬ Summable (reciprocalTerm a₁ d))
    (hzero : d = 0 → a₁ ≠ 0 →
      ¬ Summable (reciprocalTerm a₁ d))
    (hneg : d < 0 → ¬ Summable (reciprocalTerm a₁ d)) :
    ¬ Summable (reciprocalTerm a₁ d) := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · exact hneg hd
  · apply hzero hd
    rcases hdegenerate with ha₁ | hdne
    · exact ha₁
    · exact (hdne hd).elim
  · exact hpos hd

theorem gap15 :
    ∀ a₁ d : ℝ, a₁ ≠ 0 ∨ d ≠ 0 →
      ¬ Summable (reciprocalTerm a₁ d) := by
  intro a₁ d hdegenerate
  let a : ℕ → ℝ := fun n => arithmeticTerm a₁ d n
  have ha : ∀ n, a n = arithmeticTerm a₁ d n := by
    intro n
    rfl
  have hpos : d > 0 → ¬ Summable (reciprocalTerm a₁ d) := by
    intro hd
    have hthreshold := gap2 a a₁ d ha
    have hbound := gap3 a a₁ d ha hthreshold
    have hrec := gap4 a a₁ d ha hthreshold hbound
    have hcompare := gap5 a a₁ d ha hrec
    have hcomparisonDiv := gap8 a a₁ d ha
    have htail := gap9 a a₁ d ha hrec hcompare hcomparisonDiv
    exact gap10 a a₁ d ha htail hd
  have hzero : d = 0 → a₁ ≠ 0 →
      ¬ Summable (reciprocalTerm a₁ d) := by
    intro hd ha₁ hs
    have hc : ¬ Summable (fun _ : ℕ => (1 / a₁ : ℝ)) :=
      gap12 a a₁ d ha (fun _ => ha₁) hd
    have heq : reciprocalTerm a₁ 0 = fun _ : ℕ => (1 / a₁ : ℝ) := by
      funext n
      simp [reciprocalTerm, arithmeticTerm]
    rw [hd] at hs
    rw [heq] at hs
    exact hc hs
  have hneg : d < 0 → ¬ Summable (reciprocalTerm a₁ d) :=
    gap13 a a₁ d ha
  exact gap14 a a₁ d ha hdegenerate hpos hzero hneg

end

end ProofGap.Exercise2565
