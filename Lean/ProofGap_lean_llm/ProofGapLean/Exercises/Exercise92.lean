import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace ProofGap.Exercise92

noncomputable section

def ratio (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  x (n + 1) / x n

def absRatio (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  |x (n + 1)| / |x n|

def z (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ ((n - 1) / 2)

def telescopingProduct (x : ℕ → ℝ) (N n : ℕ) : ℝ :=
  |x N| * ∏ k ∈ Finset.Icc N (n - 1), |ratio x k|

/-- Source: `proof_gap/exercise_92/1.txt`; use the quotient limit law. -/
theorem gap1
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a))
    (ha : a ≠ 0) :
    Tendsto (ratio x) atTop (𝓝 (a / a)) := by
  unfold ratio
  exact (hx.comp (tendsto_add_atTop_nat 1)).div hx ha

/-- Source: `proof_gap/exercise_92/2.txt`; both shifted and original limits are a. -/
theorem gap2 (a : ℝ) (ha : a ≠ 0) :
    a / a = a / a := by
  rfl

/-- Source: `proof_gap/exercise_92/3.txt`. -/
theorem gap3 (a : ℝ) (ha : a ≠ 0) :
    a / a = 1 := by
  exact div_self ha

/-- Source: `proof_gap/exercise_92/4.txt`. -/
theorem gap4
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a))
    (ha : a ≠ 0) :
    Tendsto (ratio x) atTop (𝓝 1) := by
  simpa [gap3 a ha] using gap1 x a hx ha

/-- Source: `proof_gap/exercise_92/5.txt`; z is defined on all natural indices. -/
theorem gap5 :
    Tendsto z atTop (𝓝 0) := by
  have hindex :
      Tendsto (fun n : ℕ => (n - 1) / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (2 * M + 1)] with n hn
    omega
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hindex

/-- Source: `proof_gap/exercise_92/6.txt`; use positive pair indices. -/
theorem gap6 :
    Tendsto (fun m : ℕ => z (2 * (m + 1)) / z (2 * (m + 1) - 1))
      atTop (𝓝 1) := by
  convert tendsto_const_nhds using 1
  funext m
  unfold z
  have hnum : (2 * (m + 1) - 1) / 2 = m := by omega
  have hden : (2 * (m + 1) - 1 - 1) / 2 = m := by omega
  rw [hnum, hden]
  exact div_self (pow_ne_zero _ (by norm_num))

/-- Source: `proof_gap/exercise_92/7.txt`; use positive pair indices. -/
theorem gap7 :
    Tendsto (fun m : ℕ => z (2 * (m + 1) + 1) / z (2 * (m + 1)))
      atTop (𝓝 (1 / 2)) := by
  convert tendsto_const_nhds using 1
  funext m
  unfold z
  have hnum : (2 * (m + 1) + 1 - 1) / 2 = m + 1 := by omega
  have hden : (2 * (m + 1) - 1) / 2 = m := by omega
  rw [hnum, hden, pow_succ]
  field_simp

/-- Source: `proof_gap/exercise_92/8.txt`. -/
theorem gap8 :
    ¬ ∃ b : ℝ, Tendsto (ratio z) atTop (𝓝 b) := by
  rintro ⟨b, hb⟩
  have hevenIndex :
      Tendsto (fun m : ℕ => 2 * (m + 1) - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop (N + 1)] with m hm
    omega
  have hoddIndex :
      Tendsto (fun m : ℕ => 2 * (m + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with m hm
    omega
  have hb1 :
      Tendsto (fun m : ℕ => z (2 * (m + 1)) / z (2 * (m + 1) - 1))
        atTop (𝓝 b) := by
    simpa [ratio] using hb.comp hevenIndex
  have hb2 :
      Tendsto (fun m : ℕ => z (2 * (m + 1) + 1) / z (2 * (m + 1)))
        atTop (𝓝 b) := by
    simpa [ratio] using hb.comp hoddIndex
  have hbone : b = 1 := tendsto_nhds_unique hb1 gap6
  have hbhalf : b = 1 / 2 := tendsto_nhds_unique hb2 gap7
  norm_num [hbone] at hbhalf

/-- Source: `proof_gap/exercise_92/9.txt`; remove the shadowed existential b. -/
theorem gap9
    (x : ℕ → ℝ) (b : ℝ)
    (hratio : Tendsto (ratio x) atTop (𝓝 b)) :
    Tendsto (absRatio x) atTop (𝓝 |b|) := by
  apply hratio.abs.congr'
  filter_upwards [] with n
  simp [ratio, absRatio, abs_div]

/-- Source: `proof_gap/exercise_92/10.txt`; choose N after r. -/
theorem gap10
    (x : ℕ → ℝ) (b r : ℝ)
    (hratio : Tendsto (ratio x) atTop (𝓝 b))
    (hr : 1 < r) (hrb : r < |b|) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r < absRatio x n := by
  have hev : ∀ᶠ n : ℕ in atTop, r < absRatio x n :=
    (gap9 x b hratio).eventually (Ioi_mem_nhds hrb)
  exact eventually_atTop.1 hev

/-- Source: `proof_gap/exercise_92/11.txt`; the telescoping product is explicit. -/
theorem gap11
    (x : ℕ → ℝ) :
    ∀ N n : ℕ, N < n → x N ≠ 0 →
      (∀ k : ℕ, N ≤ k → k < n → x k ≠ 0) →
      |x n| = telescopingProduct x N n := by
  intro N n hNn hxN hnz
  rcases Nat.exists_eq_add_of_lt hNn with ⟨d, rfl⟩
  have htel :
      ∀ d : ℕ,
        (∀ k : ℕ, N ≤ k → k < N + d + 1 → x k ≠ 0) →
        |x (N + d + 1)| = telescopingProduct x N (N + d + 1) := by
    intro d
    induction d with
    | zero =>
        intro hnonzero
        unfold telescopingProduct
        simp [ratio, abs_div, hxN]
        field_simp [abs_ne_zero.mpr hxN]
    | succ d ih =>
        intro hnonzero
        have hprev_nz :
            ∀ k : ℕ, N ≤ k → k < N + d + 1 → x k ≠ 0 := by
          intro k hkN hk
          exact hnonzero k hkN (by omega)
        have hprev := ih hprev_nz
        have hxlast : x (N + d + 1) ≠ 0 :=
          hnonzero (N + d + 1) (by omega) (by omega)
        have hstep :
            |x (N + (d + 1) + 1)| =
              |ratio x (N + d + 1)| * |x (N + d + 1)| := by
          unfold ratio
          rw [abs_div]
          field_simp [abs_ne_zero.mpr hxlast]
          congr 2 <;> omega
        unfold telescopingProduct at hprev ⊢
        rw [hstep, hprev]
        have hprevTop : N + d + 1 - 1 = N + d := by omega
        have hcurrTop : N + (d + 1) + 1 - 1 = N + d + 1 := by omega
        rw [hprevTop, hcurrTop]
        have hprod :=
          Finset.prod_Icc_succ_top
            (show N ≤ (N + d) + 1 by omega)
            (fun k => |ratio x k|)
        rw [hprod]
        ring
  exact htel d hnz

/-- Source: `proof_gap/exercise_92/12.txt`; the product bound has explicit hypotheses. -/
theorem gap12
    (x : ℕ → ℝ) (r : ℝ) :
    ∀ N n : ℕ, N < n → x N ≠ 0 → 0 < r →
      (∀ k : ℕ, N ≤ k → k < n → r < absRatio x k) →
      telescopingProduct x N n > |x N| * r ^ (n - N) := by
  intro N n hNn hxN hr hratio
  let s : Finset ℕ := Finset.Icc N (n - 1)
  have hsne : s.Nonempty := by
    refine ⟨N, ?_⟩
    unfold s
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hprod :
      (∏ k ∈ s, r) < ∏ k ∈ s, |ratio x k| := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro k hk
      exact hr
    · intro k hk
      have hki := Finset.mem_Icc.mp (show k ∈ Finset.Icc N (n - 1) by
        exact hk)
      have hlt := hratio k hki.1 (by omega)
      simpa [absRatio, ratio, abs_div] using hlt
    · exact hsne
  have hcard : s.card = n - N := by
    unfold s
    simp
    omega
  have hprod' :
      r ^ (n - N) < ∏ k ∈ s, |ratio x k| := by
    simpa [hcard] using hprod
  unfold telescopingProduct
  change
    |x N| * (∏ k ∈ s, |ratio x k|) >
      |x N| * r ^ (n - N)
  exact mul_lt_mul_of_pos_left hprod' (abs_pos.mpr hxN)

/-- Source: `proof_gap/exercise_92/13.txt`. -/
theorem gap13
    (x : ℕ → ℝ) (r : ℝ) :
    ∀ N n : ℕ, N < n → x N ≠ 0 → 0 < r →
      (∀ k : ℕ, N ≤ k → k < n → r < absRatio x k) →
      |x n| > |x N| * r ^ (n - N) := by
  intro N n hNn hxN hr hratio
  have hnz : ∀ k : ℕ, N ≤ k → k < n → x k ≠ 0 := by
    intro k hkN hkn hxk
    have h := hratio k hkN hkn
    simp [absRatio, hxk] at h
    linarith
  rw [gap11 x N n hNn hxN hnz]
  exact gap12 x r N n hNn hxN hr hratio

/-- Source: `proof_gap/exercise_92/14.txt`; divergence is stated for absolute values. -/
theorem gap14
    (x : ℕ → ℝ) (b : ℝ)
    (hzero : Tendsto x atTop (𝓝 0))
    (hnz : ∀ n : ℕ, 0 < n → x n ≠ 0)
    (hratio : Tendsto (ratio x) atTop (𝓝 b))
    (hb : 1 < |b|) :
    Tendsto (fun n => |x n|) atTop (atTop : Filter ℝ) := by
  let r : ℝ := (1 + |b|) / 2
  have hr : 1 < r := by
    dsimp [r]
    linarith
  have hrb : r < |b| := by
    dsimp [r]
    linarith
  rcases gap10 x b r hratio hr hrb with ⟨N₀, hN₀⟩
  let N := max N₀ 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hratioN : ∀ k : ℕ, N ≤ k → r < absRatio x k := by
    intro k hk
    exact hN₀ k (le_trans (by
      dsimp [N]
      exact Nat.le_max_left _ _) hk)
  have hxN : x N ≠ 0 := hnz N hNpos
  have hbase : 0 < |x N| := abs_pos.mpr hxN
  have hlower :
      ∀ d : ℕ, |x N| * r ^ d ≤ |x (N + d)| := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hkpos : 0 < N + d := by omega
        have hxk : x (N + d) ≠ 0 := hnz (N + d) hkpos
        have hrat : r < absRatio x (N + d) :=
          hratioN (N + d) (by omega)
        have hid :
            |x (N + d + 1)| =
              absRatio x (N + d) * |x (N + d)| := by
          unfold absRatio
          field_simp [abs_ne_zero.mpr hxk]
        apply le_of_lt
        calc
          |x N| * r ^ (d + 1) = r * (|x N| * r ^ d) := by
            rw [pow_succ]
            ring
          _ ≤ r * |x (N + d)| :=
            mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hr))
          _ < absRatio x (N + d) * |x (N + d)| :=
            mul_lt_mul_of_pos_right hrat (abs_pos.mpr hxk)
          _ = |x (N + (d + 1))| := by
            rw [← hid]
            congr 2
  have hgeom :
      Tendsto (fun d : ℕ => |x N| * r ^ d) atTop (atTop : Filter ℝ) := by
    have hp := tendsto_pow_atTop_atTop_of_one_lt hr
    simpa [mul_comm] using hp.atTop_mul_const hbase
  have hshift :
      Tendsto (fun d : ℕ => |x (N + d)|) atTop (atTop : Filter ℝ) := by
    apply tendsto_atTop.2
    intro A
    have hev : ∀ᶠ d : ℕ in atTop, A ≤ |x N| * r ^ d :=
      tendsto_atTop.1 hgeom A
    filter_upwards [hev] with d hd
    exact le_trans hd (hlower d)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa [add_comm] using hshift

/-- Source: `proof_gap/exercise_92/15.txt`. -/
theorem gap15
    (x : ℕ → ℝ) (b : ℝ)
    (hzero : Tendsto x atTop (𝓝 0))
    (hnz : ∀ n : ℕ, 0 < n → x n ≠ 0)
    (hratio : Tendsto (ratio x) atTop (𝓝 b))
    (hb : 1 < |b|) :
    False := by
  have hinf := gap14 x b hzero hnz hratio hb
  have hhigh : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ |x n| :=
    tendsto_atTop.1 hinf 1
  have hlow : ∀ᶠ n : ℕ in atTop, |x n| < 1 := by
    have habs : Tendsto (fun n => |x n|) atTop (𝓝 0) := by
      simpa using hzero.abs
    exact habs.eventually (Iio_mem_nhds (by norm_num))
  rcases (hhigh.and hlow).exists with ⟨n, hn1, hn2⟩
  linarith

/-- Source: `proof_gap/exercise_92/16.txt`. -/
theorem gap16
    (x : ℕ → ℝ) (b : ℝ)
    (hzero : Tendsto x atTop (𝓝 0))
    (hnz : ∀ n : ℕ, 0 < n → x n ≠ 0)
    (hratio : Tendsto (ratio x) atTop (𝓝 b)) :
    -1 ≤ b := by
  by_contra h
  have hb : 1 < |b| := by
    rw [abs_of_neg (by linarith)]
    linarith
  exact gap15 x b hzero hnz hratio hb

/-- Source: `proof_gap/exercise_92/17.txt`. -/
theorem gap17
    (x : ℕ → ℝ) (b : ℝ)
    (hzero : Tendsto x atTop (𝓝 0))
    (hnz : ∀ n : ℕ, 0 < n → x n ≠ 0)
    (hratio : Tendsto (ratio x) atTop (𝓝 b)) :
    b ≤ 1 := by
  by_contra h
  have hb : 1 < |b| := lt_of_lt_of_le (by linarith) (le_abs_self b)
  exact gap15 x b hzero hnz hratio hb

/-- Source: `proof_gap/exercise_92/18.txt`. -/
theorem gap18 :
    (-1 : ℝ) ≤ 1 := by
  norm_num

/-- Source: `proof_gap/exercise_92/19.txt`. -/
theorem gap19
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a))
    (ha : a ≠ 0) :
    Tendsto (ratio x) atTop (𝓝 1) := by
  exact gap4 x a hx ha

/-- Source: `proof_gap/exercise_92/20.txt`. -/
theorem gap20
    (x : ℕ → ℝ)
    (hzero : Tendsto x atTop (𝓝 0))
    (hnz : ∀ n : ℕ, 0 < n → x n ≠ 0) :
    (¬ ∃ b : ℝ, Tendsto (ratio x) atTop (𝓝 b)) ∨
      (∃ b : ℝ, b ∈ Set.Icc (-1 : ℝ) 1 ∧
        Tendsto (ratio x) atTop (𝓝 b)) := by
  by_cases h : ∃ b : ℝ, Tendsto (ratio x) atTop (𝓝 b)
  · right
    rcases h with ⟨b, hb⟩
    exact ⟨b, ⟨gap16 x b hzero hnz hb, gap17 x b hzero hnz hb⟩, hb⟩
  · exact Or.inl h

end

end ProofGap.Exercise92
