import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto

open Filter Topology

/-!
# Exercise 76

Semantic formalization of `proof_gap/exercise_76/{1,...,27}.txt`.
-/

namespace ProofGap.Exercise76

noncomputable section

def b (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow a (1 / (n : ℝ)) - 1

def scaledRootDifference (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * b a n

def logarithmicRatio (a : ℝ) (n : ℕ) : ℝ :=
  b a n / Real.log (1 + b a n)

def reciprocalRewrite (a : ℝ) (n : ℕ) : ℝ :=
  -Real.rpow a (1 / (n : ℝ)) * (n : ℝ) *
    (Real.rpow (1 / a) (1 / (n : ℝ)) - 1)

def CutoffData (a : ℝ) (k : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n →
    0 < k n ∧
    1 / ((k n : ℝ) + 1) ≤ b a n ∧
    b a n < 1 / (k n : ℝ)

/-- Source: `proof_gap/exercise_76/1.txt`; strict positivity excludes n=0. -/
theorem gap1 :
    ∀ a : ℝ, 1 < a → ∀ n : ℕ, 0 < n → 0 < b a n := by
  intro a ha n hn
  unfold b
  have hexp : 0 < (1 / (n : ℝ)) := by positivity
  exact sub_pos.mpr (Real.one_lt_rpow ha hexp)

/-- Source: `proof_gap/exercise_76/2.txt`; the logarithmic identity uses n>0. -/
theorem gap2 :
    ∀ a : ℝ, 1 < a → ∀ n : ℕ, 0 < n →
      Real.log a / (n : ℝ) = Real.log (1 + b a n) := by
  intro a ha n hn
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  unfold b
  rw [add_sub_cancel]
  calc
    Real.log a / (n : ℝ) = (1 / (n : ℝ)) * Real.log a := by ring
    _ = Real.log (a ^ (1 / (n : ℝ))) := (Real.log_rpow ha0 _).symm

/-- Source: `proof_gap/exercise_76/3.txt`; the factorization uses n>0. -/
theorem gap3 :
    ∀ a : ℝ, 1 < a → ∀ n : ℕ, 0 < n →
      scaledRootDifference a n =
        Real.log a * logarithmicRatio a n := by
  intro a ha n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hb : 0 < b a n := gap1 a ha n hn
  have hlog : Real.log (1 + b a n) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by linarith))
  have hid := gap2 a ha n hn
  unfold scaledRootDifference logarithmicRatio
  field_simp
  field_simp at hid
  nlinarith

/-- Source: `proof_gap/exercise_76/4.txt`. -/
theorem gap4 :
    ∀ a : ℝ, 1 < a → Tendsto (b a) atTop (𝓝 0) := by
  intro a ha
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0))
  have hrpow :
      Tendsto (fun n : ℕ => Real.rpow a (1 / (n : ℝ))) atTop (𝓝 1) := by
    have hexp :
        Tendsto (fun n : ℕ => Real.exp (Real.log a * (1 / (n : ℝ))))
          atTop (𝓝 1) := by
      simpa using Real.continuous_exp.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul hinv)
    simpa [Real.rpow_def_of_pos (lt_trans zero_lt_one ha)] using hexp
  simpa only [b, sub_self] using hrpow.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- Source: `proof_gap/exercise_76/5.txt`; remove the rebound cutoff variable. -/
theorem gap5 :
    ∀ a : ℝ, 1 < a →
      ∃ N : ℕ, 0 < N ∧
        ∀ n : ℕ, N < n → 0 < b a n ∧ b a n < 1 := by
  intro a ha
  have hev : ∀ᶠ n : ℕ in atTop, b a n < 1 :=
    (gap4 a ha).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨N + 1, by omega, ?_⟩
  intro n hn
  exact ⟨gap1 a ha n (by omega), hN n (by omega)⟩

/-- Source: `proof_gap/exercise_76/6.txt`; choose one cutoff value for each fixed n. -/
theorem gap6 :
    ∀ a : ℝ, 1 < a →
      ∃ k : ℕ → ℕ,
        CutoffData a k ∧
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          ∀ j : ℕ,
            0 < j →
            1 / ((j : ℝ) + 1) ≤ b a n →
            b a n < 1 / (j : ℝ) →
            j = k n := by
  intro a ha
  rcases gap5 a ha with ⟨N, hNpos, hN⟩
  let k : ℕ → ℕ := fun n => Nat.ceil (1 / b a n) - 1
  have hdata : ∀ n : ℕ, N < n →
      0 < k n ∧
      1 / ((k n : ℝ) + 1) ≤ b a n ∧
      b a n < 1 / (k n : ℝ) := by
    intro n hn
    have hb := hN n hn
    let q : ℝ := 1 / b a n
    have hqpos : 0 < q := one_div_pos.mpr hb.1
    have hqgt : 1 < q := (one_lt_div hb.1).mpr hb.2
    have hcgt : 1 < Nat.ceil q := by
      apply (Nat.lt_ceil).mpr
      exact_mod_cast hqgt
    have hkdef : k n = Nat.ceil q - 1 := by rfl
    have hkpos : 0 < k n := by
      rw [hkdef]
      omega
    have hkadd : k n + 1 = Nat.ceil q := by
      rw [hkdef]
      omega
    have hqle : q ≤ (k n : ℝ) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, hkadd]
      exact Nat.le_ceil q
    have hklq : (k n : ℝ) < q := by
      have hc_lt : (Nat.ceil q : ℝ) < q + 1 :=
        Nat.ceil_lt_add_one hqpos.le
      have hkaddR : (k n : ℝ) + 1 = (Nat.ceil q : ℝ) := by
        exact_mod_cast hkadd
      linarith
    have hkRpos : 0 < (k n : ℝ) := by exact_mod_cast hkpos
    have hk1pos : 0 < (k n : ℝ) + 1 := by linarith
    have hlower : 1 / ((k n : ℝ) + 1) ≤ b a n := by
      rw [div_le_iff₀ hk1pos]
      dsimp [q] at hqle
      have := (div_le_iff₀ hb.1).mp hqle
      nlinarith
    have hupper : b a n < 1 / (k n : ℝ) := by
      rw [lt_div_iff₀ hkRpos]
      dsimp [q] at hklq
      have := (lt_div_iff₀ hb.1).mp hklq
      nlinarith
    exact ⟨hkpos, hlower, hupper⟩
  refine ⟨k, ⟨⟨N, hdata⟩, ⟨N, ?_⟩⟩⟩
  intro n hn j hj hjlower hjupper
  have hb := hN n hn
  let q : ℝ := 1 / b a n
  have hjRpos : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1pos : 0 < (j : ℝ) + 1 := by linarith
  have hqle : q ≤ (j : ℝ) + 1 := by
    dsimp [q]
    rw [div_le_iff₀ hb.1]
    have := (div_le_iff₀ hj1pos).mp hjlower
    nlinarith
  have hjlt : (j : ℝ) < q := by
    dsimp [q]
    rw [lt_div_iff₀ hb.1]
    have := (lt_div_iff₀ hjRpos).mp hjupper
    nlinarith
  have hceil_le : Nat.ceil q ≤ j + 1 := by
    apply (Nat.ceil_le).mpr
    exact_mod_cast hqle
  have hj_lt_ceil : j < Nat.ceil q := by
    apply (Nat.lt_ceil).mpr
    exact_mod_cast hjlt
  have hkdef : k n = Nat.ceil q - 1 := by rfl
  rw [hkdef]
  omega

/-- Source: `proof_gap/exercise_76/7.txt`; the limit is outside the pointwise binder. -/
theorem gap7 :
    ∀ a : ℝ, 1 < a → ∀ k : ℕ → ℕ,
      CutoffData a k →
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) := by
  intro a ha k hk
  rcases hk with ⟨N, hN⟩
  apply tendsto_atTop.2
  intro R
  obtain ⟨m, hm⟩ := exists_nat_gt R
  have hb :
      ∀ᶠ n : ℕ in atTop, b a n < 1 / ((m : ℝ) + 1) :=
    (gap4 a ha).eventually
      (Iio_mem_nhds (one_div_pos.mpr (by positivity)))
  filter_upwards [hb, eventually_gt_atTop N] with n hbn hn
  have hdata := hN n hn
  have hkgt : m < k n := by
    by_contra hnot
    have hkm : k n ≤ m := by omega
    have hrec :
        1 / ((m : ℝ) + 1) ≤ 1 / ((k n : ℝ) + 1) := by
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkm 1)
    linarith [hdata.2.1]
  exact le_trans (le_of_lt hm) (by exact_mod_cast (le_of_lt hkgt))

/-- Source: `proof_gap/exercise_76/8.txt`; the inequality is eventual. -/
theorem gap8 :
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) →
      ∀ᶠ n in atTop,
        1 / ((k n : ℝ) + 2) <
          Real.log (1 + 1 / ((k n : ℝ) + 1)) := by
  intro k _
  filter_upwards [] with n
  let t : ℝ := k n
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : 0 < t + 1 := by linarith
  have ht2 : 0 < t + 2 := by linarith
  have hy : 0 < (t + 1) / (t + 2) := div_pos ht1 ht2
  have hyne : (t + 1) / (t + 2) ≠ 1 := by
    exact ne_of_lt ((div_lt_one ht2).mpr (by linarith))
  have hlog := Real.log_lt_sub_one_of_pos hy hyne
  have hfrac :
      (t + 1) / (t + 2) = (1 + 1 / (t + 1))⁻¹ := by
    field_simp
    ring
  have hsub : (t + 1) / (t + 2) - 1 = -(1 / (t + 2)) := by
    field_simp
    ring
  have hsub' : (1 + 1 / (t + 1))⁻¹ - 1 = -(1 / (t + 2)) := by
    rw [← hfrac]
    exact hsub
  rw [hfrac, Real.log_inv, hsub'] at hlog
  dsimp [t] at hlog ⊢
  linarith

/-- Source: `proof_gap/exercise_76/9.txt`; use the selected cutoff eventually. -/
theorem gap9 :
    ∀ a : ℝ, ∀ k : ℕ → ℕ, CutoffData a k →
      ∀ᶠ n in atTop,
        Real.log (1 + 1 / ((k n : ℝ) + 1)) ≤
          Real.log (1 + b a n) := by
  intro a k hk
  rcases hk with ⟨N, hN⟩
  filter_upwards [eventually_gt_atTop N] with n hn
  have hb := (hN n hn).2.1
  exact Real.log_le_log (by positivity) (by linarith)

/-- Source: `proof_gap/exercise_76/10.txt`. -/
theorem gap10 :
    ∀ a : ℝ, ∀ k : ℕ → ℕ, CutoffData a k →
      ∀ᶠ n in atTop,
        Real.log (1 + b a n) <
          Real.log (1 + 1 / (k n : ℝ)) := by
  intro a k hk
  rcases hk with ⟨N, hN⟩
  filter_upwards [eventually_gt_atTop N] with n hn
  have hdata := hN n hn
  have hkpos : 0 < (k n : ℝ) := by exact_mod_cast hdata.1
  have hbpos : 0 < b a n :=
    lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hdata.2.1
  exact Real.log_lt_log (by linarith) (by linarith [hdata.2.2])

/-- Source: `proof_gap/exercise_76/11.txt`; positivity of k holds eventually. -/
theorem gap11 :
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) →
      ∀ᶠ n in atTop,
        Real.log (1 + 1 / (k n : ℝ)) < 1 / (k n : ℝ) := by
  intro k hk
  filter_upwards [tendsto_atTop.1 hk 1] with n hn
  have hkpos : 0 < (k n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hone : 0 < 1 + 1 / (k n : ℝ) := by positivity
  have hne : 1 + 1 / (k n : ℝ) ≠ 1 := by
    linarith [one_div_pos.mpr hkpos]
  simpa using Real.log_lt_sub_one_of_pos hone hne

/-- Source: `proof_gap/exercise_76/12.txt`. -/
theorem gap12 :
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) →
      ∀ᶠ n in atTop,
        1 / ((k n : ℝ) + 2) < 1 / (k n : ℝ) := by
  intro k hk
  filter_upwards [tendsto_atTop.1 hk 1] with n hn
  have hkpos : 0 < (k n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  exact one_div_lt_one_div_of_lt hkpos (by linarith)

/-- Source: `proof_gap/exercise_76/13.txt`. -/
theorem gap13 :
    ∀ k : ℕ → ℕ,
      ∀ᶠ n in atTop,
        1 - 1 / ((k n : ℝ) + 1) =
          (k n : ℝ) / ((k n : ℝ) + 1) := by
  intro k
  filter_upwards [] with n
  have hpos : 0 < (k n : ℝ) + 1 := by positivity
  field_simp
  ring

/-- Source: `proof_gap/exercise_76/14.txt`. -/
theorem gap14 :
    ∀ a : ℝ, 1 < a → ∀ k : ℕ → ℕ, CutoffData a k →
      ∀ᶠ n in atTop,
        (k n : ℝ) / ((k n : ℝ) + 1) < logarithmicRatio a n := by
  intro a ha k hk
  have hklim := gap7 a ha k hk
  have hlogcut := gap10 a k hk
  have hlogupper := gap11 k hklim
  rcases hk with ⟨N, hN⟩
  filter_upwards [eventually_gt_atTop N, hlogcut, hlogupper] with n hn hcut hupper
  have hdata := hN n hn
  have hkpos : 0 < (k n : ℝ) := by exact_mod_cast hdata.1
  have hk1pos : 0 < (k n : ℝ) + 1 := by linarith
  have hbpos : 0 < b a n :=
    lt_of_lt_of_le (one_div_pos.mpr hk1pos) hdata.2.1
  have hlogpos : 0 < Real.log (1 + b a n) :=
    Real.log_pos (by linarith)
  have hloglt :
      Real.log (1 + b a n) < 1 / (k n : ℝ) :=
    lt_trans hcut hupper
  have hklog : (k n : ℝ) * Real.log (1 + b a n) < 1 := by
    have := (lt_div_iff₀ hkpos).mp hloglt
    nlinarith
  have hbprod : 1 ≤ b a n * ((k n : ℝ) + 1) := by
    have := (div_le_iff₀ hk1pos).mp hdata.2.1
    nlinarith
  unfold logarithmicRatio
  rw [div_lt_div_iff₀ hk1pos hlogpos]
  nlinarith

/-- Source: `proof_gap/exercise_76/15.txt`. -/
theorem gap15 :
    ∀ a : ℝ, 1 < a → ∀ k : ℕ → ℕ, CutoffData a k →
      ∀ᶠ n in atTop,
        logarithmicRatio a n < ((k n : ℝ) + 2) / (k n : ℝ) := by
  intro a ha k hk
  have hklim := gap7 a ha k hk
  have hlogbase := gap8 k hklim
  have hlogcut := gap9 a k hk
  rcases hk with ⟨N, hN⟩
  filter_upwards [eventually_gt_atTop N, hlogbase, hlogcut] with n hn hbase hcut
  have hdata := hN n hn
  have hkpos : 0 < (k n : ℝ) := by exact_mod_cast hdata.1
  have hk2pos : 0 < (k n : ℝ) + 2 := by linarith
  have hbpos : 0 < b a n := by
    exact lt_of_lt_of_le
      (one_div_pos.mpr (by linarith : 0 < (k n : ℝ) + 1)) hdata.2.1
  have hlogpos : 0 < Real.log (1 + b a n) :=
    Real.log_pos (by linarith)
  have hblog : b a n * (k n : ℝ) < 1 := by
    have := (lt_div_iff₀ hkpos).mp hdata.2.2
    nlinarith
  have hone :
      1 < Real.log (1 + b a n) * ((k n : ℝ) + 2) := by
    have hlower :
        1 / ((k n : ℝ) + 2) < Real.log (1 + b a n) :=
      lt_of_lt_of_le hbase hcut
    have := (div_lt_iff₀ hk2pos).mp hlower
    nlinarith
  unfold logarithmicRatio
  rw [div_lt_div_iff₀ hlogpos hkpos]
  nlinarith

/-- Source: `proof_gap/exercise_76/16.txt`. -/
theorem gap16 :
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) →
      ∀ᶠ n in atTop,
        ((k n : ℝ) + 2) / (k n : ℝ) = 1 + 2 / (k n : ℝ) := by
  intro k hk
  filter_upwards [tendsto_atTop.1 hk 1] with n hn
  have hkpos : 0 < (k n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  field_simp [hkpos.ne']

/-- Source: `proof_gap/exercise_76/17.txt`. -/
theorem gap17 :
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ => (k n : ℝ)) atTop (atTop : Filter ℝ) →
      ∀ᶠ n in atTop,
        1 - 1 / ((k n : ℝ) + 1) < 1 + 2 / (k n : ℝ) := by
  intro k hk
  filter_upwards [tendsto_atTop.1 hk 1] with n hn
  have hkpos : 0 < (k n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hleft : 1 - 1 / ((k n : ℝ) + 1) < 1 := by
    linarith [one_div_pos.mpr (by linarith : 0 < (k n : ℝ) + 1)]
  have hright : 1 < 1 + 2 / (k n : ℝ) := by
    have : 0 < 2 / (k n : ℝ) := div_pos (by norm_num) hkpos
    linarith
  exact lt_trans hleft hright

private theorem scaledRootDifference_tendsto
    (a : ℝ) (ha : 0 < a) :
    Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[>] 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝[>] 0))
  have hmain := (tendsto_rpow_sub_one_log ha).comp hinv
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp [scaledRootDifference, b, one_div, hn0]

/-- Source: `proof_gap/exercise_76/18.txt`. -/
theorem gap18 :
    ∀ a : ℝ, 1 < a → Tendsto (logarithmicRatio a) atTop (𝓝 1) := by
  intro a ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hlog : Real.log a ≠ 0 := ne_of_gt (Real.log_pos ha)
  have hprod :
      Tendsto (fun n : ℕ => Real.log a * logarithmicRatio a n)
        atTop (𝓝 (Real.log a)) := by
    apply (scaledRootDifference_tendsto a ha0).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact gap3 a ha n hn
  have hscaled := hprod.const_mul (Real.log a)⁻¹
  convert hscaled using 1
  · funext n
    field_simp
  · field_simp

/-- Source: `proof_gap/exercise_76/19.txt`. -/
theorem gap19 :
    ∀ a : ℝ, 1 < a →
      Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  intro a ha
  exact scaledRootDifference_tendsto a (lt_trans zero_lt_one ha)

/-- Source: `proof_gap/exercise_76/20.txt`. -/
theorem gap20 :
    ∀ a : ℝ, 0 < a → a < 1 → 1 / a > 1 := by
  intro a ha hlt
  exact (one_lt_div ha).mpr hlt

/-- Source: `proof_gap/exercise_76/21.txt`; equality of raw limits is a pointwise rewrite. -/
theorem gap21 :
    ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, 0 < n →
      scaledRootDifference a n = reciprocalRewrite a n := by
  intro a ha _ n hn
  have hrpow : 0 < Real.rpow a (1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos ha _
  have hinvrpow :
      Real.rpow (1 / a) (1 / (n : ℝ)) =
        1 / Real.rpow a (1 / (n : ℝ)) := by
    calc
      Real.rpow (1 / a) (1 / (n : ℝ)) =
          Real.rpow 1 (1 / (n : ℝ)) / Real.rpow a (1 / (n : ℝ)) := by
            exact Real.div_rpow (by norm_num) ha.le _
      _ = 1 / Real.rpow a (1 / (n : ℝ)) := by
        rw [Real.rpow_eq_pow, Real.one_rpow]
  unfold scaledRootDifference reciprocalRewrite b
  rw [hinvrpow]
  field_simp [ne_of_gt hrpow]
  ring

/-- Source: `proof_gap/exercise_76/22.txt`. -/
theorem gap22 :
    ∀ a : ℝ, 0 < a → a < 1 →
      Tendsto (reciprocalRewrite a) atTop (𝓝 (-Real.log (1 / a))) := by
  intro a ha hlt
  have htarget : -Real.log (1 / a) = Real.log a := by
    simp [one_div, Real.log_inv]
  rw [htarget]
  apply (scaledRootDifference_tendsto a ha).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact gap21 a ha hlt n hn

/-- Source: `proof_gap/exercise_76/23.txt`. -/
theorem gap23 :
    ∀ a : ℝ, 0 < a → a < 1 → -Real.log (1 / a) = Real.log a := by
  intro a ha _
  simp [one_div, Real.log_inv]

/-- Source: `proof_gap/exercise_76/24.txt`. -/
theorem gap24 :
    ∀ a : ℝ, 0 < a → a < 1 →
      Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  intro a ha _
  exact scaledRootDifference_tendsto a ha

/-- Source: `proof_gap/exercise_76/25.txt`. -/
theorem gap25 :
    ∀ a : ℝ, a = 1 →
      Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  intro a ha
  subst a
  have hfun : scaledRootDifference 1 = fun _ : ℕ => 0 := by
    funext n
    simp [scaledRootDifference, b]
  rw [hfun]
  simp

/-- Source: `proof_gap/exercise_76/26.txt`. -/
theorem gap26 :
    ∀ a : ℝ, 0 < a →
      Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  exact scaledRootDifference_tendsto

/-- Source: `proof_gap/exercise_76/27.txt`; retain the source assumption a>0. -/
theorem gap27
    (a : ℝ)
    (ha : 0 < a)
    (h26 : Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a))) :
    Tendsto (scaledRootDifference a) atTop (𝓝 (Real.log a)) := by
  exact h26

end

end ProofGap.Exercise76
