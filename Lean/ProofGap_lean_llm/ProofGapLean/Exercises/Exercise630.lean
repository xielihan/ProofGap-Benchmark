import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise630

noncomputable section

def cosProduct (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).prod (fun k => Real.cos (x / (2 : ℝ) ^ k))

def sineFactorization (x : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * cosProduct x n * Real.sin (x / (2 : ℝ) ^ n)

def ratioSeq (x : ℝ) (n : ℕ) : ℝ :=
  Real.sin x / (2 : ℝ) ^ n / Real.sin (x / (2 : ℝ) ^ n)

def normalizedRatioSeq (x : ℝ) (n : ℕ) : ℝ :=
  (x / (2 : ℝ) ^ n) / Real.sin (x / (2 : ℝ) ^ n) * (Real.sin x / x)

/-- Source: `proof_gap/exercise_630/1.txt`. -/
private theorem sin_half_identity (x : ℝ) :
    Real.sin x = 2 * Real.cos (x / 2) * Real.sin (x / 2) := by
  calc
    Real.sin x = Real.sin (2 * (x / 2)) := by
      congr 1
      ring
    _ = 2 * Real.cos (x / 2) * Real.sin (x / 2) := by
      rw [Real.sin_two_mul]
      ring

private theorem sineFactorization_eq (x : ℝ) (n : ℕ) :
    Real.sin x = sineFactorization x n := by
  induction n with
  | zero =>
      simp [sineFactorization, cosProduct]
  | succ n ih =>
      calc
        Real.sin x = sineFactorization x n := ih
        _ = sineFactorization x (n + 1) := by
          have hset :
              Finset.Icc 1 (n + 1) =
                insert (n + 1) (Finset.Icc 1 n) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot : n + 1 ∉ Finset.Icc 1 n := by
            simp [Finset.mem_Icc]
          have hprod :
              cosProduct x (n + 1) =
                cosProduct x n * Real.cos (x / (2 : ℝ) ^ (n + 1)) := by
            unfold cosProduct
            rw [hset, Finset.prod_insert hnot]
            ring
          have harg :
              x / (2 : ℝ) ^ n / 2 = x / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
          simp only [sineFactorization]
          rw [hprod, sin_half_identity (x / (2 : ℝ) ^ n), harg, pow_succ]
          ring

private theorem scaled_tendsto_zero (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => x / (2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hconst :
      Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) :=
    tendsto_const_nhds
  simpa only [div_eq_mul_inv, inv_pow, mul_zero] using hconst.mul hpow

private theorem scaled_tendsto_punctured (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (fun n : ℕ => x / (2 : ℝ) ^ n)
      Filter.atTop
      (nhdsWithin (0 : ℝ) ((Set.singleton (0 : ℝ))ᶜ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨scaled_tendsto_zero x, ?_⟩
  filter_upwards [] with n
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  simpa only [Set.mem_singleton_iff] using (div_ne_zero hx hp)

private theorem tendsto_sin_div_zero :
    Filter.Tendsto (fun y : ℝ => Real.sin y / y)
      (nhdsWithin (0 : ℝ) ((Set.singleton (0 : ℝ))ᶜ)) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope
  have hslope :
      slope Real.sin 0 = (fun y : ℝ => Real.sin y / y) := by
    funext y
    unfold slope
    simp [div_eq_mul_inv, mul_comm]
  rw [hslope] at h
  simpa using h

private theorem eventually_scaled_sine_ne_zero (x : ℝ) (hx : x ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sin (x / (2 : ℝ) ^ n) ≠ 0 := by
  have hmem : Set.Ioo (-Real.pi) Real.pi ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds
      ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        x / (2 : ℝ) ^ n ∈ Set.Ioo (-Real.pi) Real.pi :=
    (scaled_tendsto_zero x).eventually hmem
  filter_upwards [hev] with n hn
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hargne : x / (2 : ℝ) ^ n ≠ 0 := div_ne_zero hx hp
  rcases lt_or_gt_of_ne hargne with hneg | hpos
  · have hsin :
        0 < Real.sin (-(x / (2 : ℝ) ^ n)) :=
      Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hn.1])
    rw [Real.sin_neg] at hsin
    exact ne_of_lt (by linarith)
  · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hn.2)

theorem gap1 (x : ℝ) :
    Real.sin x = 2 * Real.cos (x / 2) * Real.sin (x / 2) := by
  exact sin_half_identity x

/-- Source: `proof_gap/exercise_630/2.txt`. -/
theorem gap2 (x : ℝ) :
    2 * Real.cos (x / 2) * Real.sin (x / 2) =
      (2 : ℝ) ^ 2 * Real.cos (x / 2) * Real.cos (x / 4) *
        Real.sin (x / 4) := by
  rw [sin_half_identity (x / 2)]
  have harg : x / 2 / 2 = x / 4 := by ring
  rw [harg]
  ring

/-- Source: `proof_gap/exercise_630/3.txt`; replace the ellipsis by the three-factor case. -/
theorem gap3 (x : ℝ) :
    sineFactorization x 2 = sineFactorization x 3 := by
  exact (sineFactorization_eq x 2).symm.trans (sineFactorization_eq x 3)

/-- Source: `proof_gap/exercise_630/4.txt`; replace both product ellipses by `cosProduct`. -/
theorem gap4 (x : ℝ) (n : ℕ) :
    sineFactorization x n =
      (2 : ℝ) ^ n * cosProduct x n * Real.sin (x / (2 : ℝ) ^ n) := by
  rfl

/-- Source: `proof_gap/exercise_630/5.txt`; replace the product ellipsis by `Finset.prod`. -/
theorem gap5 (x : ℝ) (n : ℕ) :
    Real.sin x = sineFactorization x n := by
  exact sineFactorization_eq x n

/-- Source: `proof_gap/exercise_630/6.txt`; state equality of the represented limits. -/
theorem gap6 (x L : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (cosProduct x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (ratioSeq x) Filter.atTop (nhds L) := by
  have heq : cosProduct x =ᶠ[Filter.atTop] ratioSeq x := by
    filter_upwards [eventually_scaled_sine_ne_zero x hx] with n hs
    symm
    unfold ratioSeq
    rw [sineFactorization_eq x n]
    unfold sineFactorization
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp [hs, hp]
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

/-- Source: `proof_gap/exercise_630/7.txt`; exclude `x=0` from the displayed normalization. -/
theorem gap7 (x L : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (ratioSeq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (normalizedRatioSeq x) Filter.atTop (nhds L) := by
  have hfun : ratioSeq x = normalizedRatioSeq x := by
    funext n
    unfold ratioSeq normalizedRatioSeq
    by_cases hs : Real.sin (x / (2 : ℝ) ^ n) = 0
    · simp [hs]
    · have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hx, hs, hp]
  rw [hfun]

/-- Source: `proof_gap/exercise_630/8.txt`; the source quotient requires `x≠0`. -/
theorem gap8 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (normalizedRatioSeq x) Filter.atTop
      (nhds (Real.sin x / x)) := by
  have hsin :
      Filter.Tendsto
        (fun n : ℕ => Real.sin (x / (2 : ℝ) ^ n) /
          (x / (2 : ℝ) ^ n))
        Filter.atTop (nhds 1) := by
    simpa only [Function.comp_apply] using
      tendsto_sin_div_zero.comp (scaled_tendsto_punctured x hx)
  have hinv :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.sin (x / (2 : ℝ) ^ n) /
            (x / (2 : ℝ) ^ n))⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using hsin.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun n : ℕ =>
          (Real.sin (x / (2 : ℝ) ^ n) /
            (x / (2 : ℝ) ^ n))⁻¹) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          (x / (2 : ℝ) ^ n) /
            Real.sin (x / (2 : ℝ) ^ n)) := by
    filter_upwards [eventually_scaled_sine_ne_zero x hx] with n hs
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have ha : x / (2 : ℝ) ^ n ≠ 0 := div_ne_zero hx hp
    field_simp [hs, ha]
  have hquot :
      Filter.Tendsto
        (fun n : ℕ => (x / (2 : ℝ) ^ n) /
          Real.sin (x / (2 : ℝ) ^ n))
        Filter.atTop (nhds 1) :=
    hinv.congr' heq
  have hconst :
      Filter.Tendsto (fun _ : ℕ => Real.sin x / x) Filter.atTop
        (nhds (Real.sin x / x)) :=
    tendsto_const_nhds
  simpa [normalizedRatioSeq] using hquot.mul hconst

/-- Source: `proof_gap/exercise_630/9.txt`; the source quotient requires `x≠0`. -/
theorem gap9 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (cosProduct x) Filter.atTop
      (nhds (Real.sin x / x)) := by
  have hratio :
      Filter.Tendsto (ratioSeq x) Filter.atTop
        (nhds (Real.sin x / x)) :=
    (gap7 x (Real.sin x / x) hx).mpr (gap8 x hx)
  have heq :
      cosProduct x =ᶠ[Filter.atTop] ratioSeq x := by
    filter_upwards [eventually_scaled_sine_ne_zero x hx] with n hs
    symm
    unfold ratioSeq
    rw [sineFactorization_eq x n]
    unfold sineFactorization
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp [hs, hp]
  exact hratio.congr' heq.symm

/-- Source: `proof_gap/exercise_630/10.txt`. -/
theorem gap10 (x : ℝ) (n : ℕ) (hx : x = 0) :
    cosProduct x n = 1 := by
  subst x
  simp [cosProduct]

end

end ProofGap.Exercise630
