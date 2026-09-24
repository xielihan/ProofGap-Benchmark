import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2918

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℂ :=
  (Nat.factorial n : ℂ) /
    ∏ k ∈ Finset.Icc 1 n, ((1 : ℂ) + (k : ℂ) * Complex.I)

def ratioSeq (n : ℕ) : ℝ :=
  ‖coefficient n / coefficient (n + 1)‖

def complexRatioSeq (n : ℕ) : ℝ :=
  ‖(1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I‖ /
    ((n + 1 : ℕ) : ℝ)

def sqrtRatioSeq (n : ℕ) : ℝ :=
  Real.sqrt (1 + ((n + 1 : ℕ) : ℝ) ^ 2) /
    ((n + 1 : ℕ) : ℝ)

def SameLimit (u v : ℕ → ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto u atTop (𝓝 L) ∧ Tendsto v atTop (𝓝 L)

def seriesTerm (n : ℕ) (z : ℂ) : ℂ :=
  coefficient n * z ^ n

def SeriesConvergesAt (z : ℂ) : Prop :=
  Summable (fun k : ℕ => seriesTerm (k + 1) z)

def convergenceSet : Set ℂ :=
  {z | SeriesConvergesAt z}

def unitDisk : Set ℂ :=
  {z | ‖z‖ < 1}

def coordinateUnitDisk : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 < 1}

private theorem complex_natCast_norm (n : ℕ) :
    ‖(n : ℂ)‖ = (n : ℝ) := by
  rw [Complex.norm_def]
  have hsq : Complex.normSq (n : ℂ) = ((n : ℝ) ^ 2) := by
    simp [Complex.normSq, pow_two]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

private theorem coefficient_ne_zero (n : ℕ) : coefficient n ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero n
  · rw [Finset.prod_ne_zero_iff]
    intro k hk hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre

private theorem coefficient_succ (n : ℕ) :
    coefficient (n + 1) =
      coefficient n *
        ((((n + 1 : ℕ) : ℂ)) /
          ((1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I)) := by
  have hset : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
  have hterm : ∀ k : ℕ, (1 : ℂ) + (k : ℂ) * Complex.I ≠ 0 := by
    intro k hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hprod : (∏ k ∈ Finset.Icc 1 n,
      ((1 : ℂ) + (k : ℂ) * Complex.I)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact hterm k
  simp only [coefficient]
  rw [hset, Finset.prod_insert hnot, Nat.factorial_succ]
  push_cast
  field_simp [hprod, hterm] <;> ring

private theorem ratio_pointwise (n : ℕ) :
    ratioSeq n = complexRatioSeq n := by
  unfold ratioSeq complexRatioSeq
  rw [coefficient_succ]
  have ha := coefficient_ne_zero n
  have hm : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hq : (1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hdiv :
      coefficient n /
          (coefficient n *
            ((((n + 1 : ℕ) : ℂ)) /
              ((1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I))) =
        ((1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I) /
          (((n + 1 : ℕ) : ℂ)) := by
    field_simp [ha, hm, hq] <;> ring
  have hnorm :
      ‖(((n + 1 : ℕ) : ℂ))‖ = ((n + 1 : ℕ) : ℝ) :=
    complex_natCast_norm (n + 1)
  rw [hdiv, norm_div, hnorm]

private theorem complex_sqrt_pointwise (n : ℕ) :
    complexRatioSeq n = sqrtRatioSeq n := by
  simp [complexRatioSeq, sqrtRatioSeq, Complex.norm_def,
    Complex.normSq, pow_two, add_comm, add_left_comm]

private theorem sqrt_ratio_tendsto :
    Tendsto sqrtRatioSeq atTop (𝓝 1) := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    calc
      b ≤ (N : ℝ) := hN
      _ ≤ (n : ℝ) := by exact_mod_cast hn
      _ ≤ (n : ℝ) + 1 := by linarith
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm
  have hu : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hu ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by
      let m : ℝ := ((n + 1 : ℕ) : ℝ)
      have hm0 : 0 < m := by dsimp [m]; positivity
      have hs0 : 0 ≤ Real.sqrt (1 + m ^ 2) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (1 + m ^ 2)) ^ 2 = 1 + m ^ 2 :=
        Real.sq_sqrt (by positivity)
      unfold sqrtRatioSeq
      change 1 ≤ Real.sqrt (1 + m ^ 2) / m
      rw [le_div_iff₀ hm0]
      nlinarith)
  · exact Filter.Eventually.of_forall (fun n => by
      let m : ℝ := ((n + 1 : ℕ) : ℝ)
      have hm0 : 0 < m := by dsimp [m]; positivity
      have hs0 : 0 ≤ Real.sqrt (1 + m ^ 2) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (1 + m ^ 2)) ^ 2 = 1 + m ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hsle : Real.sqrt (1 + m ^ 2) ≤ m + 1 := by
        nlinarith
      unfold sqrtRatioSeq
      change Real.sqrt (1 + m ^ 2) / m ≤
        1 + (((n : ℝ) + 1)⁻¹)
      have hm_cast : m = (n : ℝ) + 1 := by
        dsimp [m]
        norm_num
      rw [← hm_cast]
      calc
        Real.sqrt (1 + m ^ 2) / m ≤ (m + 1) / m :=
          (div_le_div_iff_of_pos_right hm0).2 hsle
        _ = 1 + m⁻¹ := by field_simp)

private theorem ratio_seq_pos (n : ℕ) : 0 < ratioSeq n := by
  rw [ratio_pointwise, complex_sqrt_pointwise]
  unfold sqrtRatioSeq
  apply div_pos
  · apply Real.sqrt_pos.2
    positivity
  · positivity

private theorem coefficient_norm_lower (n : ℕ) (hn : 1 ≤ n) :
    (((n + 1 : ℕ) : ℝ) / (6 * (n : ℝ))) ≤ ‖coefficient n‖ := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hnorm : ‖coefficient 1‖ = 1 / Real.sqrt 2 := by
          norm_num [coefficient, Complex.norm_def, Complex.normSq]
        rw [hnorm]
        have hlhs :
            (((0 + 1 + 1 : ℕ) : ℝ) /
              (6 * ((0 + 1 : ℕ) : ℝ))) = (1 / 3 : ℝ) := by
          norm_num
        rw [hlhs]
        have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hs0]
        nlinarith
      · have hn1 : 1 ≤ n := by omega
        have hi := ih hn1
        rw [coefficient_succ, norm_mul, norm_div]
        have hcast : ‖(((n + 1 : ℕ) : ℂ))‖ = ((n + 1 : ℕ) : ℝ) :=
          complex_natCast_norm (n + 1)
        have hq :
            ‖(1 : ℂ) + ((n + 1 : ℕ) : ℂ) * Complex.I‖ =
              Real.sqrt (1 + (((n + 1 : ℕ) : ℝ)) ^ 2) := by
          simp [Complex.norm_def, Complex.normSq, pow_two,
            add_comm, add_left_comm]
        rw [hcast, hq]
        let x : ℝ := n
        let m : ℝ := x + 1
        let s : ℝ := Real.sqrt (1 + m ^ 2)
        have hx : 1 ≤ x := by
          dsimp [x]
          exact_mod_cast hn1
        have hm : 0 < m := by dsimp [m]; linarith
        have hs : 0 < s := by
          dsimp [s]
          exact Real.sqrt_pos.2 (by positivity)
        have hs2 : s ^ 2 = 1 + m ^ 2 := by
          dsimp [s]
          exact Real.sq_sqrt (by positivity)
        have hA : 0 ≤ x * (x + 2) := by positivity
        have hpoly :
            (x * (x + 2)) ^ 2 * (1 + m ^ 2) ≤ m ^ 6 := by
          have hxm : x * (x + 2) = m ^ 2 - 1 := by
            dsimp [m]
            ring
          rw [hxm]
          have hm2 : 4 ≤ m ^ 2 := by nlinarith
          have hm4 : 0 ≤ m ^ 4 := by positivity
          nlinarith [sq_nonneg (m ^ 2 - 1)]
        have hsq : (x * (x + 2) * s) ^ 2 ≤ (m ^ 3) ^ 2 := by
          calc
            (x * (x + 2) * s) ^ 2 =
                (x * (x + 2)) ^ 2 * (1 + m ^ 2) := by
                  rw [mul_pow, hs2]
            _ ≤ m ^ 6 := hpoly
            _ = (m ^ 3) ^ 2 := by ring
        have hcross : x * (x + 2) * s ≤ m ^ 3 := by
          nlinarith [mul_nonneg hA hs.le, pow_nonneg hm.le 3]
        have hfactor : x * (x + 2) / m ^ 2 ≤ m / s := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hm) hs]
          nlinarith
        have hnonneg : 0 ≤ x * (x + 2) / m ^ 2 := by positivity
        have hi' : m / (6 * x) ≤ ‖coefficient n‖ := by
          simpa [x, m] using hi
        have hmul :=
          mul_le_mul hi' hfactor hnonneg (norm_nonneg (coefficient n))
        have hfinal :
            (x + 2) / (6 * m) ≤ ‖coefficient n‖ * (m / s) := by
          calc
            (x + 2) / (6 * m) =
                (m / (6 * x)) * (x * (x + 2) / m ^ 2) := by
                  field_simp
            _ ≤ ‖coefficient n‖ * (m / s) := hmul
        simpa [x, m, s, add_assoc] using hfinal

private theorem series_norm_ratio (n : ℕ) (z : ℂ) :
    ‖seriesTerm (n + 2) z‖ * ratioSeq (n + 1) =
      ‖z‖ * ‖seriesTerm (n + 1) z‖ := by
  have h1 : ‖coefficient (n + 1)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (coefficient_ne_zero (n + 1))
  have h2 : ‖coefficient (n + 2)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (coefficient_ne_zero (n + 2))
  unfold seriesTerm ratioSeq
  rw [norm_div]
  simp only [norm_mul, norm_pow]
  rw [show n + 1 + 1 = n + 2 by omega, pow_succ]
  field_simp [h1, h2] <;> ring

theorem gap1 :
    SameLimit ratioSeq complexRatioSeq := by
  have hrs : ratioSeq = sqrtRatioSeq := by
    funext n
    exact (ratio_pointwise n).trans (complex_sqrt_pointwise n)
  have hcs : complexRatioSeq = sqrtRatioSeq := by
    funext n
    exact complex_sqrt_pointwise n
  refine ⟨1, ?_, ?_⟩
  · rw [hrs]
    exact sqrt_ratio_tendsto
  · rw [hcs]
    exact sqrt_ratio_tendsto

theorem gap2 :
    SameLimit complexRatioSeq sqrtRatioSeq := by
  have hcs : complexRatioSeq = sqrtRatioSeq := by
    funext n
    exact complex_sqrt_pointwise n
  refine ⟨1, ?_, sqrt_ratio_tendsto⟩
  rw [hcs]
  exact sqrt_ratio_tendsto

theorem gap3 :
    Tendsto sqrtRatioSeq atTop (𝓝 1) := by
  exact sqrt_ratio_tendsto

theorem gap4 :
    Tendsto ratioSeq atTop (𝓝 1) := by
  have hrs : ratioSeq = sqrtRatioSeq := by
    funext n
    exact (ratio_pointwise n).trans (complex_sqrt_pointwise n)
  rw [hrs]
  exact sqrt_ratio_tendsto

theorem gap5 :
    ∃ R : ℝ, R = 1 := by
  exact ⟨1, rfl⟩

theorem gap6 :
    convergenceSet = unitDisk := by
  ext z
  simp only [convergenceSet, unitDisk, Set.mem_setOf_eq]
  constructor
  · intro hsum
    change Summable (fun k : ℕ => seriesTerm (k + 1) z) at hsum
    by_contra hzlt
    have hz : 1 ≤ ‖z‖ := le_of_not_gt hzlt
    have ht : Tendsto (fun k : ℕ => ‖seriesTerm (k + 1) z‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hsum.tendsto_atTop_zero.norm
    have hev : ∀ᶠ k : ℕ in atTop, ‖seriesTerm (k + 1) z‖ < (1 / 12 : ℝ) :=
      (tendsto_order.1 ht).2 _ (by norm_num)
    rcases eventually_atTop.1 hev with ⟨N, hN⟩
    have hk := hN N (le_refl N)
    have hc := coefficient_norm_lower (N + 1) (by omega)
    have hzpow : 1 ≤ ‖z‖ ^ (N + 1) := one_le_pow₀ hz
    have hnum :
        (((N + 1 : ℕ) : ℝ)) ≤ (((N + 1 + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show N + 1 ≤ N + 1 + 1 by omega)
    have hfrac :
        (1 / 6 : ℝ) ≤
          (((N + 1 + 1 : ℕ) : ℝ) /
            (6 * ((N + 1 : ℕ) : ℝ))) := by
      calc
        (1 / 6 : ℝ) =
            (((N + 1 : ℕ) : ℝ) /
              (6 * ((N + 1 : ℕ) : ℝ))) := by
                field_simp [show (((N + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
        _ ≤ (((N + 1 + 1 : ℕ) : ℝ) /
              (6 * ((N + 1 : ℕ) : ℝ))) :=
          (div_le_div_iff_of_pos_right (by positivity)).2 hnum
    have hmul :
        (((N + 1 + 1 : ℕ) : ℝ) /
              (6 * ((N + 1 : ℕ) : ℝ))) * 1 ≤
          ‖coefficient (N + 1)‖ * ‖z‖ ^ (N + 1) :=
      mul_le_mul hc hzpow (by norm_num) (norm_nonneg _)
    have hterm : (1 / 6 : ℝ) ≤ ‖seriesTerm (N + 1) z‖ := by
      simp only [seriesTerm, norm_mul, norm_pow]
      exact hfrac.trans (by simpa only [mul_one] using hmul)
    nlinarith
  · intro hz
    change Summable (fun k : ℕ => seriesTerm (k + 1) z)
    let q : ℝ := (‖z‖ + 1) / 2
    have hq0 : 0 < q := by
      dsimp [q]
      positivity
    have hq1 : q < 1 := by
      dsimp [q]
      linarith
    have hthreshold : ‖z‖ / q < 1 := by
      rw [div_lt_one hq0]
      dsimp [q]
      linarith
    have hev0 : ∀ᶠ n : ℕ in atTop, ‖z‖ / q < ratioSeq n :=
      (tendsto_order.1 gap4).1 _ hthreshold
    rcases eventually_atTop.1 hev0 with ⟨N, hN⟩
    refine summable_of_ratio_norm_eventually_le hq1 ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hr := hN (n + 1) (by omega)
    have hr0 : 0 < ratioSeq (n + 1) := ratio_seq_pos (n + 1)
    have hsmall : ‖z‖ / ratioSeq (n + 1) < q := by
      rw [div_lt_iff₀ hr0]
      have hscaled := (div_lt_iff₀ hq0).1 hr
      nlinarith
    have heq := series_norm_ratio n z
    have hquot :
        ‖seriesTerm (n + 2) z‖ =
          (‖z‖ / ratioSeq (n + 1)) * ‖seriesTerm (n + 1) z‖ := by
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff hr0.ne').2 heq
    rw [show n + 1 + 1 = n + 2 by omega, hquot]
    exact mul_le_mul_of_nonneg_right (le_of_lt hsmall) (norm_nonneg _)

theorem gap7 :
    unitDisk = coordinateUnitDisk := by
  ext z
  simp only [unitDisk, coordinateUnitDisk, Set.mem_setOf_eq]
  rw [Complex.norm_def]
  have hsqNorm : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq, pow_two]
  rw [hsqNorm]
  have hnonneg : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have hs : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 =
      z.re ^ 2 + z.im ^ 2 := Real.sq_sqrt hnonneg
  have hs0 : 0 ≤ Real.sqrt (z.re ^ 2 + z.im ^ 2) := Real.sqrt_nonneg _
  constructor <;> intro h <;> nlinarith

theorem gap8 :
    convergenceSet = coordinateUnitDisk := by
  rw [gap6, gap7]

end

end ProofGap.Exercise2918
