import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3102

noncomputable section

open Filter
open scoped BigOperators Topology

def invPower (q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n q

def ratioError (a : ℕ → ℝ) (p : ℝ) (n : ℕ) : ℝ :=
  a n / a (n + 1) - (1 + p / n)

def ratioFactor (a : ℕ → ℝ) (p : ℝ) (n : ℕ) : ℝ :=
  a (n + 1) / a n * Real.rpow (1 + 1 / (n : ℝ)) p

def delta (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n / a (n + 1) - 1

def decay (ε : ℝ) (n : ℕ) : ℝ :=
  invPower (1 + ε) n + invPower 2 n

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => f (n + 1))

def partialProduct (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, r n

def HasProductFromOne (r : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (partialProduct r) atTop (𝓝 L)

def NonzeroConvergentProduct (r : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, L ≠ 0 ∧ HasProductFromOne r L

def powerPartialProduct (p : ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, Real.rpow (1 + 1 / (n : ℝ)) p

def SamePowerOrder (a : ℕ → ℝ) (p : ℝ) : Prop :=
  ∃ C : ℝ, C ≠ 0 ∧
    Tendsto
      (fun n : ℕ => a (n + 1) * Real.rpow (n + 1) p)
      atTop (𝓝 C)

private theorem real_log_one_add_sub_self_isBigO :
    (fun x : ℝ => Real.log (1 + x) - x) =O[𝓝 0] (fun x : ℝ => x ^ 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  refine Metric.eventually_nhds_iff.2 ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro x hx
  rw [Real.dist_eq, sub_zero] at hx
  have habs : |x| < 1 / 2 := hx
  have hlt : |-x| < 1 := by simpa using habs.trans (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le hlt 1
  norm_num [abs_neg, pow_two] at h ⊢
  have hden : 1 / (1 - |x|) ≤ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr (habs.trans (by norm_num)))]
    linarith
  calc
    |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - |x|) := by
      simpa [sub_eq_add_neg, add_comm, pow_two] using h
    _ = x ^ 2 * (1 / (1 - |x|)) := by ring
    _ ≤ x ^ 2 * 2 := mul_le_mul_of_nonneg_left hden (sq_nonneg x)
    _ = 2 * (x * x) := by ring

private theorem test_gap1 (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (ratioFactor a p n) =
        Real.log (a (n + 1) / a n) +
          p * Real.log (1 + 1 / (n : ℝ)) := by
  intro n hn
  have han : 0 < a n := ha n hn
  have hans : 0 < a (n + 1) := ha (n + 1) (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < (1 + 1 / (n : ℝ)) := by positivity
  unfold ratioFactor
  rw [Real.rpow_eq_pow]
  rw [Real.log_mul (div_ne_zero hans.ne' han.ne') (Real.rpow_pos_of_pos hbase p).ne']
  rw [Real.log_rpow hbase]

private theorem test_gap2 (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    (fun n : ℕ =>
      Real.log (ratioFactor a p (n + 1)) -
        (-Real.log (a (n + 1) / a (n + 2)) + p / (n + 1 : ℝ)))
      =O[atTop] (fun n : ℕ => invPower 2 (n + 1)) := by
  have hcomp := real_log_one_add_sub_self_isBigO.comp_tendsto
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpcomp := hcomp.const_mul_left p
  apply hpcomp.congr'
  · filter_upwards with n
    have hlog := test_gap1 a p ha (n + 1) (by omega)
    have ha1 : 0 < a (n + 1) := ha (n + 1) (by omega)
    have ha2 : 0 < a (n + 2) := ha (n + 2) (by omega)
    rw [hlog, Real.log_div ha2.ne' ha1.ne', Real.log_div ha1.ne' ha2.ne']
    push_cast
    simp only [Function.comp_apply]
    ring
  · filter_upwards with n
    unfold Function.comp invPower
    rw [Real.rpow_eq_pow, Real.rpow_two]
    push_cast
    have hnz : (1 + (n : ℝ)) ≠ 0 := by positivity
    field_simp

private theorem invPower_summable {q : ℝ} (hq : 1 < q) :
    Summable (invPower q) := by
  refine ((Real.summable_one_div_nat_rpow (p := q)).2 hq).congr ?_
  intro n
  rw [invPower, Real.rpow_eq_pow]

private theorem ratioError_tendsto_zero (a : ℕ → ℝ) (p ε : ℝ)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    Tendsto (ratioError a p) atTop (𝓝 0) := by
  exact hratio.trans_tendsto
    (invPower_summable (q := 1 + ε) (by linarith)).tendsto_atTop_zero

private theorem delta_tendsto_zero (a : ℕ → ℝ) (p ε : ℝ)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    Tendsto (delta a) atTop (𝓝 0) := by
  have hr := ratioError_tendsto_zero a p ε hε hratio
  have hp := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) p
  have hsum : Tendsto (fun n => ratioError a p n + p / (n : ℝ)) atTop (𝓝 0) := by
    simpa using hr.add hp
  apply hsum.congr'
  filter_upwards with n
  unfold ratioError delta
  ring

private theorem test_gap3 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    ∃ E₁ E₂ : ℕ → ℝ,
      E₁ =O[atTop] (fun n => (delta a n) ^ 2) ∧
      E₂ =O[atTop] (fun n => invPower 2 n) ∧
      ∀ n : ℕ, 1 ≤ n →
        Real.log (ratioFactor a p n) =
          -delta a n + E₁ n + p / (n : ℝ) + E₂ n := by
  let E₁ : ℕ → ℝ := fun n => Real.log (a (n + 1) / a n) + delta a n
  let E₂ : ℕ → ℝ := fun n => p * (Real.log (1 + 1 / (n : ℝ)) - 1 / (n : ℝ))
  have hdelta := delta_tendsto_zero a p ε hε hratio
  have hE₁base := (real_log_one_add_sub_self_isBigO.comp_tendsto hdelta).const_mul_left (-1)
  have hE₁ : E₁ =O[atTop] (fun n => (delta a n) ^ 2) := by
    apply hE₁base.congr'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have han : 0 < a n := ha n hn
      have hans : 0 < a (n + 1) := ha (n + 1) (by omega)
      have hrecip : a (n + 1) / a n = (a n / a (n + 1))⁻¹ := by
        field_simp
      have hratioeq : a n / a (n + 1) = 1 + delta a n := by
        unfold delta
        ring
      dsimp [E₁]
      rw [hrecip, Real.log_inv, hratioeq]
      ring
    · exact Eventually.of_forall fun _ => rfl
  have hE₂base := (real_log_one_add_sub_self_isBigO.comp_tendsto
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).const_mul_left p
  have hE₂ : E₂ =O[atTop] (fun n => invPower 2 n) := by
    apply hE₂base.congr'
    · exact Eventually.of_forall fun n => by
        dsimp [E₂]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      unfold Function.comp invPower
      rw [Real.rpow_eq_pow, Real.rpow_two]
      have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp
  refine ⟨E₁, E₂, hE₁, hE₂, ?_⟩
  intro n hn
  rw [test_gap1 a p ha n hn]
  dsimp [E₁, E₂]
  ring

private theorem invPower_nonneg (q : ℝ) (n : ℕ) : 0 ≤ invPower q n := by
  unfold invPower
  rw [Real.rpow_eq_pow]
  positivity

private theorem invPower_higher_isBigO_one (ε : ℝ) (hε : 0 < ε) :
    (fun n => invPower (1 + ε) n) =O[atTop] (invPower 1) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (show (1 : ℝ) ≤ 1 + ε by linarith)
  have hle : invPower (1 + ε) n ≤ invPower 1 n := by
    unfold invPower
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    exact one_div_le_one_div_of_le (by positivity) hpow
  simpa [Real.norm_eq_abs, abs_of_nonneg (invPower_nonneg _ _)] using hle

private theorem const_div_isBigO_invPower_one (p : ℝ) :
    (fun n : ℕ => p / (n : ℝ)) =O[atTop] (invPower 1) := by
  have h := (Asymptotics.isBigO_refl (invPower 1) atTop).const_mul_left p
  apply h.congr'
  · exact Eventually.of_forall fun n => by
      change p * (1 / Real.rpow (n : ℝ) 1) = p / (n : ℝ)
      rw [Real.rpow_eq_pow, Real.rpow_one]
      simp [div_eq_mul_inv]
  · exact Eventually.of_forall fun _ => rfl

private theorem delta_isBigO_invPower_one (a : ℕ → ℝ) (p ε : ℝ)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    delta a =O[atTop] invPower 1 := by
  have hr := hratio.trans (invPower_higher_isBigO_one ε hε)
  have hp := const_div_isBigO_invPower_one p
  have hadd := hr.add hp
  apply hadd.congr'
  · filter_upwards with n
    unfold ratioError delta
    ring
  · exact Eventually.of_forall fun _ => rfl

private theorem invPower_one_sq_isBigO_two :
    (fun n => (invPower 1 n) ^ 2) =O[atTop] (invPower 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have heq : (invPower 1 n) ^ 2 = invPower 2 n := by
    unfold invPower
    rw [Real.rpow_eq_pow, Real.rpow_one, Real.rpow_eq_pow, Real.rpow_two]
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  rw [heq, one_mul]

private theorem delta_sq_isBigO_invPower_two (a : ℕ → ℝ) (p ε : ℝ)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    (fun n => (delta a n) ^ 2) =O[atTop] (invPower 2) := by
  exact (delta_isBigO_invPower_one a p ε hε hratio).pow 2 |>.trans
    invPower_one_sq_isBigO_two

private theorem invPower_left_isBigO_decay (ε : ℝ) :
    (fun n => invPower (1 + ε) n) =O[atTop] decay ε := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with n
  have hdecay : 0 ≤ decay ε n := add_nonneg (invPower_nonneg _ _) (invPower_nonneg _ _)
  have hle : invPower (1 + ε) n ≤ decay ε n :=
    le_add_of_nonneg_right (invPower_nonneg _ _)
  simpa [Real.norm_eq_abs, abs_of_nonneg (invPower_nonneg _ _), abs_of_nonneg hdecay] using hle

private theorem invPower_right_isBigO_decay (ε : ℝ) :
    invPower 2 =O[atTop] decay ε := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with n
  have hdecay : 0 ≤ decay ε n := add_nonneg (invPower_nonneg _ _) (invPower_nonneg _ _)
  have hle : invPower 2 n ≤ decay ε n :=
    le_add_of_nonneg_left (invPower_nonneg _ _)
  simpa [Real.norm_eq_abs, abs_of_nonneg (invPower_nonneg _ _), abs_of_nonneg hdecay] using hle

private theorem test_gap4 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    (fun n => Real.log (ratioFactor a p n)) =O[atTop] decay ε := by
  obtain ⟨E₁, E₂, hE₁, hE₂, heq⟩ := test_gap3 a p ε ha hε hratio
  have hE₁' := hE₁.trans (delta_sq_isBigO_invPower_two a p ε hε hratio)
  have hr' := (hratio.const_mul_left (-1)).trans (invPower_left_isBigO_decay ε)
  have hE₁'' := hE₁'.trans (invPower_right_isBigO_decay ε)
  have hE₂' := hE₂.trans (invPower_right_isBigO_decay ε)
  have hsum := (hr'.add hE₁'').add hE₂'
  apply hsum.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [heq n hn]
    unfold ratioError delta
    ring
  · exact Eventually.of_forall fun _ => rfl

private theorem decay_summable (ε : ℝ) (hε : 0 < ε) :
    Summable (decay ε) := by
  simpa [decay] using
    (invPower_summable (q := 1 + ε) (by linarith)).add
      (invPower_summable (q := 2) (by norm_num))

private theorem test_gap5 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    SummableFromOne (fun n => Real.log (ratioFactor a p n)) := by
  have hbig := (test_gap4 a p ε ha hε hratio).comp_tendsto (tendsto_add_atTop_nat 1)
  have hsum : Summable (fun n => decay ε (n + 1)) :=
    (summable_nat_add_iff 1).2 (decay_summable ε hε)
  unfold SummableFromOne
  exact summable_of_isBigO_nat hsum (by simpa [Function.comp_def] using hbig)

private theorem partialProduct_eq_prod_range_shift (r : ℕ → ℝ) (N : ℕ) :
    partialProduct r N = ∏ n ∈ Finset.range N, r (n + 1) := by
  unfold partialProduct
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
    ext n
    simp]
  rw [Finset.prod_Ico_eq_prod_range]
  simp [Nat.add_comm]

private theorem ratioFactor_pos (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    ∀ n : ℕ, 1 ≤ n → 0 < ratioFactor a p n := by
  intro n hn
  unfold ratioFactor
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact mul_pos (div_pos (ha (n + 1) (by omega)) (ha n hn))
    (by rw [Real.rpow_eq_pow]; exact Real.rpow_pos_of_pos (by positivity) p)

private theorem hasProductFromOne_of_summable_log (r : ℕ → ℝ)
    (hrpos : ∀ n : ℕ, 1 ≤ n → 0 < r n)
    (hlog : SummableFromOne (fun n => Real.log (r n))) :
    HasProductFromOne r (Real.exp (∑' n : ℕ, Real.log (r (n + 1)))) := by
  have hpos : ∀ n : ℕ, 0 < r (n + 1) := fun n => hrpos (n + 1) (by omega)
  have hs : Summable (fun n : ℕ => Real.log (r (n + 1))) := by
    exact hlog
  have hp := Real.hasProd_of_hasSum_log hpos hs.hasSum
  unfold HasProductFromOne
  apply hp.tendsto_prod_nat.congr'
  filter_upwards with N
  exact (partialProduct_eq_prod_range_shift r N).symm

private theorem test_gap6 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio : ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    NonzeroConvergentProduct (ratioFactor a p) := by
  let L := Real.exp (∑' n : ℕ, Real.log (ratioFactor a p (n + 1)))
  refine ⟨L, Real.exp_ne_zero _, ?_⟩
  exact hasProductFromOne_of_summable_log (ratioFactor a p)
    (ratioFactor_pos a p ha) (test_gap5 a p ε ha hε hratio)

private theorem test_gap7 (r : ℕ → ℝ) (k₀ : ℝ)
    (hrpos : ∀ n : ℕ, 1 ≤ n → 0 < r n)
    (hlog : SummableFromOne (fun n => Real.log (r n)))
    (hk : HasProductFromOne r k₀) :
    k₀ ≠ 0 := by
  have hexp := hasProductFromOne_of_summable_log r hrpos hlog
  have heq : k₀ = Real.exp (∑' n : ℕ, Real.log (r (n + 1))) := by
    exact tendsto_nhds_unique hk hexp
  rw [heq]
  exact Real.exp_ne_zero _

private theorem test_gap8 (a r P : ℕ → ℝ) (k₀ : ℝ)
    (hP : ∀ N, P N = a 1 * partialProduct r N)
    (hk : HasProductFromOne r k₀) :
    Tendsto P atTop (𝓝 (a 1 * k₀)) := by
  apply (tendsto_const_nhds.mul hk).congr'
  exact Eventually.of_forall fun N => (hP N).symm

private theorem ratio_partialProduct_telescope (a : ℕ → ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) (N : ℕ) :
    partialProduct (fun n => a (n + 1) / a n) N = a (N + 1) / a 1 := by
  rw [partialProduct_eq_prod_range_shift]
  induction N with
  | zero => simp [ha 1 (by omega) |>.ne']
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      have h1 : a 1 ≠ 0 := (ha 1 (by omega)).ne'
      have hN : a (N + 1) ≠ 0 := (ha (N + 1) (by omega)).ne'
      field_simp

private theorem ratioFactor_partialProduct_telescope (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) (N : ℕ) :
    a 1 * partialProduct (ratioFactor a p) N =
      a (N + 1) * powerPartialProduct p N := by
  unfold partialProduct ratioFactor powerPartialProduct
  rw [Finset.prod_mul_distrib]
  have htel := ratio_partialProduct_telescope a ha N
  unfold partialProduct at htel
  rw [htel]
  have h1 : a 1 ≠ 0 := (ha 1 (by omega)).ne'
  field_simp

private theorem test_gap9 (a P : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hP : ∀ N, P N = a 1 * partialProduct (ratioFactor a p) N) :
    ∀ N : ℕ, P N = a (N + 1) * powerPartialProduct p N := by
  intro N
  rw [hP N]
  exact ratioFactor_partialProduct_telescope a p ha N

private theorem test_gap10 (p : ℝ) :
    ∃ G : ℕ → ℝ, ∀ N : ℕ, 1 ≤ N →
      powerPartialProduct p N = Real.rpow N p * G N := by
  refine ⟨fun N => powerPartialProduct p N / Real.rpow N p, ?_⟩
  intro N hN
  have hpow : Real.rpow N p ≠ 0 := by
    rw [Real.rpow_eq_pow]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) p).ne'
  field_simp

private theorem one_add_inv_partialProduct (N : ℕ) :
    (∏ n ∈ Finset.Icc 1 N, (1 + 1 / (n : ℝ))) = (N + 1 : ℕ) := by
  have ht := ratio_partialProduct_telescope (fun n : ℕ => (n : ℝ))
    (fun n hn => by
      change (0 : ℝ) < (n : ℝ)
      exact_mod_cast (show 0 < n by omega)) N
  unfold partialProduct at ht
  calc
    (∏ n ∈ Finset.Icc 1 N, (1 + 1 / (n : ℝ))) =
        ∏ n ∈ Finset.Icc 1 N, ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      apply Finset.prod_congr rfl
      intro n hn
      have hmem : 1 ≤ n ∧ n ≤ N := by simpa using hn
      have hnpos : 0 < n := by omega
      have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      push_cast
      field_simp
    _ = ((N + 1 : ℕ) : ℝ) / (1 : ℝ) := by simpa using ht
    _ = (N + 1 : ℕ) := by norm_num

private theorem powerPartialProduct_eq_rpow_succ (p : ℝ) (N : ℕ) :
    powerPartialProduct p N = Real.rpow (N + 1 : ℕ) p := by
  unfold powerPartialProduct
  simp only [Real.rpow_eq_pow]
  rw [Real.finset_prod_rpow]
  · rw [one_add_inv_partialProduct]
  · intro n hn
    positivity

private theorem rpow_succ_factorization (p : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Real.rpow (N + 1 : ℕ) p =
      Real.rpow N p * Real.rpow (1 + 1 / (N : ℝ)) p := by
  simp only [Real.rpow_eq_pow]
  have hbase : ((N + 1 : ℕ) : ℝ) = (N : ℝ) * (1 + 1 / (N : ℝ)) := by
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  rw [hbase, Real.mul_rpow (Nat.cast_nonneg N) (by positivity)]

private theorem one_add_inv_rpow_tendsto_one (p : ℝ) :
    Tendsto (fun N : ℕ => Real.rpow (1 + 1 / (N : ℝ)) p) atTop (𝓝 1) := by
  have hbase : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hp : Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) ^ p) atTop (𝓝 ((1 : ℝ) ^ p)) :=
    hbase.rpow_const (Or.inl one_ne_zero)
  simpa [Real.rpow_eq_pow] using hp

private theorem test_gap11 (p : ℝ) :
    ∃ (G : ℕ → ℝ) (C₀ : ℝ),
      (∀ N : ℕ, 1 ≤ N →
        powerPartialProduct p N = Real.rpow N p * G N) ∧
      Tendsto G atTop (𝓝 (Real.exp (C₀ * p))) := by
  refine ⟨fun N => Real.rpow (1 + 1 / (N : ℝ)) p, 0, ?_, ?_⟩
  · intro N hN
    rw [powerPartialProduct_eq_rpow_succ]
    exact rpow_succ_factorization p N hN
  · simpa using one_add_inv_rpow_tendsto_one p

private theorem test_gap12 (a P G : ℕ → ℝ) (p k₀ C₀ : ℝ)
    (hP : Tendsto P atTop (𝓝 (a 1 * k₀)))
    (hdecomp : ∀ N : ℕ, 1 ≤ N →
      P N = a (N + 1) * Real.rpow N p * G N)
    (hG : Tendsto G atTop (𝓝 (Real.exp (C₀ * p)))) :
    Tendsto
      (fun N : ℕ => a (N + 1) * Real.rpow N p)
      atTop (𝓝 ((a 1 * k₀) / Real.exp (C₀ * p))) := by
  have hdiv := hP.div hG (Real.exp_ne_zero _)
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 1, hG.eventually_ne (Real.exp_ne_zero _)] with N hN hGN
  change P N / G N = a (N + 1) * Real.rpow N p
  rw [hdecomp N hN]
  field_simp

private theorem test_gap13 (a : ℕ → ℝ) (p C : ℝ) (hC : C ≠ 0)
    (hscaled : Tendsto
      (fun n : ℕ => a (n + 1) * Real.rpow n p)
      atTop (𝓝 C)) :
    SamePowerOrder a p := by
  unfold SamePowerOrder
  refine ⟨C, hC, ?_⟩
  have hmul := hscaled.mul (one_add_inv_rpow_tendsto_one p)
  have hmul' : Tendsto
      (fun n : ℕ => (a (n + 1) * Real.rpow n p) *
        Real.rpow (1 + 1 / (n : ℝ)) p)
      atTop (𝓝 C) := by simpa using hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hfac : Real.rpow ((n : ℝ) + 1) p =
      Real.rpow n p * Real.rpow (1 + 1 / (n : ℝ)) p := by
    simpa using rpow_succ_factorization p n hn
  rw [hfac]
  ring

private theorem test_gap14 (a : ℕ → ℝ) (p : ℝ)
    (horder : SamePowerOrder a p) :
    SamePowerOrder a p := by
  exact horder

/-- Exercise 3102, gap 1; all divisions start at `n = 1`. -/
theorem gap1 (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (ratioFactor a p n) =
        Real.log (a (n + 1) / a n) +
          p * Real.log (1 + 1 / (n : ℝ)) := by
  exact test_gap1 a p ha

/--
Exercise 3102, gap 2; the source's `O(n⁻²)` placeholder is
represented as a function-level estimate.
-/
theorem gap2 (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    (fun n : ℕ =>
      Real.log (ratioFactor a p (n + 1)) -
        (-Real.log (a (n + 1) / a (n + 2)) + p / (n + 1 : ℝ)))
      =O[atTop] (fun n : ℕ => invPower 2 (n + 1)) := by
  exact test_gap2 a p ha

/--
Exercise 3102, gap 3; the two big-O terms are made into
separate remainder functions.
-/
theorem gap3 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio :
      ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    ∃ E₁ E₂ : ℕ → ℝ,
      E₁ =O[atTop] (fun n => (delta a n) ^ 2) ∧
      E₂ =O[atTop] (fun n => invPower 2 n) ∧
      ∀ n : ℕ, 1 ≤ n →
        Real.log (ratioFactor a p n) =
          -delta a n + E₁ n + p / (n : ℝ) + E₂ n := by
  exact test_gap3 a p ε ha hε hratio

/--
Exercise 3102, gap 4; retain both the supplied
`n⁻(1+ε)` error and the logarithmic `n⁻²` error.
-/
theorem gap4 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio :
      ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    (fun n => Real.log (ratioFactor a p n)) =O[atTop] decay ε := by
  exact test_gap4 a p ε ha hε hratio

/-- Exercise 3102, gap 5; sum from the first positive index. -/
theorem gap5 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio :
      ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    SummableFromOne (fun n => Real.log (ratioFactor a p n)) := by
  exact test_gap5 a p ε ha hε hratio

/--
Exercise 3102, gap 6; this is convergence of the infinite
product, not summability of its factors.
-/
theorem gap6 (a : ℕ → ℝ) (p ε : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hε : 0 < ε)
    (hratio :
      ratioError a p =O[atTop] (fun n => invPower (1 + ε) n)) :
    NonzeroConvergentProduct (ratioFactor a p) := by
  exact test_gap6 a p ε ha hε hratio

/--
Exercise 3102, gap 7; convergence of the logarithms and
positivity of the factors supply the nonzero product limit.
-/
theorem gap7 (r : ℕ → ℝ) (k₀ : ℝ)
    (hrpos : ∀ n : ℕ, 1 ≤ n → 0 < r n)
    (hlog : SummableFromOne (fun n => Real.log (r n)))
    (hk : HasProductFromOne r k₀) :
    k₀ ≠ 0 := by
  exact test_gap7 r k₀ hrpos hlog hk

/-- Exercise 3102, gap 8. -/
theorem gap8 (a r P : ℕ → ℝ) (k₀ : ℝ)
    (hP : ∀ N, P N = a 1 * partialProduct r N)
    (hk : HasProductFromOne r k₀) :
    Tendsto P atTop (𝓝 (a 1 * k₀)) := by
  exact test_gap8 a r P k₀ hP hk

/-- Exercise 3102, gap 9; the finite product telescopes. -/
theorem gap9 (a P : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hP : ∀ N, P N = a 1 * partialProduct (ratioFactor a p) N) :
    ∀ N : ℕ,
      P N = a (N + 1) * powerPartialProduct p N := by
  exact test_gap9 a P p ha hP

/-- Exercise 3102, gap 10; exclude `N = 0` from `N^p`. -/
theorem gap10 (p : ℝ) :
    ∃ G : ℕ → ℝ, ∀ N : ℕ, 1 ≤ N →
      powerPartialProduct p N = Real.rpow N p * G N := by
  exact test_gap10 p

/--
Exercise 3102, gap 11; the convergent `G` is the same
function used in the preceding factorization.
-/
theorem gap11 (p : ℝ) :
    ∃ (G : ℕ → ℝ) (C₀ : ℝ),
      (∀ N : ℕ, 1 ≤ N →
        powerPartialProduct p N = Real.rpow N p * G N) ∧
      Tendsto G atTop (𝓝 (Real.exp (C₀ * p))) := by
  exact test_gap11 p

/-- Exercise 3102, gap 12; retain the linked product factorization. -/
theorem gap12 (a P G : ℕ → ℝ) (p k₀ C₀ : ℝ)
    (hP : Tendsto P atTop (𝓝 (a 1 * k₀)))
    (hdecomp :
      ∀ N : ℕ, 1 ≤ N →
        P N = a (N + 1) * Real.rpow N p * G N)
    (hG : Tendsto G atTop (𝓝 (Real.exp (C₀ * p)))) :
    Tendsto
      (fun N : ℕ => a (N + 1) * Real.rpow N p)
      atTop (𝓝 ((a 1 * k₀) / Real.exp (C₀ * p))) := by
  exact test_gap12 a P G p k₀ C₀ hP hdecomp hG

/--
Exercise 3102, gap 13; `O*` means asymptotic order up to a
nonzero constant, not ratio tending specifically to one.
-/
theorem gap13 (a : ℕ → ℝ) (p C : ℝ) (hC : C ≠ 0)
    (hscaled :
      Tendsto
        (fun n : ℕ => a (n + 1) * Real.rpow n p)
        atTop (𝓝 C)) :
    SamePowerOrder a p := by
  exact test_gap13 a p C hC hscaled

/-- Exercise 3102, gap 14; the final index rename changes no semantics. -/
theorem gap14 (a : ℕ → ℝ) (p : ℝ)
    (horder : SamePowerOrder a p) :
    SamePowerOrder a p := by
  exact test_gap14 a p horder

end

end ProofGap.Exercise3102
