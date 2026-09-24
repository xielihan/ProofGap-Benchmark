import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2761

noncomputable section

open Filter
open scoped Topology

def rootTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def term (n : ℕ) (x : ℝ) : ℝ :=
  n * (rootTerm n x - 1)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem Real.tendsto_nat_mul_rpow_sub_one_atTop
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.rpow x (1 / (n : ℝ)) - 1))
      atTop (𝓝 (Real.log x)) := by
  by_cases hlog : Real.log x = 0
  · have hx1 : x = 1 :=
      Real.strictMonoOn_log.injOn
        (by
          change (0 : ℝ) < x
          exact hx)
        (by
          change (0 : ℝ) < (1 : ℝ)
          exact zero_lt_one)
        (by simpa using hlog)
    subst x
    simp
  · have hz :
        Tendsto (fun n : ℕ => Real.log x / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hz' :
        Tendsto (fun n : ℕ => Real.log x / (n : ℝ)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hz, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      exact Set.mem_compl_singleton_iff.mpr (div_ne_zero hlog hn')
    have hsl : Tendsto (slope Real.exp 0) (𝓝[≠] 0) (𝓝 1) :=
      hasDerivAt_iff_tendsto_slope.mp (by simpa using (Real.hasDerivAt_exp 0))
    have hlim :
        Tendsto
          (fun n : ℕ => Real.log x * slope Real.exp 0 (Real.log x / (n : ℝ)))
          atTop (𝓝 (Real.log x * 1)) :=
      tendsto_const_nhds.mul (hsl.comp hz')
    have heq :
        (fun n : ℕ => (n : ℝ) * (Real.rpow x (1 / (n : ℝ)) - 1)) =ᶠ[atTop]
          (fun n : ℕ => Real.log x * slope Real.exp 0 (Real.log x / (n : ℝ))) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      change (n : ℝ) * (x ^ (1 / (n : ℝ) : ℝ) - 1) =
        Real.log x * slope Real.exp 0 (Real.log x / (n : ℝ))
      rw [Real.rpow_def_of_pos hx]
      have harg :
          Real.log x * (1 / (n : ℝ)) = Real.log x / (n : ℝ) := by
        ring
      rw [harg]
      dsimp [slope]
      simp only [Real.exp_zero]
      field_simp [hn', hlog] <;> ring
    simpa only [mul_one] using hlim.congr' heq.symm

private theorem private_exp_second_order_bound
    (L t : ℝ) (ht0 : 0 ≤ t) (htL : t ≤ L) :
    |Real.exp t - 1 - t - t ^ 2 / 2| ≤ Real.exp L * t ^ 3 := by
  by_cases ht : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  let g₀ : ℝ → ℝ := fun z => Real.exp z - 1 - z - z ^ 2 / 2
  let g₁ : ℝ → ℝ := fun z => Real.exp z - 1 - z
  let g₂ : ℝ → ℝ := fun z => Real.exp z - 1
  have hd₀ (z : ℝ) : HasDerivAt g₀ (g₁ z) z := by
    dsimp [g₀, g₁]
    convert (((Real.hasDerivAt_exp z).sub_const 1).sub (hasDerivAt_id z)).sub
      (((hasDerivAt_id z).pow 2).div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hd₁ (z : ℝ) : HasDerivAt g₁ (g₂ z) z := by
    dsimp [g₁, g₂]
    convert ((Real.hasDerivAt_exp z).sub_const 1).sub (hasDerivAt_id z) using 1 <;>
      simp only [id_eq] <;> ring
  have hd₂ (z : ℝ) : HasDerivAt g₂ (Real.exp z) z := by
    dsimp [g₂]
    simpa using (Real.hasDerivAt_exp z).sub_const 1
  have hdiff₀ : Differentiable ℝ g₀ := fun z => (hd₀ z).differentiableAt
  obtain ⟨c, hc, hcSlope⟩ := exists_deriv_eq_slope g₀ htpos
    hdiff₀.continuous.continuousOn hdiff₀.differentiableOn
  have hcpos : 0 < c := hc.1
  have hct : c < t := hc.2
  have heq₀ : g₀ t = t * g₁ c := by
    rw [(hd₀ c).deriv] at hcSlope
    have hcSlope' : g₁ c = g₀ t / t := by
      simpa [slope, g₀] using hcSlope
    rw [hcSlope']
    field_simp [ne_of_gt htpos]
  have hdiff₁ : Differentiable ℝ g₁ := fun z => (hd₁ z).differentiableAt
  obtain ⟨d, hd, hdSlope⟩ := exists_deriv_eq_slope g₁ hcpos
    hdiff₁.continuous.continuousOn hdiff₁.differentiableOn
  have hdpos : 0 < d := hd.1
  have hdc : d < c := hd.2
  have heq₁ : g₁ c = c * g₂ d := by
    rw [(hd₁ d).deriv] at hdSlope
    have hdSlope' : g₂ d = g₁ c / c := by
      simpa [slope, g₁] using hdSlope
    rw [hdSlope']
    field_simp [ne_of_gt hcpos]
  have hdiff₂ : Differentiable ℝ g₂ := fun z => (hd₂ z).differentiableAt
  obtain ⟨e, he, heSlope⟩ := exists_deriv_eq_slope g₂ hdpos
    hdiff₂.continuous.continuousOn hdiff₂.differentiableOn
  have hepos : 0 < e := he.1
  have hed : e < d := he.2
  have heq₂ : g₂ d = d * Real.exp e := by
    rw [(hd₂ e).deriv] at heSlope
    have heSlope' : Real.exp e = g₂ d / d := by
      simpa [slope, g₂] using heSlope
    rw [heSlope']
    field_simp [ne_of_gt hdpos]
  have hformula : g₀ t = t * c * d * Real.exp e := by
    rw [heq₀, heq₁, heq₂]
    ring
  have hnonneg : 0 ≤ t * c * d * Real.exp e := by positivity
  have heL : e ≤ L := by linarith
  have hexp : Real.exp e ≤ Real.exp L := Real.exp_le_exp.mpr heL
  have hprod : t * c * d ≤ t ^ 3 := by
    have hc0 : 0 ≤ c := le_of_lt hcpos
    have hd0 : 0 ≤ d := le_of_lt hdpos
    have hct' : c ≤ t := le_of_lt hct
    have hdt : d ≤ t := le_trans (le_of_lt hdc) hct'
    calc
      t * c * d ≤ t * t * t := by gcongr
      _ = t ^ 3 := by ring
  dsimp [g₀] at hformula
  rw [hformula, abs_of_nonneg hnonneg]
  calc
    t * c * d * Real.exp e ≤ t ^ 3 * Real.exp e :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg e)
    _ ≤ t ^ 3 * Real.exp L :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp L * t ^ 3 := by ring

private theorem Real.exists_uniform_rpow_second_order_estimate
    (a : ℝ) (ha : 1 ≤ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x ∈ Set.Icc 1 a,
        |term n x - Real.log x -
          (Real.log x) ^ 2 / (2 * n)| ≤ K / (n : ℝ) ^ 2 := by
  let L : ℝ := Real.log a
  let K : ℝ := Real.exp L * L ^ 3
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg ha
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, 1, ?_⟩
  intro n hn x hx
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
  have hlogL : Real.log x ≤ L := by
    dsimp [L]
    exact Real.strictMonoOn_log.monotoneOn hxpos
      (lt_of_lt_of_le zero_lt_one ha) hx.2
  let t : ℝ := Real.log x / (n : ℝ)
  have ht0 : 0 ≤ t := div_nonneg hlog0 (le_of_lt hnpos)
  have htL : t ≤ L := by
    dsimp [t]
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : Real.log x / (n : ℝ) ≤ Real.log x := by
      exact div_le_self hlog0 hnone
    exact hdiv.trans hlogL
  have hrem := private_exp_second_order_bound L t ht0 htL
  have hrpow : rootTerm n x = Real.exp t := by
    unfold rootTerm
    change x ^ (1 / (n : ℝ) : ℝ) = Real.exp t
    rw [Real.rpow_def_of_pos hxpos] <;> simp [t, div_eq_mul_inv]
  have halg :
      term n x - Real.log x - (Real.log x) ^ 2 / (2 * n) =
        (n : ℝ) * (Real.exp t - 1 - t - t ^ 2 / 2) := by
    unfold term
    rw [hrpow]
    dsimp [t]
    field_simp [hn']
  rw [halg, abs_mul, abs_of_pos hnpos]
  calc
    (n : ℝ) * |Real.exp t - 1 - t - t ^ 2 / 2|
        ≤ (n : ℝ) * (Real.exp L * t ^ 3) :=
          mul_le_mul_of_nonneg_left hrem (le_of_lt hnpos)
    _ = Real.exp L * (Real.log x) ^ 3 / (n : ℝ) ^ 2 := by
      dsimp [t]
      field_simp [hn']
    _ ≤ Real.exp L * L ^ 3 / (n : ℝ) ^ 2 := by
      have hcube : (Real.log x) ^ 3 ≤ L ^ 3 := by
        gcongr
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (Real.exp_nonneg L)) (sq_nonneg _)
    _ = K / (n : ℝ) ^ 2 := by rfl

theorem gap1 :
    ∀ (a x : ℝ), 1 ≤ a → x ∈ Set.Icc 1 a →
      (fun n : ℕ => term n x) =
        (fun n : ℕ => (rootTerm n x - 1) / (1 / (n : ℝ))) := by
  intro a x ha hx
  funext n
  by_cases hn : n = 0
  · simp [term, hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold term
    field_simp [hn']

theorem gap2 :
    ∀ (a x : ℝ), 1 ≤ a → x ∈ Set.Icc 1 a →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.log x)) := by
  intro a x ha hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  simpa [term, rootTerm] using
    (Real.tendsto_nat_mul_rpow_sub_one_atTop hxpos)

theorem gap3 :
    ∀ (a x : ℝ), 1 ≤ a → x ∈ Set.Icc 1 a →
      Real.log x = Real.log x := by
  intros
  rfl

theorem gap4 :
    ∀ (a x : ℝ), 1 ≤ a → x ∈ Set.Icc 1 a →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.log x)) := by
  exact gap2

theorem gap5 :
    ∀ (a x : ℝ) (n : ℕ), 1 ≤ a → x ∈ Set.Icc 1 a → 0 < n →
      |term n x - Real.log x| =
        |n * (rootTerm n x - 1) -
          n * Real.log (1 + rootTerm n x - 1)| := by
  intro a x n ha hx hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hroot :
      Real.log (rootTerm n x) = Real.log x / (n : ℝ) := by
    unfold rootTerm
    change Real.log (x ^ (1 / (n : ℝ) : ℝ)) = Real.log x / (n : ℝ)
    rw [Real.rpow_def_of_pos hxpos, Real.log_exp] <;>
      field_simp [hn'] <;> ring
  have hinside : 1 + rootTerm n x - 1 = rootTerm n x := by ring
  rw [hinside, hroot]
  unfold term
  congr 1
  field_simp [hn']

theorem gap6 :
    ∀ a : ℝ, 1 ≤ a →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x ∈ Set.Icc 1 a,
          |term n x - Real.log x -
            (Real.log x) ^ 2 / (2 * n)| ≤ K / (n : ℝ) ^ 2 := by
  intro a ha
  exact Real.exists_uniform_rpow_second_order_estimate a ha

theorem gap7 :
    ∀ a : ℝ, 1 ≤ a →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x ∈ Set.Icc 1 a,
          |term n x - Real.log x| ≤
            (Real.log a) ^ 2 / (2 * n) + K / (n : ℝ) ^ 2 := by
  intro a ha
  obtain ⟨K, hK, N, hN⟩ := gap6 a ha
  refine ⟨K, hK, max N 1, ?_⟩
  intro n hn x hx
  have hnN : N ≤ n := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hrem := hN n hnN x hx
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlogle : Real.log x ≤ Real.log a :=
    Real.strictMonoOn_log.monotoneOn hxpos hapos hx.2
  have hsq : (Real.log x) ^ 2 ≤ (Real.log a) ^ 2 := by nlinarith
  calc
    |term n x - Real.log x| =
        |(term n x - Real.log x - (Real.log x) ^ 2 / (2 * n)) +
          (Real.log x) ^ 2 / (2 * n)| := by ring
    _ ≤ |term n x - Real.log x - (Real.log x) ^ 2 / (2 * n)| +
          |(Real.log x) ^ 2 / (2 * n)| := abs_add_le _ _
    _ ≤ K / (n : ℝ) ^ 2 + (Real.log x) ^ 2 / (2 * n) := by
      apply add_le_add hrem
      rw [abs_of_nonneg]
      positivity
    _ ≤ K / (n : ℝ) ^ 2 + (Real.log a) ^ 2 / (2 * n) := by
      gcongr
    _ = (Real.log a) ^ 2 / (2 * n) + K / (n : ℝ) ^ 2 := by ring

theorem gap8 :
    ∀ a : ℝ, 1 ≤ a →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x ∈ Set.Icc 1 a,
          |term n x - Real.log x| <
            (Real.log a) ^ 2 / (n : ℝ) + K / (n : ℝ) ^ 2 := by
  intro a ha
  obtain ⟨K, hK, N, hN⟩ := gap7 a ha
  refine ⟨K + 1, by linarith, max N 1, ?_⟩
  intro n hn x hx
  have hnN : N ≤ n := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have h := hN n hnN x hx
  have hfirst : (Real.log a) ^ 2 / (2 * n) ≤ (Real.log a) ^ 2 / (n : ℝ) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hnpos
    nlinarith
  have hsecond : K / (n : ℝ) ^ 2 < (K + 1) / (n : ℝ) ^ 2 := by
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).2
    linarith
  linarith

theorem gap9 :
    ∀ a : ℝ, 1 ≤ a →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x ∈ Set.Icc 1 a,
          |term n x - Real.log x| <
            (Real.log a) ^ 2 / (n : ℝ) + K / (n : ℝ) ^ 2 := by
  exact gap8

theorem gap10 : ∃ A : ℝ, 0 < A := by
  exact ⟨1, by norm_num⟩

theorem gap11 :
    ∀ a : ℝ, 1 ≤ a →
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x ∈ Set.Icc 1 a,
          |term n x - Real.log x| <
            (Real.log a) ^ 2 / (n : ℝ) + A / (n : ℝ) ^ 2 := by
  intro a ha
  obtain ⟨K, hK, N, hN⟩ := gap9 a ha
  refine ⟨K + 1, by linarith, max N 1, ?_⟩
  intro n hn x hx
  have hnN : N ≤ n := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have h := hN n hnN x hx
  have hKA : K / (n : ℝ) ^ 2 < (K + 1) / (n : ℝ) ^ 2 := by
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).2
    linarith
  linarith

theorem gap12 :
    ∀ (a A ε : ℝ), 1 ≤ a → 0 ≤ A → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        (Real.log a) ^ 2 / (n : ℝ) + A / (n : ℝ) ^ 2 < ε := by
  intro a A ε ha hA hε
  let C : ℝ := (Real.log a) ^ 2 + A
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / ε))
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnlarge : max 1 (C / ε) < (n : ℝ) := lt_trans hN hcast
  have hn1 : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hnlarge
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hClt : C < ε * (n : ℝ) := by
    have hquot : C / ε < (n : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hnlarge
    simpa only [mul_comm] using ((div_lt_iff₀ hε).mp hquot)
  have hAdiv : A / (n : ℝ) ^ 2 ≤ A / (n : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) hnpos).2
    nlinarith [mul_nonneg hA (sub_nonneg.mpr (le_of_lt hn1))]
  have hsum :
      (Real.log a) ^ 2 / (n : ℝ) + A / (n : ℝ) ^ 2 ≤ C / (n : ℝ) := by
    calc
      (Real.log a) ^ 2 / (n : ℝ) + A / (n : ℝ) ^ 2
          ≤ (Real.log a) ^ 2 / (n : ℝ) + A / (n : ℝ) :=
            add_le_add_right hAdiv _
      _ = C / (n : ℝ) := by simp [C, add_div]
  have hCdiv : C / (n : ℝ) < ε := by
    exact (div_lt_iff₀ hnpos).2 hClt
  exact lt_of_le_of_lt hsum hCdiv

theorem gap13 :
    ∀ (a ε : ℝ), 1 ≤ a → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Icc 1 a, |term n x - Real.log x| < ε := by
  intro a ε ha hε
  obtain ⟨A, hA, N₁, hN₁⟩ := gap11 a ha
  obtain ⟨N₂, hN₂⟩ := gap12 a A ε ha (le_of_lt hA) hε
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn x hx
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ < n := by omega
  exact lt_trans (hN₁ n hn₁ x hx) (hN₂ n hn₂)

theorem gap14 :
    ∀ a : ℝ, 1 ≤ a →
      UniformlyConvergesOn term Real.log (Set.Icc 1 a) := by
  intro a ha
  unfold UniformlyConvergesOn
  intro ε hε
  exact gap13 a ε ha hε

theorem gap15 :
    ∀ a : ℝ, 1 ≤ a →
      UniformlyConvergesOn term Real.log (Set.Icc 1 a) := by
  exact gap14

end

end ProofGap.Exercise2761
