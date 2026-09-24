import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise2635

noncomputable section

open Filter
open scoped Asymptotics

def logSinRatio (x : ℝ) : ℝ :=
  Real.log (Real.sin x) / Real.log x

def term (n : ℕ) : ℝ :=
  1 / Real.log (Real.sin (1 / (n : ℝ))) ^ 2

def model (n : ℕ) : ℝ :=
  1 / Real.log (1 / (n : ℝ)) ^ 2

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    model n / term n = logSinRatio (1 / (n : ℝ)) ^ 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp [model, term, logSinRatio]
  · have hn2 : 2 ≤ n := by omega
    have hxpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have hxlt : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      exact_mod_cast (show 1 < n by omega)
    have hsinpos : 0 < Real.sin (1 / (n : ℝ)) :=
      Real.sin_pos_of_pos_of_lt_pi hxpos (hxlt.trans_le (by linarith [Real.two_le_pi]))
    have hsinlt : Real.sin (1 / (n : ℝ)) < 1 :=
      (Real.sin_lt hxpos).trans hxlt
    have hlogx : Real.log (1 / (n : ℝ)) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hxpos hxlt.ne
    have hlogsin : Real.log (Real.sin (1 / (n : ℝ))) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hsinpos hsinlt.ne
    unfold model term logSinRatio
    field_simp

theorem gap2 :
    Tendsto (fun n : ℕ => logSinRatio (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) ∧
    Tendsto logSinRatio (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsin :
      (fun x : ℝ => Real.sin x) ~[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x) := by
    simpa only [id_eq] using Real.isEquivalent_sin.mono inf_le_left
  have hlogInv := hsin.inv.log tendsto_inv_nhdsGT_zero
  have hlog :
      (fun x : ℝ => Real.log (Real.sin x)) ~[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => Real.log x) := by
    simpa only [Pi.inv_apply, Real.log_inv, neg_neg] using hlogInv.neg
  have hlogNe : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), Real.log x ≠ 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually_ne_atBot 0
  have hcont :
      Tendsto logSinRatio (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [logSinRatio] using
      (Asymptotics.isEquivalent_iff_tendsto_one hlogNe).mp hlog
  have harg :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine tendsto_inf.2 ⟨?_, ?_⟩
    · simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact tendsto_principal.2 <| Filter.Eventually.of_forall fun n => by
        simp only [Set.mem_Ioi]
        positivity
  exact ⟨hcont.comp harg, hcont⟩

theorem gap3 :
    Tendsto
      (fun x : ℝ => (Real.cos x / Real.sin x) / (1 / x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsin :
      (fun x : ℝ => Real.sin x) ~[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x) := by
    simpa only [id_eq] using Real.isEquivalent_sin.mono inf_le_left
  have hxne : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x ≠ 0 :=
    (show ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x ∈ Set.Ioi 0 from
      self_mem_nhdsWithin).mono fun x hx => (Set.mem_Ioi.mp hx).ne'
  have hsinRatio :
      Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hxne).mp hsin
  have hcos :
      Tendsto (fun x : ℝ => Real.cos x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : Tendsto Real.cos (nhds (0 : ℝ)) (nhds (Real.cos 0)) :=
      Real.continuous_cos.continuousAt.tendsto
    simpa using hc.mono_left inf_le_left
  have hquot := hcos.div hsinRatio (by norm_num : (1 : ℝ) ≠ 0)
  convert hquot using 1
  · funext x
    change (Real.cos x / Real.sin x) / (1 / x) =
      Real.cos x / (Real.sin x / x)
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hs : Real.sin x = 0
    · simp [hs]
    field_simp
  · norm_num

theorem gap4 :
    Tendsto
      (fun x : ℝ => (Real.cos x / Real.sin x) / (1 / x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact gap3

theorem gap5 :
    Tendsto (fun n : ℕ => logSinRatio (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  exact gap2.1

theorem gap6 :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => term (n + 2))
      (fun n : ℕ => model (n + 2)) := by
  have hlog :
      Tendsto (fun n : ℕ => logSinRatio (1 / ((n + 2 : ℕ) : ℝ)))
        atTop (nhds 1) := by
    refine (gap5.comp (tendsto_add_atTop_nat 1)).congr' <|
      Filter.Eventually.of_forall fun n => ?_
    norm_num [Function.comp_apply, Nat.cast_add]
    congr 2 <;> ring
  have hsq :
      Tendsto (fun n : ℕ => logSinRatio (1 / ((n + 2 : ℕ) : ℝ)) ^ 2)
        atTop (nhds 1) := by
    simpa using hlog.pow 2
  have hratio :
      Tendsto (fun n : ℕ => model (n + 2) / term (n + 2))
        atTop (nhds 1) := by
    refine hsq.congr' <| Filter.Eventually.of_forall fun n => ?_
    exact (gap1 (n + 2) (by omega)).symm
  exact (Asymptotics.isEquivalent_of_tendsto_one hratio).symm

theorem gap7 (n : ℕ) (hn : 2 ≤ n) :
    model n = 1 / Real.log n ^ 2 := by
  simp [model, one_div]

theorem gap8 (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.log n := by
  exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))

theorem gap9 (n : ℕ) (hn : 1 ≤ n) :
    Real.log n < Real.sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hhalf := Real.log_le_sub_one_of_pos (div_pos hsqrtpos (by norm_num : (0 : ℝ) < 2))
  have htwo := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  have hdecomp :
      Real.log (Real.sqrt (n : ℝ)) =
        Real.log (Real.sqrt (n : ℝ) / 2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hroot : 2 * Real.log (Real.sqrt (n : ℝ)) < Real.sqrt (n : ℝ) := by
    rw [hdecomp]
    linarith
  rw [Real.log_sqrt hnpos.le] at hroot
  linarith

theorem gap10 (n : ℕ) (hn : 1 ≤ n) :
    0 < Real.sqrt n := by
  exact Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hn))

theorem gap11 (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.log n ^ 2 > 1 / (n : ℝ) := by
  have hlogpos := gap8 n hn
  have hlog := gap9 n (by omega)
  have hsquare : Real.log n ^ 2 < (n : ℝ) := by
    calc
      Real.log n ^ 2 < Real.sqrt n ^ 2 :=
        (sq_lt_sq₀ hlogpos.le (Real.sqrt_nonneg _)).2 hlog
      _ = (n : ℝ) := Real.sq_sqrt (by positivity)
  exact one_div_lt_one_div_of_lt (sq_pos_of_pos hlogpos) hsquare

theorem gap12 :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    (mt (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast)

theorem gap13 :
    ¬ Summable (fun n : ℕ => 1 / Real.log (n + 2) ^ 2) := by
  have hhar : ¬ Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_ofNat] using
      (mt (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp
        Real.not_summable_one_div_natCast)
  intro hlog
  apply hhar
  refine hlog.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  simpa [Nat.cast_add, Nat.cast_ofNat] using (gap11 (n + 2) (by omega)).le

theorem gap14 :
    ¬ Summable (fun n : ℕ => term (n + 2)) := by
  intro hterm
  apply gap13
  have hmodel : Summable (fun n : ℕ => model (n + 2)) :=
    gap6.summable_iff_nat.mp hterm
  exact hmodel.congr fun n => by
    simpa [Nat.cast_add, Nat.cast_ofNat] using gap7 (n + 2) (by omega)

theorem gap15 :
    ¬ Summable (fun n : ℕ => term (n + 2)) := by
  exact gap14

end

end ProofGap.Exercise2635
