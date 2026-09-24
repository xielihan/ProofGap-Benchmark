import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2828

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  ((3 : ℝ) + (-1 : ℝ) ^ n) ^ n / n

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadiusQuarter : Prop :=
  (∀ x : ℝ, |x| < 1 / 4 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 / 4 < |x| → ¬ SeriesConvergesAt x)

def evenBoundaryTerm (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ))

def oddBoundaryTerm (k : ℕ) : ℝ :=
  1 / (((2 * k + 1 : ℕ) : ℝ) * 2 ^ (2 * k + 1))

private theorem coefficient_even (k : ℕ) :
    coefficient (2 * k) = (4 : ℝ) ^ (2 * k) / ((2 * k : ℕ) : ℝ) := by
  norm_num [coefficient, pow_mul]

private theorem coefficient_odd (k : ℕ) :
    coefficient (2 * k + 1) =
      (2 : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
  norm_num [coefficient, pow_add, pow_mul]

private theorem powerTerm_even (k : ℕ) (x : ℝ) :
    powerTerm (2 * k) x =
      (4 * x) ^ (2 * k) / ((2 * k : ℕ) : ℝ) := by
  rw [powerTerm, coefficient_even, mul_pow]
  ring

private theorem powerTerm_odd (k : ℕ) (x : ℝ) :
    powerTerm (2 * k + 1) x =
      (2 * x) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
  rw [powerTerm, coefficient_odd, mul_pow]
  ring

private theorem not_summable_evenBoundary_aux :
    ¬ Summable (fun k : ℕ => evenBoundaryTerm (k + 1)) := by
  intro h
  have htwice :
      Summable (fun k : ℕ => (2 : ℝ) * evenBoundaryTerm (k + 1)) :=
    h.mul_left 2
  have htail : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
    convert htwice using 1
    funext k
    simp only [evenBoundaryTerm, Nat.cast_add, Nat.cast_one]
    field_simp
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).mp htail
  exact Real.not_summable_one_div_natCast hall

private theorem seriesConverges_inside_aux
    (x : ℝ) (hx : |x| < 1 / 4) :
    SeriesConvergesAt x := by
  have hr_nonneg : 0 ≤ 4 * |x| := by positivity
  have hr_lt : 4 * |x| < 1 := by linarith
  have hgeom0 : Summable (fun n : ℕ => (4 * |x|) ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hr_lt)
  have hgeom : Summable (fun k : ℕ => (4 * |x|) ^ (k + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (4 * |x|) ^ n) 1).mpr hgeom0
  rw [SeriesConvergesAt]
  refine hgeom.of_norm_bounded (fun k => ?_)
  let n := k + 1
  have hn : 1 ≤ n := by omega
  have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbase : |(3 : ℝ) + (-1 : ℝ) ^ n| ≤ 4 := by
    calc
      |(3 : ℝ) + (-1 : ℝ) ^ n| ≤ |(3 : ℝ)| + |(-1 : ℝ) ^ n| :=
        abs_add_le _ _
      _ = 4 := by norm_num
  have hpow :
      |(3 : ℝ) + (-1 : ℝ) ^ n| ^ n ≤ (4 : ℝ) ^ n :=
    (pow_le_pow_left₀ (abs_nonneg _) hbase) n
  rw [Real.norm_eq_abs, powerTerm, coefficient, abs_mul, abs_div, abs_pow,
    abs_pow]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  calc
    |(3 : ℝ) + (-1 : ℝ) ^ n| ^ n / (n : ℝ) * |x| ^ n
        ≤ (4 : ℝ) ^ n / 1 * |x| ^ n := by
          gcongr
    _ = (4 * |x|) ^ n := by rw [div_one, mul_pow]

private theorem not_seriesConverges_outside_aux
    (x : ℝ) (hx : 1 / 4 < |x|) :
    ¬ SeriesConvergesAt x := by
  intro hs
  rw [SeriesConvergesAt] at hs
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hab)
  have heven :
      Summable (fun k : ℕ => powerTerm (2 * (k + 1)) x) := by
    have hsub := hs.comp_injective hi
    simpa only [Function.comp_apply, show ∀ k : ℕ, (2 * k + 1) + 1 = 2 * (k + 1) by
      intro k
      omega] using hsub
  have hlower :
      ∀ k : ℕ, evenBoundaryTerm (k + 1) ≤ powerTerm (2 * (k + 1)) x := by
    intro k
    have hbase : 1 < |4 * x| := by
      rw [abs_mul]
      norm_num
      linarith
    have hpabs : 1 ≤ |4 * x| ^ (2 * (k + 1)) :=
      one_le_pow₀ hbase.le
    have hp_nonneg : 0 ≤ (4 * x) ^ (2 * (k + 1)) := by
      rw [pow_mul]
      positivity
    have hp_eq :
        (4 * x) ^ (2 * (k + 1)) = |4 * x| ^ (2 * (k + 1)) := by
      calc
        (4 * x) ^ (2 * (k + 1)) =
            |(4 * x) ^ (2 * (k + 1))| :=
          (abs_of_nonneg hp_nonneg).symm
        _ = |4 * x| ^ (2 * (k + 1)) := abs_pow _ _
    have hp :
        1 ≤ (4 * x) ^ (2 * (k + 1)) := by
      rw [hp_eq]
      exact hpabs
    rw [powerTerm_even, evenBoundaryTerm]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) <
      2 * ((k : ℝ) + 1))).mpr hp
  have hnonneg : ∀ k : ℕ, 0 ≤ evenBoundaryTerm (k + 1) := by
    intro k
    unfold evenBoundaryTerm
    positivity
  exact not_summable_evenBoundary_aux
    (Summable.of_nonneg_of_le hnonneg hlower heven)

theorem gap1 :
    Tendsto
        (fun k : ℕ =>
          Real.rpow |coefficient (2 * (k + 1))|
            (1 / ((2 * (k + 1) : ℕ) : ℝ)))
        atTop (𝓝 4) ∧
      Tendsto
        (fun k : ℕ =>
          Real.rpow |coefficient (2 * (k + 1) + 1)|
            (1 / ((2 * (k + 1) + 1 : ℕ) : ℝ)))
        atTop (𝓝 2) := by
  have hevenCast :
      Tendsto (fun k : ℕ => (((2 * (k + 1) : ℕ) : ℝ)))
        atTop (atTop : Filter ℝ) := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro k
    exact_mod_cast (show k ≤ 2 * (k + 1) by omega)
  have hoddCast :
      Tendsto (fun k : ℕ => (((2 * (k + 1) + 1 : ℕ) : ℝ)))
        atTop (atTop : Filter ℝ) := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro k
    exact_mod_cast (show k ≤ 2 * (k + 1) + 1 by omega)
  have hevenRoot :
      Tendsto
        (fun k : ℕ =>
          Real.rpow (((2 * (k + 1) : ℕ) : ℝ))
            (1 / (((2 * (k + 1) : ℕ) : ℝ))))
        atTop (𝓝 1) :=
    (tendsto_rpow_div).comp hevenCast
  have hoddRoot :
      Tendsto
        (fun k : ℕ =>
          Real.rpow (((2 * (k + 1) + 1 : ℕ) : ℝ))
            (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ))))
        atTop (𝓝 1) :=
    (tendsto_rpow_div).comp hoddCast
  constructor
  · have hlim :
        Tendsto
          (fun k : ℕ =>
            (4 : ℝ) /
              Real.rpow (((2 * (k + 1) : ℕ) : ℝ))
                (1 / (((2 * (k + 1) : ℕ) : ℝ))))
          atTop (𝓝 4) := by
      simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).div hevenRoot
        (by norm_num : (1 : ℝ) ≠ 0)
    have hfun :
        (fun k : ℕ =>
          Real.rpow |coefficient (2 * (k + 1))|
            (1 / ((2 * (k + 1) : ℕ) : ℝ))) =
          fun k : ℕ =>
            (4 : ℝ) /
              Real.rpow (((2 * (k + 1) : ℕ) : ℝ))
                (1 / (((2 * (k + 1) : ℕ) : ℝ))) := by
      funext k
      have hn : 2 * (k + 1) ≠ 0 := by omega
      have hnpos : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
      have hpnonneg : 0 ≤ (4 : ℝ) ^ (2 * (k + 1)) := by positivity
      rw [coefficient_even, abs_of_pos (div_pos (pow_pos (by norm_num) _) hnpos)]
      rw [one_div]
      change
        (((4 : ℝ) ^ (2 * (k + 1)) / ((2 * (k + 1) : ℕ) : ℝ)) ^
            ((((2 * (k + 1) : ℕ) : ℝ))⁻¹ : ℝ)) =
          (4 : ℝ) /
            ((((2 * (k + 1) : ℕ) : ℝ)) ^
              ((((2 * (k + 1) : ℕ) : ℝ))⁻¹ : ℝ))
      rw [Real.div_rpow hpnonneg hnpos.le
        ((((2 * (k + 1) : ℕ) : ℝ))⁻¹)]
      rw [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4) hn]
    rw [hfun]
    exact hlim
  · have hlim :
        Tendsto
          (fun k : ℕ =>
            (2 : ℝ) /
              Real.rpow (((2 * (k + 1) + 1 : ℕ) : ℝ))
                (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ))))
          atTop (𝓝 2) := by
      simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).div hoddRoot
        (by norm_num : (1 : ℝ) ≠ 0)
    have hfun :
        (fun k : ℕ =>
          Real.rpow |coefficient (2 * (k + 1) + 1)|
            (1 / ((2 * (k + 1) + 1 : ℕ) : ℝ))) =
          fun k : ℕ =>
            (2 : ℝ) /
              Real.rpow (((2 * (k + 1) + 1 : ℕ) : ℝ))
                (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ))) := by
      funext k
      have hn : 2 * (k + 1) + 1 ≠ 0 := by omega
      have hnpos : (0 : ℝ) < ((2 * (k + 1) + 1 : ℕ) : ℝ) := by positivity
      have hpnonneg : 0 ≤ (2 : ℝ) ^ (2 * (k + 1) + 1) := by positivity
      rw [coefficient_odd, abs_of_pos (div_pos (pow_pos (by norm_num) _) hnpos)]
      rw [one_div]
      change
        (((2 : ℝ) ^ (2 * (k + 1) + 1) /
              ((2 * (k + 1) + 1 : ℕ) : ℝ)) ^
            ((((2 * (k + 1) + 1 : ℕ) : ℝ))⁻¹ : ℝ)) =
          (2 : ℝ) /
            ((((2 * (k + 1) + 1 : ℕ) : ℝ)) ^
              ((((2 * (k + 1) + 1 : ℕ) : ℝ))⁻¹ : ℝ))
      rw [Real.div_rpow hpnonneg hnpos.le
        ((((2 * (k + 1) + 1 : ℕ) : ℝ))⁻¹)]
      rw [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) hn]
    rw [hfun]
    exact hlim

theorem gap2 :
    HasConvergenceRadiusQuarter := by
  exact ⟨seriesConverges_inside_aux, not_seriesConverges_outside_aux⟩

theorem gap3 :
    ∀ x : ℝ, |x| < 1 / 4 → SeriesConvergesAt x := by
  exact seriesConverges_inside_aux

theorem gap4 :
    (fun k : ℕ => powerTerm (k + 1) (1 / 4)) =
      fun k : ℕ => coefficient (k + 1) * (1 / 4 : ℝ) ^ (k + 1) := by
  rfl

theorem gap5 :
    (∀ k : ℕ, 1 ≤ k →
        powerTerm (2 * k) (1 / 4) = evenBoundaryTerm k) ∧
      (∀ k : ℕ,
        powerTerm (2 * k + 1) (1 / 4) = oddBoundaryTerm k) := by
  constructor
  · intro k _
    rw [powerTerm_even]
    norm_num [evenBoundaryTerm]
  · intro k
    rw [powerTerm_odd]
    norm_num [oddBoundaryTerm, div_pow]
    field_simp

theorem gap6 :
    ¬ Summable (fun k : ℕ => evenBoundaryTerm (k + 1)) := by
  exact not_summable_evenBoundary_aux

theorem gap7 :
    Summable (fun k : ℕ => oddBoundaryTerm (k + 1)) := by
  have hgeom0 : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hmajorant :
      Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (2 * (k + 1) + 1)) := by
    have hscaled := hgeom0.mul_left (1 / 8 : ℝ)
    convert hscaled using 1
    funext k
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, pow_add, pow_mul]
    norm_num
    ring
  refine hmajorant.of_norm_bounded (fun k => ?_)
  let n := 2 * (k + 1) + 1
  have hn : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hfactor : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hn
  have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have heq :
      oddBoundaryTerm (k + 1) =
        (1 / (n : ℝ)) * (1 / 2 : ℝ) ^ n := by
    dsimp [n]
    rw [oddBoundaryTerm, div_pow]
    field_simp
    simp
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hpow_nonneg)]
  exact mul_le_of_le_one_left hpow_nonneg hfactor

theorem gap8 :
    ¬ SeriesConvergesAt (1 / 4) := by
  intro hs
  rw [SeriesConvergesAt] at hs
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hab)
  have heven :
      Summable (fun k : ℕ => powerTerm (2 * (k + 1)) (1 / 4)) := by
    have hsub := hs.comp_injective hi
    simpa only [Function.comp_apply, show ∀ k : ℕ, (2 * k + 1) + 1 = 2 * (k + 1) by
      intro k
      omega] using hsub
  have hboundary :
      Summable (fun k : ℕ => evenBoundaryTerm (k + 1)) := by
    convert heven using 1
    funext k
    exact (gap5.1 (k + 1) (by omega)).symm
  exact gap6 hboundary

theorem gap9 :
    ¬ SeriesConvergesAt (-1 / 4) := by
  intro hs
  rw [SeriesConvergesAt] at hs
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hab)
  have heven :
      Summable (fun k : ℕ => powerTerm (2 * (k + 1)) (-1 / 4)) := by
    have hsub := hs.comp_injective hi
    simpa only [Function.comp_apply, show ∀ k : ℕ, (2 * k + 1) + 1 = 2 * (k + 1) by
      intro k
      omega] using hsub
  have hboundary :
      Summable (fun k : ℕ => evenBoundaryTerm (k + 1)) := by
    convert heven using 1
    funext k
    rw [powerTerm_even]
    norm_num [evenBoundaryTerm]
  exact gap6 hboundary

theorem gap10 :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4) ↔
      SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    rcases hx with ⟨hl, hu⟩
    apply gap3 x
    rw [abs_lt]
    constructor <;> linarith
  · intro hs
    have habs : |x| < 1 / 4 := by
      by_contra hnot
      have hle : 1 / 4 ≤ |x| := le_of_not_gt hnot
      rcases hle.eq_or_lt with heq | hlt
      · rcases le_total 0 x with hxnonneg | hxnonpos
        · have hxval : x = 1 / 4 := by
            rw [abs_of_nonneg hxnonneg] at heq
            exact heq.symm
          exact gap8 (hxval ▸ hs)
        · have hxval : x = -1 / 4 := by
            rw [abs_of_nonpos hxnonpos] at heq
            linarith
          exact gap9 (hxval ▸ hs)
      · exact (gap2.2 x hlt) hs
    rcases abs_lt.mp habs with ⟨hl, hu⟩
    exact ⟨by linarith, hu⟩

end

end ProofGap.Exercise2828
