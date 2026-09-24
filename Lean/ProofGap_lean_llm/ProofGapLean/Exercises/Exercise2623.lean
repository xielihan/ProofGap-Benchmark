import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2623

noncomputable section

open Filter Set MeasureTheory
open scoped Interval BigOperators

def seriesTail (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, f (n + k + 1)

def tailIntegral (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Ioi (n + 1 : ℝ), f x

def cube (x : ℝ) : ℝ := 1 / x ^ 3

def cubePartial (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 3

def cubeSeries : ℝ :=
  ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 3

theorem gap1 (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x)
    (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) :
    IntegrableOn f (Ici 1) := by
  let s : ℕ → Set ℝ := fun n =>
    Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ))
  have hsInt : ∀ n : ℕ, IntegrableOn f (s n) := by
    intro n
    apply (hcont.mono ?_).integrableOn_compact isCompact_Icc
    intro x hx
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    exact Set.mem_Ici.mpr (hn1.trans hx.1)
  have hnormSummable : Summable (fun n : ℕ =>
      ∫ x in s n, ‖f x‖) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro n
      have hconst : IntegrableOn (fun _ : ℝ => f (n + 1)) (s n) :=
        integrableOn_const (by simp [s])
      calc
        (∫ x in s n, ‖f x‖) ≤ ∫ _x in s n, f (n + 1) := by
          apply setIntegral_mono_on (hsInt n).norm hconst measurableSet_Icc
          intro x hx
          have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
          have hx1 : (1 : ℝ) ≤ x :=
            hn1.trans hx.1
          rw [Real.norm_eq_abs, abs_of_nonneg (hpos x hx1)]
          apply hanti
          · exact Set.mem_Ici.mpr (by norm_num)
          · exact Set.mem_Ici.mpr hx1
          · simpa [Nat.cast_add] using hx.1
        _ = f (n + 1) := by
          simp [s, Nat.cast_add]
          ring
    · exact hsum
  have hUnion : (⋃ n : ℕ, s n) = Ici (1 : ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ici]
    constructor
    · rintro ⟨n, hx⟩
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
      exact hn1.trans hx.1
    · intro hx
      let m : ℕ := ⌊x⌋₊
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      have hm1 : 1 ≤ m := by
        exact (Nat.one_le_floor_iff x).mpr hx
      have hmle : (m : ℝ) ≤ x := Nat.floor_le hx0
      have hxlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
      refine ⟨m - 1, ?_⟩
      dsimp only [s]
      have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
      have hmEq' : m - 1 + 2 = m + 1 := by omega
      simpa [hmEq, hmEq', Nat.cast_add] using ⟨hmle, hxlt.le⟩
  rw [← hUnion]
  exact integrableOn_iUnion_of_summable_integral_norm hsInt hnormSummable

theorem gap2 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hanti : AntitoneOn f (Ici 1))
    (n k : ℕ) (hnk : 1 ≤ n + k) :
    f (n + k + 1) ≤ ∫ x in (n + k : ℝ)..(n + k + 1 : ℝ), f x := by
  have hanti' : AntitoneOn f
      (Icc ((n + k : ℕ) : ℝ) (((n + k : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    have hbase : (1 : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast hnk
    exact hanti.mono (by
      intro x hx
      exact Set.mem_Ici.mpr (hbase.trans hx.1))
  simpa [Nat.cast_add] using
    (hanti'.sum_le_integral (x₀ := ((n + k : ℕ) : ℝ)) (a := 1))

theorem gap3 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hanti : AntitoneOn f (Ici 1))
    (n k : ℕ) (hnk : 1 ≤ n + k) :
    (∫ x in (n + k : ℝ)..(n + k + 1 : ℝ), f x) ≤ f (n + k) := by
  have hanti' : AntitoneOn f
      (Icc ((n + k : ℕ) : ℝ) (((n + k : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    have hbase : (1 : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast hnk
    exact hanti.mono (by
      intro x hx
      exact Set.mem_Ici.mpr (hbase.trans hx.1))
  simpa [Nat.cast_add] using
    (hanti'.integral_le_sum (x₀ := ((n + k : ℕ) : ℝ)) (a := 1))

theorem gap4 (f : ℝ → ℝ) (hanti : AntitoneOn f (Ici 1))
    (n k : ℕ) (hnk : 1 ≤ n + k) :
    f (n + k + 1) ≤ f (n + k) := by
  apply hanti
  · exact Set.mem_Ici.mpr (by exact_mod_cast hnk)
  · exact Set.mem_Ici.mpr (by exact_mod_cast (show 1 ≤ n + k + 1 by omega))
  · exact_mod_cast (show n + k ≤ n + k + 1 by omega)

private theorem tail_summable (f : ℝ → ℝ)
    (hsum : Summable (fun n : ℕ => f (n + 1))) (m : ℕ) :
    Summable (fun k : ℕ => f (m + k + 1)) := by
  have h := (summable_nat_add_iff m).mpr hsum
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem seriesTail_step (f : ℝ → ℝ)
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f n = f (n + 1) + seriesTail f (n + 1) := by
  have htail := tail_summable f hsum n
  unfold seriesTail
  calc
    (∑' k : ℕ, f (n + k + 1)) =
        f (n + 0 + 1) + ∑' k : ℕ, f (n + (k + 1 : ℕ) + 1) :=
      by simpa using htail.tsum_eq_zero_add
    _ = f (n + 1) + ∑' k : ℕ, f ((n + 1 : ℕ) + k + 1) := by
      congr 1
      · norm_num
      · apply tsum_congr
        intro k
        congr 1
        push_cast
        ring

theorem gap5 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f (n + 1) ≤ tailIntegral f n := by
  have htailSum : Summable (fun k : ℕ =>
      f (((n + 1 : ℕ) : ℝ) + (k : ℝ) + 1)) :=
    tail_summable f hsum (n + 1)
  have hleft : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        f (((n + 1 : ℕ) : ℝ) + (k : ℝ) + 1))
      atTop (nhds (seriesTail f (n + 1))) := by
    simpa [seriesTail] using
      htailSum.hasSum.tendsto_sum_nat
  have hIntAll := gap1 f hcont hpos hanti hsum
  have hIntTail : IntegrableOn f (Ioi (((n + 1 : ℕ) : ℝ))) := by
    apply hIntAll.mono_set
    intro x hx
    exact Set.mem_Ici.mpr ((by norm_num : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)).trans hx.le)
  have hright : Tendsto
      (fun N : ℕ => ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ) + N, f x)
      atTop (nhds (tailIntegral f n)) := by
    have htop : Tendsto (fun N : ℕ => ((n + 1 : ℕ) : ℝ) + N) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    simpa [tailIntegral, Nat.cast_add] using
      (intervalIntegral_tendsto_integral_Ioi (((n + 1 : ℕ) : ℝ))
        hIntTail htop)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro N
  have hanti' : AntitoneOn f
      (Icc (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + (N : ℝ))) :=
    hanti.mono (by
      intro x hx
      exact Set.mem_Ici.mpr
        ((by norm_num : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)).trans hx.1))
  have H := hanti'.sum_le_integral
    (x₀ := (((n + 1 : ℕ) : ℝ))) (a := N)
  convert H using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  push_cast
  ring

theorem gap6 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    tailIntegral f n ≤ seriesTail f n := by
  have htailSum : Summable (fun k : ℕ =>
      f ((n : ℝ) + (k : ℝ) + 1)) := tail_summable f hsum n
  have hright : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        f ((n : ℝ) + (k : ℝ) + 1))
      atTop (nhds (seriesTail f n)) := by
    simpa [seriesTail] using htailSum.hasSum.tendsto_sum_nat
  have hIntAll := gap1 f hcont hpos hanti hsum
  have hIntTail : IntegrableOn f (Ioi (((n + 1 : ℕ) : ℝ))) := by
    apply hIntAll.mono_set
    intro x hx
    exact Set.mem_Ici.mpr ((by norm_num : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)).trans hx.le)
  have hleft : Tendsto
      (fun N : ℕ => ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ) + N, f x)
      atTop (nhds (tailIntegral f n)) := by
    have htop : Tendsto (fun N : ℕ => ((n + 1 : ℕ) : ℝ) + N) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    simpa [tailIntegral, Nat.cast_add] using
      (intervalIntegral_tendsto_integral_Ioi (((n + 1 : ℕ) : ℝ))
        hIntTail htop)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro N
  have hanti' : AntitoneOn f
      (Icc (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + (N : ℝ))) :=
    hanti.mono (by
      intro x hx
      exact Set.mem_Ici.mpr
        ((by norm_num : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)).trans hx.1))
  have H := hanti'.integral_le_sum
    (x₀ := (((n + 1 : ℕ) : ℝ))) (a := N)
  convert H using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  push_cast
  ring

theorem gap7 (f : ℝ → ℝ) (hpos : ∀ x ≥ 1, 0 ≤ f x)
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f (n + 1) ≤ seriesTail f n := by
  rw [seriesTail_step f hsum n]
  exact le_add_of_nonneg_left (hpos (n + 1) (by norm_num))

theorem gap8 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f n - f (n + 1) ≤ tailIntegral f n := by
  calc
    seriesTail f n - f (n + 1) = seriesTail f (n + 1) := by
      rw [seriesTail_step f hsum n]
      ring
    _ ≤ tailIntegral f n := gap5 f hcont hpos hanti hsum n

theorem gap9 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    tailIntegral f n ≤ seriesTail f n := by
  exact gap6 f hcont hpos hanti hsum n

theorem gap10 (f : ℝ → ℝ) (hpos : ∀ x ≥ 1, 0 ≤ f x)
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f n - f (n + 1) ≤ seriesTail f n := by
  exact sub_le_self _ (hpos (n + 1) (by norm_num))

theorem gap11 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    tailIntegral f n ≤ seriesTail f n := by
  exact gap6 f hcont hpos hanti hsum n

theorem gap12 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) (n : ℕ) :
    seriesTail f n ≤ f (n + 1) + tailIntegral f n := by
  linarith [gap8 f hcont hpos hanti hsum n]

theorem gap13 (f : ℝ → ℝ) (hpos : ∀ x ≥ 1, 0 ≤ f x) (n : ℕ) :
    tailIntegral f n ≤ f (n + 1) + tailIntegral f n := by
  exact le_add_of_nonneg_left (hpos (n + 1) (by norm_num))

private theorem cube_continuous : ContinuousOn cube (Ici 1) := by
  intro x hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  unfold cube
  exact (continuousAt_const.div (continuousAt_id.pow 3)
    (pow_ne_zero 3 hxpos.ne')).continuousWithinAt

private theorem cube_nonneg : ∀ x ≥ (1 : ℝ), 0 ≤ cube x := by
  intro x hx
  unfold cube
  positivity

private theorem cube_antitone : AntitoneOn cube (Ici 1) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpow : x ^ 3 ≤ y ^ 3 := by
    exact pow_le_pow_left₀ hxpos.le hxy 3
  unfold cube
  exact one_div_le_one_div_of_le (pow_pos hxpos 3) hpow

private theorem cube_summable :
    Summable (fun n : ℕ => cube (n + 1)) := by
  have hall : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hall
  simpa [cube, Nat.cast_add] using hshift

theorem gap14 :
    seriesTail cube 8 ≤ 1 / (9 : ℝ) ^ 3 + tailIntegral cube 8 := by
  convert gap12 cube cube_continuous cube_nonneg cube_antitone cube_summable 8 using 1 <;>
    norm_num [cube]

private theorem tailIntegral_cube_eight :
    tailIntegral cube 8 = 1 / (162 : ℝ) := by
  have H := integral_Ioi_rpow_of_lt
    (a := (-3 : ℝ)) (c := (9 : ℝ)) (by norm_num) (by norm_num)
  unfold tailIntegral cube
  rw [show ((8 : ℕ) : ℝ) + 1 = (9 : ℝ) by norm_num]
  change (∫ x in Ioi (9 : ℝ), 1 / x ^ 3) = 1 / (162 : ℝ)
  calc
    (∫ x in Ioi (9 : ℝ), 1 / x ^ 3) =
        ∫ x in Ioi (9 : ℝ), x ^ (-3 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx9 : (9 : ℝ) < x := hx
      have hxpos : 0 < x := by linarith
      change 1 / x ^ 3 = Real.rpow x (-3 : ℝ)
      calc
        1 / x ^ 3 = (Real.rpow x (3 : ℝ))⁻¹ := by
          norm_num [Real.rpow_natCast, one_div]
        _ = Real.rpow x (-(3 : ℝ)) :=
          (Real.rpow_neg hxpos.le (3 : ℝ)).symm
        _ = Real.rpow x (-3 : ℝ) := by norm_num
    _ = 1 / (162 : ℝ) := by
      rw [H]
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 9), Real.rpow_natCast]

theorem gap15 :
    1 / (9 : ℝ) ^ 3 + tailIntegral cube 8 < 0.008 := by
  rw [tailIntegral_cube_eight]
  norm_num

theorem gap16 :
    seriesTail cube 8 < 0.008 := by
  exact lt_of_le_of_lt gap14 gap15

theorem gap17 :
    |cubePartial 8 - 1.20| < 0.005 := by
  norm_num [cubePartial, Finset.sum_Icc_succ_top, abs_lt]

private theorem cubeSeries_decomp :
    cubeSeries = cubePartial 8 + seriesTail cube 8 := by
  let u : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)
  have hu : Summable u := by
    simpa [u, cube, Nat.cast_add] using cube_summable
  have hfirst : cubePartial 8 = ∑ i ∈ Finset.range 8, u i := by
    norm_num [cubePartial, u, Finset.sum_Icc_succ_top, Finset.sum_range_succ]
  have htail : seriesTail cube 8 = ∑' i : ℕ, u (i + 8) := by
    unfold seriesTail
    apply tsum_congr
    intro i
    dsimp only [cube, u]
    congr 1
    push_cast
    ring
  rw [hfirst, htail]
  symm
  simpa [cubeSeries, u] using hu.sum_add_tsum_nat_add 8

theorem gap18 :
    |cubeSeries - 1.20| < 0.01 := by
  rw [cubeSeries_decomp, abs_lt]
  have htail0 : 0 ≤ seriesTail cube 8 := by
    unfold seriesTail
    apply tsum_nonneg
    intro k
    exact cube_nonneg _ (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith)
  constructor
  · norm_num [cubePartial, Finset.sum_Icc_succ_top]
    linarith
  · have htail := gap16
    norm_num [cubePartial, Finset.sum_Icc_succ_top] at ⊢
    linarith

theorem gap19 (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 1))
    (hpos : ∀ x ≥ 1, 0 ≤ f x) (hanti : AntitoneOn f (Ici 1))
    (hsum : Summable (fun n : ℕ => f (n + 1))) :
    (∀ n, tailIntegral f n ≤ seriesTail f n ∧
      seriesTail f n ≤ f (n + 1) + tailIntegral f n) ∧
      |cubeSeries - 1.20| < 0.01 := by
  refine ⟨?_, gap18⟩
  intro n
  exact ⟨gap11 f hcont hpos hanti hsum n,
    gap12 f hcont hpos hanti hsum n⟩

end

end ProofGap.Exercise2623
