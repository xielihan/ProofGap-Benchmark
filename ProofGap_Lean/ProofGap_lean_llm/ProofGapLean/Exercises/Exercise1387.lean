import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise1387

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.log (Real.sin x / x)

def sineQuotientSeries (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

def logIncrement (x : ℝ) : ℝ :=
  -x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

def logarithmSeries (x : ℝ) : ℝ :=
  logIncrement x - logIncrement x ^ 2 / 2 + logIncrement x ^ 3 / 3

def finalPolynomial (x : ℝ) : ℝ :=
  -x ^ 2 / 6 - x ^ 4 / 180 - x ^ 6 / 2835

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private def sineRatio (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

private theorem f_eq_log_sineRatio (x : ℝ) :
    f x = Real.log (sineRatio x) := by
  by_cases hx : x = 0
  · simp [f, sineRatio, hx]
  · simp [f, sineRatio, hx]

private theorem sine_septic_remainder :
    (fun x : ℝ => Real.sin x -
      (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
      =o[nhds 0] (fun x : ℝ => x ^ 8) := by
  have h := taylor_isLittleO_univ
    (x₀ := 0) (n := 8) Real.contDiff_sin
  convert h using 1
  · funext x
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  · funext x
    ring

private theorem ratio_remainder :
    (fun x : ℝ => sineRatio x - sineQuotientSeries x)
      =o[nhds 0] (fun x : ℝ => x ^ 7) := by
  let L : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have h :
      (fun x : ℝ => Real.sin x -
        (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
        =o[L] (fun x : ℝ => x ^ 8) :=
    sine_septic_remainder.mono nhdsWithin_le_nhds
  have hd := h.tendsto_div_nhds_zero
  have ht : Tendsto
      (fun x : ℝ => (sineRatio x - sineQuotientSeries x) / x ^ 7)
      L (nhds 0) := by
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp [sineRatio, hx0, sineQuotientSeries]
    field_simp [hx0]
  have hz : ∀ᶠ x : ℝ in L,
      x ^ 7 = 0 → sineRatio x - sineQuotientSeries x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro hp
    have hx0 : x ≠ 0 := by simpa using hx
    exact False.elim (hx0 (eq_zero_of_pow_eq_zero hp))
  have hL := (Asymptotics.isLittleO_iff_tendsto' hz).2 ht
  have hTVS :
      (fun x : ℝ => sineRatio x - sineQuotientSeries x)
        =o[ℝ; L] (fun x : ℝ => x ^ 7) :=
    hL.isLittleOTVS
  have hins := hTVS.insert (s := ({0} : Set ℝ)ᶜ)
    (by norm_num [sineRatio, sineQuotientSeries])
  have hset : insert (0 : ℝ) ({0} : Set ℝ)ᶜ = Set.univ := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact eq_or_ne x 0
  have hfilter :
      nhdsWithin 0 (insert (0 : ℝ) ({0} : Set ℝ)ᶜ) = nhds 0 := by
    rw [hset, nhdsWithin_univ]
  rw [hfilter] at hins
  exact Asymptotics.isLittleOTVS_iff_isLittleO.mp hins

private theorem sineRatio_tendsto :
    Tendsto sineRatio (nhds 0) (nhds 1) := by
  have hp : Tendsto sineQuotientSeries (nhds 0) (nhds 1) := by
    have hc : ContinuousAt sineQuotientSeries 0 := by
      unfold sineQuotientSeries
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [sineQuotientSeries]
  have hx7 : Tendsto (fun x : ℝ => x ^ 7) (nhds 0) (nhds 0) := by
    convert (tendsto_id : Tendsto (fun x : ℝ => x)
      (nhds 0) (nhds 0)).pow 7 using 1 <;> norm_num
  have he : Tendsto
      (fun x : ℝ => sineRatio x - sineQuotientSeries x)
      (nhds 0) (nhds 0) :=
    ratio_remainder.tendsto_zero_of_tendsto hx7
  convert he.add hp using 1 <;> ring

private theorem log_plus_remainder_bigO :
    (fun u : ℝ => Real.log (1 + u) -
      (u - u ^ 2 / 2 + u ^ 3 / 3))
      =O[nhds 0] (fun u : ℝ => u ^ 4) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  have he : ∀ᶠ u : ℝ in nhds 0, |u| < 1 / 2 := by
    simpa only [Real.norm_eq_abs] using
      (Metric.eventually_nhds_iff_ball.2
        ⟨(1 / 2 : ℝ), by norm_num, fun y hy => by
          simpa [Real.dist_eq] using hy⟩)
  filter_upwards [he] with u hu
  have hu1 : |-u| < 1 := by simpa using lt_trans hu (by norm_num)
  have hb := Real.abs_log_sub_add_sum_range_le hu1 3
  norm_num [Finset.sum_range_succ] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hden : 1 / 2 < 1 - |u| := by linarith
  calc
    |Real.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3)| =
        |-u + u ^ 2 / 2 + (-u) ^ 3 / 3 +
          Real.log (1 + u)| := by
      congr 1
      ring
    _ ≤ |u| ^ 4 / (1 - |u|) := hb
    _ ≤ 2 * |u ^ 4| := by
      rw [abs_pow]
      have hn : 0 ≤ |u| ^ 4 := pow_nonneg (abs_nonneg u) 4
      apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).2
      nlinarith

private theorem log_series_helper :
    AgreesToOrderAt f logarithmSeries 0 6 := by
  let v : ℝ → ℝ := fun x => sineRatio x - 1
  let u : ℝ → ℝ := logIncrement
  let P : ℝ → ℝ := fun z => z - z ^ 2 / 2 + z ^ 3 / 3
  have hv : Tendsto v (nhds 0) (nhds 0) := by
    convert sineRatio_tendsto.sub_const 1 using 1 <;> norm_num [v]
  have hu : Tendsto u (nhds 0) (nhds 0) := by
    have hc : ContinuousAt u 0 := by
      dsimp [u]
      unfold logIncrement
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [u, logIncrement]
  have hdu :
      (fun x : ℝ => v x - u x) =o[nhds 0] (fun x : ℝ => x ^ 7) := by
    convert ratio_remainder using 1
    funext x
    simp [v, u, logIncrement, sineQuotientSeries]
    ring
  have huO : u =O[nhds 0] (fun x : ℝ => x ^ 2) := by
    have hc : Tendsto
        (fun x : ℝ => -1 / 6 + x ^ 2 / 120 - x ^ 4 / 5040)
        (nhds 0) (nhds (-1 / 6 : ℝ)) := by
      have ht : ContinuousAt
          (fun x : ℝ => -1 / 6 + x ^ 2 / 120 - x ^ 4 / 5040) 0 := by
        fun_prop
      convert ht.tendsto using 1 <;> norm_num
    have hm := (Asymptotics.isBigO_refl
      (fun x : ℝ => x ^ 2) (nhds 0)).mul (hc.isBigO_one ℝ)
    refine hm.congr' (Eventually.of_forall ?_)
      (Eventually.of_forall (fun x => by simp))
    intro x
    dsimp [u]
    unfold logIncrement
    ring
  have hdu2 :
      (fun x : ℝ => v x - u x) =o[nhds 0] (fun x : ℝ => x ^ 2) :=
    hdu.trans (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 7))
  have hvO : v =O[nhds 0] (fun x : ℝ => x ^ 2) := by
    have hs := hdu2.isBigO.add huO
    refine hs.congr' (Eventually.of_forall (fun x => by ring))
      (Eventually.of_forall (fun x => rfl))
  have hlogComp := log_plus_remainder_bigO.comp_tendsto hv
  have hv4O := hvO.pow 4
  have hlog6 :
      (fun x : ℝ => Real.log (1 + v x) - P (v x))
        =o[nhds 0] (fun x : ℝ => x ^ 6) := by
    have hO8 := hlogComp.trans hv4O
    have hO8' :
        (fun x : ℝ => Real.log (1 + v x) - P (v x))
          =O[nhds 0] (fun x : ℝ => x ^ 8) := by
      refine hO8.congr' (Eventually.of_forall ?_)
        (Eventually.of_forall ?_)
      · intro x
        rfl
      · intro x
        ring
    have hp86 := Asymptotics.isLittleO_pow_pow
      (𝕜 := ℝ) (m := 6) (n := 8) (by decide)
    have ht := hO8'.trans_isLittleO hp86
    exact ht
  let q : ℝ → ℝ := fun x =>
    1 - (v x + u x) / 2 +
      (v x ^ 2 + v x * u x + u x ^ 2) / 3
  have hq : Tendsto q (nhds 0) (nhds 1) := by
    convert (tendsto_const_nhds.sub ((hv.add hu).div_const 2)).add
      ((((hv.pow 2).add (hv.mul hu) |>.add (hu.pow 2)).div_const 3))
      using 1 <;> norm_num [q]
  have hpoly7 :
      (fun x : ℝ => P (v x) - P (u x))
        =o[nhds 0] (fun x : ℝ => x ^ 7) := by
    have hp := hdu.mul_isBigO (hq.isBigO_one ℝ)
    refine hp.congr' (Eventually.of_forall ?_)
      (Eventually.of_forall (fun x => by simp))
    intro x
    dsimp [P, q]
    ring
  have hpoly6 := hpoly7.trans
    (Asymptotics.isLittleO_pow_pow (by norm_num : 6 < 7))
  have hsum := hlog6.add hpoly6
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine hsum.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  change Real.log (1 + v x) - P (v x) +
      (P (v x) - P (u x)) = f x - logarithmSeries x
  rw [f_eq_log_sineRatio]
  unfold logarithmSeries
  dsimp [v, u, P]
  ring

private theorem log_increment_remainder :
    AgreesToOrderAt
      (fun x => Real.log (sineQuotientSeries x))
      logarithmSeries 0 6 := by
  let u : ℝ → ℝ := logIncrement
  have hu : Tendsto u (nhds 0) (nhds 0) := by
    have hc : ContinuousAt u 0 := by
      dsimp [u]
      unfold logIncrement
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [u, logIncrement]
  have huO : u =O[nhds 0] (fun x : ℝ => x ^ 2) := by
    have hc : Tendsto
        (fun x : ℝ => -1 / 6 + x ^ 2 / 120 - x ^ 4 / 5040)
        (nhds 0) (nhds (-1 / 6 : ℝ)) := by
      have ht : ContinuousAt
          (fun x : ℝ => -1 / 6 + x ^ 2 / 120 - x ^ 4 / 5040) 0 := by
        fun_prop
      convert ht.tendsto using 1 <;> norm_num
    have hm := (Asymptotics.isBigO_refl
      (fun x : ℝ => x ^ 2) (nhds 0)).mul (hc.isBigO_one ℝ)
    refine hm.congr' (Eventually.of_forall ?_)
      (Eventually.of_forall (fun x => by simp))
    intro x
    dsimp [u]
    unfold logIncrement
    ring
  have hc := log_plus_remainder_bigO.comp_tendsto hu
  have hu4O := huO.pow 4
  have hO8raw := hc.trans hu4O
  have hO8 :
      (fun x : ℝ => Real.log (1 + u x) -
        (u x - u x ^ 2 / 2 + u x ^ 3 / 3))
        =O[nhds 0] (fun x : ℝ => x ^ 8) := by
    exact hO8raw.congr'
      (Eventually.of_forall (fun x => by simp [Function.comp_def]))
      (Eventually.of_forall (fun x => by ring))
  have hp86 := Asymptotics.isLittleO_pow_pow
    (𝕜 := ℝ) (m := 6) (n := 8) (by decide)
  have ht := hO8.trans_isLittleO hp86
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine ht.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  unfold sineQuotientSeries logarithmSeries
  dsimp [u]
  unfold logIncrement
  simp [Function.comp_def]
  ring

private theorem gap2_helper :
    AgreesToOrderAt f
      (fun x => Real.log (sineQuotientSeries x)) 0 6 := by
  have h1 := log_series_helper
  have h2 := log_increment_remainder
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.sub h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

private theorem gap1_helper :
    AgreesToOrderAt f
      (fun x => Real.log
        ((x - x ^ 3 / (Nat.factorial 3 : ℝ) +
          x ^ 5 / (Nat.factorial 5 : ℝ) -
          x ^ 7 / (Nat.factorial 7 : ℝ)) / x)) 0 6 := by
  have h := gap2_helper
  unfold AgreesToOrderAt at h ⊢
  refine h.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  by_cases hx : x = 0
  · subst x
    norm_num [sineQuotientSeries]
  · congr 2
    unfold sineQuotientSeries
    norm_num
    field_simp [hx]

private def finalFactor (x : ℝ) : ℝ :=
  11 / 67200 - 1 / 64800 * x ^ 2 + 23 / 31752000 * x ^ 4 -
    31 / 1524096000 * x ^ 6 + 1 / 3048192000 * x ^ 8 -
    1 / 384072192000 * x ^ 10

private theorem logarithm_final :
    AgreesToOrderAt logarithmSeries finalPolynomial 0 6 := by
  have hq : Tendsto finalFactor
      (nhds 0) (nhds (11 / 67200 : ℝ)) := by
    have hc : ContinuousAt finalFactor 0 := by
      unfold finalFactor
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [finalFactor]
  have hO := (Asymptotics.isBigO_refl
    (fun x : ℝ => x ^ 8) (nhds 0)).mul (hq.isBigO_one ℝ)
  have hO' :
      (fun x : ℝ => x ^ 8 * finalFactor x)
        =O[nhds 0] (fun x : ℝ => x ^ 8) := by
    simpa using hO
  have h6 := hO'.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 6 < 8))
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine h6.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  unfold logarithmSeries finalPolynomial logIncrement finalFactor
  ring

private theorem gap4_helper :
    AgreesToOrderAt f finalPolynomial 0 6 := by
  have h1 := log_series_helper
  have h2 := logarithm_final
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

theorem gap1 :
    AgreesToOrderAt f
      (fun x => Real.log
        ((x - x ^ 3 / (Nat.factorial 3 : ℝ) +
          x ^ 5 / (Nat.factorial 5 : ℝ) -
          x ^ 7 / (Nat.factorial 7 : ℝ)) / x)) 0 6 := by
  exact gap1_helper

theorem gap2 :
    AgreesToOrderAt f (fun x => Real.log (sineQuotientSeries x)) 0 6 := by
  exact gap2_helper

theorem gap3 :
    AgreesToOrderAt f logarithmSeries 0 6 := by
  exact log_series_helper

theorem gap4 :
    AgreesToOrderAt f finalPolynomial 0 6 := by
  exact gap4_helper

end

end ProofGap.Exercise1387
