import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise1394_3
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1407

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def y (x : ℝ) := Real.tan (Real.sin x) - Real.sin (Real.tan x)
def sinPoly (x : ℝ) :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
def tanPoly (x : ℝ) :=
  x + x ^ 3 / 3 + 2 * x ^ 5 / 15 + 17 * x ^ 7 / 315

private def sinFactor (a b : ℝ) :=
  1 - (a ^ 2 + a * b + b ^ 2) / 6 +
    (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) / 120 -
    (a ^ 6 + a ^ 5 * b + a ^ 4 * b ^ 2 + a ^ 3 * b ^ 3 +
      a ^ 2 * b ^ 4 + a * b ^ 5 + b ^ 6) / 5040

private def tanFactor (a b : ℝ) :=
  1 + (a ^ 2 + a * b + b ^ 2) / 3 +
    2 * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) / 15 +
    17 * (a ^ 6 + a ^ 5 * b + a ^ 4 * b ^ 2 + a ^ 3 * b ^ 3 +
      a ^ 2 * b ^ 4 + a * b ^ 5 + b ^ 6) / 315

private theorem sinPoly_sub (a b : ℝ) :
    sinPoly a - sinPoly b = (a - b) * sinFactor a b := by
  simp only [sinPoly, sinFactor]
  ring

private theorem tanPoly_sub (a b : ℝ) :
    tanPoly a - tanPoly b = (a - b) * tanFactor a b := by
  simp only [tanPoly, tanFactor]
  ring

private theorem sinFactor_zero : sinFactor 0 0 = 1 := by
  norm_num [sinFactor]

private theorem tanFactor_zero : tanFactor 0 0 = 1 := by
  norm_num [tanFactor]

private def compositionFactor (x : ℝ) :=
  (109275246826577 * x ^ 40
    + 1889818974530298 * x ^ 38
    + 18731441012243820 * x ^ 36
    + 141883554325916760 * x ^ 34
    + 872704593180317520 * x ^ 32
    + 4540517162513779104 * x ^ 30
    + 20610029395886172480 * x ^ 28
    + 81027113909157698688 * x ^ 26
    + 276097805285404838400 * x ^ 24
    + 807327929250148561920 * x ^ 22
    + 1903021863038489088000 * x ^ 20
    + 3162986677794237235200 * x ^ 18
    + 827856828693522432000 * x ^ 16
    - 19840299223310254080000 * x ^ 14
    - 93103283116001894400000 * x ^ 12
    - 216247068925758259200000 * x ^ 10
    - 672260825791328256000000 * x ^ 8
    + 1058161041036700876800000 * x ^ 6
    - 2150070420781301760000000 * x ^ 4
    + 19486535538350555136000000 * x ^ 2
    + 15843822264306892800000000) /
      (413032056269517619200000000 : ℝ)

private theorem polynomial_composition_error (x : ℝ) :
    tanPoly (sinPoly x) - sinPoly (tanPoly x) - x ^ 7 / 30 =
      x ^ 9 * compositionFactor x := by
  set_option maxHeartbeats 800000 in
    unfold sinPoly tanPoly compositionFactor
    ring

private def taylor8 (g : ℝ → ℝ) (x : ℝ) :=
  ∑ k ∈ Finset.range 9,
    x ^ k / (Nat.factorial k : ℝ) * iteratedDeriv k g 0

private theorem taylor8_isLittleO (g : ℝ → ℝ)
    (hg : ContDiffAt ℝ 8 g 0) :
    Asymptotics.IsLittleO punctured
      (fun x => g x - taylor8 g x) (fun x => x ^ 8) := by
  have hs : ContDiffWithinAt ℝ 8 g Set.univ 0 := hg
  rcases hs.contDiffOn' le_rfl (by simp) with
    ⟨u, huopen, h0u, hgu⟩
  have hgu' : ContDiffOn ℝ 8 g u := by simpa using hgu
  rcases Metric.isOpen_iff.1 huopen 0 h0u with ⟨ε, hε, hball⟩
  have hgball : ContDiffOn ℝ 8 g (Metric.ball 0 ε) :=
    hgu'.mono hball
  have ht := taylor_isLittleO (convex_ball 0 ε)
    (Metric.mem_ball_self hε) hgball
  rw [Metric.isOpen_ball.nhdsWithin_eq
    (Metric.mem_ball_self hε)] at ht
  have heval :
      taylorWithinEval g 8 (Metric.ball 0 ε) 0 = taylor8 g := by
    funext x
    rw [taylor_within_apply]
    dsimp [taylor8]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_ball
      (Metric.mem_ball_self hε)]
    rw [← iteratedDeriv_eq_iterate]
    ring
  rw [heval] at ht
  have ht' :
      Asymptotics.IsLittleO (nhds 0)
        (fun x => g x - taylor8 g x) (fun x : ℝ => x ^ 8) := by
    simpa using ht
  exact ht'.mono nhdsWithin_le_nhds

private theorem taylor8_isLittleO_nhds (g : ℝ → ℝ)
    (hg : ContDiffAt ℝ 8 g 0) :
    Asymptotics.IsLittleO (nhds 0)
      (fun x => g x - taylor8 g x) (fun x => x ^ 8) := by
  have hs : ContDiffWithinAt ℝ 8 g Set.univ 0 := hg
  rcases hs.contDiffOn' le_rfl (by simp) with
    ⟨u, huopen, h0u, hgu⟩
  have hgu' : ContDiffOn ℝ 8 g u := by simpa using hgu
  rcases Metric.isOpen_iff.1 huopen 0 h0u with ⟨ε, hε, hball⟩
  have hgball : ContDiffOn ℝ 8 g (Metric.ball 0 ε) :=
    hgu'.mono hball
  have ht := taylor_isLittleO (convex_ball 0 ε)
    (Metric.mem_ball_self hε) hgball
  rw [Metric.isOpen_ball.nhdsWithin_eq
    (Metric.mem_ball_self hε)] at ht
  have heval :
      taylorWithinEval g 8 (Metric.ball 0 ε) 0 = taylor8 g := by
    funext x
    rw [taylor_within_apply]
    dsimp [taylor8]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_ball
      (Metric.mem_ball_self hε)]
    rw [← iteratedDeriv_eq_iterate]
    ring
  rw [heval] at ht
  simpa using ht

private theorem tan_iteratedDeriv_zero_values :
    iteratedDeriv 0 Real.tan 0 = 0 ∧
    iteratedDeriv 1 Real.tan 0 = 1 ∧
    iteratedDeriv 2 Real.tan 0 = 0 ∧
    iteratedDeriv 3 Real.tan 0 = 2 ∧
    iteratedDeriv 4 Real.tan 0 = 0 ∧
    iteratedDeriv 5 Real.tan 0 = 16 ∧
    iteratedDeriv 6 Real.tan 0 = 0 ∧
    iteratedDeriv 7 Real.tan 0 = 272 ∧
    iteratedDeriv 8 Real.tan 0 = 0 := by
  have h1 := ProofGap.Exercise1394_3.gap2 0 (by norm_num)
  have h2 := ProofGap.Exercise1394_3.gap3 0 (by norm_num)
  have hs4 : ContDiffAt ℝ 4 ProofGap.Exercise1394_3.f 0 := by
    simpa only [ProofGap.Exercise1394_3.f] using
      (Real.contDiffAt_tan (n := (4 : WithTop ℕ∞))).mpr (by norm_num)
  have hs5 : ContDiffAt ℝ 5 ProofGap.Exercise1394_3.f 0 := by
    simpa only [ProofGap.Exercise1394_3.f] using
      (Real.contDiffAt_tan (n := (5 : WithTop ℕ∞))).mpr (by norm_num)
  have hs6 : ContDiffAt ℝ 6 ProofGap.Exercise1394_3.f 0 := by
    simpa only [ProofGap.Exercise1394_3.f] using
      (Real.contDiffAt_tan (n := (6 : WithTop ℕ∞))).mpr (by norm_num)
  have h3 := ProofGap.Exercise1394_3.gap4 0 (by norm_num)
  have h4 := ProofGap.Exercise1394_3.gap5 0 (by norm_num) hs4
  have h5 := ProofGap.Exercise1394_3.gap6 0 (by norm_num) hs5
  have h6 := ProofGap.Exercise1394_3.gap7 0 (by norm_num) hs6
  have hcos :
      ∀ᶠ x : ℝ in nhds 0, Real.cos x ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne (by norm_num)
  have heq :
      (deriv^[6]) Real.tan =ᶠ[nhds 0]
        (fun x =>
          32 * Real.sin x / Real.cos x ^ 3 +
            240 * Real.sin x / Real.cos x ^ 5 +
            720 * Real.sin x ^ 3 / Real.cos x ^ 7) := by
    filter_upwards [hcos] with x hc
    have hs : ContDiffAt ℝ 6 ProofGap.Exercise1394_3.f x := by
      simpa only [ProofGap.Exercise1394_3.f] using
        (Real.contDiffAt_tan (n := (6 : WithTop ℕ∞))).mpr hc
    simpa only [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] using
        ProofGap.Exercise1394_3.gap7 x hc hs
  have hd6 :
      HasDerivAt
        (fun x =>
          32 * Real.sin x / Real.cos x ^ 3 +
            240 * Real.sin x / Real.cos x ^ 5 +
            720 * Real.sin x ^ 3 / Real.cos x ^ 7)
        272 0 := by
    have h32 := ((Real.hasDerivAt_sin 0).const_mul 32).div
      ((Real.hasDerivAt_cos 0).pow 3) (by norm_num)
    have h240 := ((Real.hasDerivAt_sin 0).const_mul 240).div
      ((Real.hasDerivAt_cos 0).pow 5) (by norm_num)
    have h720 := (((Real.hasDerivAt_sin 0).pow 3).const_mul 720).div
      ((Real.hasDerivAt_cos 0).pow 7) (by norm_num)
    convert (h32.add h240).add h720 using 1 <;> norm_num
  have h7it : (deriv^[7]) Real.tan 0 = 272 := by
    rw [show (deriv^[7]) Real.tan =
      deriv ((deriv^[6]) Real.tan) by
        rw [show 7 = 6 + 1 by norm_num, Function.iterate_succ_apply']]
    rw [heq.deriv_eq]
    exact hd6.deriv
  have h8it : iteratedDeriv 8 Real.tan 0 = 0 := by
    have hfun : (fun t : ℝ => Real.tan (-t)) = fun t => -Real.tan t := by
      funext t
      simp
    have h := congrArg
      (fun g : ℝ → ℝ => iteratedDeriv 8 g 0) hfun
    change iteratedDeriv 8 (fun t => Real.tan (-t)) 0 =
      iteratedDeriv 8 (-Real.tan) 0 at h
    rw [iteratedDeriv_comp_neg, iteratedDeriv_neg] at h
    norm_num at h
    linarith
  have ih1 : iteratedDeriv 1 Real.tan 0 = 1 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h1
    norm_num at h1
    simpa only [iteratedDeriv_eq_iterate] using h1
  have ih2 : iteratedDeriv 2 Real.tan 0 = 0 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h2
    norm_num at h2
    simpa only [iteratedDeriv_eq_iterate] using h2
  have ih3 : iteratedDeriv 3 Real.tan 0 = 2 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h3
    norm_num at h3
    simpa only [iteratedDeriv_eq_iterate] using h3
  have ih4 : iteratedDeriv 4 Real.tan 0 = 0 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h4
    norm_num at h4
    simpa only [iteratedDeriv_eq_iterate] using h4
  have ih5 : iteratedDeriv 5 Real.tan 0 = 16 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h5
    norm_num at h5
    simpa only [iteratedDeriv_eq_iterate] using h5
  have ih6 : iteratedDeriv 6 Real.tan 0 = 0 := by
    dsimp [ProofGap.Exercise1394_3.iterDeriv,
      ProofGap.Exercise1394_3.f] at h6
    norm_num at h6
    simpa only [iteratedDeriv_eq_iterate] using h6
  refine ⟨by norm_num, ih1, ih2, ih3, ih4, ih5, ih6, ?_, h8it⟩
  simpa only [← iteratedDeriv_eq_iterate] using h7it

private theorem sin_error_nhds :
    Asymptotics.IsLittleO (nhds 0)
      (fun x => Real.sin x - sinPoly x) (fun x => x ^ 7) := by
  have ht := taylor8_isLittleO_nhds Real.sin
    (Real.contDiff_sin (n := (8 : WithTop ℕ∞))).contDiffAt
  have h87 :
      (fun x : ℝ => x ^ 8) =o[nhds 0] (fun x => x ^ 7) :=
    Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 7 < 8)
  have hpoly : taylor8 Real.sin = sinPoly := by
    funext x
    norm_num [taylor8, sinPoly, Finset.sum_range_succ,
      Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  simpa only [hpoly] using ht.trans h87

theorem gap1 :
    Asymptotics.IsLittleO punctured
      (fun x => Real.sin x - sinPoly x) (fun x => x ^ 7) := by
  have ht := taylor8_isLittleO Real.sin
    (Real.contDiff_sin (n := (8 : WithTop ℕ∞))).contDiffAt
  have h87 :
      (fun x : ℝ => x ^ 8) =o[punctured] (fun x => x ^ 7) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 7 < 8)).mono
      nhdsWithin_le_nhds
  have hpoly : taylor8 Real.sin = sinPoly := by
    funext x
    norm_num [taylor8, sinPoly, Finset.sum_range_succ,
      Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  simpa only [hpoly] using ht.trans h87

private theorem tan_error_nhds :
    Asymptotics.IsLittleO (nhds 0)
      (fun x => Real.tan x - tanPoly x) (fun x => x ^ 7) := by
  have ht := taylor8_isLittleO_nhds Real.tan
    ((Real.contDiffAt_tan (n := (8 : WithTop ℕ∞))).mpr (by norm_num))
  have h87 :
      (fun x : ℝ => x ^ 8) =o[nhds 0] (fun x => x ^ 7) :=
    Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 7 < 8)
  rcases tan_iteratedDeriv_zero_values with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hpoly : taylor8 Real.tan = tanPoly := by
    funext x
    norm_num [taylor8, tanPoly, Finset.sum_range_succ,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
    ring
  simpa only [hpoly] using ht.trans h87
theorem gap2 :
    Asymptotics.IsLittleO punctured
      (fun x => Real.tan x - tanPoly x) (fun x => x ^ 7) := by
  have ht := taylor8_isLittleO Real.tan
    ((Real.contDiffAt_tan (n := (8 : WithTop ℕ∞))).mpr (by norm_num))
  have h87 :
      (fun x : ℝ => x ^ 8) =o[punctured] (fun x => x ^ 7) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 7 < 8)).mono
      nhdsWithin_le_nhds
  rcases tan_iteratedDeriv_zero_values with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hpoly : taylor8 Real.tan = tanPoly := by
    funext x
    norm_num [taylor8, tanPoly, Finset.sum_range_succ,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
    ring
  simpa only [hpoly] using ht.trans h87
theorem gap3 (x : ℝ) :
    y x = Real.tan (Real.sin x) - Real.sin (Real.tan x) := by
  rfl
theorem gap4 :
    Asymptotics.IsLittleO punctured
      (fun x =>
        y x - (tanPoly (sinPoly x) -
          sinPoly (tanPoly x))) (fun x => x ^ 7) := by
  have hp : punctured ≤ nhds (0 : ℝ) := by
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) punctured (nhds 0) :=
    tendsto_id.mono_left hp
  have hsin0 : Tendsto Real.sin punctured (nhds 0) := by
    simpa using Real.continuous_sin.continuousAt.tendsto.comp hid
  have htan0 : Tendsto Real.tan punctured (nhds 0) := by
    have ht : ContinuousAt Real.tan 0 :=
      Real.continuousAt_tan.mpr (by norm_num)
    simpa using ht.tendsto.comp hid
  have hsinPoly0 : Tendsto sinPoly punctured (nhds 0) := by
    have ht : ContinuousAt sinPoly 0 := by
      unfold sinPoly
      fun_prop
    simpa [sinPoly] using ht.tendsto.comp hid
  have htanPoly0 : Tendsto tanPoly punctured (nhds 0) := by
    have ht : ContinuousAt tanPoly 0 := by
      unfold tanPoly
      fun_prop
    simpa [tanPoly] using ht.tendsto.comp hid
  have hsinO : Real.sin =O[punctured] (fun x : ℝ => x) := by
    have h := (Real.hasDerivAt_sin 0).isBigO_sub.mono hp
    simpa using h
  have htanO : Real.tan =O[punctured] (fun x : ℝ => x) := by
    have h := (Real.hasDerivAt_tan (by norm_num : Real.cos 0 ≠ 0)).isBigO_sub.mono hp
    simpa using h
  have hA :
      (fun x => Real.tan (Real.sin x) - tanPoly (Real.sin x)) =o[punctured]
        (fun x : ℝ => x ^ 7) := by
    have hc := tan_error_nhds.comp_tendsto hsin0
    have hp7 := hsinO.pow 7
    simpa only [Function.comp_apply] using hc.trans_isBigO hp7
  have hC :
      (fun x => Real.sin (Real.tan x) - sinPoly (Real.tan x)) =o[punctured]
        (fun x : ℝ => x ^ 7) := by
    have hc := sin_error_nhds.comp_tendsto htan0
    have hp7 := htanO.pow 7
    simpa only [Function.comp_apply] using hc.trans_isBigO hp7
  have htanFactor0 :
      Tendsto (fun x => tanFactor (Real.sin x) (sinPoly x))
        punctured (nhds 1) := by
    have h :
        Tendsto (fun x => tanFactor (Real.sin x) (sinPoly x))
          punctured (nhds (tanFactor 0 0)) := by
      have hpairs :
          Tendsto (fun x => (Real.sin x, sinPoly x)) punctured
            (nhds (0, 0)) := by
        simpa only [nhds_prod_eq] using hsin0.prodMk hsinPoly0
      have hc :
          ContinuousAt (fun p : ℝ × ℝ => tanFactor p.1 p.2) (0, 0) := by
        set_option maxHeartbeats 800000 in
          unfold tanFactor
          fun_prop
      simpa only [Function.comp_apply] using hc.tendsto.comp hpairs
    simpa only [tanFactor_zero] using h
  have hsinFactor0 :
      Tendsto (fun x => sinFactor (Real.tan x) (tanPoly x))
        punctured (nhds 1) := by
    have h :
        Tendsto (fun x => sinFactor (Real.tan x) (tanPoly x))
          punctured (nhds (sinFactor 0 0)) := by
      have hpairs :
          Tendsto (fun x => (Real.tan x, tanPoly x)) punctured
            (nhds (0, 0)) := by
        simpa only [nhds_prod_eq] using htan0.prodMk htanPoly0
      have hc :
          ContinuousAt (fun p : ℝ × ℝ => sinFactor p.1 p.2) (0, 0) := by
        set_option maxHeartbeats 800000 in
          unfold sinFactor
          fun_prop
      simpa only [Function.comp_apply] using hc.tendsto.comp hpairs
    simpa only [sinFactor_zero] using h
  have hB :
      (fun x => tanPoly (Real.sin x) - tanPoly (sinPoly x)) =o[punctured]
        (fun x : ℝ => x ^ 7) := by
    have h := gap1.mul_isBigO (htanFactor0.isBigO_one ℝ)
    convert h using 1
    · funext x
      exact tanPoly_sub (Real.sin x) (sinPoly x)
    · funext x
      ring
  have hD :
      (fun x => sinPoly (Real.tan x) - sinPoly (tanPoly x)) =o[punctured]
        (fun x : ℝ => x ^ 7) := by
    have h := gap2.mul_isBigO (hsinFactor0.isBigO_one ℝ)
    convert h using 1
    · funext x
      exact sinPoly_sub (Real.tan x) (tanPoly x)
    · funext x
      ring
  have hsum := (hA.add hB).sub (hC.add hD)
  refine hsum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  exact Eventually.of_forall fun x => by
    simp only [y]
    ring
theorem gap5 :
    Asymptotics.IsLittleO punctured
      (fun x => y x - x ^ 7 / 30) (fun x => x ^ 7) := by
  have hp : punctured ≤ nhds (0 : ℝ) := inf_le_left
  have h97 :
      (fun x : ℝ => x ^ 9) =o[punctured] (fun x => x ^ 7) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 7 < 9)).mono hp
  have hfactor0 :
      Tendsto compositionFactor punctured (nhds (compositionFactor 0)) := by
    have hc : ContinuousAt compositionFactor 0 := by
      unfold compositionFactor
      fun_prop
    exact hc.tendsto.mono_left hp
  have hfactorO :
      compositionFactor =O[punctured] (fun _ : ℝ => (1 : ℝ)) :=
    hfactor0.isBigO_one ℝ
  have hpoly :
      (fun x =>
        tanPoly (sinPoly x) - sinPoly (tanPoly x) - x ^ 7 / 30) =o[punctured]
        (fun x : ℝ => x ^ 7) := by
    have h := h97.mul_isBigO hfactorO
    convert h using 1
    · funext x
      exact polynomial_composition_error x
    · funext x
      ring
  have h := gap4.add hpoly
  convert h using 1 <;> ext x <;> ring
theorem gap6 :
    Asymptotics.IsEquivalent punctured y (fun x => x ^ 7 / 30) := by
  change (fun x => y x - x ^ 7 / 30) =o[punctured]
    (fun x => x ^ 7 / 30)
  have h := gap5.const_mul_right (by norm_num : (1 / 30 : ℝ) ≠ 0)
  convert h using 1 <;> ext x <;> ring

end
end ProofGap.Exercise1407
