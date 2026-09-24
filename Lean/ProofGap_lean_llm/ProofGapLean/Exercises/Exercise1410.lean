import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1410

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def y (a b x : ℝ) := x - (a + b * Real.cos x) * Real.sin x
def fifthModel (c x : ℝ) := c * x ^ 5
def FifthOrder (a b : ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧
    Asymptotics.IsEquivalent punctured (y a b) (fifthModel c)

private def sinFifth (x : ℝ) :=
  x - x ^ 3 / 6 + x ^ 5 / 120

private def taylor6 (g : ℝ → ℝ) (x : ℝ) :=
  ∑ k ∈ Finset.range 7,
    x ^ k / (Nat.factorial k : ℝ) * iteratedDeriv k g 0

private theorem taylor6_isLittleO (g : ℝ → ℝ)
    (hg : ContDiffAt ℝ 6 g 0) :
    (fun x => g x - taylor6 g x) =o[punctured]
      (fun x : ℝ => x ^ 6) := by
  have hs : ContDiffWithinAt ℝ 6 g Set.univ 0 := hg
  rcases hs.contDiffOn' le_rfl (by simp) with
    ⟨u, huopen, h0u, hgu⟩
  have hgu' : ContDiffOn ℝ 6 g u := by simpa using hgu
  rcases Metric.isOpen_iff.1 huopen 0 h0u with ⟨ε, hε, hball⟩
  have hgball : ContDiffOn ℝ 6 g (Metric.ball 0 ε) :=
    hgu'.mono hball
  have ht := taylor_isLittleO (convex_ball 0 ε)
    (Metric.mem_ball_self hε) hgball
  rw [Metric.isOpen_ball.nhdsWithin_eq
    (Metric.mem_ball_self hε)] at ht
  have heval :
      taylorWithinEval g 6 (Metric.ball 0 ε) 0 = taylor6 g := by
    funext x
    rw [taylor_within_apply]
    dsimp [taylor6]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_ball
      (Metric.mem_ball_self hε)]
    rw [← iteratedDeriv_eq_iterate]
    ring
  rw [heval] at ht
  have ht' :
      (fun x => g x - taylor6 g x) =o[nhds 0]
        (fun x : ℝ => x ^ 6) := by
    simpa using ht
  exact ht'.mono nhdsWithin_le_nhds

private theorem sin_fifth_isLittleO :
    (fun x : ℝ => Real.sin x - sinFifth x) =o[punctured]
      (fun x => x ^ 5) := by
  have ht := taylor6_isLittleO Real.sin
    (Real.contDiff_sin (n := (6 : WithTop ℕ∞))).contDiffAt
  have h65 :
      (fun x : ℝ => x ^ 6) =o[punctured] (fun x => x ^ 5) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 5 < 6)).mono
      nhdsWithin_le_nhds
  have hpoly : taylor6 Real.sin = sinFifth := by
    funext x
    norm_num [taylor6, sinFifth, Finset.sum_range_succ,
      Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  simpa only [hpoly] using ht.trans h65

private theorem scale_two_tendsto_punctured :
    Tendsto (fun x : ℝ => 2 * x) punctured punctured := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  haveI : NeBot punctured := by
    unfold punctured
    infer_instance
  have hid : Tendsto (fun x : ℝ => x) punctured (𝓝 0) :=
    tendsto_id.mono_left hp_le
  have hnhds : Tendsto (fun x : ℝ => 2 * x) punctured (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hid :
        Tendsto (fun x : ℝ => 2 * x) punctured (𝓝 (2 * 0)))
  unfold punctured
  refine tendsto_nhdsWithin_iff.mpr ⟨hnhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  exact mul_ne_zero (by norm_num) hx0

private theorem sin_two_fifth_isLittleO :
    (fun x : ℝ => Real.sin (2 * x) - sinFifth (2 * x)) =o[punctured]
      (fun x => x ^ 5) := by
  have hcomp := sin_fifth_isLittleO.comp_tendsto scale_two_tendsto_punctured
  have hmodel :
      (fun x : ℝ => (2 * x) ^ 5) =O[punctured] (fun x => x ^ 5) := by
    convert (Asymptotics.isBigO_refl (fun x : ℝ => x ^ 5) punctured).const_mul_left
      32 using 1 <;> ext x <;> ring
  exact hcomp.trans_isBigO hmodel

theorem gap1 (a b x : ℝ) :
    y a b x = x - a * Real.sin x - (b / 2) * Real.sin (2 * x) := by
  rw [Real.sin_two_mul]
  unfold y
  ring
theorem gap2 (a b : ℝ) :
    Asymptotics.IsLittleO punctured
      (fun x => y a b x -
        ((1 - a - b) * x + (a / 6 + 2 * b / 3) * x ^ 3 -
          (a / 120 + 2 * b / 15) * x ^ 5))
      (fun x => x ^ 5) := by
  have h :=
    (sin_fifth_isLittleO.const_mul_left (-a)).add
      (sin_two_fifth_isLittleO.const_mul_left (-b / 2))
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards with x
  rw [gap1]
  unfold sinFifth
  ring
theorem gap3 (a b : ℝ) :
    Asymptotics.IsLittleO punctured
      (fun x => y a b x -
        ((1 - a - b) * x + (a / 6 + 2 * b / 3) * x ^ 3 -
          (a / 120 + 2 * b / 15) * x ^ 5))
      (fun x => x ^ 5) := by
  exact gap2 a b
theorem gap4 (a b : ℝ) :
    FifthOrder a b ↔
      1 - a - b = 0 ∧ a / 6 + 2 * b / 3 = 0 := by
  let p : ℝ → ℝ := fun x =>
    (1 - a - b) * x + (a / 6 + 2 * b / 3) * x ^ 3 -
      (a / 120 + 2 * b / 15) * x ^ 5
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  haveI : NeBot punctured := by
    unfold punctured
    infer_instance
  have hid : Tendsto (fun x : ℝ => x) punctured (𝓝 0) :=
    tendsto_id.mono_left hp_le
  have hxne : ∀ᶠ x : ℝ in punctured, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have h51 :
      (fun x : ℝ => x ^ 5) =o[punctured] (fun x => x) := by
    simpa using
      (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 1 < 5)).mono hp_le
  have h53 :
      (fun x : ℝ => x ^ 5) =o[punctured] (fun x => x ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 3 < 5)).mono hp_le
  constructor
  · rintro ⟨c, hc, hequiv⟩
    change (fun x => y a b x - c * x ^ 5) =o[punctured]
      (fun x => c * x ^ 5) at hequiv
    have hcO :
        (fun x : ℝ => c * x ^ 5) =O[punctured] (fun x => x ^ 5) := by
      exact (Asymptotics.isBigO_refl (fun x : ℝ => x ^ 5) punctured).const_mul_left c
    have hyc :
        (fun x => y a b x - c * x ^ 5) =o[punctured]
          (fun x => x ^ 5) :=
      hequiv.trans_isBigO hcO
    have hpc :
        (fun x => p x - c * x ^ 5) =o[punctured]
          (fun x => x ^ 5) := by
      have h :=
        ((gap2 a b).const_mul_left (-1 : ℝ)).add hyc
      convert h using 1 <;> ext x <;> simp [p] <;> ring
    have hp1 : p =o[punctured] (fun x : ℝ => x) := by
      have h :=
        (hpc.trans h51).add (h51.const_mul_left c)
      convert h using 1 <;> ext x <;> ring
    have hratio1 :
        Tendsto (fun x => p x / x) punctured (𝓝 0) := by
      apply (Asymptotics.isLittleO_iff_tendsto ?_).1 hp1
      intro x hx
      subst x
      simp [p]
    have heqratio1 :
        (fun x => p x / x) =ᶠ[punctured]
          (fun x =>
            (1 - a - b) + (a / 6 + 2 * b / 3) * x ^ 2 -
              (a / 120 + 2 * b / 15) * x ^ 4) := by
      filter_upwards [hxne] with x hx
      dsimp [p]
      field_simp
    have hpoly1 :
        Tendsto
          (fun x : ℝ =>
            (1 - a - b) + (a / 6 + 2 * b / 3) * x ^ 2 -
              (a / 120 + 2 * b / 15) * x ^ 4)
          punctured (𝓝 (1 - a - b)) := by
      have hc :
          ContinuousAt
            (fun x : ℝ =>
              (1 - a - b) + (a / 6 + 2 * b / 3) * x ^ 2 -
                (a / 120 + 2 * b / 15) * x ^ 4) 0 :=
        (continuousAt_const.add
          (continuousAt_const.mul (continuousAt_id.pow 2))).sub
            (continuousAt_const.mul (continuousAt_id.pow 4))
      convert hc.tendsto.mono_left hp_le using 1 <;> ring
    have hlin : 1 - a - b = 0 := by
      have hratio1' := hpoly1.congr' heqratio1.symm
      exact (tendsto_nhds_unique hratio1 hratio1').symm
    have hp3 : p =o[punctured] (fun x : ℝ => x ^ 3) := by
      have h :=
        (hpc.trans h53).add (h53.const_mul_left c)
      convert h using 1 <;> ext x <;> ring
    have hratio3 :
        Tendsto (fun x => p x / x ^ 3) punctured (𝓝 0) := by
      apply (Asymptotics.isLittleO_iff_tendsto ?_).1 hp3
      intro x hx
      have hx0 : x = 0 := pow_eq_zero hx
      subst x
      simp [p]
    have heqratio3 :
        (fun x => p x / x ^ 3) =ᶠ[punctured]
          (fun x =>
            (a / 6 + 2 * b / 3) -
              (a / 120 + 2 * b / 15) * x ^ 2) := by
      filter_upwards [hxne] with x hx
      dsimp [p]
      rw [hlin]
      field_simp
      ring
    have hpoly3 :
        Tendsto
          (fun x : ℝ =>
            (a / 6 + 2 * b / 3) -
              (a / 120 + 2 * b / 15) * x ^ 2)
          punctured (𝓝 (a / 6 + 2 * b / 3)) := by
      have hc :
          ContinuousAt
            (fun x : ℝ =>
              (a / 6 + 2 * b / 3) -
                (a / 120 + 2 * b / 15) * x ^ 2) 0 :=
        continuousAt_const.sub
          (continuousAt_const.mul (continuousAt_id.pow 2))
      convert hc.tendsto.mono_left hp_le using 1 <;> ring
    have hcubic : a / 6 + 2 * b / 3 = 0 := by
      have hratio3' := hpoly3.congr' heqratio3.symm
      exact (tendsto_nhds_unique hratio3 hratio3').symm
    exact ⟨hlin, hcubic⟩
  · rintro ⟨hlin, hcubic⟩
    have ha : a = 4 / 3 := by linarith
    have hb : b = -(1 / 3 : ℝ) := by linarith
    subst a
    subst b
    refine ⟨1 / 30, by norm_num, ?_⟩
    change (fun x => y (4 / 3) (-(1 / 3)) x - (1 / 30) * x ^ 5)
      =o[punctured] (fun x => (1 / 30) * x ^ 5)
    have hrem :
        (fun x => y (4 / 3) (-(1 / 3)) x - (1 / 30) * x ^ 5)
          =o[punctured] (fun x => x ^ 5) := by
      convert gap2 (4 / 3) (-(1 / 3)) using 1 <;> ext x <;> norm_num <;> ring
    have hmodel :
        (fun x : ℝ => x ^ 5) =O[punctured]
          (fun x => (1 / 30) * x ^ 5) := by
      convert
        (Asymptotics.isBigO_refl (fun x : ℝ => (1 / 30) * x ^ 5) punctured)
          |>.const_mul_left 30 using 1 <;> ext x <;> ring
    exact hrem.trans_isBigO hmodel
theorem gap5 (a b : ℝ) (hlin : 1 - a - b = 0) :
    FifthOrder a b ↔ a = 4 / 3 := by
  constructor
  · intro hF
    have hcubic := (gap4 a b).1 hF |>.2
    linarith
  · intro ha
    apply (gap4 a b).2
    constructor
    · exact hlin
    · linarith
theorem gap6 (a b : ℝ) (hcubic : a / 6 + 2 * b / 3 = 0) :
    FifthOrder a b ↔ b = -(1 / 3 : ℝ) := by
  constructor
  · intro hF
    have hlin := (gap4 a b).1 hF |>.1
    linarith
  · intro hb
    apply (gap4 a b).2
    constructor
    · linarith
    · exact hcubic
theorem gap7 (a b : ℝ) :
    (a, b) = ((4 / 3 : ℝ), -(1 / 3 : ℝ)) ↔ FifthOrder a b := by
  constructor
  · intro hab
    have ha := congrArg Prod.fst hab
    have hb := congrArg Prod.snd hab
    simp only at ha hb
    subst a
    subst b
    apply (gap4 (4 / 3) (-(1 / 3))).2
    constructor <;> norm_num
  · intro hF
    rcases (gap4 a b).1 hF with ⟨hlin, hcubic⟩
    apply Prod.ext <;> dsimp <;> linarith

end
end ProofGap.Exercise1410
