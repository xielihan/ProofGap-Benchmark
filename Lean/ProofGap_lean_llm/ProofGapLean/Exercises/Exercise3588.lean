import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3588

noncomputable section

abbrev Triple := ℝ × (ℝ × ℝ)

def target (q : Triple) : ℝ :=
  Real.cos (q.1 + q.2.1 + q.2.2) -
    Real.cos q.1 * Real.cos q.2.1 * Real.cos q.2.2

def quadraticStage (q : Triple) : ℝ :=
  1 - (1 / 2 : ℝ) * (q.1 + q.2.1 + q.2.2) ^ 2 -
    (1 - (1 / 2 : ℝ) * q.1 ^ 2) *
      (1 - (1 / 2 : ℝ) * q.2.1 ^ 2) *
      (1 - (1 / 2 : ℝ) * q.2.2 ^ 2)

def expandedStage (q : Triple) : ℝ :=
  1 - (1 / 2 : ℝ) * (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2) -
    (q.1 * q.2.1 + q.2.1 * q.2.2 + q.2.2 * q.1) -
    (1 - (1 / 2 : ℝ) * q.1 ^ 2 -
      (1 / 2 : ℝ) * q.2.1 ^ 2 - (1 / 2 : ℝ) * q.2.2 ^ 2)

def crossTerm (q : Triple) : ℝ :=
  -(q.1 * q.2.1 + q.2.1 * q.2.2 + q.2.2 * q.1)

def AgreesToSecondOrder (g p : Triple → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, (0, 0)))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 2)

private theorem secondOrderCore :
    AgreesToSecondOrder target quadraticStage ∧
      AgreesToSecondOrder target expandedStage := by
  let l := nhds ((0, (0, 0)) : Triple)
  let N : Triple → ℝ := fun q => ‖q‖ ^ 2
  have hsin :
      (fun x : ℝ => Real.sin x - x) =o[nhds 0]
        (fun x : ℝ => x) := by
    exact Real.isEquivalent_sin
  have hhalfT :
      Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
    have hc : Continuous (fun x : ℝ => x * (2 : ℝ)⁻¹) :=
      continuous_id.mul continuous_const
    simpa only [ContinuousAt, div_eq_mul_inv, zero_mul] using
      (hc.continuousAt :
        ContinuousAt (fun x : ℝ => x * (2 : ℝ)⁻¹) 0)
  have hsinHalf :
      (fun x : ℝ => Real.sin (x / 2) - x / 2) =o[nhds 0]
        (fun x : ℝ => x / 2) := by
    simpa using hsin.comp_tendsto hhalfT
  have hplus :
      (fun x : ℝ => Real.sin (x / 2) + x / 2) =O[nhds 0]
        (fun x : ℝ => x / 2) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    calc
      |Real.sin (x / 2) + x / 2| ≤
          |Real.sin (x / 2)| + |x / 2| := abs_add_le _ _
      _ ≤ |x / 2| + |x / 2| :=
        add_le_add
          (show |Real.sin (x / 2)| ≤ |x / 2| from Real.abs_sin_le_abs)
          (le_refl _)
      _ = 2 * |x / 2| := by ring
  have hscale :
      (fun x : ℝ => (x / 2) * (x / 2)) =O[nhds 0]
        (fun x : ℝ => x ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with x
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    simp only [pow_two, Real.norm_eq_abs, abs_mul, abs_div, one_mul, h2]
    nlinarith [sq_nonneg |x|]
  have hraw :
      (fun x : ℝ =>
        (-2 : ℝ) *
          ((Real.sin (x / 2) - x / 2) *
            (Real.sin (x / 2) + x / 2))) =o[nhds 0]
        (fun x : ℝ => (x / 2) * (x / 2)) := by
    convert (hsinHalf.mul_isBigO hplus).const_mul_left (-2 : ℝ) using 1 <;>
      funext x <;> ring
  have hfun :
      (fun x : ℝ =>
        Real.cos x - (1 - (1 / 2 : ℝ) * x ^ 2)) =
      (fun x : ℝ =>
        (-2 : ℝ) *
          ((Real.sin (x / 2) - x / 2) *
            (Real.sin (x / 2) + x / 2))) := by
    funext x
    have hcosid :
        Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      calc
        Real.cos x = Real.cos (x / 2 + x / 2) := by
          exact congrArg Real.cos (by ring)
        _ = Real.cos (x / 2) * Real.cos (x / 2) -
            Real.sin (x / 2) * Real.sin (x / 2) :=
          Real.cos_add _ _
        _ = 1 - 2 * Real.sin (x / 2) ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    rw [hcosid]
    ring
  have hcos :
      (fun x : ℝ =>
        Real.cos x - (1 - (1 / 2 : ℝ) * x ^ 2)) =o[nhds 0]
        (fun x : ℝ => x ^ 2) := by
    rw [hfun]
    exact hraw.trans_isBigO hscale
  have hsquareO : ∀ (u : Triple → ℝ),
      Filter.Tendsto u l (nhds 0) → ∀ C : ℝ,
      (∀ q, ‖u q‖ ≤ C * ‖q‖) →
      (fun q => u q ^ 2) =O[l] N := by
    intro u hu C hbound
    refine Asymptotics.IsBigO.of_bound (C ^ 2) ?_
    filter_upwards with q
    have hsq := mul_self_le_mul_self (norm_nonneg (u q)) (hbound q)
    simp only [N, norm_pow, norm_norm]
    nlinarith [hsq]
  have hsquareSmall : ∀ (u : Triple → ℝ),
      Filter.Tendsto u l (nhds 0) →
      (fun q => u q ^ 2) =o[l] (fun _ => (1 : ℝ)) := by
    intro u hu
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    have hmin : 0 < min c 1 := lt_min hc zero_lt_one
    have hevent : ∀ᶠ q in l, u q ∈ Metric.ball (0 : ℝ) (min c 1) :=
      hu.eventually (Metric.ball_mem_nhds 0 hmin)
    filter_upwards [hevent] with q hq
    have huabs : |u q| < min c 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have huc : |u q| < c :=
      lt_of_lt_of_le huabs (min_le_left _ _)
    have huone : |u q| < 1 :=
      lt_of_lt_of_le huabs (min_le_right _ _)
    have hprod : 0 ≤ |u q| * (1 - |u q|) :=
      mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (le_of_lt huone))
    simp only [norm_pow, Real.norm_eq_abs, norm_one, mul_one]
    nlinarith
  have hlift : ∀ (u : Triple → ℝ),
      Filter.Tendsto u l (nhds 0) → ∀ C : ℝ,
      (∀ q, ‖u q‖ ≤ C * ‖q‖) →
      (fun q => Real.cos (u q) - (1 - (1 / 2 : ℝ) * u q ^ 2)) =o[l] N := by
    intro u hu C hbound
    exact (hcos.comp_tendsto hu).trans_isBigO
      (hsquareO u hu C hbound)
  have hquadraticO : ∀ (u : Triple → ℝ),
      Filter.Tendsto u l (nhds 0) →
      (fun q => 1 - (1 / 2 : ℝ) * u q ^ 2) =O[l]
        (fun _ => (1 : ℝ)) := by
    intro u hu
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have hevent : ∀ᶠ q in l, u q ∈ Metric.ball (0 : ℝ) 1 :=
      hu.eventually (Metric.ball_mem_nhds 0 zero_lt_one)
    filter_upwards [hevent] with q hq
    have huabs : |u q| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have hu_sq_lt : u q ^ 2 < 1 := by
      rcases abs_lt.mp huabs with ⟨hu_lower, hu_upper⟩
      nlinarith [mul_pos (sub_pos.mpr hu_upper)
        (by linarith : 0 < u q + 1)]
    have hnon : 0 ≤ 1 - (1 / 2 : ℝ) * u q ^ 2 := by
      nlinarith [sq_nonneg (u q)]
    simp only [norm_one, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg hnon]
    nlinarith
  have hcosO : ∀ u : Triple → ℝ,
      (fun q => Real.cos (u q)) =O[l] (fun _ => (1 : ℝ)) := by
    intro u
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with q
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (u q)
  have haC : Continuous (fun q : Triple => q.1) := continuous_fst
  have hbC : Continuous (fun q : Triple => q.2.1) :=
    continuous_fst.comp continuous_snd
  have hcC : Continuous (fun q : Triple => q.2.2) :=
    continuous_snd.comp continuous_snd
  have hsC : Continuous (fun q : Triple => q.1 + q.2.1 + q.2.2) :=
    (haC.add hbC).add hcC
  have haT : Filter.Tendsto (fun q : Triple => q.1) l (nhds 0) := by
    simpa [l] using
      (haC.continuousAt :
        ContinuousAt (fun q : Triple => q.1) ((0, (0, 0)) : Triple))
  have hbT : Filter.Tendsto (fun q : Triple => q.2.1) l (nhds 0) := by
    simpa [l] using
      (hbC.continuousAt :
        ContinuousAt (fun q : Triple => q.2.1) ((0, (0, 0)) : Triple))
  have hcT : Filter.Tendsto (fun q : Triple => q.2.2) l (nhds 0) := by
    simpa [l] using
      (hcC.continuousAt :
        ContinuousAt (fun q : Triple => q.2.2) ((0, (0, 0)) : Triple))
  have hsT : Filter.Tendsto
      (fun q : Triple => q.1 + q.2.1 + q.2.2) l (nhds 0) := by
    simpa [l, ContinuousAt] using
      (hsC.continuousAt :
        ContinuousAt (fun q : Triple => q.1 + q.2.1 + q.2.2)
          ((0, (0, 0)) : Triple))
  have haB : ∀ q : Triple, ‖q.1‖ ≤ 1 * ‖q‖ := by
    intro q
    simp [Prod.norm_def]
  have hbB : ∀ q : Triple, ‖q.2.1‖ ≤ 1 * ‖q‖ := by
    intro q
    simp [Prod.norm_def]
  have hcB : ∀ q : Triple, ‖q.2.2‖ ≤ 1 * ‖q‖ := by
    intro q
    simp [Prod.norm_def]
  have hsB : ∀ q : Triple,
      ‖q.1 + q.2.1 + q.2.2‖ ≤ 3 * ‖q‖ := by
    intro q
    have ha := haB q
    have hb := hbB q
    have hc := hcB q
    calc
      ‖q.1 + q.2.1 + q.2.2‖ ≤ ‖q.1 + q.2.1‖ + ‖q.2.2‖ :=
        norm_add_le _ _
      _ ≤ (‖q.1‖ + ‖q.2.1‖) + ‖q.2.2‖ := by
        exact add_le_add (norm_add_le q.1 q.2.1) (le_refl ‖q.2.2‖)
      _ ≤ 3 * ‖q‖ := by nlinarith
  have hrs := hlift (fun q : Triple => q.1 + q.2.1 + q.2.2) hsT 3 hsB
  have hra := hlift (fun q : Triple => q.1) haT 1 haB
  have hrb := hlift (fun q : Triple => q.2.1) hbT 1 hbB
  have hrc := hlift (fun q : Triple => q.2.2) hcT 1 hcB
  have hcosB := hcosO (fun q : Triple => q.2.1)
  have hcosC := hcosO (fun q : Triple => q.2.2)
  have hquadA := hquadraticO (fun q : Triple => q.1) haT
  have hquadB := hquadraticO (fun q : Triple => q.2.1) hbT
  have ht1 :
      (fun q : Triple =>
        (Real.cos q.1 - (1 - (1 / 2 : ℝ) * q.1 ^ 2)) *
          Real.cos q.2.1 * Real.cos q.2.2) =o[l] N := by
    convert (hra.mul_isBigO hcosB).mul_isBigO hcosC using 1 <;>
      funext q <;> simp
  have ht2 :
      (fun q : Triple =>
        (1 - (1 / 2 : ℝ) * q.1 ^ 2) *
          (Real.cos q.2.1 - (1 - (1 / 2 : ℝ) * q.2.1 ^ 2)) *
          Real.cos q.2.2) =o[l] N := by
    convert (hquadA.mul_isLittleO hrb).mul_isBigO hcosC using 1 <;>
      funext q <;> simp
  have ht3 :
      (fun q : Triple =>
        (1 - (1 / 2 : ℝ) * q.1 ^ 2) *
          (1 - (1 / 2 : ℝ) * q.2.1 ^ 2) *
          (Real.cos q.2.2 - (1 - (1 / 2 : ℝ) * q.2.2 ^ 2))) =o[l] N := by
    convert (hquadA.mul hquadB).mul_isLittleO hrc using 1 <;>
      funext q <;> simp
  have hprod :
      (fun q : Triple =>
        Real.cos q.1 * Real.cos q.2.1 * Real.cos q.2.2 -
          (1 - (1 / 2 : ℝ) * q.1 ^ 2) *
            (1 - (1 / 2 : ℝ) * q.2.1 ^ 2) *
            (1 - (1 / 2 : ℝ) * q.2.2 ^ 2)) =o[l] N := by
    convert (ht1.add ht2).add ht3 using 1 <;> funext q <;> ring
  have hquadRaw :
      (fun q : Triple => target q - quadraticStage q) =o[l] N := by
    convert hrs.sub hprod using 1 <;> funext q <;>
      unfold target quadraticStage <;> ring
  have haO := hsquareO (fun q : Triple => q.1) haT 1 haB
  have hbO := hsquareO (fun q : Triple => q.2.1) hbT 1 hbB
  have haSmall := hsquareSmall (fun q : Triple => q.1) haT
  have hbSmall := hsquareSmall (fun q : Triple => q.2.1) hbT
  have hcSmall := hsquareSmall (fun q : Triple => q.2.2) hcT
  have hab :
      (fun q : Triple => q.1 ^ 2 * q.2.1 ^ 2) =o[l] N := by
    convert haO.mul_isLittleO hbSmall using 1 <;> funext q <;> simp
  have hbc :
      (fun q : Triple => q.2.1 ^ 2 * q.2.2 ^ 2) =o[l] N := by
    convert hbO.mul_isLittleO hcSmall using 1 <;> funext q <;> simp
  have hca :
      (fun q : Triple => q.2.2 ^ 2 * q.1 ^ 2) =o[l] N := by
    convert haO.mul_isLittleO hcSmall using 1 <;> funext q <;> simp [mul_comm]
  have habc :
      (fun q : Triple => q.1 ^ 2 * q.2.1 ^ 2 * q.2.2 ^ 2) =o[l] N := by
    convert hab.mul_isBigO hcSmall.isBigO using 1 <;> funext q <;> simp
  have hpoly :=
    (((hab.const_mul_left (-(1 / 4 : ℝ))).add
      (hbc.const_mul_left (-(1 / 4 : ℝ)))).add
      (hca.const_mul_left (-(1 / 4 : ℝ)))).add
      (habc.const_mul_left (1 / 8 : ℝ))
  have hhigh :
      (fun q : Triple => quadraticStage q - expandedStage q) =o[l] N := by
    convert hpoly using 1 <;> funext q <;>
      unfold quadraticStage expandedStage <;> ring
  have hexpandedRaw :
      (fun q : Triple => target q - expandedStage q) =o[l] N := by
    convert hquadRaw.add hhigh using 1 <;> funext q <;> ring
  constructor
  · unfold AgreesToSecondOrder
    simpa [l, N] using hquadRaw
  · unfold AgreesToSecondOrder
    simpa [l, N] using hexpandedRaw

theorem gap1 :
    AgreesToSecondOrder target quadraticStage := by
  exact secondOrderCore.1

theorem gap2 :
    AgreesToSecondOrder target expandedStage := by
  exact secondOrderCore.2

theorem gap3 :
    ∀ q : Triple, expandedStage q = crossTerm q := by
  intro q
  unfold expandedStage crossTerm
  ring

theorem gap4 :
    AgreesToSecondOrder target crossTerm := by
  simpa only [AgreesToSecondOrder, gap3] using gap2

end

end ProofGap.Exercise3588
