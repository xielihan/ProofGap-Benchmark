import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4293_2

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def force (k : ℝ) (p : Point) : Point :=
  (-k * p.1, -k * p.2)

def potential (k : ℝ) (p : Point) : ℝ :=
  -(k / 2) * (p.1 ^ 2 + p.2 ^ 2)

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (A : Point → ℝ) (p v : Point) : ℝ :=
  deriv (fun x => A (x, p.2)) p.1 * v.1 +
    deriv (fun y => A (p.1, y)) p.2 * v.2

def lineIntegral (k : ℝ) (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    coordinateDifferential (force k (γ t))
      (deriv (fun s => (γ s).1) t, deriv (fun s => (γ s).2) t)

def radialIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (γ t).1 * deriv (fun s => (γ s).1) t +
      (γ t).2 * deriv (fun s => (γ s).2) t

def EllipsePath (a b : ℝ) (γ : ℝ → Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = (a, 0) ∧ γ 1 = (0, b) ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
      (γ t).1 ^ 2 / a ^ 2 + (γ t).2 ^ 2 / b ^ 2 = 1

private theorem primitive_hasDerivAt
    (d : ℝ → ℝ) (hd : Continuous d) (a x : ℝ) :
    HasDerivAt (fun u => ∫ t in a..u, d t) (d x) x := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hU : d ⁻¹' Metric.ball (d x) c ∈ nhds x :=
    hd.continuousAt (Metric.ball_mem_nhds _ hc)
  rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hδU⟩
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hres :
      (∫ t in a..y, d t) - (∫ t in a..x, d t) - (y - x) * d x =
        ∫ t in x..y, (d t - d x) := by
    rw [intervalIntegral.integral_interval_sub_left
      (hd.intervalIntegrable a y) (hd.intervalIntegrable a x)]
    rw [intervalIntegral.integral_sub
      (hd.intervalIntegrable x y) (continuous_const.intervalIntegrable x y)]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  change ‖(∫ t in a..y, d t) - (∫ t in a..x, d t) -
      (y - x) * d x‖ ≤ c * ‖y - x‖
  rw [hres]
  calc
    ‖∫ t in x..y, (d t - d x)‖ ≤ c * |y - x| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have hdist : dist t x ≤ dist y x := by
        rw [Real.dist_eq, Real.dist_eq]
        rcases Set.mem_uIoc.mp ht with hxy | hyx
        · rw [abs_of_nonneg (sub_nonneg.mpr hxy.1.le),
            abs_of_nonneg (sub_nonneg.mpr (hxy.1.le.trans hxy.2))]
          linarith
        · rw [abs_of_nonpos (sub_nonpos.mpr hyx.2),
            abs_of_nonpos (sub_nonpos.mpr (hyx.1.le.trans hyx.2))]
          linarith
      have htδ : t ∈ Metric.ball x δ :=
        lt_of_le_of_lt hdist hy
      have htU := hδU htδ
      simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using
        (le_of_lt htU)
    _ = c * ‖y - x‖ := by rw [Real.norm_eq_abs]

private theorem localMax_hasDerivAt_eq_zero
    {f : ℝ → ℝ} {f' x : ℝ} (hmax : IsLocalMax f x)
    (hf : HasDerivAt f f' x) : f' = 0 := by
  rcases lt_trichotomy f' 0 with hneg | hzero | hpos
  · have hc : 0 < -f' / 2 := by linarith
    have herr : ∀ᶠ h in nhds 0,
        ‖f (x + h) - f x - h • f'‖ ≤ (-f' / 2) * ‖h‖ :=
      (Asymptotics.isLittleO_iff.mp
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)) hc
    have hconst : Filter.Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x) :=
      tendsto_const_nhds
    have hid : Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) :=
      Filter.tendsto_id
    have hshift : Filter.Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
      simpa using hconst.add hid
    have hmax0 : ∀ᶠ h in nhds 0, f (x + h) ≤ f x :=
      hshift hmax
    have herr' : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0),
        ‖f (x + h) - f x - h • f'‖ ≤ (-f' / 2) * ‖h‖ :=
      herr.filter_mono inf_le_left
    have hmax' : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0), f (x + h) ≤ f x :=
      hmax0.filter_mono inf_le_left
    have hlt : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0), h < 0 :=
      self_mem_nhdsWithin
    rcases (herr'.and (hmax'.and hlt)).exists with ⟨h, he, hm, hh⟩
    have he' :
        |f (x + h) - f x - h * f'| ≤ (-f' / 2) * (-h) := by
      simpa [Real.norm_eq_abs, smul_eq_mul, abs_of_neg hh] using he
    have hlow := (abs_le.mp he').1
    have hprod : 0 < h * f' := mul_pos_of_neg_of_neg hh hneg
    nlinarith
  · exact hzero
  · have hc : 0 < f' / 2 := by linarith
    have herr : ∀ᶠ h in nhds 0,
        ‖f (x + h) - f x - h • f'‖ ≤ (f' / 2) * ‖h‖ :=
      (Asymptotics.isLittleO_iff.mp
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)) hc
    have hconst : Filter.Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x) :=
      tendsto_const_nhds
    have hid : Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) :=
      Filter.tendsto_id
    have hshift : Filter.Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
      simpa using hconst.add hid
    have hmax0 : ∀ᶠ h in nhds 0, f (x + h) ≤ f x :=
      hshift hmax
    have herr' : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖f (x + h) - f x - h • f'‖ ≤ (f' / 2) * ‖h‖ :=
      herr.filter_mono inf_le_left
    have hmax' : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (x + h) ≤ f x :=
      hmax0.filter_mono inf_le_left
    have hgt : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < h :=
      self_mem_nhdsWithin
    rcases (herr'.and (hmax'.and hgt)).exists with ⟨h, he, hm, hh⟩
    have he' :
        |f (x + h) - f x - h * f'| ≤ (f' / 2) * h := by
      simpa [Real.norm_eq_abs, smul_eq_mul, abs_of_pos hh] using he
    have hlow := (abs_le.mp he').1
    have hprod : 0 < h * f' := mul_pos hh hpos
    nlinarith

private theorem localExtr_hasDerivAt_eq_zero
    {f : ℝ → ℝ} {f' x : ℝ} (hext : IsLocalExtr f x)
    (hf : HasDerivAt f f' x) : f' = 0 := by
  rcases hext with hmin | hmax
  · have hfneg : HasDerivAt (fun y => -f y) (-f') x := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert hf.hasFDerivAt.neg using 1 <;>
        ext z <;> simp [smul_eq_mul]
    have hneg := localMax_hasDerivAt_eq_zero hmin.neg hfneg
    linarith
  · exact localMax_hasDerivAt_eq_zero hmax hf

private theorem exists_localExtr_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Set.Ioo a b, IsLocalExtr f c := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
  obtain ⟨c, cmem, cle⟩ :=
    isCompact_Icc.exists_isMinOn hne hfc
  obtain ⟨C, Cmem, Cge⟩ :=
    isCompact_Icc.exists_isMaxOn hne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have hall : ∀ x ∈ Set.Icc a b, f x = f a := fun x hx =>
        le_antisymm (hC ▸ Cge hx) (hc ▸ cle hx)
      rcases Set.nonempty_Ioo.mpr hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl ?_⟩
      filter_upwards [Icc_mem_nhds hc'.1 hc'.2] with x hx
      rw [hall x hx, hall c' (Set.Ioo_subset_Icc_self hc')]
    · have hCa : C ≠ a := by
        intro h
        apply hC
        simpa [h] using rfl
      have hCb : C ≠ b := by
        intro h
        apply hC
        rw [h, ← hfI]
      have hCIoo : C ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne Cmem.1 (Ne.symm hCa),
          lt_of_le_of_ne Cmem.2 hCb⟩
      exact ⟨C, hCIoo, Or.inr (Cge.isLocalMax (Icc_mem_nhds hCIoo.1 hCIoo.2))⟩
  · have hca : c ≠ a := by
      intro h
      apply hc
      simpa [h] using rfl
    have hcb : c ≠ b := by
      intro h
      apply hc
      rw [h, ← hfI]
    have hcIoo : c ∈ Set.Ioo a b :=
      ⟨lt_of_le_of_ne cmem.1 (Ne.symm hca),
        lt_of_le_of_ne cmem.2 hcb⟩
    exact ⟨c, hcIoo, Or.inl (cle.isLocalMin (Icc_mem_nhds hcIoo.1 hcIoo.2))⟩

private theorem endpoint_eq_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) :
    f 1 = f 0 := by
  let m : ℝ := f 1 - f 0
  let g : ℝ → ℝ := fun t => f t - m * t
  have hcontf : Continuous f :=
    continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hcontg : Continuous g := by
    dsimp [g]
    exact hcontf.sub (continuous_const.mul continuous_id)
  have hgend : g 0 = g 1 := by
    dsimp [g, m]
    ring
  obtain ⟨c, hc, hext⟩ :=
    exists_localExtr_Ioo (f := g) zero_lt_one hcontg.continuousOn hgend
  have hgderiv : HasDerivAt g (-m) c := by
    have hmul : HasDerivAt (fun t : ℝ => m * t) m c := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert (hasDerivAt_id c).hasFDerivAt.const_smul m using 1 <;>
        ext z <;> simp [smul_eq_mul]
    rw [hasDerivAt_iff_hasFDerivAt]
    convert (hf c).hasFDerivAt.sub hmul.hasFDerivAt using 1 <;>
      ext z <;> simp [g, smul_eq_mul]
  have hm : -m = 0 := localExtr_hasDerivAt_eq_zero hext hgderiv
  dsimp [m] at hm
  linarith

private theorem square_hasDerivAt
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => f y ^ 2) (2 * f x * f') x := by
  have hs :
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * f x) (f x) := by
    apply HasDerivAt.of_isLittleO
    refine
      (Asymptotics.isLittleO_pow_sub_sub (f x)
        (by norm_num : 1 < 2)).congr_left ?_
    intro y
    simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul]
    ring
  change HasDerivAt ((fun y : ℝ => y ^ 2) ∘ f) (2 * f x * f') x
  have hcomp :=
    HasFDerivAtFilter.comp hs.hasFDerivAt hf.hasFDerivAt
      (hf.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure _ _))
  change HasDerivAtFilter ((fun y : ℝ => y ^ 2) ∘ f)
    (2 * f x * f') (nhds x ×ˢ pure x)
  convert hcomp.hasDerivAtFilter using 1
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

private theorem integral_eq_sub_of_hasDerivAt_continuous
    (f d : ℝ → ℝ) (hd : Continuous d)
    (hf : ∀ x, HasDerivAt f (d x) x) :
    (∫ x in (0 : ℝ)..1, d x) = f 1 - f 0 := by
  let P : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, d t
  have hP : ∀ x, HasDerivAt P (d x) x := by
    intro x
    simpa [P] using primitive_hasDerivAt d hd 0 x
  let H : ℝ → ℝ := fun u => f u - P u
  have hH : ∀ x, HasDerivAt H 0 x := by
    intro x
    rw [hasDerivAt_iff_hasFDerivAt]
    convert (hf x).hasFDerivAt.sub (hP x).hasFDerivAt using 1 <;>
      ext z <;> simp [H, smul_eq_mul]
  have hconst := endpoint_eq_of_hasDerivAt_zero H hH
  dsimp [H, P] at hconst
  simp only [intervalIntegral.integral_same, sub_zero] at hconst
  linarith

private theorem continuous_deriv_of_contDiff_one
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (deriv f) := by
  have hsplit :
      Differentiable ℝ f ∧ ContDiff ℝ 0 (fderiv ℝ f) := by
    simpa using (contDiff_succ_iff_fderiv (n := 0)).mp hf
  simpa only [deriv] using
    hsplit.2.continuous.clm_apply
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))

theorem gap1 (k : ℝ) (p : Point) :
    force k p = (-k * p.1, -k * p.2) := by
  rfl

theorem gap2 (k : ℝ) :
    ∃ A : Point → ℝ, ∀ p v,
      differential A p v = coordinateDifferential (force k p) v := by
  refine ⟨potential k, ?_⟩
  intro p v
  have hx :
      deriv (fun x : ℝ => potential k (x, p.2)) p.1 = -k * p.1 := by
    apply HasDerivAt.deriv
    apply HasDerivAt.of_isLittleO
    refine
      ((Asymptotics.isLittleO_pow_sub_sub p.1
        (by norm_num : 1 < 2)).const_mul_left (-(k / 2))).congr_left ?_
    intro x
    simp only [potential, Real.norm_eq_abs, sq_abs, smul_eq_mul]
    ring
  have hy :
      deriv (fun y : ℝ => potential k (p.1, y)) p.2 = -k * p.2 := by
    apply HasDerivAt.deriv
    apply HasDerivAt.of_isLittleO
    refine
      ((Asymptotics.isLittleO_pow_sub_sub p.2
        (by norm_num : 1 < 2)).const_mul_left (-(k / 2))).congr_left ?_
    intro y
    simp only [potential, Real.norm_eq_abs, sq_abs, smul_eq_mul]
    ring
  unfold differential
  rw [hx, hy]
  simp [coordinateDifferential, force]

theorem gap3 (k : ℝ) (p v : Point) :
    coordinateDifferential (force k p) v =
      (-k * p.1) * v.1 + (-k * p.2) * v.2 := by
  rfl

theorem gap4 (k : ℝ) (p v : Point) :
    (-k * p.1) * v.1 + (-k * p.2) * v.2 =
      differential (potential k) p v := by
  have hx :
      deriv (fun x : ℝ => potential k (x, p.2)) p.1 = -k * p.1 := by
    apply HasDerivAt.deriv
    apply HasDerivAt.of_isLittleO
    refine
      ((Asymptotics.isLittleO_pow_sub_sub p.1
        (by norm_num : 1 < 2)).const_mul_left (-(k / 2))).congr_left ?_
    intro x
    simp only [potential, Real.norm_eq_abs, sq_abs, smul_eq_mul]
    ring
  have hy :
      deriv (fun y : ℝ => potential k (p.1, y)) p.2 = -k * p.2 := by
    apply HasDerivAt.deriv
    apply HasDerivAt.of_isLittleO
    refine
      ((Asymptotics.isLittleO_pow_sub_sub p.2
        (by norm_num : 1 < 2)).const_mul_left (-(k / 2))).congr_left ?_
    intro y
    simp only [potential, Real.norm_eq_abs, sq_abs, smul_eq_mul]
    ring
  unfold differential
  rw [hx, hy]

theorem gap5 (k : ℝ) :
    ∃ A : Point → ℝ, ∀ p v,
      differential A p v = differential (potential k) p v := by
  exact ⟨potential k, fun p v => rfl⟩

theorem gap6 (a b k : ℝ) (γ : ℝ → Point)
    (ha : 0 < a) (hb : 0 < b)
    (hγ : EllipsePath a b γ) :
    lineIntegral k γ = -k * radialIntegral γ := by
  unfold lineIntegral radialIntegral coordinateDifferential force
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

theorem gap7 (a b k : ℝ) (γ : ℝ → Point)
    (ha : 0 < a) (hb : 0 < b)
    (hγ : EllipsePath a b γ) :
    -k * radialIntegral γ =
      potential k (0, b) - potential k (a, 0) := by
  rcases hγ with ⟨hcont, hzero, hone, hellipse⟩
  let X : ℝ → ℝ := fun t => (γ t).1
  let Y : ℝ → ℝ := fun t => (γ t).2
  let E : ℝ → ℝ := fun t => (X t ^ 2 + Y t ^ 2) / 2
  let d : ℝ → ℝ := fun t =>
    X t * deriv X t + Y t * deriv Y t
  have hX : ContDiff ℝ 1 X := by
    simpa [X] using
      hcont.continuousLinearMap_comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hY : ContDiff ℝ 1 Y := by
    simpa [Y] using
      hcont.continuousLinearMap_comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hXdiff : Differentiable ℝ X :=
    hX.differentiable (by simp)
  have hYdiff : Differentiable ℝ Y :=
    hY.differentiable (by simp)
  have hderivX : Continuous (deriv X) :=
    continuous_deriv_of_contDiff_one X hX
  have hderivY : Continuous (deriv Y) :=
    continuous_deriv_of_contDiff_one Y hY
  have hd : Continuous d := by
    dsimp [d]
    exact (hX.continuous.mul hderivX).add
      (hY.continuous.mul hderivY)
  have hE : ∀ t, HasDerivAt E (d t) t := by
    intro t
    have hsqX :
        HasDerivAt (fun s => X s ^ 2)
          (2 * X t * deriv X t) t :=
      square_hasDerivAt (hXdiff t).hasDerivAt
    have hsqY :
        HasDerivAt (fun s => Y s ^ 2)
          (2 * Y t * deriv Y t) t :=
      square_hasDerivAt (hYdiff t).hasDerivAt
    rw [hasDerivAt_iff_hasFDerivAt]
    convert
      (hsqX.hasFDerivAt.add hsqY.hasFDerivAt).const_smul (1 / 2 : ℝ) using 1 <;>
      ext z <;> simp [E, d, smul_eq_mul] <;> ring
  have hFTC :
      (∫ t in (0 : ℝ)..1, d t) = E 1 - E 0 :=
    integral_eq_sub_of_hasDerivAt_continuous E d hd hE
  have hradial : radialIntegral γ = E 1 - E 0 := by
    rw [← hFTC]
    unfold radialIntegral
    rfl
  rw [hradial]
  simp [E, X, Y, hzero, hone, potential]
  ring

theorem gap8 (a b k : ℝ) :
    potential k (0, b) - potential k (a, 0) =
      k / 2 * (a ^ 2 - b ^ 2) := by
  unfold potential
  ring

theorem gap9 (a b k : ℝ) (γ : ℝ → Point)
    (ha : 0 < a) (hb : 0 < b)
    (hγ : EllipsePath a b γ) :
    lineIntegral k γ = k / 2 * (a ^ 2 - b ^ 2) := by
  calc
    lineIntegral k γ = -k * radialIntegral γ :=
      gap6 a b k γ ha hb hγ
    _ = potential k (0, b) - potential k (a, 0) :=
      gap7 a b k γ ha hb hγ
    _ = k / 2 * (a ^ 2 - b ^ 2) := gap8 a b k

end

end ProofGap.Exercise4293_2
