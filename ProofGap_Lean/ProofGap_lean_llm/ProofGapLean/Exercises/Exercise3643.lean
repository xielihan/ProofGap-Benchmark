import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3643

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (p : Point3) : ℝ :=
  p.x ^ 3 + p.y ^ 2 + p.z ^ 2 + 12 * p.x * p.y + 2 * p.z

def partialX (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun x => g ⟨x, p.y, p.z⟩) p.x

def partialY (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun y => g ⟨p.x, y, p.z⟩) p.y

def partialZ (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun z => g ⟨p.x, p.y, z⟩) p.z

def gradient (g : Point3 → ℝ) (p : Point3) : Point3 :=
  ⟨partialX g p, partialY g p, partialZ g p⟩

def p₀ : Point3 :=
  ⟨0, 0, -1⟩

def p₁ : Point3 :=
  ⟨24, -144, -1⟩

def criticalPoints : Set Point3 :=
  {p₀, p₁}

def secondVariationAt (p v : Point3) : ℝ :=
  6 * p.x * v.x ^ 2 + 2 * v.y ^ 2 + 2 * v.z ^ 2 +
    24 * v.x * v.y

def distanceSquared (p q : Point3) : ℝ :=
  (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2 + (q.z - p.z) ^ 2

def IsLocalMinimum (g : Point3 → ℝ) (p : Point3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Point3, distanceSquared p q < ε ^ 2 → g p ≤ g q

def IsLocalMaximum (g : Point3 → ℝ) (p : Point3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Point3, distanceSquared p q < ε ^ 2 → g q ≤ g p

def localMinimumPoints : Set Point3 :=
  {p | IsLocalMinimum u p}

private theorem hasDerivAt_square_add_linear (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 + a * t + b) (2 * x + a) x := by
  apply HasDerivAt.of_isLittleO
  refine
    (Asymptotics.isLittleO_pow_sub_sub x
      (by norm_num : 1 < 2)).congr_left ?_
  intro t
  simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul]
  ring

private theorem hasDerivAt_cube_add_linear (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3 + a * t + b) (3 * x ^ 2 + a) x := by
  have hsq :
      (fun t : ℝ => (t - x) ^ 2) =o[nhds x] fun t => t - x := by
    refine
      (Asymptotics.isLittleO_pow_sub_sub x
        (by norm_num : 1 < 2)).congr_left ?_
    intro t
    simp only [Real.norm_eq_abs, sq_abs]
  have hcube :
      (fun t : ℝ => (t - x) ^ 3) =o[nhds x] fun t => t - x := by
    apply Asymptotics.IsLittleO.of_norm_left
    simpa only [norm_pow] using
      (Asymptotics.isLittleO_pow_sub_sub x
        (by norm_num : 1 < 3))
  apply HasDerivAt.of_isLittleO
  refine (hcube.add (hsq.const_mul_left (3 * x))).congr_left ?_
  intro t
  simp only [smul_eq_mul]
  ring

private theorem hasDerivAt_eq_zero_of_isLocalMin
    {f : ℝ → ℝ} {a d : ℝ}
    (h : IsLocalMin f a) (hf : HasDerivAt f d a) :
    d = 0 := by
  have hF :
      HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ d) a :=
    hasDerivAt_iff_hasFDerivAt.mp hf
  have hnonneg (y : ℝ) :
      0 ≤ (ContinuousLinearMap.toSpanSingleton ℝ d) y := by
    have hid :
        Filter.Tendsto (fun t : ℝ => t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      continuousAt_id.mono_left inf_le_left
    have he0 :
        Filter.Tendsto (fun t : ℝ => t * y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hid.mul_const y
    have hpos :
        Filter.Eventually (fun t : ℝ => 0 < t)
          (nhdsWithin 0 (Set.Ioi 0)) :=
      self_mem_nhdsWithin
    have hceq :
        Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
          (fun t : ℝ => (1 / t) * (t * y)) (fun _ : ℝ => y) := by
      filter_upwards [hpos] with t ht
      field_simp [ne_of_gt ht]
    have hce :
        Filter.Tendsto (fun t : ℝ => (1 / t) * (t * y))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds y) :=
      hceq.tendsto
    have hFW :
        HasFDerivWithinAt f
          (ContinuousLinearMap.toSpanSingleton ℝ d) Set.univ a :=
      hF.hasFDerivWithinAt
    have hlim :=
      hFW.lim he0
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hce
    have hpath :
        Filter.Tendsto (fun t : ℝ => a + t * y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
      simpa using tendsto_const_nhds.add he0
    have hmin :
        Filter.Eventually (fun t : ℝ => f a ≤ f (a + t * y))
          (nhdsWithin 0 (Set.Ioi 0)) :=
      hpath.eventually h
    apply ge_of_tendsto hlim
    filter_upwards [hpos, hmin] with t ht hft
    exact
      mul_nonneg (one_div_nonneg.mpr ht.le) (sub_nonneg.mpr hft)
  have hp := hnonneg 1
  have hn := hnonneg (-1)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    neg_smul] at hp hn
  linarith

theorem gap1 :
    ∀ p : Point3,
      gradient u p =
        ⟨3 * p.x ^ 2 + 12 * p.y, 2 * p.y + 12 * p.x,
          2 * p.z + 2⟩ := by
  intro p
  unfold gradient
  rw [Point3.mk.injEq]
  constructor
  · unfold partialX
    have hfun :
        (fun x : ℝ => u ⟨x, p.y, p.z⟩) =
          fun x : ℝ =>
            x ^ 3 + (12 * p.y) * x +
              (p.y ^ 2 + p.z ^ 2 + 2 * p.z) := by
      funext x
      simp only [u]
      ring
    rw [hfun]
    exact (hasDerivAt_cube_add_linear
      (12 * p.y) (p.y ^ 2 + p.z ^ 2 + 2 * p.z) p.x).deriv
  · constructor
    · unfold partialY
      have hfun :
          (fun y : ℝ => u ⟨p.x, y, p.z⟩) =
            fun y : ℝ =>
              y ^ 2 + (12 * p.x) * y +
                (p.x ^ 3 + p.z ^ 2 + 2 * p.z) := by
        funext y
        simp only [u]
        ring
      rw [hfun]
      exact (hasDerivAt_square_add_linear
        (12 * p.x) (p.x ^ 3 + p.z ^ 2 + 2 * p.z) p.y).deriv
    · unfold partialZ
      have hfun :
          (fun z : ℝ => u ⟨p.x, p.y, z⟩) =
            fun z : ℝ =>
              z ^ 2 + 2 * z +
                (p.x ^ 3 + p.y ^ 2 + 12 * p.x * p.y) := by
        funext z
        simp only [u]
        ring
      rw [hfun]
      exact (hasDerivAt_square_add_linear
        2 (p.x ^ 3 + p.y ^ 2 + 12 * p.x * p.y) p.z).deriv

theorem gap2 :
    p₀ = ⟨0, 0, -1⟩ := by
  rfl

theorem gap3 :
    p₁ = ⟨24, -144, -1⟩ := by
  rfl

theorem gap4 :
    ∀ p : Point3, p ∈ criticalPoints →
      3 * p.x ^ 2 + 12 * p.y = 0 ∧
      2 * p.y + 12 * p.x = 0 ∧
      2 * p.z + 2 = 0 := by
  intro p hp
  simp only [criticalPoints, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · subst p
    norm_num [p₀]
  · subst p
    norm_num [p₁]

theorem gap5 :
    ∀ v : Point3,
      secondVariationAt p₀ v =
        2 * v.y ^ 2 + 2 * v.z ^ 2 + 24 * v.x * v.y := by
  intro v
  simp [secondVariationAt, p₀]

theorem gap6 :
    ∃ v : Point3, v ≠ ⟨0, 0, 0⟩ ∧ 0 < secondVariationAt p₀ v := by
  refine ⟨⟨0, 1, 0⟩, ?_, ?_⟩
  · norm_num
  · norm_num [secondVariationAt, p₀]

theorem gap7 :
    ∃ v : Point3, v ≠ ⟨0, 0, 0⟩ ∧ secondVariationAt p₀ v < 0 := by
  refine ⟨⟨1, -1, 0⟩, ?_, ?_⟩
  · norm_num
  · norm_num [secondVariationAt, p₀]

theorem gap8 :
    ¬ IsLocalMaximum u p₀ ∧ ¬ IsLocalMinimum u p₀ := by
  constructor
  · rintro ⟨ε, hε, hmax⟩
    have hd :
        distanceSquared p₀ ⟨ε / 2, 0, -1⟩ < ε ^ 2 := by
      simp [distanceSquared, p₀]
      nlinarith [sq_pos_of_pos hε]
    have hbad := hmax ⟨ε / 2, 0, -1⟩ hd
    norm_num [u, p₀] at hbad
    nlinarith [pow_pos hε 3]
  · rintro ⟨ε, hε, hmin⟩
    have hd :
        distanceSquared p₀ ⟨-(ε / 2), 0, -1⟩ < ε ^ 2 := by
      simp [distanceSquared, p₀]
      nlinarith [sq_pos_of_pos hε]
    have hbad := hmin ⟨-(ε / 2), 0, -1⟩ hd
    norm_num [u, p₀] at hbad
    nlinarith [pow_pos hε 3]

theorem gap9 :
    ∀ v : Point3,
      secondVariationAt p₁ v =
        (12 * v.x + v.y) ^ 2 + v.y ^ 2 + 2 * v.z ^ 2 := by
  intro v
  simp only [secondVariationAt, p₁]
  ring

theorem gap10 :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      0 <
        (12 * v.x + v.y) ^ 2 + v.y ^ 2 + 2 * v.z ^ 2 := by
  intro v hv
  by_contra h
  have hle :
      (12 * v.x + v.y) ^ 2 + v.y ^ 2 + 2 * v.z ^ 2 ≤ 0 :=
    le_of_not_gt h
  have hs₁ : 0 ≤ (12 * v.x + v.y) ^ 2 :=
    sq_nonneg _
  have hs₂ : 0 ≤ v.y ^ 2 :=
    sq_nonneg _
  have hs₃ : 0 ≤ v.z ^ 2 :=
    sq_nonneg _
  have hy : v.y = 0 := by nlinarith
  have hz : v.z = 0 := by nlinarith
  have hx : v.x = 0 := by nlinarith
  apply hv
  cases v
  simp_all

theorem gap11 :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      0 < secondVariationAt p₁ v := by
  intro v hv
  rw [gap9 v]
  exact gap10 v hv

theorem gap12 :
    IsLocalMinimum u p₁ := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro q hq
  have hdist :
      (q.x - 24) ^ 2 + (q.y + 144) ^ 2 + (q.z + 1) ^ 2 < 1 := by
    simpa [distanceSquared, p₁] using hq
  have hx_sq : (q.x - 24) ^ 2 < 1 := by
    nlinarith [sq_nonneg (q.y + 144), sq_nonneg (q.z + 1)]
  have hx_low : -1 < q.x - 24 := by
    nlinarith [sq_nonneg ((q.x - 24) + 1)]
  have hcoef : 0 ≤ (q.x - 24) + 36 := by
    linarith
  have hrewrite :
      u q - u p₁ =
        (q.x - 24) ^ 2 * ((q.x - 24) + 36) +
          (6 * (q.x - 24) + (q.y + 144)) ^ 2 +
            (q.z + 1) ^ 2 := by
    simp only [u, p₁]
    ring
  rw [← sub_nonneg, hrewrite]
  exact
    add_nonneg
      (add_nonneg
        (mul_nonneg (sq_nonneg _) hcoef)
        (sq_nonneg _))
      (sq_nonneg _)

theorem gap13 :
    u p₁ = -6913 := by
  norm_num [u, p₁]

theorem gap14 :
    localMinimumPoints = {p₁} := by
  ext p
  change IsLocalMinimum u p ↔ p ∈ ({p₁} : Set Point3)
  constructor
  · intro hp
    have hpMin : IsLocalMinimum u p := hp
    rcases hp with ⟨ε, hε, hlocal⟩
    have hxlocal :
        IsLocalMin (fun x : ℝ => u ⟨x, p.y, p.z⟩) p.x := by
      change
        ∀ᶠ x in nhds p.x,
          u ⟨p.x, p.y, p.z⟩ ≤ u ⟨x, p.y, p.z⟩
      rw [Metric.eventually_nhds_iff]
      refine ⟨ε, hε, ?_⟩
      intro x hx
      rw [Real.dist_eq] at hx
      have hd :
          distanceSquared p ⟨x, p.y, p.z⟩ < ε ^ 2 := by
        simp [distanceSquared]
        nlinarith [sq_abs (x - p.x), abs_nonneg (x - p.x)]
      simpa using hlocal ⟨x, p.y, p.z⟩ hd
    have hylocal :
        IsLocalMin (fun y : ℝ => u ⟨p.x, y, p.z⟩) p.y := by
      change
        ∀ᶠ y in nhds p.y,
          u ⟨p.x, p.y, p.z⟩ ≤ u ⟨p.x, y, p.z⟩
      rw [Metric.eventually_nhds_iff]
      refine ⟨ε, hε, ?_⟩
      intro y hy
      rw [Real.dist_eq] at hy
      have hd :
          distanceSquared p ⟨p.x, y, p.z⟩ < ε ^ 2 := by
        simp [distanceSquared]
        nlinarith [sq_abs (y - p.y), abs_nonneg (y - p.y)]
      simpa using hlocal ⟨p.x, y, p.z⟩ hd
    have hzlocal :
        IsLocalMin (fun z : ℝ => u ⟨p.x, p.y, z⟩) p.z := by
      change
        ∀ᶠ z in nhds p.z,
          u ⟨p.x, p.y, p.z⟩ ≤ u ⟨p.x, p.y, z⟩
      rw [Metric.eventually_nhds_iff]
      refine ⟨ε, hε, ?_⟩
      intro z hz
      rw [Real.dist_eq] at hz
      have hd :
          distanceSquared p ⟨p.x, p.y, z⟩ < ε ^ 2 := by
        simp [distanceSquared]
        nlinarith [sq_abs (z - p.z), abs_nonneg (z - p.z)]
      simpa using hlocal ⟨p.x, p.y, z⟩ hd
    have hxderiv :
        HasDerivAt (fun x : ℝ => u ⟨x, p.y, p.z⟩)
          (3 * p.x ^ 2 + 12 * p.y) p.x := by
      have hfun :
          (fun x : ℝ => u ⟨x, p.y, p.z⟩) =
            fun x : ℝ =>
              x ^ 3 + (12 * p.y) * x +
                (p.y ^ 2 + p.z ^ 2 + 2 * p.z) := by
        funext x
        simp only [u]
        ring
      rw [hfun]
      exact hasDerivAt_cube_add_linear
        (12 * p.y) (p.y ^ 2 + p.z ^ 2 + 2 * p.z) p.x
    have hyderiv :
        HasDerivAt (fun y : ℝ => u ⟨p.x, y, p.z⟩)
          (2 * p.y + 12 * p.x) p.y := by
      have hfun :
          (fun y : ℝ => u ⟨p.x, y, p.z⟩) =
            fun y : ℝ =>
              y ^ 2 + (12 * p.x) * y +
                (p.x ^ 3 + p.z ^ 2 + 2 * p.z) := by
        funext y
        simp only [u]
        ring
      rw [hfun]
      exact hasDerivAt_square_add_linear
        (12 * p.x) (p.x ^ 3 + p.z ^ 2 + 2 * p.z) p.y
    have hzderiv :
        HasDerivAt (fun z : ℝ => u ⟨p.x, p.y, z⟩)
          (2 * p.z + 2) p.z := by
      have hfun :
          (fun z : ℝ => u ⟨p.x, p.y, z⟩) =
            fun z : ℝ =>
              z ^ 2 + 2 * z +
                (p.x ^ 3 + p.y ^ 2 + 12 * p.x * p.y) := by
        funext z
        simp only [u]
        ring
      rw [hfun]
      exact hasDerivAt_square_add_linear
        2 (p.x ^ 3 + p.y ^ 2 + 12 * p.x * p.y) p.z
    have hxcrit :
        3 * p.x ^ 2 + 12 * p.y = 0 :=
      hasDerivAt_eq_zero_of_isLocalMin hxlocal hxderiv
    have hycrit :
        2 * p.y + 12 * p.x = 0 :=
      hasDerivAt_eq_zero_of_isLocalMin hylocal hyderiv
    have hzcrit :
        2 * p.z + 2 = 0 :=
      hasDerivAt_eq_zero_of_isLocalMin hzlocal hzderiv
    have hyval : p.y = -6 * p.x := by
      linarith
    have hzval : p.z = -1 := by
      linarith
    have hxpoly : p.x * (p.x - 24) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hxpoly with hxzero | hxrest
    · have hp0 : p = p₀ := by
        cases p
        simp_all [p₀]
      subst p
      exact (gap8.2 hpMin).elim
    · have hxval : p.x = 24 := by
        linarith
      have hp1 : p = p₁ := by
        cases p
        simp_all [p₁]
        norm_num
      simpa [hp1]
  · intro hp
    have hp' : p = p₁ := by
      simpa using hp
    subst p
    exact gap12

end

end ProofGap.Exercise3643
