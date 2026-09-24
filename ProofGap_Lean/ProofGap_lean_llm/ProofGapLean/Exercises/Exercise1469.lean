import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace ProofGap.Exercise1469

noncomputable section

open Filter

def f (k x : ℝ) : ℝ := Real.cosh x - k * x
def g (x : ℝ) : ℝ := Real.cosh x - x * Real.sinh x
def critical (k : ℝ) : ℝ :=
  Real.log (k + Real.sqrt (k ^ 2 + 1))
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

def IsGlobalMinimizer (u : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ x : ℝ, u x₀ ≤ u x

def UniqueRootOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, u x = 0 ∧ ∀ y ∈ s, u y = 0 → y = x

def CriticalThreshold (ξ : ℝ) : Prop :=
  0 < ξ ∧ g ξ = 0 ∧ ∀ x, 0 < x → g x = 0 → x = ξ

def ApproxWithin (a b ε : ℝ) : Prop := |a - b| < ε

private lemma critical_eq_arsinh (k : ℝ) : critical k = Real.arsinh k := by
  simp [critical, Real.arsinh, add_comm]

private lemma sinh_critical (k : ℝ) : Real.sinh (critical k) = k := by
  rw [critical_eq_arsinh]
  simp

private lemma hasDerivAt_f (k x : ℝ) :
    HasDerivAt (f k) (Real.sinh x - k) x := by
  unfold f
  convert (Real.hasDerivAt_cosh x).sub
    ((hasDerivAt_const x k).mul (hasDerivAt_id x)) using 1 <;> simp [id]

private lemma deriv_f (k x : ℝ) : deriv (f k) x = Real.sinh x - k :=
  (hasDerivAt_f k x).deriv

private lemma continuous_f (k : ℝ) : Continuous (f k) := by
  unfold f
  fun_prop

private lemma global_min (k : ℝ) : ∀ x, f k (critical k) ≤ f k x := by
  intro x
  rcases le_total x (critical k) with hx | hx
  · have hanti : AntitoneOn (f k) (Set.Iic (critical k)) :=
      antitoneOn_of_deriv_nonpos (convex_Iic (critical k)) (continuous_f k).continuousOn
        (fun y _ => (hasDerivAt_f k y).differentiableAt.differentiableWithinAt) (by
          intro y hy
          rw [interior_Iic] at hy
          rw [deriv_f, ← sinh_critical k]
          exact sub_nonpos.2 (Real.sinh_le_sinh.mpr hy.le))
    exact hanti (show x ∈ Set.Iic (critical k) from hx) (by simp) hx
  · have hmono : MonotoneOn (f k) (Set.Ici (critical k)) :=
      monotoneOn_of_deriv_nonneg (convex_Ici (critical k)) (continuous_f k).continuousOn
        (fun y _ => (hasDerivAt_f k y).differentiableAt.differentiableWithinAt) (by
          intro y hy
          rw [interior_Ici] at hy
          rw [deriv_f, ← sinh_critical k]
          exact sub_nonneg.2 (Real.sinh_le_sinh.mpr hy.le))
    exact hmono (by simp) (show x ∈ Set.Ici (critical k) from hx) hx

private lemma exp_one_lt : Real.exp 1 < (68 : ℝ) / 25 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (n := 8) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private lemma exp_small_lt : Real.exp ((19 : ℝ) / 50) < 3 / 2 := by
  have h := Real.exp_bound' (x := (19 : ℝ) / 50) (n := 6)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private lemma exp_238_lt : Real.exp ((119 : ℝ) / 50) < 219 / 19 := by
  rw [show (119 : ℝ) / 50 = 1 + 1 + 19 / 50 by norm_num,
    Real.exp_add, Real.exp_add]
  have h1 := exp_one_lt
  have h2 := exp_small_lt
  have hp := Real.exp_pos 1
  have hp2 := Real.exp_pos ((19 : ℝ) / 50)
  have hsq : Real.exp 1 * Real.exp 1 < ((68 : ℝ) / 25) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp 1 - 68 / 25)]
  have hprod := mul_lt_mul hsq h2.le hp2
    (by positivity : (0 : ℝ) ≤ ((68 : ℝ) / 25) ^ 2)
  norm_num at hprod ⊢
  linarith

private lemma exp_242_gt : (221 : ℝ) / 21 < Real.exp ((121 : ℝ) / 50) := by
  have h := Real.sum_le_exp_of_nonneg (x := (121 : ℝ) / 50) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private lemma g_119_pos : 0 < g ((119 : ℝ) / 100) := by
  have he := exp_238_lt
  have hp := Real.exp_pos ((119 : ℝ) / 100)
  rw [g, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp [hp.ne']
  have hesq : Real.exp ((119 : ℝ) / 100) ^ 2 = Real.exp ((119 : ℝ) / 50) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hesq]
  norm_num at he ⊢
  nlinarith

private lemma g_121_neg : g ((121 : ℝ) / 100) < 0 := by
  have he := exp_242_gt
  have hp := Real.exp_pos ((121 : ℝ) / 100)
  rw [g, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp [hp.ne']
  have hesq : Real.exp ((121 : ℝ) / 100) ^ 2 = Real.exp ((121 : ℝ) / 50) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hesq]
  norm_num at he ⊢
  nlinarith

private lemma tendsto_f_atTop (k : ℝ) : Tendsto (f k) atTop atTop := by
  have hxe : Tendsto (fun x : ℝ => x / Real.exp x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_exp_atTop (n := 1)).tendsto_div_nhds_zero
  have hnegexp : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (nhds 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    exact tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0)
  have hfac : Tendsto
      (fun x : ℝ => (1 + Real.exp (-2 * x)) / 2 - k * (x / Real.exp x))
      atTop (nhds (1 / 2)) := by
    convert ((tendsto_const_nhds.add hnegexp).div_const 2).sub
      (tendsto_const_nhds.mul hxe) using 1 <;> norm_num
  have ht := Real.tendsto_exp_atTop.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hfac
  apply ht.congr'
  filter_upwards with x
  unfold f
  rw [Real.cosh_eq]
  field_simp [Real.exp_ne_zero x]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero x]
  have he : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [he]

private lemma reflect_f (k x : ℝ) : f (-k) (-x) = f k x := by
  unfold f
  calc
    Real.cosh (-x) - (-k) * (-x) = Real.cosh x - (-k) * (-x) :=
      congrArg (fun z => z - (-k) * (-x)) (Real.cosh_neg x)
    _ = Real.cosh x - k * x := by ring

private lemma tendsto_f_atBot (k : ℝ) : Tendsto (f k) atBot atTop := by
  have ht := (tendsto_f_atTop (-k)).comp tendsto_neg_atBot_atTop
  apply ht.congr'
  filter_upwards with x
  exact reflect_f k x

private lemma hasDerivAt_g (x : ℝ) :
    HasDerivAt g (-x * Real.cosh x) x := by
  unfold g
  convert (Real.hasDerivAt_cosh x).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)) using 1 <;> simp [id]

private lemma continuous_g : Continuous g := by
  unfold g
  fun_prop

private lemma strictAntiOn_g_positive : StrictAntiOn g (Set.Ici 0) :=
  strictAntiOn_of_deriv_neg (D := Set.Ici (0 : ℝ)) (convex_Ici _)
    continuous_g.continuousOn (by
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_g x).deriv]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) (Real.cosh_pos x))

private lemma approximate_threshold (θ : ℝ) (hθ : CriticalThreshold θ) :
    ApproxWithin θ 1.2 0.01 := by
  have hiv := intermediate_value_Icc' (by norm_num : (119 : ℝ) / 100 ≤ 121 / 100)
    continuous_g.continuousOn
  rcases hiv ⟨g_121_neg.le, g_119_pos.le⟩ with ⟨x, hx, hzero⟩
  have hxpos : 0 < x := by linarith [hx.1]
  have hxopen : (119 : ℝ) / 100 < x ∧ x < 121 / 100 := by
    constructor
    · exact lt_of_le_of_ne hx.1 (by
        intro heq
        subst x
        linarith [g_119_pos])
    · exact lt_of_le_of_ne hx.2 (by
        intro heq
        subst x
        linarith [g_121_neg])
  have hxeq : x = θ := hθ.2.2 x hxpos hzero
  rw [← hxeq]
  unfold ApproxWithin
  rw [abs_lt]
  constructor <;> norm_num at hxopen ⊢ <;> linarith [hxopen.1, hxopen.2]

private lemma strictAntiOn_f_left (k : ℝ) :
    StrictAntiOn (f k) (Set.Iic (critical k)) :=
  strictAntiOn_of_deriv_neg (D := Set.Iic (critical k)) (convex_Iic _)
    (continuous_f k).continuousOn (by
      intro x hx
      rw [interior_Iic] at hx
      rw [deriv_f, ← sinh_critical k]
      exact sub_neg.2 (Real.sinh_lt_sinh.mpr hx))

private lemma strictMonoOn_f_right (k : ℝ) :
    StrictMonoOn (f k) (Set.Ici (critical k)) :=
  strictMonoOn_of_deriv_pos (D := Set.Ici (critical k)) (convex_Ici _)
    (continuous_f k).continuousOn (by
      intro x hx
      rw [interior_Ici] at hx
      rw [deriv_f, ← sinh_critical k]
      exact sub_pos.2 (Real.sinh_lt_sinh.mpr hx))

private lemma unique_root_left_positive (k θ : ℝ) (hθ0 : 0 < θ)
    (hθc : θ < critical k) (hfθ : f k θ < 0) :
    UniqueRootOn (f k) (Set.Ioo 0 θ) := by
  have hiv := intermediate_value_Icc' hθ0.le (continuous_f k).continuousOn
  have hf0 : f k 0 = 1 := by norm_num [f]
  rcases hiv ⟨hfθ.le, by rw [hf0]; norm_num⟩ with ⟨x, hx, hzero⟩
  have hxmem : x ∈ Set.Ioo (0 : ℝ) θ := by
    constructor
    · exact lt_of_le_of_ne hx.1 (by
        intro heq
        subst x
        linarith)
    · exact lt_of_le_of_ne hx.2 (by
        intro heq
        subst x
        linarith)
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  exact (strictAntiOn_f_left k).injOn (x₁ := y) (x₂ := x)
    (show y ≤ critical k from hy.2.le.trans hθc.le)
    (show x ≤ critical k from hxmem.2.le.trans hθc.le)
    (hyzero.trans hzero.symm)

private lemma unique_root_right_positive (k θ : ℝ) (hθc : θ < critical k)
    (hfθ : f k θ < 0) :
    UniqueRootOn (f k) (Set.Ioi θ) := by
  have hfc : f k (critical k) < 0 :=
    lt_of_le_of_lt (global_min k θ) hfθ
  rcases (((tendsto_f_atTop k).eventually_gt_atTop 0).and
    (eventually_gt_atTop (critical k))).exists with ⟨b, hfb, hbc⟩
  have hiv := intermediate_value_Icc (le_of_lt hbc) (continuous_f k).continuousOn
  rcases hiv ⟨hfc.le, hfb.le⟩ with ⟨x, hx, hzero⟩
  have hxc : critical k < x := lt_of_le_of_ne hx.1 (by
    intro heq
    subst x
    linarith)
  have hxθ : θ < x := hθc.trans hxc
  refine ⟨x, hxθ, hzero, ?_⟩
  intro y hy hyzero
  have hyc : critical k < y := by
    by_contra hnot
    have hycle : y ≤ critical k := le_of_not_gt hnot
    have hfylt : f k y < f k θ :=
      (strictAntiOn_f_left k) (show θ ≤ critical k from hθc.le) hycle hy
    linarith
  exact (strictMonoOn_f_right k).injOn (x₁ := y) (x₂ := x)
    hyc.le hxc.le (hyzero.trans hzero.symm)

private lemma unique_root_at_critical (k : ℝ) (hzero : f k (critical k) = 0) :
    UniqueRootOn (f k) Set.univ := by
  refine ⟨critical k, Set.mem_univ _, hzero, ?_⟩
  intro y _ hyzero
  rcases le_total y (critical k) with hy | hy
  · by_contra hne
    have hlt : y < critical k := lt_of_le_of_ne hy hne
    have h := (strictAntiOn_f_left k) hy (by simp) hlt
    linarith
  · by_contra hne
    have hlt : critical k < y := lt_of_le_of_ne hy (Ne.symm hne)
    have h := (strictMonoOn_f_right k) (by simp) hy hlt
    linarith

private lemma no_root_of_min_pos (k : ℝ) (hmin : 0 < f k (critical k)) :
    ¬ ∃ x : ℝ, f k x = 0 := by
  rintro ⟨x, hx⟩
  have h := global_min k x
  linarith

theorem gap1 (k x : ℝ) :
    deriv (f k) x = Real.sinh x - k := by
  exact deriv_f k x

theorem gap2 (k x : ℝ) (hzero : deriv (f k) x = 0) :
    x = critical k := by
  rw [gap1, sub_eq_zero] at hzero
  exact Real.sinh_injective (hzero.trans (sinh_critical k).symm)

theorem gap3 (k : ℝ) :
    k = Real.sinh (critical k) := by
  exact (sinh_critical k).symm

theorem gap4 (k x : ℝ) :
    deriv (deriv (f k)) x = Real.cosh x := by
  have heq : deriv (f k) = fun y => Real.sinh y - k := funext (gap1 k)
  rw [heq]
  exact ((Real.hasDerivAt_sinh x).sub_const k).deriv

theorem gap5 (x : ℝ) :
    Real.cosh x > 0 := by
  exact Real.cosh_pos x

theorem gap6 (k x : ℝ) :
    deriv (deriv (f k)) x > 0 := by
  rw [gap4]
  exact gap5 x

theorem gap7 (k : ℝ) :
    IsGlobalMinimizer (f k) (critical k) := by
  exact global_min k

theorem gap8 (k : ℝ) :
    Tendsto (f k) atBot atTop := by
  exact tendsto_f_atBot k

theorem gap9 (k : ℝ) :
    Tendsto (f k) atTop atTop := by
  exact tendsto_f_atTop k

theorem gap10 (k : ℝ) :
    f k (critical k) = Real.cosh (critical k) - k * critical k := by
  rfl

theorem gap11 (k : ℝ) :
    Real.cosh (critical k) - k * critical k =
      Real.cosh (critical k) - critical k * Real.sinh (critical k) := by
  rw [← gap3 k]
  ring

theorem gap12 (k : ℝ) :
    f k (critical k) =
      Real.cosh (critical k) - critical k * Real.sinh (critical k) := by
  exact (gap10 k).trans (gap11 k)

theorem gap13 (k : ℝ) (hk : 0 < k) :
    0 < critical k := by
  rw [critical_eq_arsinh]
  exact Real.arsinh_pos_iff.mpr hk

theorem gap14 (x : ℝ) (hx : 0 < x) :
    g x = 0 ↔ coth x = x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  unfold g coth
  rw [div_eq_iff hs]
  constructor <;> intro h <;> nlinarith

theorem gap15 (ξ : ℝ) (hξ : CriticalThreshold ξ) :
    coth ξ = ξ := by
  exact (gap14 ξ hξ.1).mp hξ.2.1

theorem gap16 (ξ : ℝ) (hξ : CriticalThreshold ξ) :
    ApproxWithin ξ 1.2 0.01 := by
  exact approximate_threshold ξ hξ

theorem gap17 (x : ℝ) :
    deriv g x = Real.sinh x - (Real.sinh x + x * Real.cosh x) := by
  have h := (Real.hasDerivAt_cosh x).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x))
  convert h.deriv using 1 <;> simp [g, id]

theorem gap18 (x : ℝ) :
    Real.sinh x - (Real.sinh x + x * Real.cosh x) =
      -x * Real.cosh x := by
  ring

theorem gap19 (x : ℝ) :
    deriv g x = -x * Real.cosh x := by
  exact (hasDerivAt_g x).deriv

theorem gap20 (x : ℝ) (hx : 0 < x) :
    deriv g x < 0 := by
  rw [gap19]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) (Real.cosh_pos x)

theorem gap21 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < k) :
    ξ < critical k := by
  rw [← Real.sinh_lt_sinh, ← gap3 k]
  exact hlarge

theorem gap22 (k : ℝ) :
    f k (critical k) =
      Real.cosh (critical k) - critical k * Real.sinh (critical k) := by
  exact gap12 k

theorem gap23 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < k) :
    g (critical k) < g ξ := by
  have hξc := gap21 k ξ hk hξ hlarge
  exact strictAntiOn_g_positive hξ.1.le (gap13 k hk).le hξc

theorem gap24 (ξ : ℝ) (hξ : CriticalThreshold ξ) :
    Real.cosh ξ - ξ * Real.sinh ξ = 0 := by
  exact hξ.2.1

theorem gap25 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < k) :
    f k (critical k) < 0 := by
  rw [gap22]
  have h := gap23 k ξ hk hξ hlarge
  change g (critical k) < g ξ at h
  rw [hξ.2.1] at h
  exact h

theorem gap26 (k ξ : ℝ) :
    f k ξ = Real.cosh ξ - k * ξ := by
  rfl

theorem gap27 (k ξ : ℝ) (hξ0 : 0 < ξ) (hlarge : Real.sinh ξ < k) :
    Real.cosh ξ - k * ξ < Real.cosh ξ - ξ * Real.sinh ξ := by
  nlinarith [mul_lt_mul_of_pos_right hlarge hξ0]

theorem gap28 (ξ : ℝ) (hξ : CriticalThreshold ξ) :
    Real.cosh ξ - ξ * Real.sinh ξ = 0 := by
  exact hξ.2.1

theorem gap29 (k : ℝ) :
    f k 0 = 1 := by
  norm_num [f]

theorem gap30 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < k) :
    UniqueRootOn (f k) (Set.Ioo 0 ξ) := by
  have hξc := gap21 k ξ hk hξ hlarge
  have hfξ : f k ξ < 0 := by
    rw [gap26]
    exact (gap27 k ξ hξ.1 hlarge).trans_eq (gap28 ξ hξ)
  exact unique_root_left_positive k ξ hξ.1 hξc hfξ

theorem gap31 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < k) :
    UniqueRootOn (f k) (Set.Ioi ξ) := by
  have hξc := gap21 k ξ hk hξ hlarge
  have hfξ : f k ξ < 0 := by
    rw [gap26]
    exact (gap27 k ξ hξ.1 hlarge).trans_eq (gap28 ξ hξ)
  exact unique_root_right_positive k ξ hξc hfξ

theorem gap32 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (heq : k = Real.sinh ξ) :
    critical k = ξ := by
  apply Real.sinh_injective
  rw [sinh_critical, heq]

theorem gap33 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (heq : k = Real.sinh ξ) :
    f k (critical k) = 0 := by
  rw [gap32 k ξ hk hξ heq, gap26, heq]
  simpa [g, mul_comm] using hξ.2.1

theorem gap34 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (heq : k = Real.sinh ξ) :
    UniqueRootOn (f k) Set.univ := by
  exact unique_root_at_critical k (gap33 k ξ hk hξ heq)

theorem gap35 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hsmall : k < Real.sinh ξ) :
    critical k < ξ := by
  rw [← Real.sinh_lt_sinh, sinh_critical]
  exact hsmall

theorem gap36 (k : ℝ) :
    f k (critical k) =
      Real.cosh (critical k) - critical k * Real.sinh (critical k) := by
  exact gap12 k

theorem gap37 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hsmall : k < Real.sinh ξ) :
    g ξ < g (critical k) := by
  have hcξ := gap35 k ξ hk hξ hsmall
  exact strictAntiOn_g_positive (gap13 k hk).le hξ.1.le hcξ

theorem gap38 (ξ : ℝ) (hξ : CriticalThreshold ξ) :
    Real.cosh ξ - ξ * Real.sinh ξ = 0 := by
  exact hξ.2.1

theorem gap39 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hsmall : k < Real.sinh ξ) :
    f k (critical k) > 0 := by
  rw [gap36]
  have h := gap37 k ξ hk hξ hsmall
  change g ξ < g (critical k) at h
  rw [hξ.2.1] at h
  exact h

theorem gap40 (k ξ : ℝ) (hk : 0 < k) (hξ : CriticalThreshold ξ)
    (hsmall : k < Real.sinh ξ) :
    ¬ ∃ x : ℝ, f k x = 0 := by
  exact no_root_of_min_pos k (gap39 k ξ hk hξ hsmall)

theorem gap41 :
    ¬ ∃ x : ℝ, f 0 x = 0 := by
  have hc : critical 0 = 0 := by rw [critical_eq_arsinh]; simp
  apply no_root_of_min_pos 0
  rw [hc, gap29]
  norm_num

theorem gap42 (k x t : ℝ) (hk : k < 0) (ht : t = -x)
    (hroot : f k x = 0) :
    Real.cosh t = (-k) * t := by
  subst t
  have hr : f (-k) (-x) = 0 := by rwa [reflect_f]
  unfold f at hr
  linarith

theorem gap43 (k ξ : ℝ) (hk : k < 0) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < -k) :
    UniqueRootOn (f k) (Set.Ioo (-ξ) 0) := by
  rcases gap30 (-k) ξ (neg_pos.2 hk) hξ hlarge with ⟨x, hx, hzero, huniq⟩
  refine ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_, ?_⟩
  · simpa only [neg_neg] using (reflect_f (-k) x).trans hzero
  · intro y hy hyzero
    have hmy : -y ∈ Set.Ioo (0 : ℝ) ξ := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hmyzero : f (-k) (-y) = 0 := (reflect_f k y).trans hyzero
    have h := huniq (-y) hmy hmyzero
    linarith

theorem gap44 (k ξ : ℝ) (hk : k < 0) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < -k) :
    UniqueRootOn (f k) (Set.Iio (-ξ)) := by
  rcases gap31 (-k) ξ (neg_pos.2 hk) hξ hlarge with ⟨x, hx, hzero, huniq⟩
  have hx' : ξ < x := hx
  refine ⟨-x, (show -x < -ξ by linarith), ?_, ?_⟩
  · simpa only [neg_neg] using (reflect_f (-k) x).trans hzero
  · intro y hy hyzero
    have hy' : y < -ξ := hy
    have hmy : -y ∈ Set.Ioi ξ := by
      show ξ < -y
      linarith
    have hmyzero : f (-k) (-y) = 0 := (reflect_f k y).trans hyzero
    have h := huniq (-y) hmy hmyzero
    linarith

theorem gap45 (k ξ : ℝ) (hk : k < 0) (hξ : CriticalThreshold ξ)
    (hsmall : -Real.sinh ξ < k) :
    ¬ ∃ x : ℝ, f k x = 0 := by
  have hnsmall : -k < Real.sinh ξ := by linarith
  have hnone := gap40 (-k) ξ (neg_pos.2 hk) hξ hnsmall
  rintro ⟨x, hx⟩
  apply hnone
  exact ⟨-x, (reflect_f k x).trans hx⟩

theorem gap46 (k ξ : ℝ) (hξ : CriticalThreshold ξ)
    (hlarge : Real.sinh ξ < |k|) :
    ∃ x₁ x₂, x₁ ≠ x₂ ∧ f k x₁ = 0 ∧ f k x₂ = 0 ∧
      0 < |x₁| ∧ |x₁| < ξ ∧ ξ < |x₂| := by
  have hspos : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ.1
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    simp at hlarge
    exact (not_lt_of_ge hξ.1.le hlarge)
  rcases lt_or_gt_of_ne hk0 with hk | hk
  · rw [abs_of_neg hk] at hlarge
    rcases gap43 k ξ hk hξ hlarge with
      ⟨x₁, ⟨hx₁lo, hx₁hi⟩, hzero₁, _⟩
    rcases gap44 k ξ hk hξ hlarge with ⟨x₂, hx₂, hzero₂, _⟩
    change x₂ < -ξ at hx₂
    have hx₂neg : x₂ < 0 := hx₂.trans (neg_lt_zero.mpr hξ.1)
    refine ⟨x₁, x₂, ne_of_gt (hx₂.trans hx₁lo), hzero₁, hzero₂, ?_⟩
    rw [abs_of_neg hx₁hi, abs_of_neg hx₂neg]
    constructor
    · linarith [hx₁hi]
    constructor <;> linarith [hx₁lo, hx₂]
  · rw [abs_of_pos hk] at hlarge
    rcases gap30 k ξ hk hξ hlarge with
      ⟨x₁, ⟨hx₁lo, hx₁hi⟩, hzero₁, _⟩
    rcases gap31 k ξ hk hξ hlarge with ⟨x₂, hx₂, hzero₂, _⟩
    change ξ < x₂ at hx₂
    refine ⟨x₁, x₂, ne_of_lt (hx₁hi.trans hx₂), hzero₁, hzero₂, ?_⟩
    rw [abs_of_pos hx₁lo, abs_of_pos (hξ.1.trans hx₂)]
    exact ⟨hx₁lo, hx₁hi, hx₂⟩

theorem gap47 (k ξ : ℝ) (hξ : CriticalThreshold ξ)
    (heq : |k| = Real.sinh ξ) :
    UniqueRootOn (f k) Set.univ := by
  have hspos : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ.1
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    simp at heq
    linarith
  rcases lt_or_gt_of_ne hk0 with hk | hk
  · have heq' : -k = Real.sinh ξ := by
      rw [abs_of_neg hk] at heq
      exact heq
    rcases gap34 (-k) ξ (neg_pos.2 hk) hξ heq' with ⟨x, _, hzero, huniq⟩
    refine ⟨-x, Set.mem_univ _, ?_, ?_⟩
    · simpa only [neg_neg] using (reflect_f (-k) x).trans hzero
    · intro y _ hyzero
      have hmyzero : f (-k) (-y) = 0 := (reflect_f k y).trans hyzero
      have h := huniq (-y) (Set.mem_univ _) hmyzero
      linarith
  · rw [abs_of_pos hk] at heq
    exact gap34 k ξ hk hξ heq

theorem gap48 (k ξ : ℝ) (hξ : CriticalThreshold ξ)
    (hsmall : |k| < Real.sinh ξ) :
    ¬ ∃ x : ℝ, f k x = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · apply gap45 k ξ hk hξ
    rw [abs_of_neg hk] at hsmall
    linarith
  · subst k
    exact gap41
  · rw [abs_of_pos hk] at hsmall
    exact gap40 k ξ hk hξ hsmall

theorem gap49 (k x : ℝ) :
    x ∈ {y : ℝ | Real.cosh y = k * y} ↔ Real.cosh x = k * x := by
  rfl

end

end ProofGap.Exercise1469
