import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Taylor

namespace ProofGap.Exercise1393

noncomputable section

open Filter

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f

def lowerTaylor (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n,
    h ^ k / (Nat.factorial k : ℝ) * iterDeriv k f x

def taylorThrough (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    h ^ k / (Nat.factorial k : ℝ) * iterDeriv k f x

def puncturedZero : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ

def lagrangeTerm (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ)
    (n : ℕ) (h : ℝ) : ℝ :=
  h ^ n / (Nat.factorial n : ℝ) * iterDeriv n f (x + θ h * h)

def derivativeQuotient (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ)
    (n : ℕ) (h : ℝ) : ℝ :=
  (iterDeriv n f (x + θ h * h) - iterDeriv n f x) / (θ h * h)

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhdsWithin a ({a} : Set ℝ)ᶜ)
    (fun h => g h - p h)
    (fun h => (h - a) ^ n)

def ThetaBounds (θ : ℝ → ℝ) : Prop :=
  ∀ᶠ h in puncturedZero, θ h ∈ Set.Ioo (0 : ℝ) 1

def LagrangeRepresentation (f : ℝ → ℝ) (x : ℝ)
    (θ : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ᶠ h in puncturedZero,
    f (x + h) = lowerTaylor f x n h + lagrangeTerm f x θ n h

def ThetaBalance (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ r : ℝ → ℝ,
    Asymptotics.IsLittleO puncturedZero r (fun h : ℝ => h ^ (n + 1)) ∧
      ∀ᶠ h in puncturedZero,
        θ h * derivativeQuotient f x θ n h =
          (1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x +
            (Nat.factorial n : ℝ) * r h / h ^ (n + 1)

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hformula : LagrangeRepresentation f x θ n) :
    LagrangeRepresentation f x θ n := by
  exact hformula

theorem gap2 (θ : ℝ → ℝ) (hθ : ThetaBounds θ) :
    ∀ᶠ h in puncturedZero, 0 < θ h := by
  exact hθ.mono fun h hh => hh.1

theorem gap3 (θ : ℝ → ℝ) (hθ : ThetaBounds θ) :
    ∀ᶠ h in puncturedZero, θ h < 1 := by
  exact hθ.mono fun h hh => hh.2

theorem gap4 :
    (0 : ℝ) < 1 := by
  norm_num

theorem gap5 (f : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hsmooth : ContDiffAt ℝ (n + 1) f x) :
    AgreesToOrderAt (fun h => f (x + h))
      (taylorThrough f x (n + 1)) 0 (n + 1) := by
  have hs :
      ContDiffWithinAt ℝ (n + 1) f Set.univ x := hsmooth
  rcases hs.contDiffOn' le_rfl (by simp) with
    ⟨u, huopen, hxu, hfu⟩
  have hfu' : ContDiffOn ℝ (n + 1) f u := by
    simpa using hfu
  rcases Metric.isOpen_iff.1 huopen x hxu with ⟨ε, hε, hballu⟩
  have hfball : ContDiffOn ℝ (n + 1) f (Metric.ball x ε) :=
    hfu'.mono hballu
  have ht := taylor_isLittleO (convex_ball x ε)
    (Metric.mem_ball_self hε) hfball
  rw [Metric.isOpen_ball.nhdsWithin_eq
    (Metric.mem_ball_self hε)] at ht
  have heval :
      taylorWithinEval f (n + 1) (Metric.ball x ε) x =
        fun y => taylorThrough f x (n + 1) (y - x) := by
    funext y
    rw [taylor_within_apply]
    dsimp [taylorThrough]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_ball
      (Metric.mem_ball_self hε)]
    simp only [iterDeriv, smul_eq_mul]
    ring
  have hadd :
      Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_id :
          Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)))
  have ht0 := ht.comp_tendsto hadd
  rw [heval] at ht0
  change Asymptotics.IsLittleO (nhds 0)
    (fun h => f (x + h) -
      taylorThrough f x (n + 1) (x + h - x))
    (fun h : ℝ => (x + h - x) ^ (n + 1)) at ht0
  have hnhds :
      Asymptotics.IsLittleO (nhds 0)
        (fun h => f (x + h) - taylorThrough f x (n + 1) h)
        (fun h : ℝ => h ^ (n + 1)) := by
    simpa only [add_sub_cancel_left] using ht0
  simpa [AgreesToOrderAt] using hnhds.mono nhdsWithin_le_nhds

theorem gap6 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hrep : LagrangeRepresentation f x θ n)
    (hsmooth : ContDiffAt ℝ (n + 1) f x)
    (hpeano : AgreesToOrderAt (fun h => f (x + h))
      (taylorThrough f x (n + 1)) 0 (n + 1)) :
    AgreesToOrderAt (lagrangeTerm f x θ n)
      (fun h => h ^ n / (Nat.factorial n : ℝ) * iterDeriv n f x +
        h ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
          iterDeriv (n + 1) f x) 0 (n + 1) := by
  unfold AgreesToOrderAt at hpeano ⊢
  refine hpeano.congr' ?_
    (Eventually.of_forall (fun h => by simp))
  filter_upwards [hrep] with h hh
  have hsplit :
      taylorThrough f x (n + 1) h =
        lowerTaylor f x n h +
          h ^ n / (Nat.factorial n : ℝ) * iterDeriv n f x +
          h ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            iterDeriv (n + 1) f x := by
    simp only [taylorThrough, lowerTaylor, Finset.sum_range_succ,
      Nat.add_assoc]
  rw [hsplit]
  linarith

theorem gap7 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hrep : LagrangeRepresentation f x θ n)
    (hcompare : AgreesToOrderAt (lagrangeTerm f x θ n)
      (fun h => h ^ n / (Nat.factorial n : ℝ) * iterDeriv n f x +
        h ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
          iterDeriv (n + 1) f x) 0 (n + 1)) :
    ThetaBalance f x θ n := by
  let r : ℝ → ℝ := fun h =>
    lagrangeTerm f x θ n h -
      (h ^ n / (Nat.factorial n : ℝ) * iterDeriv n f x +
        h ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
          iterDeriv (n + 1) f x)
  refine ⟨r, ?_, ?_⟩
  · simpa [AgreesToOrderAt, r] using hcompare
  · have hpunc : ∀ᶠ h in puncturedZero, h ≠ 0 := by
      unfold puncturedZero
      filter_upwards [self_mem_nhdsWithin] with h hh
      simpa using hh
    filter_upwards [hpunc] with h hh
    by_cases hθ0 : θ h = 0
    · simp [derivativeQuotient, lagrangeTerm, r, hθ0,
        Nat.factorial_succ]
      field_simp
      ring
    · simp only [derivativeQuotient, lagrangeTerm, r]
      field_simp [hh, hθ0, Nat.factorial_succ]
      simp [Nat.factorial_succ, Nat.add_comm]
      ring

theorem gap8 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hθ : ThetaBounds θ) (hsmooth : ContDiffAt ℝ (n + 1) f x) :
    Tendsto (derivativeQuotient f x θ n)
      puncturedZero
      (nhds (iterDeriv (n + 1) f x)) := by
  have hs :
      ContDiffWithinAt ℝ (n + 1) f Set.univ x := hsmooth
  have hdwithin :=
    hs.differentiableWithinAt_iteratedDerivWithin
      (m := n) (by
        exact WithTop.coe_lt_coe.mpr
          (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)))
      (show UniqueDiffOn ℝ (insert x Set.univ) by simpa)
  have hd : DifferentiableAt ℝ (iterDeriv n f) x := by
    simpa [iterDeriv, iteratedDerivWithin_univ,
      iteratedDeriv_eq_iterate, differentiableWithinAt_univ] using
        hdwithin
  have habs :
      Tendsto (fun h : ℝ => |h|) puncturedZero (nhds 0) := by
    have habs0 :
        Tendsto (fun h : ℝ => |h|) (nhds 0) (nhds |(0 : ℝ)|) :=
      continuous_abs.tendsto 0
    have habs1 := habs0.mono_left
      (show puncturedZero ≤ nhds 0 from nhdsWithin_le_nhds)
    simpa only [abs_zero] using habs1
  have hprod :
      Tendsto (fun h => θ h * h) puncturedZero (nhds 0) := by
    have hneg :
        Tendsto (fun h : ℝ => -|h|) puncturedZero (nhds 0) := by
      simpa using habs.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hneg habs ?_ ?_
    · exact hθ.mono fun h hh => by
        have habsmul : |θ h * h| ≤ |h| := by
          rw [abs_mul, abs_of_pos hh.1]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hh.2.le (abs_nonneg h)
        exact (abs_le.mp habsmul).1
    · exact hθ.mono fun h hh => by
        have habsmul : |θ h * h| ≤ |h| := by
          rw [abs_mul, abs_of_pos hh.1]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hh.2.le (abs_nonneg h)
        exact (abs_le.mp habsmul).2
  have hpoint :
      Tendsto (fun h => x + θ h * h) puncturedZero (nhds x) := by
    simpa using tendsto_const_nhds.add hprod
  have hpunc : ∀ᶠ h in puncturedZero, h ≠ 0 := by
    unfold puncturedZero
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  have hpoint_ne :
      ∀ᶠ h in puncturedZero, x + θ h * h ∈ ({x} : Set ℝ)ᶜ := by
    filter_upwards [hθ, hpunc] with h hθh hh
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hθne : θ h ≠ 0 := hθh.1.ne'
    intro heq
    apply mul_ne_zero hθne hh
    linarith
  have hpoint_within :
      Tendsto (fun h => x + θ h * h) puncturedZero
        (nhdsWithin x ({x} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨hpoint, hpoint_ne⟩
  have hslope := hd.hasDerivAt.tendsto_slope.comp hpoint_within
  have hcoef : iterDeriv (n + 1) f x =
      deriv (iterDeriv n f) x := by
    calc
      iterDeriv (n + 1) f x = iteratedDeriv (n + 1) f x := by
        rw [iterDeriv, iteratedDeriv_eq_iterate]
      _ = deriv (iteratedDeriv n f) x := by
        rw [iteratedDeriv_succ]
      _ = deriv (iterDeriv n f) x := by
        rw [iterDeriv, iteratedDeriv_eq_iterate]
  rw [hcoef]
  convert hslope using 1
  ext h
  simp [derivativeQuotient, slope_def_field]

theorem gap9 (f : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hne : iterDeriv (n + 1) f x ≠ 0) :
    iterDeriv (n + 1) f x ≠ 0 := by
  exact hne

theorem gap10 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hlim : Tendsto (derivativeQuotient f x θ n)
      puncturedZero
      (nhds (iterDeriv (n + 1) f x)))
    (hne : iterDeriv (n + 1) f x ≠ 0) :
    ¬ Tendsto (derivativeQuotient f x θ n)
      puncturedZero (nhds 0) := by
  letI : NeBot puncturedZero := by
    unfold puncturedZero
    exact Filter.NeBot.mono
      (nhdsWithin_Ioi_neBot (le_refl (0 : ℝ)))
      (nhdsWithin_mono _ (by
        intro y hy
        have hy' : 0 < y := hy
        simp [hy'.ne']))
  intro hzero
  have heq := tendsto_nhds_unique hlim hzero
  exact hne heq

theorem gap11 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hbal : ThetaBalance f x θ n)
    (hlim : Tendsto (derivativeQuotient f x θ n)
      puncturedZero (nhds (iterDeriv (n + 1) f x)))
    (hne : iterDeriv (n + 1) f x ≠ 0) :
    Tendsto θ puncturedZero
      (nhds (((1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x) /
        iterDeriv (n + 1) f x)) := by
  rcases hbal with ⟨r, hr, hbalance⟩
  have hratio :
      Tendsto (fun h => r h / h ^ (n + 1))
        puncturedZero (nhds 0) :=
    hr.tendsto_div_nhds_zero
  have htail :
      Tendsto
        (fun h => (Nat.factorial n : ℝ) * r h / h ^ (n + 1))
        puncturedZero (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ℝ => (Nat.factorial n : ℝ))
          puncturedZero (nhds (Nat.factorial n : ℝ)) :=
      tendsto_const_nhds
    have hmul := hconst.mul hratio
    have hmul' :
        Tendsto
          (fun h => (Nat.factorial n : ℝ) * r h / h ^ (n + 1))
          puncturedZero
          (nhds ((Nat.factorial n : ℝ) * 0)) := by
      refine hmul.congr' (Eventually.of_forall ?_)
      intro h
      ring
    simpa only [mul_zero] using hmul'
  have hright :
      Tendsto
        (fun h =>
          (1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x +
            (Nat.factorial n : ℝ) * r h / h ^ (n + 1))
        puncturedZero
        (nhds ((1 / (n + 1 : ℕ) : ℝ) *
          iterDeriv (n + 1) f x)) := by
    simpa using tendsto_const_nhds.add htail
  have hproduct :
      Tendsto
        (fun h => θ h * derivativeQuotient f x θ n h)
        puncturedZero
        (nhds ((1 / (n + 1 : ℕ) : ℝ) *
          iterDeriv (n + 1) f x)) := by
    have hbeq :
        (fun h => θ h * derivativeQuotient f x θ n h) =ᶠ[puncturedZero]
          (fun h =>
            (1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x +
              (Nat.factorial n : ℝ) * r h / h ^ (n + 1)) :=
      hbalance
    exact hright.congr' hbeq.symm
  have hquot := hproduct.div hlim hne
  have hnonzero :
      ∀ᶠ h in puncturedZero,
        derivativeQuotient f x θ n h ≠ 0 :=
    hlim.eventually_ne hne
  refine hquot.congr' ?_
  filter_upwards [hnonzero] with h hh
  change (θ h * derivativeQuotient f x θ n h) /
    derivativeQuotient f x θ n h = θ h
  field_simp

theorem gap12 (f : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hne : iterDeriv (n + 1) f x ≠ 0) :
    ((1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x) /
        iterDeriv (n + 1) f x =
      (1 / (n + 1 : ℕ) : ℝ) := by
  field_simp

theorem gap13 (f : ℝ → ℝ) (x : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (hne : iterDeriv (n + 1) f x ≠ 0)
    (hθ : Tendsto θ puncturedZero
      (nhds (((1 / (n + 1 : ℕ) : ℝ) * iterDeriv (n + 1) f x) /
        iterDeriv (n + 1) f x))) :
    Tendsto θ puncturedZero
      (nhds (1 / (n + 1 : ℕ) : ℝ)) := by
  rw [gap12 f x n hne] at hθ
  exact hθ

theorem gap14 (θ : ℝ → ℝ) (n : ℕ)
    (hθ : Tendsto θ puncturedZero
      (nhds (1 / (n + 1 : ℕ) : ℝ))) :
    Tendsto θ puncturedZero
      (nhds (1 / (n + 1 : ℕ) : ℝ)) := by
  exact hθ

end

end ProofGap.Exercise1393
