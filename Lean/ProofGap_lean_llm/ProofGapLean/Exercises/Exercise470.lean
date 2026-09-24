import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise470

noncomputable section

def curve (x : ℝ) : ℝ := Real.sqrt (x ^ 2 - x + 1)
def residual (a b x : ℝ) : ℝ := curve x - a * x - b
def conjugate (a b x : ℝ) : ℝ := curve x + a * x + b
def numerator (a b x : ℝ) : ℝ :=
  (1 - a ^ 2) * x ^ 2 - (1 + 2 * a * b) * x + 1 - b ^ 2
def HasLeftAsymptote (a b : ℝ) : Prop :=
  Filter.Tendsto (residual a b) Filter.atBot (nhds 0)
def HasRightAsymptote (a b : ℝ) : Prop :=
  Filter.Tendsto (residual a b) Filter.atTop (nhds 0)

/-- Source: `proof_gap/exercise_470/1.txt`; exclude zeros of the rationalizing denominator. -/
private theorem radicand_nonneg (x : ℝ) : 0 ≤ x ^ 2 - x + 1 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

private theorem factor_product (x : ℝ) :
    (curve x + x - 1 / 2) * (curve x - x + 1 / 2) = 3 / 4 := by
  have hs := Real.sq_sqrt (radicand_nonneg x)
  unfold curve
  nlinarith [hs]

private theorem left_rationalized (x : ℝ) :
    curve x + x - 1 / 2 = (3 / 4) / (curve x - x + 1 / 2) := by
  have hd : curve x - x + 1 / 2 ≠ 0 := by
    intro hd
    have hp := factor_product x
    rw [hd, mul_zero] at hp
    norm_num at hp
  apply (eq_div_iff hd).2
  exact factor_product x

private theorem right_rationalized (x : ℝ) :
    curve x - x + 1 / 2 = (3 / 4) / (curve x + x - 1 / 2) := by
  have hu : curve x + x - 1 / 2 ≠ 0 := by
    intro hu
    have hp := factor_product x
    rw [hu, zero_mul] at hp
    norm_num at hp
  apply (eq_div_iff hu).2
  simpa [mul_comm] using factor_product x

private theorem left_large :
    Filter.Tendsto (fun x : ℝ => curve x - x + 1 / 2)
      Filter.atBot Filter.atTop := by
  refine Filter.tendsto_atTop.2 (fun z => ?_)
  exact (Filter.eventually_le_atBot (1 / 2 - z)).mono (by
    intro x hx
    have hs : 0 ≤ curve x := Real.sqrt_nonneg _
    linarith)

private theorem right_large :
    Filter.Tendsto (fun x : ℝ => curve x + x - 1 / 2)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 (fun z => ?_)
  exact (Filter.eventually_ge_atTop (z + 1 / 2)).mono (by
    intro x hx
    have hs : 0 ≤ curve x := Real.sqrt_nonneg _
    linarith)

private theorem left_small :
    Filter.Tendsto (fun x : ℝ => curve x + x - 1 / 2)
      Filter.atBot (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => (curve x - x + 1 / 2)⁻¹)
        Filter.atBot (nhds 0) :=
    tendsto_inv_atTop_zero.comp left_large
  have hquot :
      Filter.Tendsto
        (fun x : ℝ => (3 / 4 : ℝ) / (curve x - x + 1 / 2))
        Filter.atBot (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  exact hquot.congr' (Filter.Eventually.of_forall
    (fun x => (left_rationalized x).symm))

private theorem right_small :
    Filter.Tendsto (fun x : ℝ => curve x - x + 1 / 2)
      Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => (curve x + x - 1 / 2)⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp right_large
  have hquot :
      Filter.Tendsto
        (fun x : ℝ => (3 / 4 : ℝ) / (curve x + x - 1 / 2))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  exact hquot.congr' (Filter.Eventually.of_forall
    (fun x => (right_rationalized x).symm))

private theorem constant_zero_atBot {k : ℝ}
    (h : Filter.Tendsto (fun _ : ℝ => k) Filter.atBot (nhds 0)) : k = 0 := by
  by_contra hk
  have hkabs : 0 < |k| := abs_pos.mpr hk
  have hev : ∀ᶠ _ in (Filter.atBot : Filter ℝ), k ∈ Metric.ball 0 |k| :=
    h.eventually (Metric.ball_mem_nhds 0 hkabs)
  rcases hev.exists with ⟨x, hx⟩
  have hlt : dist k 0 < |k| := by
    simpa [Metric.mem_ball] using hx
  have : |k| < |k| := by
    simpa [Real.dist_eq] using hlt
  exact (lt_irrefl _ this)

private theorem constant_zero_atTop {k : ℝ}
    (h : Filter.Tendsto (fun _ : ℝ => k) Filter.atTop (nhds 0)) : k = 0 := by
  by_contra hk
  have hkabs : 0 < |k| := abs_pos.mpr hk
  have hev : ∀ᶠ _ in (Filter.atTop : Filter ℝ), k ∈ Metric.ball 0 |k| :=
    h.eventually (Metric.ball_mem_nhds 0 hkabs)
  rcases hev.exists with ⟨x, hx⟩
  have hlt : dist k 0 < |k| := by
    simpa [Metric.mem_ball] using hx
  have : |k| < |k| := by
    simpa [Real.dist_eq] using hlt
  exact (lt_irrefl _ this)

private theorem affine_zero_atBot {c d : ℝ}
    (h : Filter.Tendsto (fun x : ℝ => c * x + d)
      Filter.atBot (nhds 0)) : c = 0 ∧ d = 0 := by
  have hshift : Filter.Tendsto (fun x : ℝ => x - 1)
      Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot.2 (fun z => ?_)
    exact (Filter.eventually_le_atBot (z + 1)).mono (by
      intro x hx
      linarith)
  have hdiff :
      Filter.Tendsto
        (fun x : ℝ => (c * (x - 1) + d) - (c * x + d))
        Filter.atBot (nhds (0 - 0)) :=
    (h.comp hshift).sub h
  have heq :
      (fun _ : ℝ => -c) =ᶠ[Filter.atBot]
        (fun x : ℝ => (c * (x - 1) + d) - (c * x + d)) :=
    Filter.Eventually.of_forall (fun x => by ring)
  have hconst : Filter.Tendsto (fun _ : ℝ => -c)
      Filter.atBot (nhds 0) := by
    simpa using hdiff.congr' heq.symm
  have hcneg : -c = 0 := constant_zero_atBot hconst
  have hc : c = 0 := by linarith
  have hdlim : Filter.Tendsto (fun _ : ℝ => d)
      Filter.atBot (nhds 0) := by
    simpa [hc] using h
  exact ⟨hc, constant_zero_atBot hdlim⟩

private theorem affine_zero_atTop {c d : ℝ}
    (h : Filter.Tendsto (fun x : ℝ => c * x + d)
      Filter.atTop (nhds 0)) : c = 0 ∧ d = 0 := by
  have hshift : Filter.Tendsto (fun x : ℝ => x + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun z => ?_)
    exact (Filter.eventually_ge_atTop (z - 1)).mono (by
      intro x hx
      linarith)
  have hdiff :
      Filter.Tendsto
        (fun x : ℝ => (c * (x + 1) + d) - (c * x + d))
        Filter.atTop (nhds (0 - 0)) :=
    (h.comp hshift).sub h
  have heq :
      (fun _ : ℝ => c) =ᶠ[Filter.atTop]
        (fun x : ℝ => (c * (x + 1) + d) - (c * x + d)) :=
    Filter.Eventually.of_forall (fun x => by ring)
  have hconst : Filter.Tendsto (fun _ : ℝ => c)
      Filter.atTop (nhds 0) := by
    simpa using hdiff.congr' heq.symm
  have hc : c = 0 := constant_zero_atTop hconst
  have hdlim : Filter.Tendsto (fun _ : ℝ => d)
      Filter.atTop (nhds 0) := by
    simpa [hc] using h
  exact ⟨hc, constant_zero_atTop hdlim⟩

private theorem left_parameters (a b : ℝ)
    (h : HasLeftAsymptote a b) : a = -1 ∧ b = 1 / 2 := by
  change Filter.Tendsto (residual a b) Filter.atBot (nhds 0) at h
  have hraw := h.sub left_small
  have heq :
      (fun x : ℝ => (-a - 1) * x + (1 / 2 - b)) =ᶠ[Filter.atBot]
        (fun x : ℝ => residual a b x - (curve x + x - 1 / 2)) :=
    Filter.Eventually.of_forall (fun x => by
      unfold residual
      ring)
  have hdiff :
      Filter.Tendsto
        (fun x : ℝ => (-a - 1) * x + (1 / 2 - b))
        Filter.atBot (nhds 0) := by
    simpa using hraw.congr' heq.symm
  rcases affine_zero_atBot hdiff with ⟨hc, hd⟩
  constructor <;> linarith

private theorem right_parameters (a b : ℝ)
    (h : HasRightAsymptote a b) : a = 1 ∧ b = -1 / 2 := by
  change Filter.Tendsto (residual a b) Filter.atTop (nhds 0) at h
  have hraw := h.sub right_small
  have heq :
      (fun x : ℝ => (1 - a) * x + (-b - 1 / 2)) =ᶠ[Filter.atTop]
        (fun x : ℝ => residual a b x - (curve x - x + 1 / 2)) :=
    Filter.Eventually.of_forall (fun x => by
      unfold residual
      ring)
  have hdiff :
      Filter.Tendsto
        (fun x : ℝ => (1 - a) * x + (-b - 1 / 2))
        Filter.atTop (nhds 0) := by
    simpa using hraw.congr' heq.symm
  rcases affine_zero_atTop hdiff with ⟨hc, hd⟩
  constructor <;> linarith

theorem gap1 (a₁ b₁ x : ℝ) (hx : conjugate a₁ b₁ x ≠ 0) :
    residual a₁ b₁ x = numerator a₁ b₁ x / conjugate a₁ b₁ x := by
  apply (eq_div_iff hx).2
  have hs := Real.sq_sqrt (radicand_nonneg x)
  unfold residual numerator conjugate curve
  nlinarith [hs]

/-- Source: `proof_gap/exercise_470/2.txt`; restore the omitted asymptote hypothesis. -/
theorem gap2 (a₁ b₁ : ℝ) (h : HasLeftAsymptote a₁ b₁) :
    1 - a₁ ^ 2 = 0 := by
  have ha := (left_parameters a₁ b₁ h).1
  rw [ha]
  norm_num

/-- Source: `proof_gap/exercise_470/3.txt`; restore the omitted asymptote hypothesis. -/
theorem gap3 (a₁ b₁ : ℝ) (h : HasLeftAsymptote a₁ b₁) :
    1 + 2 * a₁ * b₁ = 0 := by
  rcases left_parameters a₁ b₁ h with ⟨ha, hb⟩
  rw [ha, hb]
  norm_num

/-- Source: `proof_gap/exercise_470/4.txt`. -/
theorem gap4 (a₁ : ℝ) (h : 1 - a₁ ^ 2 = 0) :
    a₁ = 1 ∨ a₁ = -1 := by
  have hfac : (a₁ - 1) * (a₁ + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with h₁ | h₁
  · left
    linarith
  · right
    linarith

/-- Source: `proof_gap/exercise_470/5.txt`. -/
theorem gap5 (a₁ b₁ : ℝ) (ha : a₁ = 1 ∨ a₁ = -1)
    (hab : 1 + 2 * a₁ * b₁ = 0) :
    b₁ = -1 / 2 ∨ b₁ = 1 / 2 := by
  rcases ha with rfl | rfl
  · left
    norm_num at hab ⊢
    linarith
  · right
    norm_num at hab ⊢
    linarith

/-- Source: `proof_gap/exercise_470/6.txt`; specialize the first candidate pair. -/
theorem gap6 (x : ℝ) :
    conjugate 1 (-1 / 2) x = curve x + x - 1 / 2 := by
  unfold conjugate
  ring

/-- Source: `proof_gap/exercise_470/7.txt`; rationalize the first candidate. -/
theorem gap7 (x : ℝ) (hx : curve x - x + 1 / 2 ≠ 0) :
    curve x + x - 1 / 2 = (3 / 4) / (curve x - x + 1 / 2) := by
  exact left_rationalized x

/-- Source: `proof_gap/exercise_470/8.txt`. -/
theorem gap8 :
    Filter.Tendsto (fun x => curve x + x - 1 / 2) Filter.atBot (nhds 0) := by
  exact left_small

/-- Source: `proof_gap/exercise_470/9.txt`. -/
theorem gap9 :
    Filter.Tendsto (residual 1 (-1 / 2)) Filter.atBot Filter.atTop := by
  exact left_large.congr' (Filter.Eventually.of_forall (fun x => by
    unfold residual
    ring))

/-- Source: `proof_gap/exercise_470/10.txt`; the first candidate contradicts a left asymptote. -/
theorem gap10 : ¬ HasLeftAsymptote 1 (-1 / 2) := by
  intro h
  change Filter.Tendsto (residual 1 (-1 / 2)) Filter.atBot (nhds 0) at h
  have hlt : ∀ᶠ x in Filter.atBot, residual 1 (-1 / 2) x < 1 :=
    h.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hge : ∀ᶠ x in Filter.atBot, (1 : ℝ) ≤ residual 1 (-1 / 2) x :=
    (Filter.tendsto_atTop.1 gap9) 1
  rcases (hlt.and hge).exists with ⟨x, hx, hx'⟩
  exact (not_lt_of_ge hx') hx

/-- Source: `proof_gap/exercise_470/11.txt`; specialize the surviving left candidate. -/
theorem gap11 (x : ℝ) :
    conjugate (-1) (1 / 2) x = curve x - x + 1 / 2 := by
  unfold conjugate
  ring

/-- Source: `proof_gap/exercise_470/12.txt`. -/
theorem gap12 :
    Filter.Tendsto (fun x => curve x - x + 1 / 2) Filter.atBot Filter.atTop := by
  exact left_large

/-- Source: `proof_gap/exercise_470/13.txt`. -/
theorem gap13 : HasLeftAsymptote (-1) (1 / 2) := by
  unfold HasLeftAsymptote
  exact left_small.congr' (Filter.Eventually.of_forall (fun x => by
    unfold residual
    ring))

/-- Source: `proof_gap/exercise_470/14.txt`. -/
theorem gap14 (a₁ b₁ : ℝ) (h : HasLeftAsymptote a₁ b₁) : a₁ = -1 := by
  exact (left_parameters a₁ b₁ h).1

/-- Source: `proof_gap/exercise_470/15.txt`. -/
theorem gap15 (a₁ b₁ : ℝ) (h : HasLeftAsymptote a₁ b₁) : b₁ = 1 / 2 := by
  exact (left_parameters a₁ b₁ h).2

/-- Source: `proof_gap/exercise_470/16.txt`. -/
theorem gap16 (a₂ b₂ : ℝ) (h : HasRightAsymptote a₂ b₂) : a₂ = 1 := by
  exact (right_parameters a₂ b₂ h).1

/-- Source: `proof_gap/exercise_470/17.txt`. -/
theorem gap17 (a₂ b₂ : ℝ) (h : HasRightAsymptote a₂ b₂) : b₂ = -1 / 2 := by
  exact (right_parameters a₂ b₂ h).2

/-- Source: `proof_gap/exercise_470/18.txt`. -/
theorem gap18 (a₁ b₁ a₂ b₂ : ℝ)
    (h : (a₁, b₁, a₂, b₂) = (-1, 1 / 2, 1, -1 / 2)) :
    HasLeftAsymptote a₁ b₁ ∧ HasRightAsymptote a₂ b₂ := by
  have ha₁ : a₁ = -1 := by
    simpa using congrArg (fun p => p.1) h
  have hb₁ : b₁ = 1 / 2 := by
    simpa using congrArg (fun p => p.2.1) h
  have ha₂ : a₂ = 1 := by
    simpa using congrArg (fun p => p.2.2.1) h
  have hb₂ : b₂ = -1 / 2 := by
    simpa using congrArg (fun p => p.2.2.2) h
  rw [ha₁, hb₁, ha₂, hb₂]
  constructor
  · unfold HasLeftAsymptote
    exact left_small.congr' (Filter.Eventually.of_forall (fun x => by
      unfold residual
      ring))
  · unfold HasRightAsymptote
    exact right_small.congr' (Filter.Eventually.of_forall (fun x => by
      unfold residual
      ring))

end

end ProofGap.Exercise470
