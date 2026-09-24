import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise459

noncomputable section

def t (x : ℝ) : ℝ := 1 / x
def original (x : ℝ) : ℝ :=
  x * (Real.sqrt (x ^ 2 + 2 * x) - 2 * Real.sqrt (x ^ 2 + x) + x)
def transformed (u : ℝ) : ℝ :=
  (Real.sqrt (1 + 2 * u) - 2 * Real.sqrt (1 + u) + 1) / u ^ 2
def closed (u : ℝ) : ℝ :=
  -4 / ((Real.sqrt (1 + 2 * u) + 1 + 2 * Real.sqrt (1 + u)) *
    (1 + Real.sqrt (1 + 2 * u)) ^ 2)
def HasLimitAtPosInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |g x - L| < ε

/-- Source: `proof_gap/exercise_459/1.txt`; bind `t(x)=1/x`. -/
private theorem transformed_eq_closed_of_domain (u : ℝ)
    (hu : -(1 / 2 : ℝ) ≤ u) (hu0 : u ≠ 0) :
    transformed u = closed u := by
  let A : ℝ := Real.sqrt (1 + 2 * u)
  let B : ℝ := Real.sqrt (1 + u)
  have hA : A ^ 2 = 1 + 2 * u := by
    dsimp [A]
    exact Real.sq_sqrt (by linarith)
  have hB : B ^ 2 = 1 + u := by
    dsimp [B]
    exact Real.sq_sqrt (by linarith)
  have hAn : 0 ≤ A := by
    dsimp [A]
    exact Real.sqrt_nonneg _
  have hBn : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hinner :
      (A + 1) ^ 2 - 4 * (1 + u) = -(A - 1) ^ 2 := by
    nlinarith [hA]
  have hdiff : A ^ 2 - 1 = 2 * u := by
    linarith [hA]
  have hpoly :
      (A - 2 * B + 1) * (A + 1 + 2 * B) * (1 + A) ^ 2 =
        -4 * u ^ 2 := by
    calc
      (A - 2 * B + 1) * (A + 1 + 2 * B) * (1 + A) ^ 2 =
          ((A + 1) ^ 2 - 4 * B ^ 2) * (1 + A) ^ 2 := by ring
      _ = ((A + 1) ^ 2 - 4 * (1 + u)) * (1 + A) ^ 2 := by rw [hB]
      _ = (-(A - 1) ^ 2) * (1 + A) ^ 2 := by rw [hinner]
      _ = -(A ^ 2 - 1) ^ 2 := by ring
      _ = -4 * u ^ 2 := by rw [hdiff]; ring
  have hd1pos : 0 < A + 1 + 2 * B := by
    nlinarith [hAn, hBn]
  have hd2pos : 0 < 1 + A := by
    linarith [hAn]
  have hd1 : A + 1 + 2 * B ≠ 0 := ne_of_gt hd1pos
  have hd2 : 1 + A ≠ 0 := ne_of_gt hd2pos
  change
    (A - 2 * B + 1) / u ^ 2 =
      -4 / ((A + 1 + 2 * B) * (1 + A) ^ 2)
  refine (div_eq_div_iff (pow_ne_zero 2 hu0)
    (mul_ne_zero hd1 (pow_ne_zero 2 hd2))).2 ?_
  calc
    (A - 2 * B + 1) * ((A + 1 + 2 * B) * (1 + A) ^ 2) =
        (A - 2 * B + 1) * (A + 1 + 2 * B) * (1 + A) ^ 2 := by ring
    _ = -4 * u ^ 2 := hpoly

theorem gap1 : ∀ x : ℝ, 0 < x →
    original x = transformed (t x) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsqrt2 :
      Real.sqrt (x ^ 2 + 2 * x) =
        x * Real.sqrt (1 + 2 * (1 / x)) := by
    calc
      Real.sqrt (x ^ 2 + 2 * x) =
          Real.sqrt (x ^ 2 * (1 + 2 * (1 / x))) := by
            congr 1
            field_simp [hx0] <;> ring
      _ = Real.sqrt (x ^ 2) * Real.sqrt (1 + 2 * (1 / x)) := by
            rw [Real.sqrt_mul (sq_nonneg x)]
      _ = x * Real.sqrt (1 + 2 * (1 / x)) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hsqrt1 :
      Real.sqrt (x ^ 2 + x) =
        x * Real.sqrt (1 + 1 / x) := by
    calc
      Real.sqrt (x ^ 2 + x) =
          Real.sqrt (x ^ 2 * (1 + 1 / x)) := by
            congr 1
            field_simp [hx0] <;> ring
      _ = Real.sqrt (x ^ 2) * Real.sqrt (1 + 1 / x) := by
            rw [Real.sqrt_mul (sq_nonneg x)]
      _ = x * Real.sqrt (1 + 1 / x) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hx]
  unfold original transformed t
  rw [hsqrt2, hsqrt1]
  field_simp [hx0] <;> ring

/-- Source: `proof_gap/exercise_459/2.txt`. -/
theorem gap2 : ∀ u : ℝ, u ≠ 0 →
    -1 ≤ u →
    transformed u =
      ((Real.sqrt (1 + 2 * u) + 1) ^ 2 - 4 * (1 + u)) /
        (u ^ 2 * (Real.sqrt (1 + 2 * u) + 1 + 2 * Real.sqrt (1 + u))) := by
  intro u hu0 hu
  let A : ℝ := Real.sqrt (1 + 2 * u)
  let B : ℝ := Real.sqrt (1 + u)
  have hB : B ^ 2 = 1 + u := by
    dsimp [B]
    exact Real.sq_sqrt (by linarith)
  have hAn : 0 ≤ A := by
    dsimp [A]
    exact Real.sqrt_nonneg _
  have hBn : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hden : A + 1 + 2 * B ≠ 0 := by
    apply ne_of_gt
    nlinarith
  change
    (A - 2 * B + 1) / u ^ 2 =
      ((A + 1) ^ 2 - 4 * (1 + u)) /
        (u ^ 2 * (A + 1 + 2 * B))
  field_simp [hu0, hden]
  nlinarith [hB]

/-- Source: `proof_gap/exercise_459/3.txt`. -/
theorem gap3 : ∀ u : ℝ, u ≠ 0 → -(1 / 2 : ℝ) ≤ u →
    transformed u = closed u := by
  intro u hu0 hu
  exact transformed_eq_closed_of_domain u hu hu0

/-- Source: `proof_gap/exercise_459/4.txt`. -/
theorem gap4 : Filter.Tendsto t Filter.atTop (nhds 0) := by
  unfold t
  simpa only [one_div] using
    (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))

/-- Source: `proof_gap/exercise_459/5.txt`. -/
theorem gap5 : HasLimitAtPosInfinity original (-1 / 4) := by
  have hclosed_value : closed 0 = (-1 / 4 : ℝ) := by
    norm_num [closed]
  have hsqrt2 :
      ContinuousAt (fun u : ℝ => Real.sqrt (1 + 2 * u)) 0 := by
    exact Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
  have hsqrt1 :
      ContinuousAt (fun u : ℝ => Real.sqrt (1 + u)) 0 := by
    exact Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have hden_cont :
      ContinuousAt
        (fun u : ℝ =>
          (Real.sqrt (1 + 2 * u) + 1 + 2 * Real.sqrt (1 + u)) *
            (1 + Real.sqrt (1 + 2 * u)) ^ 2) 0 := by
    exact
      ((hsqrt2.add continuousAt_const).add
        (continuousAt_const.mul hsqrt1)).mul
        ((continuousAt_const.add hsqrt2).pow 2)
  have hclosed_cont : ContinuousAt closed 0 := by
    unfold closed
    refine continuousAt_const.div hden_cont ?_
    norm_num
  have hclosed_tend :
      Filter.Tendsto closed (nhds 0) (nhds (-1 / 4 : ℝ)) := by
    rw [← hclosed_value]
    exact hclosed_cont
  have hcomp :
      Filter.Tendsto (fun x : ℝ => closed (t x)) Filter.atTop
        (nhds (-1 / 4 : ℝ)) :=
    hclosed_tend.comp gap4
  have heq :
      ∀ᶠ x : ℝ in Filter.atTop, original x = closed (t x) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have htpos : 0 < t x := by
      unfold t
      exact one_div_pos.mpr hxpos
    exact (gap1 x hxpos).trans
      (transformed_eq_closed_of_domain (t x) (by linarith) htpos.ne')
  have heq' :
      (fun x : ℝ => closed (t x)) =ᶠ[Filter.atTop] original := by
    filter_upwards [heq] with x hx
    exact hx.symm
  have horiginal :
      Filter.Tendsto original Filter.atTop (nhds (-1 / 4 : ℝ)) :=
    hcomp.congr' heq'
  unfold HasLimitAtPosInfinity
  intro ε hε
  have hev :
      ∀ᶠ x : ℝ in Filter.atTop, |original x - (-1 / 4 : ℝ)| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (horiginal.eventually (Metric.ball_mem_nhds _ hε))
  rcases Filter.eventually_atTop.1 hev with ⟨a, ha⟩
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right a 1), ?_⟩
  intro x hx
  exact ha x (le_trans (le_max_left a 1) (le_of_lt hx))

end

end ProofGap.Exercise459
