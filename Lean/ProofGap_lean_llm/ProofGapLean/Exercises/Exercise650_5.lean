import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise650_5

noncomputable section

def nested (x : ℝ) : ℝ :=
  Real.sqrt (x + Real.sqrt (x + Real.sqrt x))
def scale (x : ℝ) : ℝ := Real.rpow x (1 / 8)
def normalized (x : ℝ) : ℝ := nested x / scale x
def rewritten (x : ℝ) : ℝ :=
  Real.sqrt (Real.rpow x (3 / 4) +
    Real.sqrt (Real.rpow x (1 / 2) + 1))

/-- Source: `proof_gap/exercise_650_5/1.txt`. -/
private lemma positive_identities {x : ℝ} (hx : 0 < x) :
    normalized x = rewritten x ∧
      rewritten x =
        Real.sqrt (Real.sqrt x * Real.sqrt (Real.sqrt x) +
          Real.sqrt (Real.sqrt x + 1)) := by
  have hhalf_mul :
      Real.rpow x (1 / 2) * Real.rpow x (1 / 2) = x := by
    calc
      Real.rpow x (1 / 2) * Real.rpow x (1 / 2) =
          Real.rpow x ((1 / 2) + (1 / 2)) :=
        (Real.rpow_add hx (1 / 2) (1 / 2)).symm
      _ = x := by norm_num
  have hquarter_mul :
      Real.rpow x (1 / 4) * Real.rpow x (3 / 4) = x := by
    calc
      Real.rpow x (1 / 4) * Real.rpow x (3 / 4) =
          Real.rpow x ((1 / 4) + (3 / 4)) :=
        (Real.rpow_add hx (1 / 4) (3 / 4)).symm
      _ = x := by norm_num
  have hhalf : Real.rpow x (1 / 2) = Real.sqrt x := by
    have hrpow_nonneg : 0 ≤ Real.rpow x (1 / 2) :=
      Real.rpow_nonneg hx.le (1 / 2)
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
    nlinarith
  have hsqrt_half :
      Real.sqrt (Real.rpow x (1 / 2)) = Real.rpow x (1 / 4) := by
    calc
      Real.sqrt (Real.rpow x (1 / 2)) =
          Real.rpow (Real.rpow x (1 / 2)) (1 / 2) :=
        Real.sqrt_eq_rpow _
      _ = Real.rpow x ((1 / 2) * (1 / 2)) :=
        (Real.rpow_mul hx.le (1 / 2) (1 / 2)).symm
      _ = Real.rpow x (1 / 4) := by norm_num
  have hsqrt_quarter :
      Real.sqrt (Real.rpow x (1 / 4)) = Real.rpow x (1 / 8) := by
    calc
      Real.sqrt (Real.rpow x (1 / 4)) =
          Real.rpow (Real.rpow x (1 / 4)) (1 / 2) :=
        Real.sqrt_eq_rpow _
      _ = Real.rpow x ((1 / 4) * (1 / 2)) :=
        (Real.rpow_mul hx.le (1 / 4) (1 / 2)).symm
      _ = Real.rpow x (1 / 8) := by norm_num
  have hquarter :
      Real.rpow x (1 / 4) = Real.sqrt (Real.sqrt x) := by
    calc
      Real.rpow x (1 / 4) = Real.sqrt (Real.rpow x (1 / 2)) :=
        hsqrt_half.symm
      _ = Real.sqrt (Real.sqrt x) := by rw [hhalf]
  have hthree_quarters :
      Real.rpow x (3 / 4) =
        Real.sqrt x * Real.sqrt (Real.sqrt x) := by
    calc
      Real.rpow x (3 / 4) =
          Real.rpow x ((1 / 2) + (1 / 4)) := by norm_num
      _ = Real.rpow x (1 / 2) * Real.rpow x (1 / 4) :=
        Real.rpow_add hx (1 / 2) (1 / 4)
      _ = Real.sqrt x * Real.sqrt (Real.sqrt x) := by
        rw [hhalf, hquarter]
  have hinner :
      x + Real.sqrt x =
        Real.rpow x (1 / 2) * (Real.rpow x (1 / 2) + 1) := by
    calc
      x + Real.sqrt x =
          Real.rpow x (1 / 2) * Real.rpow x (1 / 2) +
            Real.rpow x (1 / 2) := by
        rw [hhalf_mul, hhalf]
      _ = Real.rpow x (1 / 2) *
          (Real.rpow x (1 / 2) + 1) := by
        rw [mul_add, mul_one]
  have hmiddle :
      Real.sqrt (x + Real.sqrt x) =
        Real.rpow x (1 / 4) *
          Real.sqrt (Real.rpow x (1 / 2) + 1) := by
    calc
      Real.sqrt (x + Real.sqrt x) =
          Real.sqrt (Real.rpow x (1 / 2) *
            (Real.rpow x (1 / 2) + 1)) := by rw [hinner]
      _ = Real.sqrt (Real.rpow x (1 / 2)) *
          Real.sqrt (Real.rpow x (1 / 2) + 1) := by
        exact Real.sqrt_mul (Real.rpow_nonneg hx.le (1 / 2)) _
      _ = Real.rpow x (1 / 4) *
          Real.sqrt (Real.rpow x (1 / 2) + 1) := by
        rw [hsqrt_half]
  have houter :
      x + Real.sqrt (x + Real.sqrt x) =
        Real.rpow x (1 / 4) *
          (Real.rpow x (3 / 4) +
            Real.sqrt (Real.rpow x (1 / 2) + 1)) := by
    calc
      x + Real.sqrt (x + Real.sqrt x) =
          x + Real.rpow x (1 / 4) *
            Real.sqrt (Real.rpow x (1 / 2) + 1) := by rw [hmiddle]
      _ = Real.rpow x (1 / 4) *
          (Real.rpow x (3 / 4) +
            Real.sqrt (Real.rpow x (1 / 2) + 1)) := by
        rw [mul_add, hquarter_mul]
  have hnested : nested x = scale x * rewritten x := by
    unfold nested scale rewritten
    rw [houter]
    calc
      Real.sqrt (Real.rpow x (1 / 4) *
          (Real.rpow x (3 / 4) +
            Real.sqrt (Real.rpow x (1 / 2) + 1))) =
          Real.sqrt (Real.rpow x (1 / 4)) *
            Real.sqrt (Real.rpow x (3 / 4) +
              Real.sqrt (Real.rpow x (1 / 2) + 1)) := by
        exact Real.sqrt_mul (Real.rpow_nonneg hx.le (1 / 4)) _
      _ = Real.rpow x (1 / 8) *
          Real.sqrt (Real.rpow x (3 / 4) +
            Real.sqrt (Real.rpow x (1 / 2) + 1)) := by
        rw [hsqrt_quarter]
  have hscale : scale x ≠ 0 := by
    simpa [scale] using (Real.rpow_pos_of_pos hx (1 / 8 : ℝ)).ne'
  have hnormalized : normalized x = rewritten x := by
    rw [normalized]
    apply (div_eq_iff hscale).mpr
    rw [hnested]
    exact mul_comm _ _
  refine ⟨hnormalized, ?_⟩
  unfold rewritten
  rw [hhalf, hthree_quarters]

theorem gap1 (L : ℝ) :
    Filter.Tendsto normalized (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Filter.Tendsto rewritten (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0)) normalized rewritten := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (positive_identities hx).1
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_650_5/2.txt`. -/
theorem gap2 :
    Filter.Tendsto rewritten (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  let model : ℝ → ℝ := fun x =>
    Real.sqrt (Real.sqrt x * Real.sqrt (Real.sqrt x) +
      Real.sqrt (Real.sqrt x + 1))
  have hcont : ContinuousAt model 0 := by
    dsimp [model]
    fun_prop
  have hmodel_full : Filter.Tendsto model (nhds 0) (nhds 1) := by
    simpa [model] using hcont.tendsto
  have hmodel :
      Filter.Tendsto model (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    hmodel_full.mono_left inf_le_left
  have heq :
      Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0)) rewritten model := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (positive_identities hx).2
  exact hmodel.congr' heq.symm

/-- Source: `proof_gap/exercise_650_5/3.txt`. -/
theorem gap3 :
    Filter.Tendsto normalized (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact (gap1 1).mpr gap2

/-- Source: `proof_gap/exercise_650_5/4.txt`. -/
theorem gap4 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0)) nested scale := by
  change Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
    (fun x => nested x - scale x) scale
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hzero :
      Filter.Tendsto (fun x => normalized x - 1)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert gap3.sub (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) using 1 <;> norm_num
  have hev :
      ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
        dist (normalized x - 1) 0 < c :=
    (Metric.tendsto_nhds.mp hzero) c hc
  filter_upwards [hev, self_mem_nhdsWithin] with x hdist hx
  have hs : scale x ≠ 0 := by
    simpa [scale] using (Real.rpow_pos_of_pos hx (1 / 8 : ℝ)).ne'
  have halg :
      nested x - scale x = scale x * (normalized x - 1) := by
    rw [normalized]
    field_simp [hs]
  have hnorm : ‖normalized x - 1‖ < c := by
    simpa [Real.dist_eq] using hdist
  calc
    ‖nested x - scale x‖ =
        ‖scale x‖ * ‖normalized x - 1‖ := by rw [halg, norm_mul]
    _ ≤ ‖scale x‖ * c :=
      mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg _)
    _ = c * ‖scale x‖ := mul_comm _ _

/-- Source: `proof_gap/exercise_650_5/5.txt`. -/
theorem gap5 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0)) nested scale := by
  exact gap4

end

end ProofGap.Exercise650_5
