import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1452

noncomputable section

def f (x : ℝ) : ℝ := (1 + x ^ 2) / (1 + x ^ 4)
def domain : Set ℝ := Set.Ioi 0
def maximizer : ℝ := Real.sqrt (Real.sqrt 2 - 1)
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private lemma Ici_mem_atTop (a : ℝ) : Set.Ici a ∈ Filter.atTop := by
  exact Filter.eventually_ge_atTop a

private lemma sqrtTwo_sq_aux : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

private lemma sqrtTwo_cube_aux : (Real.sqrt (2 : ℝ)) ^ 3 = 2 * Real.sqrt 2 := by
  calc
    (Real.sqrt (2 : ℝ)) ^ 3 = Real.sqrt 2 * (Real.sqrt 2) ^ 2 := by ring
    _ = Real.sqrt 2 * 2 := by rw [sqrtTwo_sq_aux]
    _ = 2 * Real.sqrt 2 := by ring

private lemma maximizer_sq_aux : maximizer ^ 2 = Real.sqrt 2 - 1 := by
  unfold maximizer
  apply Real.sq_sqrt
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr2 := sqrtTwo_sq_aux
  nlinarith

private lemma maximizer_pos_aux : 0 < maximizer := by
  unfold maximizer
  apply Real.sqrt_pos.2
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr2 := sqrtTwo_sq_aux
  nlinarith

private lemma f_le_bound_aux (x : ℝ) :
    f x ≤ (1 / 2) * (1 + Real.sqrt 2) := by
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 + Real.sqrt 2) := by
    have hr0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hfac :
      0 ≤ (1 / 2 : ℝ) * (1 + Real.sqrt 2) *
        (x ^ 2 - (Real.sqrt 2 - 1)) ^ 2 :=
    mul_nonneg hcoef (sq_nonneg _)
  have hid :
      (1 / 2 : ℝ) * (1 + Real.sqrt 2) * (1 + x ^ 4) -
          (1 + x ^ 2) =
        (1 / 2 : ℝ) * (1 + Real.sqrt 2) *
          (x ^ 2 - (Real.sqrt 2 - 1)) ^ 2 := by
    ring_nf
    simp [sqrtTwo_cube_aux] <;> ring
  have hdiff :
      0 ≤ (1 / 2 : ℝ) * (1 + Real.sqrt 2) * (1 + x ^ 4) -
        (1 + x ^ 2) := by
    rw [hid]
    exact hfac
  have hden : 0 < 1 + x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2)]
  unfold f
  apply (div_le_iff₀ hden).2
  exact sub_nonneg.mp hdiff

private lemma maximizer_value_aux :
    f maximizer = (1 / 2) * (1 + Real.sqrt 2) := by
  unfold f
  rw [show maximizer ^ 4 = (maximizer ^ 2) ^ 2 by ring, maximizer_sq_aux]
  have hd : 1 + (Real.sqrt 2 - 1) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 1)]
  field_simp [hd] <;>
    ring_nf <;>
    simp [sqrtTwo_sq_aux, sqrtTwo_cube_aux] <;>
    ring

theorem gap1 (x : ℝ) : 0 < f x := by
  unfold f
  apply div_pos <;> nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

theorem gap2 : Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hratio :
      Filter.Tendsto
        (fun x : ℝ => ((x⁻¹) ^ 4 + (x⁻¹) ^ 2) / ((x⁻¹) ^ 4 + 1))
        Filter.atTop (nhds 0) := by
    simpa using
      (((hinv.pow 4).add (hinv.pow 2)).div
        ((hinv.pow 4).add
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)))
        (by norm_num : (0 : ℝ) ^ 4 + 1 ≠ 0))
  refine hratio.congr' ?_
  filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
  unfold f
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hx4pos : 0 < x ^ 4 := pow_pos hxpos 4
  have hinvden : (x ^ 4)⁻¹ + 1 ≠ 0 := by
    exact ne_of_gt
      (add_pos_of_nonneg_of_pos (inv_nonneg.mpr hx4pos.le) zero_lt_one)
  have hfden : 1 + x ^ 4 ≠ 0 := by
    exact ne_of_gt (add_pos zero_lt_one hx4pos)
  simp only [inv_pow]
  field_simp [hx0, hinvden, hfden] <;> ring

theorem gap3 : sInf (f '' domain) = 0 := by
  apply le_antisymm
  · apply ge_of_tendsto gap2
    filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact le_of_lt (gap1 z)
    · refine ⟨x, ?_, rfl⟩
      simpa [domain] using
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)
  · apply le_csInf
    · exact ⟨f 1, ⟨1, by norm_num [domain], rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_of_lt (gap1 x)

theorem gap4 : IsMaxOn f domain maximizer := by
  intro x hx
  rw [maximizer_value_aux]
  exact f_le_bound_aux x

theorem gap5 : f maximizer = (1 / 2) * (1 + Real.sqrt 2) := by
  exact maximizer_value_aux

theorem gap6 :
    Approx ((1 / 2) * (1 + Real.sqrt 2)) 1.2 0.01 := by
  have hr2 := sqrtTwo_sq_aux
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hl : (69 / 50 : ℝ) < Real.sqrt 2 := by
    by_contra h
    have hle : Real.sqrt 2 ≤ (69 / 50 : ℝ) := le_of_not_gt h
    have hp :
        0 ≤ ((69 / 50 : ℝ) + Real.sqrt 2) *
          ((69 / 50 : ℝ) - Real.sqrt 2) :=
      mul_nonneg (by nlinarith) (sub_nonneg.mpr hle)
    nlinarith
  have hu : Real.sqrt 2 < (71 / 50 : ℝ) := by
    by_contra h
    have hle : (71 / 50 : ℝ) ≤ Real.sqrt 2 := le_of_not_gt h
    have hp :
        0 ≤ (Real.sqrt 2 + (71 / 50 : ℝ)) *
          (Real.sqrt 2 - (71 / 50 : ℝ)) :=
      mul_nonneg (by nlinarith) (sub_nonneg.mpr hle)
    nlinarith
  unfold Approx
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap7 : Approx (f maximizer) 1.2 0.01 := by
  rw [gap5]
  exact gap6

theorem gap8 :
    sSup (f '' domain) = (1 / 2) * (1 + Real.sqrt 2) := by
  apply le_antisymm
  · apply csSup_le
    · exact
        ⟨f maximizer,
          ⟨maximizer, by simpa [domain] using maximizer_pos_aux, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact f_le_bound_aux x
  · apply le_csSup
    · refine ⟨(1 / 2 : ℝ) * (1 + Real.sqrt 2), ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact f_le_bound_aux x
    · exact
        ⟨maximizer, by simpa [domain] using maximizer_pos_aux,
          maximizer_value_aux⟩

end
end ProofGap.Exercise1452
