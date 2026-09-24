import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise832

noncomputable section

def differenceQuotient (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (f (a + h) - f a) / h

/-- Source: `proof_gap/exercise_832/1.txt`; replace symbolic arrows by `Tendsto`. -/
private theorem differentiableAt_punctured_slope
    (f : ℝ → ℝ) (a : ℝ) (hf : DifferentiableAt ℝ f a) :
    Filter.Tendsto (fun x => (f x - f a) / (x - a))
      (nhdsWithin a {a}ᶜ) (nhds (deriv f a)) := by
  have hrem :
      (fun x => f x - f a - (x - a) * deriv f a) =o[nhds a]
        (fun x => x - a) := by
    simpa [mul_comm] using hf.hasDerivAt.isLittleO
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have heps : 0 < ε / 2 := by linarith
  have hb :
      ∀ᶠ x in nhdsWithin a {a}ᶜ,
        ‖f x - f a - (x - a) * deriv f a‖ ≤
          (ε / 2) * ‖x - a‖ :=
    (hrem.def heps).filter_mono inf_le_left
  filter_upwards [hb, self_mem_nhdsWithin] with x hbound hx
  change x ≠ a at hx
  have hne : x - a ≠ 0 := sub_ne_zero.mpr hx
  have hnorm : 0 < ‖x - a‖ := norm_pos_iff.mpr hne
  have hquot :
      (f x - f a) / (x - a) - deriv f a =
        (f x - f a - (x - a) * deriv f a) / (x - a) := by
    field_simp [hne]
    <;> ring
  rw [dist_eq_norm, hquot, norm_div, div_lt_iff₀ hnorm]
  nlinarith

theorem gap1 (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => x - a) (nhds a) (nhds 0) := by
  have h :
      Filter.Tendsto (fun x : ℝ => x - a)
        (nhds a) (nhds (a - a)) :=
    ((continuousAt_id.sub continuousAt_const) :
      ContinuousAt (fun x : ℝ => x - a) a)
  simpa only [sub_self] using h

/-- Source: `proof_gap/exercise_832/2.txt`; express change of variables as equivalence of punctured limits. -/
theorem gap2 (f : ℝ → ℝ) (a L : ℝ) :
    Filter.Tendsto (fun x => (f x - f a) / (x - a))
      (nhdsWithin a {a}ᶜ) (nhds L) ↔
    Filter.Tendsto (differenceQuotient f a)
      (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  have hforward :
      Filter.Tendsto (fun h : ℝ => a + h)
        (nhdsWithin 0 {0}ᶜ) (nhdsWithin a {a}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hadd :
          Filter.Tendsto (fun h : ℝ => a + h)
            (nhds 0) (nhds (a + 0)) :=
        ((continuousAt_const.add continuousAt_id) :
          ContinuousAt (fun h : ℝ => a + h) 0)
      simpa only [add_zero] using hadd.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with h hh
      change h ≠ 0 at hh
      change a + h ≠ a
      intro hah
      have ha : a + h = a + 0 := by simpa using hah
      exact hh (add_left_cancel ha)
  have hbackward :
      Filter.Tendsto (fun x : ℝ => x - a)
        (nhdsWithin a {a}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (gap1 a).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x ≠ a at hx
      change x - a ≠ 0
      exact sub_ne_zero.mpr hx
  constructor
  · intro h
    apply (h.comp hforward).congr'
    apply Filter.Eventually.of_forall
    intro y
    simp only [Function.comp_apply, differenceQuotient]
    rw [show a + y - a = y by ring]
  · intro h
    apply (h.comp hbackward).congr'
    apply Filter.Eventually.of_forall
    intro x
    simp only [Function.comp_apply, differenceQuotient]
    rw [show a + (x - a) = x by ring]

/-- Source: `proof_gap/exercise_832/3.txt`; replace the undefined limit value by `Tendsto`. -/
theorem gap3 (f : ℝ → ℝ) (a : ℝ) (hf : DifferentiableAt ℝ f a) :
    Filter.Tendsto (differenceQuotient f a)
      (nhdsWithin 0 {0}ᶜ) (nhds (deriv f a)) := by
  exact
    (gap2 f a (deriv f a)).mp
      (differentiableAt_punctured_slope f a hf)

/-- Source: `proof_gap/exercise_832/4.txt`; replace the undefined limit value by `Tendsto`. -/
theorem gap4 (f : ℝ → ℝ) (a : ℝ) (hf : DifferentiableAt ℝ f a) :
    Filter.Tendsto (fun x => (f x - f a) / (x - a))
      (nhdsWithin a {a}ᶜ) (nhds (deriv f a)) := by
  exact differentiableAt_punctured_slope f a hf

end

end ProofGap.Exercise832
