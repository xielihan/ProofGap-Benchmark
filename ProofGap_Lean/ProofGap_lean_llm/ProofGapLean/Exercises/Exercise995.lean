import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise995

open Filter

noncomputable section

def f (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  |x - a| * φ x

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (g (a + h) - g a) / h

def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')

def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

theorem gap1 (a h : ℝ) (φ : ℝ → ℝ) (hh : h ≠ 0) :
    dq (f a φ) a h = |h| / h * φ (a + h) := by
  simp only [dq, f, add_sub_cancel_left, sub_self, abs_zero, zero_mul, sub_zero]
  exact (div_mul_eq_mul_div _ _ _).symm

theorem gap2 (a h : ℝ) (φ : ℝ → ℝ) (hh : h ≠ 0) :
    dq (f a φ) a h =
      if 0 < h then φ (a + h) else -φ (a + h) := by
  rw [gap1 a h φ hh]
  by_cases hp : 0 < h
  · simp [hp, abs_of_pos hp, hh]
  · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hh
    simp [hp, abs_of_neg hn, hh]

theorem gap3 (a h : ℝ) (φ : ℝ → ℝ) (hh : h < 0) :
    dq (f a φ) a h = -φ (a + h) := by
  rw [gap2 a h φ (ne_of_lt hh)]
  simp [not_lt_of_ge (le_of_lt hh)]

theorem gap4 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (fun h => -φ (a + h))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-φ a)) := by
  have ha0 :
      Tendsto (fun h : ℝ => a + h) (nhds 0) (nhds a) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => a) (nhds (0 : ℝ)) (nhds a)).add
        (tendsto_id :
          Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)))
  have ha :
      Tendsto (fun h : ℝ => a + h)
        (nhdsWithin 0 (Set.Iio 0)) (nhds a) :=
    ha0.mono_left inf_le_left
  exact (hφ.tendsto.comp ha).neg

theorem gap5 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (dq (f a φ) a)
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-φ a)) := by
  refine (gap4 a φ hφ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (gap3 a h φ hh).symm

theorem gap6 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    HasLeftDerivAt (f a φ) (-φ a) a := by
  simpa [HasLeftDerivAt] using gap5 a φ hφ

theorem gap7 (a h : ℝ) (φ : ℝ → ℝ) (hh : 0 < h) :
    dq (f a φ) a h = φ (a + h) := by
  rw [gap2 a h φ (ne_of_gt hh)]
  simp [hh]

theorem gap8 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (fun h => φ (a + h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ a)) := by
  have ha0 :
      Tendsto (fun h : ℝ => a + h) (nhds 0) (nhds a) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => a) (nhds (0 : ℝ)) (nhds a)).add
        (tendsto_id :
          Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)))
  have ha :
      Tendsto (fun h : ℝ => a + h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a) :=
    ha0.mono_left inf_le_left
  exact hφ.tendsto.comp ha

theorem gap9 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (dq (f a φ) a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ a)) := by
  refine (gap8 a φ hφ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (gap7 a h φ hh).symm

theorem gap10 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    HasRightDerivAt (f a φ) (φ a) a := by
  simpa [HasRightDerivAt] using gap9 a φ hφ

theorem gap11 (a : ℝ) (φ : ℝ → ℝ) (hφ0 : φ a ≠ 0) :
    -φ a ≠ φ a := by
  intro heq
  apply hφ0
  linarith

theorem gap12 (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContinuousAt φ a) (hφ0 : φ a ≠ 0) :
    ¬ DifferentiableAt ℝ (f a φ) a := by
  intro hdiff
  have hd :
      HasDerivAt (f a φ) (deriv (f a φ) a) a :=
    hdiff.hasDerivAt
  have ha0 :
      Tendsto (fun h : ℝ => a + h) (nhds 0) (nhds a) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => a) (nhds (0 : ℝ)) (nhds a)).add
        (tendsto_id :
          Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)))
  have hleftMap :
      Tendsto (fun h : ℝ => a + h)
        (nhdsWithin 0 (Set.Iio 0))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact ha0.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      change h < 0 at hh
      intro heq
      apply ne_of_lt hh
      have heq' : a + h = a + 0 := by
        simpa using heq
      exact add_left_cancel heq'
  have hrightMap :
      Tendsto (fun h : ℝ => a + h)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact ha0.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      change 0 < h at hh
      intro heq
      apply ne_of_gt hh
      have heq' : a + h = a + 0 := by
        simpa using heq
      exact add_left_cancel heq'
  have hdl' :
      Tendsto (fun h : ℝ => h⁻¹ *
        ((f a φ) (a + h) - (f a φ) a))
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv (f a φ) a)) := by
    simpa [slope, Function.comp_def, div_eq_mul_inv, smul_eq_mul] using
      hd.tendsto_slope.comp hleftMap
  have hdl :
      Tendsto (dq (f a φ) a)
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv (f a φ) a)) := by
    refine hdl'.congr' ?_
    filter_upwards [] with h
    simp [dq, div_eq_mul_inv, mul_comm]
  have hdr' :
      Tendsto (fun h : ℝ => h⁻¹ *
        ((f a φ) (a + h) - (f a φ) a))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (deriv (f a φ) a)) := by
    simpa [slope, Function.comp_def, div_eq_mul_inv, smul_eq_mul] using
      hd.tendsto_slope.comp hrightMap
  have hdr :
      Tendsto (dq (f a φ) a)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (deriv (f a φ) a)) := by
    refine hdr'.congr' ?_
    filter_upwards [] with h
    simp [dq, div_eq_mul_inv, mul_comm]
  have hl : deriv (f a φ) a = -φ a :=
    tendsto_nhds_unique hdl (gap5 a φ hφ)
  have hr : deriv (f a φ) a = φ a :=
    tendsto_nhds_unique hdr (gap9 a φ hφ)
  exact (gap11 a φ hφ0) (hl.symm.trans hr)

theorem gap13 (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContinuousAt φ a) (hφ0 : φ a ≠ 0) :
    ¬ DifferentiableAt ℝ (f a φ) a ∧
      HasLeftDerivAt (f a φ) (-φ a) a ∧
      HasRightDerivAt (f a φ) (φ a) a := by
  exact ⟨gap12 a φ hφ hφ0, gap6 a φ hφ, gap10 a φ hφ⟩

end

end ProofGap.Exercise995
