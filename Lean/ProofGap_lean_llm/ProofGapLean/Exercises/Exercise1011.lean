import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRight

namespace ProofGap.Exercise1011

open Filter

noncomputable section

def F (f : ℝ → ℝ) (a b x₀ x : ℝ) : ℝ :=
  if x ≤ x₀ then f x else a * x + b

def dq (g : ℝ → ℝ) (x₀ h : ℝ) : ℝ := (g (x₀ + h) - g x₀) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' x₀ : ℝ) : Prop :=
  Tendsto (dq g x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' x₀ : ℝ) : Prop :=
  Tendsto (dq g x₀) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

theorem gap1 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀) :
    Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (F f a b x₀ x₀)) := by
  unfold HasLeftDerivAt at hf
  have hzero :
      Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hdiff :
      Tendsto (fun h : ℝ => f (x₀ + h) - f x₀)
        (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    have hprod :
        Tendsto (fun h : ℝ => h * dq f x₀ h)
          (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
      simpa using hzero.mul hf
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    change h < 0 at hh
    have hh0 : h ≠ 0 := ne_of_lt hh
    simp only [dq]
    field_simp [hh0]
  have hfshift :
      Tendsto (fun h : ℝ => f (x₀ + h))
        (nhdsWithin 0 (Set.Iio 0)) (nhds (f x₀)) := by
    have hconst :
        Tendsto (fun _ : ℝ => f x₀) (nhdsWithin 0 (Set.Iio 0))
          (nhds (f x₀)) :=
      tendsto_const_nhds
    have hadd :
        Tendsto (fun h : ℝ => f x₀ + (f (x₀ + h) - f x₀))
          (nhdsWithin 0 (Set.Iio 0)) (nhds (f x₀)) := by
      simpa using hconst.add hdiff
    apply hadd.congr'
    exact Filter.Eventually.of_forall (fun h => by ring)
  have hsub :
      Tendsto (fun z : ℝ => z - x₀)
        (nhdsWithin x₀ (Set.Iio x₀)) (nhdsWithin 0 (Set.Iio 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hconst :
          Tendsto (fun _ : ℝ => x₀) (nhds x₀) (nhds x₀) :=
        tendsto_const_nhds
      simpa using (tendsto_id.sub hconst).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z < x₀ at hz
      exact sub_neg.mpr hz
  have hleft :
      Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) := by
    simpa [Function.comp_def] using hfshift.comp hsub
  have hF :
      Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Iio x₀))
        (nhds (f x₀)) := by
    apply hleft.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z < x₀ at hz
    simp [F, le_of_lt hz]
  simpa [F] using hF

theorem gap2 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀) :
    Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (f x₀)) := by
  simpa [F] using gap1 f a b x₀ m hf

theorem gap3 (f : ℝ → ℝ) (a b x₀ : ℝ) :
    F f a b x₀ x₀ = f x₀ := by
  simp [F]

theorem gap4 (f : ℝ → ℝ) (a b x₀ : ℝ) :
    Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Ioi x₀))
      (nhds (a * x₀ + b)) := by
  have hlin :
      Tendsto (fun x : ℝ => a * x + b) (nhdsWithin x₀ (Set.Ioi x₀))
        (nhds (a * x₀ + b)) := by
    exact
      ((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds).mono_left
        inf_le_left
  apply hlin.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change x₀ < z at hz
  simp [F, not_le_of_gt hz]

theorem gap5 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀) (hvalue : f x₀ = a * x₀ + b) :
    ContinuousAt (F f a b x₀) x₀ := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · show
      Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Iio x₀))
        (nhds (F f a b x₀ x₀))
    exact gap1 f a b x₀ m hf
  · show
      Tendsto (F f a b x₀) (nhdsWithin x₀ (Set.Ioi x₀))
        (nhds (F f a b x₀ x₀))
    rw [gap3, hvalue]
    exact gap4 f a b x₀

theorem gap6 (f : ℝ → ℝ) (a b x₀ m L : ℝ)
    (hf : HasLeftDerivAt f m x₀) :
    Tendsto (dq (F f a b x₀) x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds L) ↔
      Tendsto (dq f x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  have heq :
      dq (F f a b x₀) x₀ =ᶠ[nhdsWithin 0 (Set.Iio 0)] dq f x₀ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change h < 0 at hh
    have hx : x₀ + h ≤ x₀ := le_of_lt (by linarith)
    simp [dq, F, hx]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap7 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hvalue : f x₀ = a * x₀ + b) :
    HasRightDerivAt (F f a b x₀) a x₀ := by
  unfold HasRightDerivAt
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  have hx : ¬x₀ + h ≤ x₀ := not_le_of_gt (by linarith)
  have hh0 : h ≠ 0 := ne_of_gt hh
  simp only [dq, F, if_neg hx, if_pos (le_refl x₀)]
  rw [hvalue]
  field_simp [hh0]
  ring

theorem gap8 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀) (hvalue : f x₀ = a * x₀ + b)
    (ha : a = m) :
    DifferentiableAt ℝ (F f a b x₀) x₀ := by
  have hleft :
      Tendsto (dq (F f a b x₀) x₀) (nhdsWithin 0 (Set.Iio 0))
        (nhds m) :=
    (gap6 f a b x₀ m m hf).mpr hf
  have hright :
      Tendsto (dq (F f a b x₀) x₀) (nhdsWithin 0 (Set.Ioi 0))
        (nhds m) := by
    simpa [ha] using gap7 f a b x₀ hvalue
  have hpunc :
      Tendsto (dq (F f a b x₀) x₀) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds m) := by
    rw [← Set.Iio_union_Ioi, nhdsWithin_union]
    exact hleft.sup hright
  have hd : HasDerivAt (F f a b x₀) m x₀ := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    apply hpunc.congr'
    exact Filter.Eventually.of_forall (fun t => by
      simp only [dq, div_eq_mul_inv, smul_eq_mul]
      ring)
  exact hd.differentiableAt

theorem gap9 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀) :
    (a, b) ∈ ({(m, f x₀ - x₀ * m)} : Set (ℝ × ℝ)) ↔
      a = m ∧ f x₀ = a * x₀ + b := by
  constructor
  · intro hab
    have hab' : (a, b) = (m, f x₀ - x₀ * m) :=
      Set.mem_singleton_iff.mp hab
    constructor
    · exact congrArg Prod.fst hab'
    · have hb : b = f x₀ - x₀ * m := congrArg Prod.snd hab'
      have ha : a = m := congrArg Prod.fst hab'
      rw [ha, hb]
      ring
  · rintro ⟨ha, hvalue⟩
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · exact ha
    · rw [ha] at hvalue
      linarith

theorem gap10 (f : ℝ → ℝ) (a b x₀ m : ℝ)
    (hf : HasLeftDerivAt f m x₀)
    (hab : (a, b) ∈ ({(m, f x₀ - x₀ * m)} : Set (ℝ × ℝ))) :
    ContinuousAt (F f a b x₀) x₀ ∧
      DifferentiableAt ℝ (F f a b x₀) x₀ := by
  have hconditions := (gap9 f a b x₀ m hf).mp hab
  constructor
  · exact gap5 f a b x₀ m hf hconditions.2
  · exact gap8 f a b x₀ m hf hconditions.2 hconditions.1

end

end ProofGap.Exercise1011
