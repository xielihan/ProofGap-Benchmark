import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1001

open Filter

noncomputable section

def f (x : ℝ) : ℝ :=
  (Int.floor x : ℝ) * Real.sin (Real.pi * x)

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')
def IsInteger (x : ℝ) : Prop := ∃ k : ℤ, (k : ℝ) = x
def intSign (k : ℤ) : ℝ := Real.cos ((k : ℝ) * Real.pi)

def rightRaw (k : ℤ) (h : ℝ) : ℝ :=
  (Int.floor ((k : ℝ) + h) : ℝ) *
    Real.sin (Real.pi * ((k : ℝ) + h)) / h

def rightModel (k : ℤ) (h : ℝ) : ℝ :=
  (k : ℝ) * intSign k * Real.sin (Real.pi * h) / h

private theorem eventually_floor_eq_of_not_integer (x : ℝ)
    (hx : ¬ IsInteger x) :
    ∀ᶠ y in nhds x, Int.floor y = Int.floor x := by
  have hne : (Int.floor x : ℝ) ≠ x := by
    intro heq
    exact hx ⟨Int.floor x, heq⟩
  have hlo : (Int.floor x : ℝ) < x :=
    lt_of_le_of_ne (Int.floor_le x) hne
  have hhi : x < (Int.floor x : ℝ) + 1 :=
    Int.lt_floor_add_one x
  filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
  exact Int.floor_eq_iff.mpr ⟨le_of_lt hy.1, hy.2⟩

private theorem hasLeftDerivAt_of_hasDerivAt {g : ℝ → ℝ} {g' a : ℝ}
    (hg : HasDerivAt g g' a) : HasLeftDerivAt g g' a := by
  unfold HasLeftDerivAt
  have ht :
      Tendsto (dq g a) (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds g') := by
    simpa [dq, div_eq_mul_inv, mul_comm, add_comm] using hg.tendsto_slope_zero
  apply ht.mono_left
  apply nhdsWithin_mono
  intro h hh
  simp only [Set.mem_Iio] at hh
  simpa using (ne_of_lt hh)

private theorem hasRightDerivAt_of_hasDerivAt {g : ℝ → ℝ} {g' a : ℝ}
    (hg : HasDerivAt g g' a) : HasRightDerivAt g g' a := by
  unfold HasRightDerivAt
  have ht :
      Tendsto (dq g a) (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds g') := by
    simpa [dq, div_eq_mul_inv, mul_comm, add_comm] using hg.tendsto_slope_zero
  apply ht.mono_left
  apply nhdsWithin_mono
  intro h hh
  simp only [Set.mem_Ioi] at hh
  simpa using (ne_of_gt hh)

private theorem hasDerivAt_sin_pi (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (Real.pi * y))
      (Real.pi * Real.cos (Real.pi * x)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    convert (hasDerivAt_id x).const_mul Real.pi using 1 <;> ring
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (Real.pi * x)).comp x hinner

private theorem sin_pi_int_add (k : ℤ) (h : ℝ) :
    Real.sin (Real.pi * ((k : ℝ) + h)) =
      intSign k * Real.sin (Real.pi * h) := by
  rw [show Real.pi * ((k : ℝ) + h) =
      (k : ℝ) * Real.pi + Real.pi * h by ring, Real.sin_add]
  simp [intSign]

private theorem tendsto_sin_pi_div_right :
    Tendsto (fun h : ℝ => Real.sin (Real.pi * h) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
  have ht :
      HasRightDerivAt (fun h : ℝ => Real.sin (Real.pi * h)) Real.pi 0 := by
    simpa using hasRightDerivAt_of_hasDerivAt (hasDerivAt_sin_pi 0)
  have heq :
      dq (fun h : ℝ => Real.sin (Real.pi * h)) 0 =
        fun h : ℝ => Real.sin (Real.pi * h) / h := by
    funext h
    simp [dq]
  unfold HasRightDerivAt at ht
  rw [heq] at ht
  exact ht

private theorem tendsto_sin_pi_div_left :
    Tendsto (fun h : ℝ => Real.sin (Real.pi * h) / h)
      (nhdsWithin 0 (Set.Iio 0)) (nhds Real.pi) := by
  have ht :
      HasLeftDerivAt (fun h : ℝ => Real.sin (Real.pi * h)) Real.pi 0 := by
    simpa using hasLeftDerivAt_of_hasDerivAt (hasDerivAt_sin_pi 0)
  have heq :
      dq (fun h : ℝ => Real.sin (Real.pi * h)) 0 =
        fun h : ℝ => Real.sin (Real.pi * h) / h := by
    funext h
    simp [dq]
  unfold HasLeftDerivAt at ht
  rw [heq] at ht
  exact ht

theorem gap1 (x : ℝ) (hx : ¬ IsInteger x) :
    HasLeftDerivAt f
        (Real.pi * (Int.floor x : ℝ) * Real.cos (Real.pi * x)) x ∧
      HasRightDerivAt f
        (Real.pi * (Int.floor x : ℝ) * Real.cos (Real.pi * x)) x := by
  have hg :
      HasDerivAt
        (fun y : ℝ => (Int.floor x : ℝ) * Real.sin (Real.pi * y))
        (Real.pi * (Int.floor x : ℝ) * Real.cos (Real.pi * x)) x := by
    convert (hasDerivAt_sin_pi x).const_mul (Int.floor x : ℝ) using 1 <;> ring
  constructor
  · have hzero :
        Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
      exact tendsto_id.mono_right inf_le_left
    have hshift :
        Tendsto (fun h : ℝ => x + h) (nhdsWithin 0 (Set.Iio 0)) (nhds x) := by
      simpa using tendsto_const_nhds.add hzero
    have hlocal :
        ∀ᶠ h in nhdsWithin 0 (Set.Iio 0),
          Int.floor (x + h) = Int.floor x :=
      hshift.eventually (eventually_floor_eq_of_not_integer x hx)
    have heq :
        dq (fun y : ℝ => (Int.floor x : ℝ) * Real.sin (Real.pi * y)) x
          =ᶠ[nhdsWithin 0 (Set.Iio 0)] dq f x := by
      filter_upwards [hlocal] with h hh
      simp only [dq, f]
      rw [hh]
    have ht := hasLeftDerivAt_of_hasDerivAt hg
    unfold HasLeftDerivAt at ht ⊢
    exact ht.congr' heq
  · have hzero :
        Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      exact tendsto_id.mono_right inf_le_left
    have hshift :
        Tendsto (fun h : ℝ => x + h) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      simpa using tendsto_const_nhds.add hzero
    have hlocal :
        ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0),
          Int.floor (x + h) = Int.floor x :=
      hshift.eventually (eventually_floor_eq_of_not_integer x hx)
    have heq :
        dq (fun y : ℝ => (Int.floor x : ℝ) * Real.sin (Real.pi * y)) x
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)] dq f x := by
      filter_upwards [hlocal] with h hh
      simp only [dq, f]
      rw [hh]
    have ht := hasRightDerivAt_of_hasDerivAt hg
    unfold HasRightDerivAt at ht ⊢
    exact ht.congr' heq

theorem gap2 (x : ℝ) (hx : ¬ IsInteger x) :
    HasRightDerivAt f
      (Real.pi * (Int.floor x : ℝ) * Real.cos (Real.pi * x)) x := by
  exact (gap1 x hx).2

theorem gap3 (x : ℝ) (hx : ¬ IsInteger x) :
    HasLeftDerivAt f
      (Real.pi * (Int.floor x : ℝ) * Real.cos (Real.pi * x)) x := by
  exact (gap1 x hx).1

theorem gap4 (k : ℤ) (L : ℝ) :
    Tendsto (dq f (k : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (rightRaw k) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hkzero : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    simpa using (sin_pi_int_add k 0)
  have hfun : dq f (k : ℝ) = rightRaw k := by
    funext h
    simp [dq, rightRaw, f, hkzero]
  rw [hfun]

theorem gap5 (k : ℤ) (L : ℝ) :
    Tendsto (rightRaw k) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (rightModel k) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      rightRaw k =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rightModel k := by
    filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (show (0 : ℝ) < 1 by linarith))] with h hh hlt
    simp only [Set.mem_Ioi] at hh
    simp only [Set.mem_Iio] at hlt
    have hfloor : Int.floor ((k : ℝ) + h) = k := by
      apply Int.floor_eq_iff.mpr
      constructor
      · linarith
      · linarith
    rw [rightRaw, rightModel, hfloor, sin_pi_int_add]
    ring
  exact tendsto_congr' heq

theorem gap6 (k : ℤ) :
    Tendsto (rightModel k) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((k : ℝ) * Real.pi * intSign k)) := by
  have hc :
      Tendsto (fun _ : ℝ => (k : ℝ) * intSign k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((k : ℝ) * intSign k)) :=
    tendsto_const_nhds
  have ht :
      Tendsto
        (fun h : ℝ => ((k : ℝ) * intSign k) *
          (Real.sin (Real.pi * h) / h))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((k : ℝ) * intSign k) * Real.pi)) :=
    hc.mul tendsto_sin_pi_div_right
  have hmodel :
      rightModel k = fun h : ℝ => ((k : ℝ) * intSign k) *
        (Real.sin (Real.pi * h) / h) := by
    funext h
    unfold rightModel
    ring
  rw [hmodel]
  convert ht using 1 <;> ring

theorem gap7 (k : ℤ) :
    HasRightDerivAt f ((k : ℝ) * Real.pi * intSign k) (k : ℝ) := by
  exact (gap4 k _).2 ((gap5 k _).2 (gap6 k))

theorem gap8 (k : ℤ) :
    HasLeftDerivAt f (((k : ℝ) - 1) * Real.pi * intSign k) (k : ℝ) := by
  unfold HasLeftDerivAt
  have hc :
      Tendsto (fun _ : ℝ => ((k : ℝ) - 1) * intSign k)
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (((k : ℝ) - 1) * intSign k)) :=
    tendsto_const_nhds
  have ht0 :
      Tendsto
        (fun h : ℝ => (((k : ℝ) - 1) * intSign k) *
          (Real.sin (Real.pi * h) / h))
        (nhdsWithin 0 (Set.Iio 0))
        (nhds ((((k : ℝ) - 1) * intSign k) * Real.pi)) :=
    hc.mul tendsto_sin_pi_div_left
  have ht :
      Tendsto
        (fun h : ℝ => (((k : ℝ) - 1) * intSign k) *
          (Real.sin (Real.pi * h) / h))
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (((k : ℝ) - 1) * Real.pi * intSign k)) := by
    convert ht0 using 1 <;> ring
  refine ht.congr' ?_
  filter_upwards
    [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Ioi_mem_nhds (show (-1 : ℝ) < 0 by linarith))] with h hh hlow
  simp only [Set.mem_Iio] at hh
  simp only [Set.mem_Ioi] at hlow
  have hfloor : Int.floor ((k : ℝ) + h) = k - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · simp only [Int.cast_sub, Int.cast_one]
      linarith
    · simp only [Int.cast_sub, Int.cast_one]
      linarith
  have hkzero : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    simpa using (sin_pi_int_add k 0)
  have hfk : f (k : ℝ) = 0 := by
    simp [f, hkzero]
  simp only [dq]
  rw [hfk, sub_zero, f, hfloor, sin_pi_int_add]
  simp only [Int.cast_sub, Int.cast_one]
  ring

end

end ProofGap.Exercise1001
