import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1010

open Filter

noncomputable section

def f (a b x₀ x : ℝ) : ℝ :=
  if x ≤ x₀ then x ^ 2 else a * x + b

def dq (g : ℝ → ℝ) (x₀ h : ℝ) : ℝ := (g (x₀ + h) - g x₀) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' x₀ : ℝ) : Prop :=
  Tendsto (dq g x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' x₀ : ℝ) : Prop :=
  Tendsto (dq g x₀) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

theorem gap1 (a b x₀ : ℝ) :
    f a b x₀ x₀ = x₀ ^ 2 := by
  simp [f]

theorem gap2 (a b x₀ : ℝ) :
    Tendsto (f a b x₀) (nhdsWithin x₀ (Set.Iio x₀)) (nhds (x₀ ^ 2)) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (x₀ ^ 2)) := by
    have hsq' : Tendsto (fun x : ℝ => x ^ 2) (nhds x₀) (nhds (x₀ ^ 2)) :=
      continuousAt_id.pow 2
    exact hsq'.mono_left inf_le_left
  apply hsq.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change x < x₀ at hx
  rw [f, if_pos (le_of_lt hx)]

theorem gap3 (a b x₀ : ℝ) :
    Tendsto (f a b x₀) (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (f a b x₀ x₀)) := by
  rw [gap1]
  exact gap2 a b x₀

theorem gap4 (a b x₀ : ℝ) :
    Tendsto (f a b x₀) (nhdsWithin x₀ (Set.Ioi x₀))
      (nhds (a * x₀ + b)) := by
  have hlin : Tendsto (fun x : ℝ => a * x + b) (nhdsWithin x₀ (Set.Ioi x₀))
      (nhds (a * x₀ + b)) := by
    have hlin' : Tendsto (fun x : ℝ => a * x + b) (nhds x₀)
        (nhds (a * x₀ + b)) :=
      (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
    exact hlin'.mono_left inf_le_left
  apply hlin.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : ¬x ≤ x₀ := not_le_of_gt hx
  simp [f, hx']

theorem gap5 (a b x₀ : ℝ) (hvalue : x₀ ^ 2 = a * x₀ + b) :
    ContinuousAt (f a b x₀) x₀ := by
  show Tendsto (f a b x₀) (nhds x₀) (nhds (f a b x₀ x₀))
  rw [gap1]
  have hsq : Tendsto (fun x : ℝ => x ^ 2) (nhds x₀) (nhds (x₀ ^ 2)) :=
    continuousAt_id.pow 2
  have hlin₀ : Tendsto (fun x : ℝ => a * x + b) (nhds x₀)
      (nhds (a * x₀ + b)) :=
    (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
  have hlin : Tendsto (fun x : ℝ => a * x + b) (nhds x₀)
      (nhds (x₀ ^ 2)) := by
    simpa [hvalue] using hlin₀
  rw [tendsto_def] at hsq hlin ⊢
  intro s hs
  filter_upwards [hsq s hs, hlin s hs] with x hx_sq hx_lin
  by_cases hx : x ≤ x₀
  · simpa [f, hx] using hx_sq
  · simpa [f, hx] using hx_lin

theorem gap6 (a b x₀ : ℝ) :
    HasLeftDerivAt (f a b x₀) (2 * x₀) x₀ := by
  unfold HasLeftDerivAt
  have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hlim : Tendsto (fun h : ℝ => 2 * x₀ + h)
      (nhdsWithin 0 (Set.Iio 0)) (nhds (2 * x₀)) := by
    simpa using (tendsto_const_nhds.add hid :
      Tendsto (fun h : ℝ => 2 * x₀ + h)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (2 * x₀ + 0)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change h < 0 at hh
  have hx : x₀ + h ≤ x₀ := by linarith
  have hn : h ≠ 0 := ne_of_lt hh
  simp only [dq, f, if_pos hx, if_pos (le_refl x₀)]
  field_simp [hn]
  ring

theorem gap7 (a b x₀ : ℝ) (hvalue : x₀ ^ 2 = a * x₀ + b) :
    HasRightDerivAt (f a b x₀) a x₀ := by
  unfold HasRightDerivAt
  have hlim : Tendsto (fun _ : ℝ => a) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) :=
    tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  have hx : ¬x₀ + h ≤ x₀ := by linarith
  have hn : h ≠ 0 := ne_of_gt hh
  simp only [dq, f, if_neg hx, if_pos (le_refl x₀)]
  rw [hvalue]
  field_simp [hn]
  ring

theorem gap8 (a b x₀ : ℝ) (hvalue : x₀ ^ 2 = a * x₀ + b)
    (ha : a = 2 * x₀) :
    DifferentiableAt ℝ (f a b x₀) x₀ := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x₀) x₀ := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id x₀).mul (hasDerivAt_id x₀))
  have hlinA : HasDerivAt (fun x : ℝ => a * x + b) a x₀ := by
    simpa only [Pi.mul_apply, Pi.add_apply, id_eq, zero_mul, zero_add,
      mul_one, one_mul, add_zero, mul_zero] using
      (((hasDerivAt_const x₀ a).mul (hasDerivAt_id x₀)).add
        (hasDerivAt_const x₀ b))
  have hlin : HasDerivAt (fun x : ℝ => a * x + b) (2 * x₀) x₀ := by
    rw [← ha]
    exact hlinA
  have hderiv : HasDerivAt (f a b x₀) (2 * x₀) x₀ := by
    rw [hasDerivAt_iff_tendsto_slope] at hsq hlin ⊢
    rw [tendsto_def] at hsq hlin ⊢
    intro s hs
    filter_upwards [hsq s hs, hlin s hs] with x hx_sq hx_lin
    by_cases hx : x ≤ x₀
    · simpa [slope, f, hx] using hx_sq
    · simpa [slope, f, hx, hvalue] using hx_lin
  exact hderiv.differentiableAt

theorem gap9 (a b x₀ : ℝ) (ha : a = 2 * x₀)
    (hcont : x₀ ^ 2 = a * x₀ + b) :
    x₀ ^ 2 = 2 * x₀ ^ 2 + b := by
  simpa [ha, pow_two, mul_assoc] using hcont

theorem gap10 (b x₀ : ℝ) (h : x₀ ^ 2 = 2 * x₀ ^ 2 + b) :
    b = -(x₀ ^ 2) := by
  linarith

theorem gap11 (a b x₀ : ℝ)
    (hab : (a, b) ∈ ({(2 * x₀, -(x₀ ^ 2))} : Set (ℝ × ℝ))) :
    ContinuousAt (f a b x₀) x₀ ∧
      DifferentiableAt ℝ (f a b x₀) x₀ := by
  have hab' : (a, b) = (2 * x₀, -(x₀ ^ 2)) :=
    Set.mem_singleton_iff.mp hab
  have ha : a = 2 * x₀ := by
    simpa using congrArg Prod.fst hab'
  have hb : b = -(x₀ ^ 2) := by
    simpa using congrArg Prod.snd hab'
  subst a
  subst b
  have hvalue : x₀ ^ 2 = (2 * x₀) * x₀ + -(x₀ ^ 2) := by
    ring
  constructor
  · exact gap5 (2 * x₀) (-(x₀ ^ 2)) x₀ hvalue
  · exact gap8 (2 * x₀) (-(x₀ ^ 2)) x₀ hvalue rfl

end

end ProofGap.Exercise1010
