import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace ProofGap.Exercise1584

noncomputable section

def intensity (S₁ S₂ a x : ℝ) := S₁ / x ^ 2 + S₂ / (a - x) ^ 2
def cubeRoot (x : ℝ) := Real.rpow x (1 / 3 : ℝ)
def optimizer (S₁ S₂ a : ℝ) := a / (1 + cubeRoot (S₂ / S₁))
def Optimal (S₁ S₂ a x : ℝ) : Prop :=
  x ∈ Set.Ioo 0 a ∧ ∀ x₁ ∈ Set.Ioo 0 a,
    intensity S₁ S₂ a x ≤ intensity S₁ S₂ a x₁

private lemma cubeRoot_pos {x : ℝ} (hx : 0 < x) : 0 < cubeRoot x := by
  unfold cubeRoot
  exact Real.rpow_pos_of_pos hx _

private lemma cubeRoot_cube {x : ℝ} (hx : 0 < x) :
    (cubeRoot x) ^ 3 = x := by
  unfold cubeRoot
  calc
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx.le _ _).symm
    _ = x := by norm_num

private lemma optimizer_mem (S₁ S₂ a : ℝ)
    (h₁ : 0 < S₁) (h₂ : 0 < S₂) (ha : 0 < a) :
    optimizer S₁ S₂ a ∈ Set.Ioo 0 a := by
  have hc : 0 < cubeRoot (S₂ / S₁) := cubeRoot_pos (by positivity)
  unfold optimizer
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 1 + cubeRoot (S₂ / S₁))).2
    nlinarith

private lemma intensity_min (S₁ S₂ a x : ℝ)
    (h₁ : 0 < S₁) (h₂ : 0 < S₂) (ha : 0 < a)
    (hx : x ∈ Set.Ioo 0 a) :
    intensity S₁ S₂ a (optimizer S₁ S₂ a) ≤ intensity S₁ S₂ a x := by
  let c := cubeRoot (S₂ / S₁)
  have hc : 0 < c := cubeRoot_pos (by positivity)
  have hc3 : c ^ 3 = S₂ / S₁ := cubeRoot_cube (by positivity)
  have hS₂ : S₂ = S₁ * c ^ 3 := by
    field_simp [h₁.ne'] at hc3
    nlinarith
  have hax : 0 < a - x := sub_pos.mpr hx.2
  have hbr : 0 < a ^ 2 + 2 * a * c * x - (c + 1) * x ^ 2 := by
    have hfirst : 0 < a ^ 2 - x ^ 2 := by
      convert mul_pos (sub_pos.mpr hx.2)
        (add_pos_of_pos_of_nonneg ha hx.1.le) using 1 <;> ring
    have hsecond : 0 < c * x * (2 * a - x) := by
      have : 0 < 2 * a - x := by linarith
      exact mul_pos (mul_pos hc hx.1) this
    nlinarith
  have hnonneg : 0 ≤ S₁ *
      (((c + 1) * x - a) ^ 2 *
        (a ^ 2 + 2 * a * c * x - (c + 1) * x ^ 2)) /
      (a ^ 2 * x ^ 2 * (a - x) ^ 2) := by positivity
  have hopt :
      intensity S₁ S₂ a (optimizer S₁ S₂ a) =
        S₁ * (1 + c) ^ 3 / a ^ 2 := by
    change S₁ / (a / (1 + c)) ^ 2 +
        S₂ / (a - a / (1 + c)) ^ 2 = S₁ * (1 + c) ^ 3 / a ^ 2
    rw [hS₂]
    field_simp [ha.ne', hc.ne']
    ring
  have hdiff :
      intensity S₁ S₂ a x - S₁ * (1 + c) ^ 3 / a ^ 2 =
        S₁ * (((c + 1) * x - a) ^ 2 *
          (a ^ 2 + 2 * a * c * x - (c + 1) * x ^ 2)) /
        (a ^ 2 * x ^ 2 * (a - x) ^ 2) := by
    unfold intensity
    rw [hS₂]
    field_simp [ha.ne', hx.1.ne', hax.ne']
    ring
  rw [hopt]
  linarith

theorem gap1 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂)
    (ha : 0 < a) (h : Optimal S₁ S₂ a x) : x = x := by rfl
theorem gap2 (S₁ S₂ a x : ℝ) (h : Optimal S₁ S₂ a x) :
    intensity S₁ S₂ a x = S₁ / x ^ 2 + S₂ / (a - x) ^ 2 := by rfl
theorem gap3 (S₁ S₂ a x : ℝ) (hx : x ≠ 0) (hax : a - x ≠ 0) :
    deriv (intensity S₁ S₂ a) x =
      -(2 * S₁ / x ^ 3) + 2 * S₂ / (a - x) ^ 3 := by
  unfold intensity
  have hfirst : HasDerivAt (fun y : ℝ => S₁ / y ^ 2) (-2 * S₁ / x ^ 3) x := by
    convert (hasDerivAt_const x (S₁ : ℝ)).div ((hasDerivAt_id x).pow 2)
      (pow_ne_zero 2 hx) using 1 <;> simp [id] <;> field_simp [hx] <;> ring
  have hinner : HasDerivAt (fun y : ℝ => a - y) (-1) x := by
    convert (hasDerivAt_const x a).sub (hasDerivAt_id x) using 1 <;> simp [id]
  have hsecond : HasDerivAt (fun y : ℝ => S₂ / (a - y) ^ 2)
      (2 * S₂ / (a - x) ^ 3) x := by
    convert (hasDerivAt_const x (S₂ : ℝ)).div (hinner.pow 2)
      (pow_ne_zero 2 hax) using 1 <;> simp [id] <;> field_simp [hax] <;> ring
  change deriv ((fun y : ℝ => S₁ / y ^ 2) + fun y => S₂ / (a - y) ^ 2) x = _
  convert (hfirst.add hsecond).deriv using 1 <;> ring
theorem gap4 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂)
    (ha : 0 < a) (h : Optimal S₁ S₂ a x) :
    -(2 * S₁ / x ^ 3) + 2 * S₂ / (a - x) ^ 3 = 0 := by
  have hmin : IsMinOn (intensity S₁ S₂ a) (Set.Ioo 0 a) x := h.2
  have hlocal : IsLocalMin (intensity S₁ S₂ a) x :=
    hmin.isLocalMin (Ioo_mem_nhds h.1.1 h.1.2)
  have hderiv := hlocal.deriv_eq_zero
  rw [gap3 S₁ S₂ a x h.1.1.ne' (sub_pos.mpr h.1.2).ne'] at hderiv
  exact hderiv
theorem gap5 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂)
    (ha : 0 < a) (h : Optimal S₁ S₂ a x) :
    deriv (intensity S₁ S₂ a) x = 0 := by
  rw [gap3 S₁ S₂ a x h.1.1.ne' (sub_pos.mpr h.1.2).ne',
    gap4 S₁ S₂ a x h₁ h₂ ha h]
theorem gap6 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂)
    (ha : 0 < a) (h : Optimal S₁ S₂ a x) :
    S₂ * x ^ 3 = S₁ * (a - x) ^ 3 := by
  have hc := gap4 S₁ S₂ a x h₁ h₂ ha h
  field_simp [h.1.1.ne', (sub_pos.mpr h.1.2).ne'] at hc
  nlinarith
theorem gap7 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂)
    (ha : 0 < a) (h : Optimal S₁ S₂ a x) :
    x = optimizer S₁ S₂ a := by
  let c := cubeRoot (S₂ / S₁)
  have hc : 0 < c := cubeRoot_pos (by positivity)
  have hc3 : c ^ 3 = S₂ / S₁ := cubeRoot_cube (by positivity)
  have hbalance := gap6 S₁ S₂ a x h₁ h₂ ha h
  have hcubes : (c * x) ^ 3 = (a - x) ^ 3 := by
    rw [mul_pow, hc3]
    field_simp [h₁.ne']
    exact hbalance
  have hlin : c * x = a - x :=
    (show Odd 3 by decide).pow_injective hcubes
  unfold optimizer
  apply (eq_div_iff (by positivity : 1 + cubeRoot (S₂ / S₁) ≠ 0)).2
  change x * (1 + c) = a
  nlinarith
theorem gap8 (S₁ S₂ a : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂) (ha : 0 < a) :
    IsMinOn (intensity S₁ S₂ a) (Set.Ioo 0 a) (optimizer S₁ S₂ a) := by
  intro x hx
  exact intensity_min S₁ S₂ a x h₁ h₂ ha hx
theorem gap9 (S₁ S₂ a x : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂) (ha : 0 < a) :
    x = optimizer S₁ S₂ a ↔ Optimal S₁ S₂ a x := by
  constructor
  · intro hx
    subst x
    exact ⟨optimizer_mem S₁ S₂ a h₁ h₂ ha,
      fun x hx => intensity_min S₁ S₂ a x h₁ h₂ ha hx⟩
  · intro h
    exact gap7 S₁ S₂ a x h₁ h₂ ha h

end
end ProofGap.Exercise1584
