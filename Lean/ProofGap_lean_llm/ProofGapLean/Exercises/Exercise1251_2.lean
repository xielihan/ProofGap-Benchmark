import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1251_2

noncomputable section

def pow (x p : ℝ) : ℝ := Real.rpow x p

theorem gap1 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    ∃ ξ ∈ Set.Ioo y x,
      pow x p - pow y p = p * (x - y) * pow ξ (p - 1) := by
  have hrpow_deriv (z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun t : ℝ => Real.rpow t p)
        (p * Real.rpow z (p - 1)) z := by
    simpa only using
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt hz)))
  have hcont :
      ContinuousOn (fun t : ℝ => Real.rpow t p) (Set.Icc y x) := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hy hz.1
    exact (hrpow_deriv z hzpos).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope
      (fun t : ℝ => Real.rpow t p)
      (fun z : ℝ => p * Real.rpow z (p - 1))
      hyx hcont
      (fun z hz => hrpow_deriv z (lt_trans hy hz.1))
  refine ⟨ξ, hξ, ?_⟩
  have heq :
      p * Real.rpow ξ (p - 1) =
        (Real.rpow x p - Real.rpow y p) / (x - y) := by
    simpa only using hslope
  have hxy : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hyx)
  have hmul :
      p * Real.rpow ξ (p - 1) * (x - y) =
        Real.rpow x p - Real.rpow y p :=
    (eq_div_iff hxy).mp heq
  unfold pow
  calc
    Real.rpow x p - Real.rpow y p =
        p * Real.rpow ξ (p - 1) * (x - y) := hmul.symm
    _ = p * (x - y) * Real.rpow ξ (p - 1) := by ring

theorem gap2 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    0 < y := by
  exact hy

theorem gap3 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    ∃ ξ, y < ξ := by
  refine ⟨(x + y) / 2, ?_⟩
  linarith

theorem gap4 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    ∃ ξ, ξ < x := by
  refine ⟨(x + y) / 2, ?_⟩
  linarith

theorem gap5 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    0 < x := by
  linarith

theorem gap6 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    ∃ ξ ∈ Set.Ioo y x, pow y (p - 1) < pow ξ (p - 1) := by
  let ξ : ℝ := (x + y) / 2
  have hyξ : y < ξ := by
    dsimp [ξ]
    linarith
  have hξx : ξ < x := by
    dsimp [ξ]
    linarith
  refine ⟨ξ, ⟨hyξ, hξx⟩, ?_⟩
  unfold pow
  exact Real.rpow_lt_rpow (le_of_lt hy) hyξ (sub_pos.mpr hp)

theorem gap7 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    ∃ ξ ∈ Set.Ioo y x, pow ξ (p - 1) < pow x (p - 1) := by
  let ξ : ℝ := (x + y) / 2
  have hyξ : y < ξ := by
    dsimp [ξ]
    linarith
  have hξx : ξ < x := by
    dsimp [ξ]
    linarith
  have hξpos : 0 < ξ := lt_trans hy hyξ
  refine ⟨ξ, ⟨hyξ, hξx⟩, ?_⟩
  unfold pow
  exact Real.rpow_lt_rpow (le_of_lt hξpos) hξx (sub_pos.mpr hp)

theorem gap8 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    pow y (p - 1) < pow x (p - 1) := by
  unfold pow
  exact Real.rpow_lt_rpow (le_of_lt hy) hyx (sub_pos.mpr hp)

theorem gap9 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    p * pow y (p - 1) * (x - y) < pow x p - pow y p := by
  obtain ⟨ξ, hξ, heq⟩ := gap1 x y p hy hyx hp
  have hpow : pow y (p - 1) < pow ξ (p - 1) := by
    unfold pow
    exact Real.rpow_lt_rpow (le_of_lt hy) hξ.1 (sub_pos.mpr hp)
  have hfactor : 0 < p * (x - y) :=
    mul_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hyx)
  calc
    p * pow y (p - 1) * (x - y) =
        (p * (x - y)) * pow y (p - 1) := by ring
    _ < (p * (x - y)) * pow ξ (p - 1) :=
      mul_lt_mul_of_pos_left hpow hfactor
    _ = pow x p - pow y p := by
      simpa [mul_assoc] using heq.symm

theorem gap10 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    pow x p - pow y p < p * pow x (p - 1) * (x - y) := by
  obtain ⟨ξ, hξ, heq⟩ := gap1 x y p hy hyx hp
  have hξpos : 0 < ξ := lt_trans hy hξ.1
  have hpow : pow ξ (p - 1) < pow x (p - 1) := by
    unfold pow
    exact Real.rpow_lt_rpow (le_of_lt hξpos) hξ.2 (sub_pos.mpr hp)
  have hfactor : 0 < p * (x - y) :=
    mul_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hyx)
  calc
    pow x p - pow y p =
        (p * (x - y)) * pow ξ (p - 1) := by
      simpa [mul_assoc] using heq
    _ < (p * (x - y)) * pow x (p - 1) :=
      mul_lt_mul_of_pos_left hpow hfactor
    _ = p * pow x (p - 1) * (x - y) := by ring

theorem gap11 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    p * pow y (p - 1) * (x - y) <
      p * pow x (p - 1) * (x - y) := by
  have hpow := gap8 x y p hy hyx hp
  have hfactor : 0 < p * (x - y) :=
    mul_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hyx)
  calc
    p * pow y (p - 1) * (x - y) =
        (p * (x - y)) * pow y (p - 1) := by ring
    _ < (p * (x - y)) * pow x (p - 1) :=
      mul_lt_mul_of_pos_left hpow hfactor
    _ = p * pow x (p - 1) * (x - y) := by ring

theorem gap12 (x y p : ℝ) (hy : 0 < y) (hyx : y < x) (hp : 1 < p) :
    p * pow y (p - 1) * (x - y) < pow x p - pow y p ∧
      pow x p - pow y p < p * pow x (p - 1) * (x - y) := by
  exact ⟨gap9 x y p hy hyx hp, gap10 x y p hy hyx hp⟩

end

end ProofGap.Exercise1251_2
