import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1450

noncomputable section

def f (x : ℝ) : ℝ := x * Real.exp (-(1 / 100) * x)
def domain : Set ℝ := Set.Ioi 0
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

theorem gap1 (x : ℝ) (hx : x ∈ domain) : 0 < f x := by
  have hx' : 0 < x := by
    simpa [domain] using hx
  unfold f
  exact mul_pos hx' (Real.exp_pos _)

theorem gap2 :
    Filter.Tendsto f (nhdsWithin 0 domain) (nhds 0) := by
  have harg : Continuous (fun x : ℝ => -(1 / 100) * x) :=
    continuous_const.mul continuous_id
  have hf : Continuous f := by
    unfold f
    exact continuous_id.mul (Real.continuous_exp.comp harg)
  have hglobal : Filter.Tendsto f (nhds 0) (nhds (f 0)) :=
    hf.continuousAt
  simpa [f] using
    hglobal.mono_left
      (show nhdsWithin 0 domain ≤ nhds 0 from inf_le_left)

theorem gap3 : sInf (f '' domain) = 0 := by
  have hnonempty : (f '' domain).Nonempty := by
    refine ⟨f 1, 1, ?_, rfl⟩
    norm_num [domain]
  have hbdd : BddBelow (f '' domain) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact le_of_lt (gap1 x hx)
  have hlow : 0 ≤ sInf (f '' domain) := by
    apply le_csInf hnonempty
    rintro y ⟨x, hx, rfl⟩
    exact le_of_lt (gap1 x hx)
  apply le_antisymm
  · by_contra h
    have hspos : 0 < sInf (f '' domain) := lt_of_not_ge h
    let x : ℝ := sInf (f '' domain) / 2
    have hxpos : 0 < x := by
      dsimp [x]
      linarith
    have hxdom : x ∈ domain := by
      simpa [domain] using hxpos
    have hinf : sInf (f '' domain) ≤ f x :=
      csInf_le hbdd ⟨x, hxdom, rfl⟩
    have harg : -(1 / 100 : ℝ) * x < 0 :=
      mul_neg_of_neg_of_pos (by norm_num) hxpos
    have hexp : Real.exp (-(1 / 100 : ℝ) * x) < 1 := by
      calc
        Real.exp (-(1 / 100 : ℝ) * x) < Real.exp 0 :=
          Real.exp_lt_exp.mpr harg
        _ = 1 := Real.exp_zero
    have hfx : f x < x := by
      have hmul := mul_lt_mul_of_pos_left hexp hxpos
      simpa [f] using hmul
    have hxhalf : x = sInf (f '' domain) / 2 := rfl
    linarith
  · exact hlow

theorem gap4 : IsMaxOn f domain 100 := by
  intro x hx
  have hexp : x / 100 ≤ Real.exp (x / 100 - 1) := by
    linarith [Real.add_one_le_exp (x / 100 - 1)]
  have hscale : 0 ≤ 100 * Real.exp (-(x / 100)) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
  have hneg : -(1 / 100 : ℝ) * x = -(x / 100) := by
    ring
  calc
    f x = (x / 100) * (100 * Real.exp (-(x / 100))) := by
      rw [f, hneg]
      ring
    _ ≤ Real.exp (x / 100 - 1) *
        (100 * Real.exp (-(x / 100))) :=
      mul_le_mul_of_nonneg_right hexp hscale
    _ = 100 * (Real.exp (x / 100 - 1) *
        Real.exp (-(x / 100))) := by ring
    _ = 100 * Real.exp ((x / 100 - 1) + (-(x / 100))) := by
      rw [Real.exp_add]
    _ = 100 * Real.exp (-1) := by
      rw [show (x / 100 - 1) + (-(x / 100)) = (-1 : ℝ) by ring]
    _ = f 100 := by
      norm_num [f]

theorem gap5 : f 100 = 100 / Real.exp 1 := by
  norm_num [f, Real.exp_neg, div_eq_mul_inv]

theorem gap6 : Approx (100 / Real.exp 1) 36.8 0.1 := by
  have hbase_lower :
      ((257 : ℝ) / 256) ≤ Real.exp ((1 : ℝ) / 256) := by
    nlinarith [Real.add_one_le_exp ((1 : ℝ) / 256)]
  have hnegbase :
      ((255 : ℝ) / 256) ≤ Real.exp (-((1 : ℝ) / 256)) := by
    nlinarith [Real.add_one_le_exp (-((1 : ℝ) / 256))]
  have hprod :
      ((255 : ℝ) / 256) * Real.exp ((1 : ℝ) / 256) ≤ 1 := by
    calc
      ((255 : ℝ) / 256) * Real.exp ((1 : ℝ) / 256) ≤
          Real.exp (-((1 : ℝ) / 256)) * Real.exp ((1 : ℝ) / 256) :=
        mul_le_mul_of_nonneg_right hnegbase
          (le_of_lt (Real.exp_pos _))
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hbase_upper :
      Real.exp ((1 : ℝ) / 256) ≤ (256 : ℝ) / 255 := by
    nlinarith [hprod]
  have hexp_pow :
      (Real.exp ((1 : ℝ) / 256)) ^ (256 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow_lower :
      ((257 : ℝ) / 256) ^ (256 : ℕ) ≤
        (Real.exp ((1 : ℝ) / 256)) ^ (256 : ℕ) := by
    exact pow_le_pow_left₀ (by norm_num) hbase_lower (256 : ℕ)
  have hpow_upper :
      (Real.exp ((1 : ℝ) / 256)) ^ (256 : ℕ) ≤
        ((256 : ℝ) / 255) ^ (256 : ℕ) := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hbase_upper (256 : ℕ)
  have he_lower : (1000 : ℝ) / 369 < Real.exp 1 := by
    calc
      (1000 : ℝ) / 369 < ((257 : ℝ) / 256) ^ (256 : ℕ) := by
        norm_num
      _ ≤ (Real.exp ((1 : ℝ) / 256)) ^ (256 : ℕ) := hpow_lower
      _ = Real.exp 1 := hexp_pow
  have he_upper : Real.exp 1 < (1000 : ℝ) / 367 := by
    calc
      Real.exp 1 = (Real.exp ((1 : ℝ) / 256)) ^ (256 : ℕ) :=
        hexp_pow.symm
      _ ≤ ((256 : ℝ) / 255) ^ (256 : ℕ) := hpow_upper
      _ < (1000 : ℝ) / 367 := by
        norm_num
  have hl : (367 : ℝ) / 10 < 100 / Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).2
    nlinarith [he_upper]
  have hu : 100 / Real.exp 1 < (369 : ℝ) / 10 := by
    apply (div_lt_iff₀ (Real.exp_pos 1)).2
    nlinarith [he_lower]
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith

theorem gap7 : Approx (f 100) 36.8 0.1 := by
  rw [gap5]
  exact gap6

theorem gap8 : sSup (f '' domain) = 100 / Real.exp 1 := by
  rw [← gap5]
  have h100 : 100 ∈ domain := by
    norm_num [domain]
  have hmem : f 100 ∈ f '' domain := ⟨100, h100, rfl⟩
  have hnonempty : (f '' domain).Nonempty := ⟨f 100, hmem⟩
  have hbdd : BddAbove (f '' domain) := by
    refine ⟨f 100, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact gap4 hx
  apply le_antisymm
  · apply csSup_le hnonempty
    rintro y ⟨x, hx, rfl⟩
    exact gap4 hx
  · exact le_csSup hbdd hmem

end
end ProofGap.Exercise1450
