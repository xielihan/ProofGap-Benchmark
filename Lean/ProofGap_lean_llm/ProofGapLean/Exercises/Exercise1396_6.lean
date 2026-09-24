import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1396_6

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def logPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (k + 1) * x ^ k / k
def remainder : ℝ := |Real.log 1.2 - logPartial 0.2 7|
def remainderBound : ℝ := (1 / 8 : ℝ) * 0.2 ^ 8

private theorem log_seventh_order_error :
    |Real.log (1 + (1 / 5 : ℝ)) -
        ((1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 2 / 2 + (1 / 5 : ℝ) ^ 3 / 3 -
          (1 / 5 : ℝ) ^ 4 / 4 + (1 / 5 : ℝ) ^ 5 / 5 -
          (1 / 5 : ℝ) ^ 6 / 6 + (1 / 5 : ℝ) ^ 7 / 7)| <
      (1 / 5 : ℝ) ^ 8 / 8 := by
  let p : ℝ → ℝ := fun x =>
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5 -
      x ^ 6 / 6 + x ^ 7 / 7
  let e : ℝ → ℝ := fun x => Real.log (1 + x) - p x
  have he (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 5 : ℝ)) :
      HasDerivAt e (-x ^ 7 / (1 + x)) x := by
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 + x)⁻¹ x := by
      simpa using
        (Real.hasDerivAt_log (by linarith [hx.1] : 1 + x ≠ 0)).comp x
          ((hasDerivAt_const x 1).add (hasDerivAt_id x))
    have h1 := hasDerivAt_id x
    have h2 := ((hasDerivAt_id x).pow 2).div_const 2
    have h3 := ((hasDerivAt_id x).pow 3).div_const 3
    have h4 := ((hasDerivAt_id x).pow 4).div_const 4
    have h5 := ((hasDerivAt_id x).pow 5).div_const 5
    have h6 := ((hasDerivAt_id x).pow 6).div_const 6
    have h7 := ((hasDerivAt_id x).pow 7).div_const 7
    have hp :
        HasDerivAt p (1 - x + x ^ 2 - x ^ 3 + x ^ 4 - x ^ 5 + x ^ 6) x := by
      dsimp [p]
      convert (((((h1.sub h2).add h3).sub h4).add h5).sub h6).add h7 using 1 <;>
        simp only [id_eq] <;> ring
    change HasDerivAt (fun y : ℝ => Real.log (1 + y) - p y)
      (-x ^ 7 / (1 + x)) x
    convert hlog.sub hp using 1
    field_simp [show 1 + x ≠ 0 by linarith [hx.1]]
    ring
  have hne (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 5 : ℝ)) :
      HasDerivAt (fun y => -e y) (x ^ 7 / (1 + x)) x := by
    convert (he x hx).neg using 1
    ring
  have hh (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 5 : ℝ)) :
      HasDerivAt (fun y => e y + y ^ 8 / 8) (x ^ 8 / (1 + x)) x := by
    convert (he x hx).add (((hasDerivAt_id x).pow 8).div_const 8) using 1
    simp only [id_eq]
    field_simp [show 1 + x ≠ 0 by linarith [hx.1]]
    ring
  have hzero : e 0 = 0 := by
    norm_num [e, p]
  have hneg : e (1 / 5 : ℝ) < 0 := by
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope
        (f := fun y : ℝ => -e y)
        (f' := fun x : ℝ => x ^ 7 / (1 + x))
        (by norm_num : (0 : ℝ) < 1 / 5)
        (by
          intro x hx
          exact (hne x hx).continuousAt.continuousWithinAt)
        (by
          intro x hx
          exact hne x ⟨hx.1.le, hx.2.le⟩)
    have hslope :
        ((-e (1 / 5 : ℝ)) - (-e 0)) / ((1 / 5 : ℝ) - 0) =
          c ^ 7 / (1 + c) :=
      hcderiv.symm
    have hcpos : 0 < c ^ 7 / (1 + c) :=
      div_pos (pow_pos hc.1 7) (by linarith [hc.1])
    have hslopepos :
        0 < ((-e (1 / 5 : ℝ)) - (-e 0)) / ((1 / 5 : ℝ) - 0) := by
      rw [hslope]
      exact hcpos
    rcases div_pos_iff.mp hslopepos with h | h
    · have hn := h.1
      rw [hzero] at hn
      linarith
    · norm_num at h
  have hpos : 0 < e (1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 8 / 8 := by
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope
        (f := fun y : ℝ => e y + y ^ 8 / 8)
        (f' := fun x : ℝ => x ^ 8 / (1 + x))
        (by norm_num : (0 : ℝ) < 1 / 5)
        (by
          intro x hx
          exact (hh x hx).continuousAt.continuousWithinAt)
        (by
          intro x hx
          exact hh x ⟨hx.1.le, hx.2.le⟩)
    have hslope :
        ((e (1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 8 / 8) -
            (e 0 + (0 : ℝ) ^ 8 / 8)) /
            ((1 / 5 : ℝ) - 0) = c ^ 8 / (1 + c) :=
      hcderiv.symm
    have hcpos : 0 < c ^ 8 / (1 + c) :=
      div_pos (pow_pos hc.1 8) (by linarith [hc.1])
    have hslopepos :
        0 <
          ((e (1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 8 / 8) -
              (e 0 + (0 : ℝ) ^ 8 / 8)) /
            ((1 / 5 : ℝ) - 0) := by
      rw [hslope]
      exact hcpos
    rcases div_pos_iff.mp hslopepos with h | h
    · simpa [hzero] using h.1
    · norm_num at h
  change |e (1 / 5 : ℝ)| < (1 / 5 : ℝ) ^ 8 / 8
  rw [abs_lt]
  constructor
  · linarith
  · have hb : 0 < (1 / 5 : ℝ) ^ 8 / 8 := by positivity
    linarith

theorem gap1 : Real.log 1.2 = Real.log (1 + 0.2) := by
  norm_num
theorem gap2 :
    Approx (Real.log (1 + 0.2)) (logPartial 0.2 7)
      (32 / 100000000 : ℝ) := by
  unfold Approx
  have hs :
      logPartial (1 / 5 : ℝ) 7 =
        (1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 2 / 2 + (1 / 5 : ℝ) ^ 3 / 3 -
          (1 / 5 : ℝ) ^ 4 / 4 + (1 / 5 : ℝ) ^ 5 / 5 -
          (1 / 5 : ℝ) ^ 6 / 6 + (1 / 5 : ℝ) ^ 7 / 7 := by
    norm_num [logPartial, Finset.sum_Icc_succ_top]
  rw [show (0.2 : ℝ) = 1 / 5 by norm_num, hs]
  convert log_seventh_order_error using 1 <;> norm_num
theorem gap3 :
    Approx (Real.log 1.2) (logPartial 0.2 7)
      (32 / 100000000 : ℝ) := by
  rw [gap1]
  exact gap2
theorem gap4 :
    Approx (Real.log 1.2) 0.182322 (5 / 10000000 : ℝ) := by
  have h := gap3
  unfold Approx at h ⊢
  calc
    |Real.log 1.2 - 0.182322| ≤
        |Real.log 1.2 - logPartial 0.2 7| +
          |logPartial 0.2 7 - 0.182322| := abs_sub_le _ _ _
    _ < (5 / 10000000 : ℝ) := by
      have hs : |logPartial 0.2 7 - 0.182322| = (3 / 17500000 : ℝ) := by
        norm_num [logPartial, Finset.sum_Icc_succ_top]
      rw [hs]
      linarith
theorem gap5 : ∃ Δ : ℝ, Δ = remainder ∧ Δ < remainderBound := by
  refine ⟨remainder, rfl, ?_⟩
  have hb : remainderBound = (32 / 100000000 : ℝ) := by
    norm_num [remainderBound]
  rw [hb]
  simpa [Approx, remainder] using gap3
theorem gap6 :
    Approx remainderBound (3.2 * 10 ^ (-7 : ℤ))
      (1 / 1000000000000 : ℝ) := by
  norm_num [Approx, remainderBound]

end
end ProofGap.Exercise1396_6
