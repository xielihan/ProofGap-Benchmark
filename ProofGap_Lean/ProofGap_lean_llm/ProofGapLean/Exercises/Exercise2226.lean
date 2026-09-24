import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise2193
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2226

noncomputable section

def riemannSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ k ∈ Finset.Icc 1 n,
      f (a + (k : ℝ) * ((b - a) / n))

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hab : a < b) :
    Tendsto (riemannSum f a b) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f (a + (b - a) * x))) := by
  let g : ℝ → ℝ := fun x => f (a + (b - a) * x)
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply hf.comp
    · exact (continuous_const.add
        (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      constructor
      · dsimp
        exact le_add_of_nonneg_right
          (mul_nonneg (sub_nonneg.mpr hab.le) hx.1)
      · dsimp
        have hmul : (b - a) * x ≤ (b - a) * 1 :=
          mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr hab.le)
        calc
          a + (b - a) * x ≤ a + (b - a) * 1 :=
            by linarith
          _ = b := by ring
  let nseq : ℕ → ℕ := fun k => k + 1
  let xseq : ℕ → ℕ → ℝ := fun k i => (i : ℝ) / (k + 1 : ℕ)
  let tags : ℕ → ℕ → ℝ := fun k i => ((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ)
  have hp : ∀ k, ProofGap.Exercise2193.IsTaggedPartition
      0 1 (nseq k) (xseq k) (tags k) (tags k) := by
    intro k
    have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    refine ⟨by simp [xseq], ?_, ?_⟩
    · dsimp [nseq, xseq]
      exact div_self (ne_of_gt hkR)
    · intro i hi
      have hle : (i : ℝ) / (k + 1 : ℕ) ≤
          ((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ) := by
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.le_succ i) hkR.le
      exact ⟨hle, le_rfl, hle, le_rfl, hle⟩
  have hmesh : ProofGap.Exercise2193.FineSequence nseq xseq := by
    intro δ hδ
    have hcast : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℕ))
        atTop (𝓝 0) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hcast)
    filter_upwards [hzero.eventually (Metric.ball_mem_nhds 0 hδ)] with k hk
    intro i hi
    have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hw : ((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ) -
        (i : ℝ) / (k + 1 : ℕ) = 1 / (k + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hkR]
      ring
    have hk' : dist ((1 : ℝ) / (k + 1 : ℕ)) 0 < δ := by
      simpa [Metric.mem_ball] using hk
    have hfrac : (1 : ℝ) / (k + 1 : ℕ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hkR)] at hk'
      exact hk'
    change |((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ) -
      (i : ℝ) / (k + 1 : ℕ)| < δ
    rw [hw, abs_of_pos (one_div_pos.mpr hkR)]
    exact hfrac
  have hlim := ProofGap.Exercise2193.gap2
    (fun _ : ℝ => (1 : ℝ)) g 0 1 (by norm_num)
    continuousOn_const hg nseq xseq tags tags hp hmesh
  have hEq : ∀ k : ℕ,
      ProofGap.Exercise2193.StandardSum (fun _ : ℝ => (1 : ℝ)) g
        (nseq k) (xseq k) (tags k) = riemannSum f a b (k + 1) := by
    intro k
    have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hindex : (Finset.range (k + 1)).image (fun i : ℕ => i + 1) =
        Finset.Icc 1 (k + 1) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩
        constructor <;> omega
      · rintro ⟨hj1, hjn⟩
        refine ⟨j - 1, ?_, ?_⟩ <;> omega
    have hshift (H : ℕ → ℝ) :
        (∑ i ∈ Finset.range (k + 1), H (i + 1)) =
          ∑ j ∈ Finset.Icc 1 (k + 1), H j := by
      rw [← hindex]
      symm
      apply Finset.sum_image
      intro i hi j hj hij
      simpa using hij
    unfold ProofGap.Exercise2193.StandardSum riemannSum
    dsimp [nseq]
    rw [← hshift (fun j => f
      (a + (j : ℝ) * ((b - a) / (k + 1 : ℕ)))), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hw : ((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ) -
        (i : ℝ) / (k + 1 : ℕ) = 1 / (k + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hkR]
      ring
    have harg : a + (b - a) *
          (((i + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) =
        a + ((i + 1 : ℕ) : ℝ) * ((b - a) / (k + 1 : ℕ)) := by ring
    simp only [nseq, xseq, tags, one_mul, g]
    rw [hw, harg]
    ring
  have hshifted : Tendsto (fun k => riemannSum f a b (k + 1)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f (a + (b - a) * x))) := by
    have hlim' : Tendsto
        (fun k => ProofGap.Exercise2193.StandardSum (fun _ : ℝ => (1 : ℝ)) g
          (nseq k) (xseq k) (tags k)) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, f (a + (b - a) * x))) := by
      simpa [g] using hlim
    exact hlim'.congr' (Filter.Eventually.of_forall fun k => hEq k)
  exact (tendsto_add_atTop_iff_nat 1).mp hshifted

theorem gap2 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hab : a < b) :
    (∫ x in (0 : ℝ)..1, f (a + (b - a) * x)) =
      (1 / (b - a)) * ∫ x in a..b, f x := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  simpa [one_div, smul_eq_mul] using
    (intervalIntegral.integral_comp_add_mul (f := f) (a := (0 : ℝ))
      (b := (1 : ℝ)) hba a)

theorem gap3 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hab : a < b) :
    Tendsto (riemannSum f a b) atTop
      (𝓝 ((1 / (b - a)) * ∫ x in a..b, f x)) := by
  rw [← gap2 f a b hf hab]
  exact gap1 f a b hf hab

end

end ProofGap.Exercise2226
