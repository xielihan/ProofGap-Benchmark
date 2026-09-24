import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1398

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (Real.cos x - Real.exp (-(x ^ 2 / 2))) / x ^ 4
def leadingStage (x : ℝ) :=
  ((1 / (Nat.factorial 4 : ℝ) - 1 / (4 * Nat.factorial 2)) * x ^ 4) /
    x ^ 4

theorem gap1 : Tendsto original (punctured 0) (nhds (-1 / 12 : ℝ)) := by
  let E : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2))
  let f0 : ℝ → ℝ := fun x => Real.cos x - E x
  let f1 : ℝ → ℝ := fun x => -Real.sin x + x * E x
  let f2 : ℝ → ℝ := fun x => -Real.cos x + E x - x ^ 2 * E x
  let f3 : ℝ → ℝ := fun x => Real.sin x - 3 * (x * E x) + x ^ 3 * E x
  let f4 : ℝ → ℝ := fun x =>
    Real.cos x - 3 * E x + 6 * (x ^ 2 * E x) - x ^ 4 * E x
  let g0 : ℝ → ℝ := fun x => x ^ 4
  let g1 : ℝ → ℝ := fun x => 4 * x ^ 3
  let g2 : ℝ → ℝ := fun x => 12 * x ^ 2
  let g3 : ℝ → ℝ := fun x => 24 * x
  let g4 : ℝ → ℝ := fun _ => 24
  have hinner (x : ℝ) :
      HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    convert ((((hasDerivAt_id x).pow 2).div_const 2).neg) using 1 <;>
      simp only [id_eq] <;> ring
  have hE (x : ℝ) : HasDerivAt E (-x * E x) x := by
    convert (Real.hasDerivAt_exp (-(x ^ 2 / 2))).comp x (hinner x) using 1 <;>
      dsimp [E] <;> ring
  have hdf0 (x : ℝ) : HasDerivAt f0 (f1 x) x := by
    convert (Real.hasDerivAt_cos x).sub (hE x) using 1 <;>
      dsimp [f0, f1] <;> ring
  have hdf1 (x : ℝ) : HasDerivAt f1 (f2 x) x := by
    convert (Real.hasDerivAt_sin x).neg.add ((hasDerivAt_id x).mul (hE x)) using 1 <;>
      dsimp [f1, f2] <;> ring
  have hdf2 (x : ℝ) : HasDerivAt f2 (f3 x) x := by
    convert ((Real.hasDerivAt_cos x).neg.add (hE x)).sub
      (((hasDerivAt_id x).pow 2).mul (hE x)) using 1 <;>
      dsimp [f2, f3] <;> ring
  have hdf3 (x : ℝ) : HasDerivAt f3 (f4 x) x := by
    convert ((Real.hasDerivAt_sin x).sub
      (((hasDerivAt_id x).mul (hE x)).const_mul 3)).add
      (((hasDerivAt_id x).pow 3).mul (hE x)) using 1 <;>
      dsimp [f3, f4] <;> ring
  have hdf4 (x : ℝ) : DifferentiableAt ℝ f4 x := by
    exact (((Real.hasDerivAt_cos x).sub ((hE x).const_mul 3)).add
      ((((hasDerivAt_id x).pow 2).mul (hE x)).const_mul 6)).sub
      (((hasDerivAt_id x).pow 4).mul (hE x)) |>.differentiableAt
  have hdg0 (x : ℝ) : HasDerivAt g0 (g1 x) x := by
    convert (hasDerivAt_id x).pow 4 using 1 <;> dsimp [g0, g1] <;> ring
  have hdg1 (x : ℝ) : HasDerivAt g1 (g2 x) x := by
    convert ((hasDerivAt_id x).pow 3).const_mul 4 using 1 <;>
      dsimp [g1, g2] <;> ring
  have hdg2 (x : ℝ) : HasDerivAt g2 (g3 x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul 12 using 1 <;>
      dsimp [g2, g3] <;> ring
  have hdg3 (x : ℝ) : HasDerivAt g3 (g4 x) x := by
    convert (hasDerivAt_id x).const_mul 24 using 1 <;>
      dsimp [g3, g4] <;> ring
  have hf0z : Tendsto f0 (𝓝 0) (𝓝 0) := by
    have h := (hdf0 0).continuousAt
    change Tendsto f0 (𝓝 0) (𝓝 (f0 0)) at h
    simpa [f0, E] using h
  have hf1z : Tendsto f1 (𝓝 0) (𝓝 0) := by
    have h := (hdf1 0).continuousAt
    change Tendsto f1 (𝓝 0) (𝓝 (f1 0)) at h
    simpa [f1, E] using h
  have hf2z : Tendsto f2 (𝓝 0) (𝓝 0) := by
    have h := (hdf2 0).continuousAt
    change Tendsto f2 (𝓝 0) (𝓝 (f2 0)) at h
    simpa [f2, E] using h
  have hf3z : Tendsto f3 (𝓝 0) (𝓝 0) := by
    have h := (hdf3 0).continuousAt
    change Tendsto f3 (𝓝 0) (𝓝 (f3 0)) at h
    simpa [f3, E] using h
  have hg0z : Tendsto g0 (𝓝 0) (𝓝 0) := by
    have h := (hdg0 0).continuousAt
    change Tendsto g0 (𝓝 0) (𝓝 (g0 0)) at h
    simpa [g0] using h
  have hg1z : Tendsto g1 (𝓝 0) (𝓝 0) := by
    have h := (hdg1 0).continuousAt
    change Tendsto g1 (𝓝 0) (𝓝 (g1 0)) at h
    simpa [g1] using h
  have hg2z : Tendsto g2 (𝓝 0) (𝓝 0) := by
    have h := (hdg2 0).continuousAt
    change Tendsto g2 (𝓝 0) (𝓝 (g2 0)) at h
    simpa [g2] using h
  have hg3z : Tendsto g3 (𝓝 0) (𝓝 0) := by
    have h := (hdg3 0).continuousAt
    change Tendsto g3 (𝓝 0) (𝓝 (g3 0)) at h
    simpa [g3] using h
  have hfinalN :
      Tendsto (fun x => f4 x / g4 x) (𝓝 (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
    have h := (hdf4 0).continuousAt.div_const (24 : ℝ)
    change Tendsto (fun x => f4 x / 24) (𝓝 0) (𝓝 (f4 0 / 24)) at h
    convert h using 1 <;> norm_num [f4, g4, E]
  have hright :
      Tendsto (fun x => f0 x / g0 x) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
    have hf0R := hf0z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf1R := hf1z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf2R := hf2z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf3R := hf3z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg0R := hg0z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg1R := hg1z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg2R := hg2z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg3R := hg3z.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hdf0R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f0 (f1 x) x :=
      Eventually.of_forall hdf0
    have hdf1R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f1 (f2 x) x :=
      Eventually.of_forall hdf1
    have hdf2R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f2 (f3 x) x :=
      Eventually.of_forall hdf2
    have hdf3R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f3 (f4 x) x :=
      Eventually.of_forall hdf3
    have hdg0R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g0 (g1 x) x :=
      Eventually.of_forall hdg0
    have hdg1R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g1 (g2 x) x :=
      Eventually.of_forall hdg1
    have hdg2R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g2 (g3 x) x :=
      Eventually.of_forall hdg2
    have hdg3R : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g3 (g4 x) x :=
      Eventually.of_forall hdg3
    have hg1neR : ∀ᶠ x in 𝓝[>] (0 : ℝ), g1 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_gt hx))
    have hg2neR : ∀ᶠ x in 𝓝[>] (0 : ℝ), g2 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hx))
    have hg3neR : ∀ᶠ x in 𝓝[>] (0 : ℝ), g3 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (ne_of_gt hx)
    have hg4neR : ∀ᶠ x in 𝓝[>] (0 : ℝ), g4 x ≠ 0 :=
      Eventually.of_forall (fun _ => by norm_num [g4])
    have hfinalR := hfinalN.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hlim3 :
        Tendsto (fun x => f3 x / g3 x) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsGT (f' := f4) (g' := g4)
      all_goals assumption
    have hlim2 :
        Tendsto (fun x => f2 x / g2 x) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsGT (f' := f3) (g' := g3)
      all_goals assumption
    have hlim1 :
        Tendsto (fun x => f1 x / g1 x) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsGT (f' := f2) (g' := g2)
      all_goals assumption
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := f1) (g' := g1)
    all_goals assumption
  have hleft :
      Tendsto (fun x => f0 x / g0 x) (𝓝[<] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
    have hf0L := hf0z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf1L := hf1z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf2L := hf2z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hf3L := hf3z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg0L := hg0z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg1L := hg1z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg2L := hg2z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hg3L := hg3z.mono_left (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hdf0L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt f0 (f1 x) x :=
      Eventually.of_forall hdf0
    have hdf1L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt f1 (f2 x) x :=
      Eventually.of_forall hdf1
    have hdf2L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt f2 (f3 x) x :=
      Eventually.of_forall hdf2
    have hdf3L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt f3 (f4 x) x :=
      Eventually.of_forall hdf3
    have hdg0L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt g0 (g1 x) x :=
      Eventually.of_forall hdg0
    have hdg1L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt g1 (g2 x) x :=
      Eventually.of_forall hdg1
    have hdg2L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt g2 (g3 x) x :=
      Eventually.of_forall hdg2
    have hdg3L : ∀ᶠ x in 𝓝[<] (0 : ℝ), HasDerivAt g3 (g4 x) x :=
      Eventually.of_forall hdg3
    have hg1neL : ∀ᶠ x in 𝓝[<] (0 : ℝ), g1 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_lt hx))
    have hg2neL : ∀ᶠ x in 𝓝[<] (0 : ℝ), g2 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_lt hx))
    have hg3neL : ∀ᶠ x in 𝓝[<] (0 : ℝ), g3 x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (ne_of_lt hx)
    have hg4neL : ∀ᶠ x in 𝓝[<] (0 : ℝ), g4 x ≠ 0 :=
      Eventually.of_forall (fun _ => by norm_num [g4])
    have hfinalL := hfinalN.mono_left
      (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hlim3 :
        Tendsto (fun x => f3 x / g3 x) (𝓝[<] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsLT (f' := f4) (g' := g4)
      all_goals assumption
    have hlim2 :
        Tendsto (fun x => f2 x / g2 x) (𝓝[<] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsLT (f' := f3) (g' := g3)
      all_goals assumption
    have hlim1 :
        Tendsto (fun x => f1 x / g1 x) (𝓝[<] (0 : ℝ)) (𝓝 (-1 / 12 : ℝ)) := by
      apply HasDerivAt.lhopital_zero_nhdsLT (f' := f2) (g' := g2)
      all_goals assumption
    apply HasDerivAt.lhopital_zero_nhdsLT (f' := f1) (g' := g1)
    all_goals assumption
  have hset : ({(0 : ℝ)} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    change x ≠ 0 ↔ x < 0 ∨ x > 0
    exact ne_iff_lt_or_gt
  have hsplit : punctured 0 = 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] 0 := by
    rw [punctured, hset, nhdsWithin_union]
  rw [hsplit]
  change map (fun x => f0 x / g0 x) (𝓝[<] (0 : ℝ) ⊔ 𝓝[>] 0) ≤
    𝓝 (-1 / 12 : ℝ)
  rw [Filter.map_sup]
  exact sup_le hleft hright
theorem gap2 : Tendsto leadingStage (punctured 0) (nhds (-1 / 12 : ℝ)) := by
  have h :
      leadingStage =ᶠ[punctured 0] (fun _ : ℝ => (-1 / 12 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa [punctured] using hx
    unfold leadingStage
    rw [div_eq_iff (pow_ne_zero 4 hx0)]
    norm_num [Nat.factorial]
  exact tendsto_const_nhds.congr' h.symm
theorem gap3 : Tendsto leadingStage (punctured 0) (nhds (-1 / 12 : ℝ)) := by
  exact gap2
theorem gap4 : Tendsto original (punctured 0) (nhds (-1 / 12 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1398
