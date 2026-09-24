import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise446

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) : ℝ := (cbrt (8 + 3 * x - x ^ 2) - 2) / (x + x ^ 2)
def cancelled (x : ℝ) : ℝ :=
  (3 - x) /
    ((1 + x) * (cbrt ((8 + 3 * x - x ^ 2) ^ 2) +
      2 * cbrt (8 + 3 * x - x ^ 2) + 4))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_446/1.txt`. -/
private theorem cbrt_spec (x : ℝ) (hx : 0 ≤ x) :
    cbrt x ^ 3 = x ∧ cbrt (x ^ 2) = cbrt x ^ 2 := by
  constructor
  · unfold cbrt
    calc
      Real.rpow x (1 / 3 : ℝ) ^ (3 : ℕ) =
          Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
        exact
          (Real.rpow_natCast (Real.rpow x (1 / 3 : ℝ)) 3).symm
      _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
        exact (Real.rpow_mul hx (1 / 3 : ℝ) 3).symm
      _ = x := by norm_num
  · unfold cbrt
    calc
      Real.rpow (x ^ 2) (1 / 3 : ℝ) =
          Real.rpow (x * x) (1 / 3 : ℝ) := by rw [pow_two]
      _ = Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) := by
        exact Real.mul_rpow hx hx
      _ = Real.rpow x (1 / 3 : ℝ) ^ 2 := by rw [pow_two]

theorem gap1 : HasLimitAt original 0 (1 / 4) ↔
    HasLimitAt cancelled 0 (1 / 4) := by
  unfold HasLimitAt
  have hIoo :
      ∀ᶠ x in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact mem_nhdsWithin_of_mem_nhds
      (isOpen_Ioo.mem_nhds (by norm_num))
  have heq :
      original =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [hIoo,
      (self_mem_nhdsWithin :
        ∀ᶠ x in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
          x ∈ ({0} : Set ℝ)ᶜ)] with x hx hxmem
    have hx0 : x ≠ 0 := by
      simpa using hxmem
    have hprod : 0 < (1 - x) * (1 + x) := by
      exact mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
    have hxsq : x ^ 2 < 1 := by
      nlinarith [hprod]
    let u : ℝ := 8 + 3 * x - x ^ 2
    have hu : 0 < u := by
      dsimp [u]
      nlinarith
    have hs := cbrt_spec u hu.le
    unfold original cancelled
    change
      (cbrt u - 2) / (x + x ^ 2) =
        (3 - x) /
          ((1 + x) *
            (cbrt (u ^ 2) + 2 * cbrt u + 4))
    rw [hs.2]
    have h1x : 1 + x ≠ 0 := by
      nlinarith [hx.1]
    have hsum : cbrt u ^ 2 + 2 * cbrt u + 4 ≠ 0 := by
      apply ne_of_gt
      nlinarith [sq_nonneg (cbrt u + 1)]
    have hxx : x + x ^ 2 ≠ 0 := by
      rw [show x + x ^ 2 = x * (1 + x) by ring]
      exact mul_ne_zero hx0 h1x
    apply (div_eq_div_iff hxx (mul_ne_zero h1x hsum)).2
    calc
      (cbrt u - 2) *
          ((1 + x) * (cbrt u ^ 2 + 2 * cbrt u + 4)) =
          (1 + x) *
            ((cbrt u - 2) *
              (cbrt u ^ 2 + 2 * cbrt u + 4)) := by ring
      _ = (1 + x) * (u - 8) := by
        congr 1
        calc
          (cbrt u - 2) *
              (cbrt u ^ 2 + 2 * cbrt u + 4) =
              cbrt u ^ 3 - 8 := by ring
          _ = u - 8 := by rw [hs.1]
      _ = (3 - x) * (x + x ^ 2) := by
        dsimp [u]
        ring
  constructor
  · intro horiginal
    rw [Filter.tendsto_def] at horiginal ⊢
    intro s hs
    filter_upwards [horiginal s hs, heq] with x hx hxeq
    change original x ∈ s at hx
    change cancelled x ∈ s
    rwa [← hxeq]
  · intro hcancelled
    rw [Filter.tendsto_def] at hcancelled ⊢
    intro s hs
    filter_upwards [hcancelled s hs, heq] with x hx hxeq
    change cancelled x ∈ s at hx
    change original x ∈ s
    rwa [hxeq]

/-- Source: `proof_gap/exercise_446/2.txt`. -/
theorem gap2 : HasLimitAt original 0 (1 / 4) ↔
    HasLimitAt cancelled 0 (1 / 4) := by
  exact gap1

/-- Source: `proof_gap/exercise_446/3.txt`. -/
theorem gap3 : HasLimitAt cancelled 0 (1 / 4) := by
  have hspec8 := cbrt_spec (8 : ℝ) (by norm_num)
  have h8cube : cbrt 8 ^ 3 = 8 := hspec8.1
  have h8 : cbrt 8 = 2 := by
    have hfactor :
        (cbrt 8 - 2) * (cbrt 8 ^ 2 + 2 * cbrt 8 + 4) = 0 := by
      calc
        (cbrt 8 - 2) * (cbrt 8 ^ 2 + 2 * cbrt 8 + 4) =
            cbrt 8 ^ 3 - 8 := by ring
        _ = 0 := by norm_num [h8cube]
    have hfactor_ne : cbrt 8 ^ 2 + 2 * cbrt 8 + 4 ≠ 0 := by
      apply ne_of_gt
      nlinarith [sq_nonneg (cbrt 8 + 1)]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hfactor_ne)
  have h64 : cbrt 64 = 4 := by
    have hsq := hspec8.2
    norm_num [h8] at hsq
    exact hsq
  have hcbrt_pos : ∀ {x : ℝ}, 0 < x → ContinuousAt cbrt x := by
    intro x hx
    unfold cbrt
    have hinner : ContinuousAt
        (fun y : ℝ => Real.log y * (1 / 3 : ℝ)) x :=
      (Real.continuousAt_log (ne_of_gt hx)).mul continuousAt_const
    have hcont : ContinuousAt
        (fun y : ℝ => Real.exp (Real.log y * (1 / 3 : ℝ))) x := by
      simpa only [Function.comp_apply] using
        Real.continuous_exp.continuousAt.comp hinner
    have hpos : ∀ᶠ y in nhds x, 0 < y :=
      isOpen_Ioi.mem_nhds hx
    have heq :
        (fun y : ℝ => Real.rpow y (1 / 3 : ℝ)) =ᶠ[nhds x]
          (fun y : ℝ => Real.exp (Real.log y * (1 / 3 : ℝ))) := by
      filter_upwards [hpos] with y hy
      exact Real.rpow_def_of_pos hy (1 / 3 : ℝ)
    have hxdef :
        Real.rpow x (1 / 3 : ℝ) =
          Real.exp (Real.log x * (1 / 3 : ℝ)) :=
      Real.rpow_def_of_pos hx (1 / 3 : ℝ)
    change Filter.Tendsto
      (fun y : ℝ => Real.rpow y (1 / 3 : ℝ))
      (nhds x) (nhds (Real.rpow x (1 / 3 : ℝ)))
    rw [hxdef]
    change Filter.Tendsto
      (fun y : ℝ => Real.exp (Real.log y * (1 / 3 : ℝ)))
      (nhds x)
      (nhds (Real.exp (Real.log x * (1 / 3 : ℝ)))) at hcont
    rw [Filter.tendsto_def] at hcont ⊢
    intro s hs
    filter_upwards [hcont s hs, heq] with y hy hyeq
    change Real.rpow y (1 / 3 : ℝ) ∈ s
    rwa [hyeq]
  have hp : ContinuousAt
      (fun x : ℝ => 8 + 3 * x - x ^ 2) 0 :=
    (continuousAt_const.add
      (continuousAt_const.mul continuousAt_id)).sub
      (continuousAt_id.pow 2)
  have hc8 : ContinuousAt
      (fun x : ℝ => cbrt (8 + 3 * x - x ^ 2)) 0 := by
    have houter : ContinuousAt cbrt
        (8 + 3 * (0 : ℝ) - 0 ^ 2) :=
      hcbrt_pos (by norm_num)
    have ht : Filter.Tendsto
        (cbrt ∘ (fun x : ℝ => 8 + 3 * x - x ^ 2))
        (nhds 0)
        (nhds (cbrt (8 + 3 * (0 : ℝ) - 0 ^ 2))) :=
      houter.tendsto.comp hp
    simpa only [Function.comp_apply] using ht
  have hp2 : ContinuousAt
      (fun x : ℝ => (8 + 3 * x - x ^ 2) ^ 2) 0 :=
    hp.pow 2
  have hc64 : ContinuousAt
      (fun x : ℝ => cbrt ((8 + 3 * x - x ^ 2) ^ 2)) 0 := by
    have houter : ContinuousAt cbrt
        ((8 + 3 * (0 : ℝ) - 0 ^ 2) ^ 2) :=
      hcbrt_pos (by norm_num)
    have ht : Filter.Tendsto
        (cbrt ∘ (fun x : ℝ => (8 + 3 * x - x ^ 2) ^ 2))
        (nhds 0)
        (nhds (cbrt ((8 + 3 * (0 : ℝ) - 0 ^ 2) ^ 2))) :=
      houter.tendsto.comp hp2
    simpa only [Function.comp_apply] using ht
  have htwo : ContinuousAt
      (fun x : ℝ => 2 * cbrt (8 + 3 * x - x ^ 2)) 0 :=
    continuousAt_const.mul hc8
  have hsum : ContinuousAt
      (fun x : ℝ =>
        cbrt ((8 + 3 * x - x ^ 2) ^ 2) +
          2 * cbrt (8 + 3 * x - x ^ 2) + 4) 0 :=
    (hc64.add htwo).add continuousAt_const
  have hone : ContinuousAt (fun x : ℝ => 1 + x) 0 :=
    continuousAt_const.add continuousAt_id
  have hden : ContinuousAt
      (fun x : ℝ =>
        (1 + x) *
          (cbrt ((8 + 3 * x - x ^ 2) ^ 2) +
            2 * cbrt (8 + 3 * x - x ^ 2) + 4)) 0 :=
    hone.mul hsum
  have hnum : ContinuousAt (fun x : ℝ => 3 - x) 0 :=
    continuousAt_const.sub continuousAt_id
  have hc : ContinuousAt cancelled 0 := by
    unfold cancelled
    exact hnum.div hden (by norm_num [h8, h64])
  have hvalue : cancelled 0 = (1 / 4 : ℝ) := by
    norm_num [cancelled, h8, h64]
  unfold HasLimitAt
  rw [← hvalue]
  exact hc.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_446/4.txt`. -/
theorem gap4 : HasLimitAt original 0 (1 / 4) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise446
