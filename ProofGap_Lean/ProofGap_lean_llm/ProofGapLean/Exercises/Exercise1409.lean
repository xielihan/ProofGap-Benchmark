import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise1408
import Mathlib.Analysis.Complex.Exponential

namespace ProofGap.Exercise1409

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def y (x : ℝ) :=
  1 - Real.rpow (1 + x) (1 / x) / Real.exp 1
def exponentialForm (x : ℝ) :=
  1 - Real.exp ((1 / x) * Real.log (1 + x) - 1)
def logRemainder (x : ℝ) :=
  Real.log (1 + x) - (x - x ^ 2 / 2)
def exponentRemainder (x : ℝ) :=
  (1 / x) * Real.log (1 + x) - 1 + x / 2

theorem gap1 (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) :
    y x = exponentialForm x := by
  unfold y exponentialForm
  change 1 - (1 + x) ^ (1 / x : ℝ) / Real.exp 1 =
    1 - Real.exp ((1 / x) * Real.log (1 + x) - 1)
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x)]
  rw [← Real.exp_sub]
  congr 2
  ring
theorem gap2 :
    Asymptotics.IsLittleO punctured logRemainder (fun x => x ^ 2) := by
  simpa only [punctured, logRemainder, ProofGap.Exercise1408.punctured,
    ProofGap.Exercise1408.logRemainder] using ProofGap.Exercise1408.gap2
theorem gap3 :
    Asymptotics.IsLittleO punctured exponentRemainder (fun x => x) := by
  have hxne : ∀ᶠ x : ℝ in punctured, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have h := gap2.mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => 1 / x) punctured)
  refine h.congr' ?_ ?_
  · filter_upwards [hxne] with x hx
    unfold logRemainder exponentRemainder
    field_simp
    ring
  · filter_upwards [hxne] with x hx
    field_simp
theorem gap4 :
    ∀ᶠ x in punctured, y x = exponentialForm x := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have hnear : ∀ᶠ x : ℝ in punctured, -1 < x :=
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono hp_le
  have hxne : ∀ᶠ x : ℝ in punctured, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hnear, hxne] with x hx hx0
  exact gap1 x hx hx0
theorem gap5 :
    Asymptotics.IsLittleO punctured
      (fun x => exponentialForm x - x / 2) (fun x => x) := by
  let z : ℝ → ℝ := fun x => (1 / x) * Real.log (1 + x) - 1
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) punctured (𝓝 0) :=
    tendsto_id.mono_left hp_le
  have h21 : (fun x : ℝ => x ^ 2) =o[punctured] (fun x => x) :=
    by
      simpa using
        (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 1 < 2)).mono hp_le
  have hr : (fun x => z x + x / 2) =o[punctured] (fun x => x) := by
    convert gap3 using 1 <;> ext x <;> simp [z, exponentRemainder] <;> ring
  have hlin : (fun x : ℝ => -x / 2) =O[punctured] (fun x => x) := by
    convert (Asymptotics.isBigO_refl (fun x : ℝ => x) punctured).const_mul_left
      (-1 / 2 : ℝ) using 1 <;> ext x <;> ring
  have hz : z =O[punctured] (fun x : ℝ => x) := by
    have h := hr.isBigO.add hlin
    convert h using 1 <;> ext x <;> ring
  have hz0 : Tendsto z punctured (𝓝 0) :=
    hz.trans_tendsto hid
  have hzsmall : ∀ᶠ x in punctured, ‖z x‖ ≤ 1 := by
    have hzlt : ∀ᶠ x in punctured, ‖z x‖ < 1 :=
      hz0.norm.eventually (eventually_lt_nhds (by norm_num : ‖(0 : ℝ)‖ < 1))
    exact hzlt.mono fun _ hx => hx.le
  have hexpO :
      (fun x => Real.exp (z x) - 1 - z x) =O[punctured]
        (fun x => z x ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hzsmall] with x hx
    simpa [Real.norm_eq_abs, norm_pow] using
      Real.norm_exp_sub_one_sub_id_le hx
  have hzsq :
      (fun x => z x ^ 2) =O[punctured] (fun x : ℝ => x ^ 2) := by
    have h := hz.mul hz
    convert h using 1 <;> ext x <;> ring
  have hexp :
      (fun x => Real.exp (z x) - 1 - z x) =o[punctured]
        (fun x : ℝ => x) :=
    (hexpO.trans hzsq).trans_isLittleO h21
  have hsum :=
    (hexp.const_mul_left (-1 : ℝ)).add
      (gap3.const_mul_left (-1 : ℝ))
  refine hsum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards with x
  simp only [z, exponentRemainder, exponentialForm]
  ring
theorem gap6 :
    Asymptotics.IsLittleO punctured
      (fun x => (x / 2 : ℝ) - x / 2) (fun x => x) := by
  simpa using Asymptotics.isLittleO_zero (fun x : ℝ => x) punctured
theorem gap7 :
    Asymptotics.IsLittleO punctured
      (fun x => y x - x / 2) (fun x => x) := by
  refine gap5.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [gap4] with x hx
  rw [hx]
theorem gap8 :
    Asymptotics.IsEquivalent punctured y (fun x => x / 2) := by
  change (fun x => y x - x / 2) =o[punctured] (fun x => x / 2)
  have hconst :
      (fun x : ℝ => x) =O[punctured] (fun x => x / 2) := by
    convert (Asymptotics.isBigO_refl (fun x : ℝ => x / 2) punctured).const_mul_left
      2 using 1 <;> ext x <;> ring
  exact gap7.trans_isBigO hconst

end
end ProofGap.Exercise1409
