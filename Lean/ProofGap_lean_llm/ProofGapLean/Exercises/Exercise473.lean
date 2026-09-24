import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise473

noncomputable section

def sign (k : ℤ) : ℝ := if Even k then 1 else -1
def original (m n : ℤ) (x : ℝ) : ℝ :=
  Real.sin ((m : ℝ) * x) / Real.sin ((n : ℝ) * x)
def shifted (m n : ℤ) (y : ℝ) : ℝ :=
  sign m * Real.sin ((m : ℝ) * y) /
    (sign n * Real.sin ((n : ℝ) * y))
def factored (m n : ℤ) (y : ℝ) : ℝ :=
  sign (m - n) *
    (Real.sin ((m : ℝ) * y) / ((m : ℝ) * y) *
      (((n : ℝ) * y) / Real.sin ((n : ℝ) * y)) *
      ((m : ℝ) / (n : ℝ)))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 473, gap 1; bind the substitution as `y=x-π`. -/
private theorem tendsto_add_punctured (a b : ℝ) :
    Filter.Tendsto (fun x : ℝ => x + b)
      (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhdsWithin (a + b) ({a + b} : Set ℝ)ᶜ) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hi : ContinuousAt (fun x : ℝ => x) a := continuousAt_id
    have hb : ContinuousAt (fun _ : ℝ => b) a := continuousAt_const
    exact (hi.add hb).tendsto.mono_left inf_le_left
  · have hx :
        ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
          x ∈ ({a} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    filter_upwards [hx] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h
    exact hx (add_right_cancel h)

private theorem tendsto_mul_punctured (c : ℝ) (hc : c ≠ 0) :
    Filter.Tendsto (fun x : ℝ => c * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc' : ContinuousAt (fun _ : ℝ => c) 0 := continuousAt_const
    have hi : ContinuousAt (fun x : ℝ => x) 0 := continuousAt_id
    simpa using (hc'.mul hi).tendsto.mono_left inf_le_left
  · have hx :
        ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
          x ∈ ({0} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    filter_upwards [hx] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact mul_ne_zero hc hx

private theorem tendsto_sin_div_zero :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have h := (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope_zero
  simpa [div_eq_mul_inv, mul_comm] using h

private theorem sign_ne (k : ℤ) : sign k ≠ 0 := by
  unfold sign
  split <;> norm_num

private theorem sign_sub_div (m n : ℤ) :
    sign m / sign n = sign (m - n) := by
  by_cases hm : Even m
  · by_cases hn : Even n
    · have hmn : Even (m - n) := by
        rcases hm with ⟨a, ha⟩
        rcases hn with ⟨b, hb⟩
        refine ⟨a - b, ?_⟩
        rw [ha, hb]
        ring
      simp [sign, hm, hn, hmn]
    · have hmn : ¬ Even (m - n) := by
        intro hd
        apply hn
        rcases hm with ⟨a, ha⟩
        rcases hd with ⟨d, hd⟩
        refine ⟨a - d, ?_⟩
        calc
          n = m - (m - n) := by ring
          _ = m - (d + d) := by rw [hd]
          _ = (a + a) - (d + d) := by rw [ha]
          _ = (a - d) + (a - d) := by ring
      simp [sign, hm, hn, hmn]
  · by_cases hn : Even n
    · have hmn : ¬ Even (m - n) := by
        intro hd
        apply hm
        rcases hn with ⟨b, hb⟩
        rcases hd with ⟨d, hd⟩
        refine ⟨d + b, ?_⟩
        calc
          m = (m - n) + n := by ring
          _ = (d + d) + (b + b) := by rw [hd, hb]
          _ = (d + b) + (d + b) := by ring
      simp [sign, hm, hn, hmn]
    · have hom : Odd m := by
        rcases Int.even_or_odd m with he | ho
        · exact (hm he).elim
        · exact ho
      have hon : Odd n := by
        rcases Int.even_or_odd n with he | ho
        · exact (hn he).elim
        · exact ho
      have hmn : Even (m - n) := by
        rcases hom with ⟨a, ha⟩
        rcases hon with ⟨b, hb⟩
        refine ⟨a - b, ?_⟩
        rw [ha, hb]
        ring
      simp [sign, hm, hn, hmn]

private theorem sin_int_add_pi (k : ℤ) (y : ℝ) :
    Real.sin ((k : ℝ) * (y + Real.pi)) =
      sign k * Real.sin ((k : ℝ) * y) := by
  rcases Int.even_or_odd k with hk | hk
  · rcases hk with ⟨j, hj⟩
    rw [sign, if_pos ⟨j, hj⟩, one_mul, hj]
    calc
      Real.sin (((j + j : ℤ) : ℝ) * (y + Real.pi)) =
          Real.sin (((j + j : ℤ) : ℝ) * y +
            (j : ℝ) * (2 * Real.pi)) := by
        congr 1
        simp only [Int.cast_add]
        ring
      _ = Real.sin (((j + j : ℤ) : ℝ) * y) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Real.sin_add_int_mul_two_pi
            (((j + j : ℤ) : ℝ) * y) j)
  · rcases hk with ⟨j, hj⟩
    have hknot : ¬ Even k := by
      intro he
      rcases he with ⟨i, hi⟩
      omega
    have hj' : k = j + j + 1 := by
      rw [hj]
      ring
    rw [sign, if_neg hknot, neg_one_mul, hj']
    calc
      Real.sin (((j + j + 1 : ℤ) : ℝ) * (y + Real.pi)) =
          Real.sin ((((j + j + 1 : ℤ) : ℝ) * y + Real.pi) +
            (j : ℝ) * (2 * Real.pi)) := by
        congr 1
        simp only [Int.cast_add, Int.cast_one]
        ring
      _ = Real.sin (((j + j + 1 : ℤ) : ℝ) * y + Real.pi) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Real.sin_add_int_mul_two_pi
            (((j + j + 1 : ℤ) : ℝ) * y + Real.pi) j)
      _ = -Real.sin (((j + j + 1 : ℤ) : ℝ) * y) :=
        Real.sin_add_pi _

private theorem original_add_pi (m n : ℤ) (y : ℝ) :
    original m n (y + Real.pi) = shifted m n y := by
  unfold original shifted
  rw [sin_int_add_pi m y, sin_int_add_pi n y]

private theorem shifted_eq_factored
    (m n : ℤ) (hn : n ≠ 0) (y : ℝ) (hy : y ≠ 0) :
    shifted m n y = factored m n y := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  by_cases hm : m = 0
  · subst m
    simp [shifted, factored, sign]
  · have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast hm
    by_cases hs : Real.sin ((n : ℝ) * y) = 0
    · simp [shifted, factored, hs]
    · unfold shifted factored
      rw [← sign_sub_div m n]
      field_simp [sign_ne, hmR, hnR, hy, hs]
      <;> ring

theorem gap1 : HasLimitAt (fun x => x - Real.pi) Real.pi 0 := by
  unfold HasLimitAt
  have hi : ContinuousAt (fun x : ℝ => x) Real.pi := continuousAt_id
  have hp : ContinuousAt (fun _ : ℝ => Real.pi) Real.pi := continuousAt_const
  have h := (hi.sub hp).tendsto
  simpa using h.mono_left inf_le_left

/-- Exercise 473, gap 2. -/
theorem gap2 (m n : ℤ) (hn : n ≠ 0) (L : ℝ) :
    HasLimitAt (original m n) Real.pi L ↔ HasLimitAt (shifted m n) 0 L := by
  have hadd :
      Filter.Tendsto (fun y : ℝ => y + Real.pi)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin Real.pi ({Real.pi} : Set ℝ)ᶜ) := by
    simpa using tendsto_add_punctured (0 : ℝ) Real.pi
  have hsub :
      Filter.Tendsto (fun x : ℝ => x - Real.pi)
        (nhdsWithin Real.pi ({Real.pi} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    simpa [sub_eq_add_neg] using
      tendsto_add_punctured Real.pi (-Real.pi)
  constructor
  · intro h
    unfold HasLimitAt at h ⊢
    have hc :
        Filter.Tendsto (fun y : ℝ => original m n (y + Real.pi))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) :=
      h.comp hadd
    have heq :
        (fun y : ℝ => original m n (y + Real.pi)) =ᶠ[
          nhdsWithin 0 ({0} : Set ℝ)ᶜ] shifted m n := by
      filter_upwards with y
      exact original_add_pi m n y
    exact (Filter.tendsto_congr' heq).mp hc
  · intro h
    unfold HasLimitAt at h ⊢
    have hc :
        Filter.Tendsto (fun x : ℝ => shifted m n (x - Real.pi))
          (nhdsWithin Real.pi ({Real.pi} : Set ℝ)ᶜ) (nhds L) :=
      h.comp hsub
    have heq :
        (fun x : ℝ => shifted m n (x - Real.pi)) =ᶠ[
          nhdsWithin Real.pi ({Real.pi} : Set ℝ)ᶜ] original m n := by
      filter_upwards with x
      simpa using (original_add_pi m n (x - Real.pi)).symm
    exact (Filter.tendsto_congr' heq).mp hc

/-- Exercise 473, gap 3. -/
theorem gap3 (m n : ℤ) (hn : n ≠ 0) (L : ℝ) :
    HasLimitAt (shifted m n) 0 L ↔ HasLimitAt (factored m n) 0 L := by
  unfold HasLimitAt
  apply Filter.tendsto_congr'
  have hy_mem :
      ∀ᶠ y in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        y ∈ ({0} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  filter_upwards [hy_mem] with y hy
  apply shifted_eq_factored m n hn y
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy

/-- Exercise 473, gap 4. -/
theorem gap4 (m n : ℤ) (hn : n ≠ 0) :
    HasLimitAt (factored m n) 0
      (sign (m - n) * ((m : ℝ) / (n : ℝ))) := by
  by_cases hm : m = 0
  · subst m
    unfold HasLimitAt
    have hf : factored 0 n = fun _ : ℝ => 0 := by
      funext y
      simp [factored]
    rw [hf]
    simpa using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0))
  · have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast hm
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hmSinc :
        Filter.Tendsto
          (fun y : ℝ => Real.sin ((m : ℝ) * y) / ((m : ℝ) * y))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      exact tendsto_sin_div_zero.comp
        (tendsto_mul_punctured (m : ℝ) hmR)
    have hnSinc :
        Filter.Tendsto
          (fun y : ℝ => Real.sin ((n : ℝ) * y) / ((n : ℝ) * y))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      exact tendsto_sin_div_zero.comp
        (tendsto_mul_punctured (n : ℝ) hnR)
    have hnInv :
        Filter.Tendsto
          (fun y : ℝ => ((n : ℝ) * y) / Real.sin ((n : ℝ) * y))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      simpa only [inv_div, inv_one] using
        hnSinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hsign :
        Filter.Tendsto (fun _ : ℝ => sign (m - n))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (sign (m - n))) :=
      tendsto_const_nhds
    have hratio :
        Filter.Tendsto (fun _ : ℝ => (m : ℝ) / (n : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
          (nhds ((m : ℝ) / (n : ℝ))) :=
      tendsto_const_nhds
    have h := hsign.mul ((hmSinc.mul hnInv).mul hratio)
    simpa [HasLimitAt, factored] using h

end

end ProofGap.Exercise473
