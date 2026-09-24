import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise501

noncomputable section

def sixthRoot (x : ℝ) : ℝ := Real.rpow x (1 / 6 : ℝ)
def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) : ℝ :=
  (Real.sqrt (Real.cos x) - cubeRoot (Real.cos x)) / Real.sin x ^ 2
def rewritten (x : ℝ) : ℝ :=
  (-cubeRoot (Real.cos x) * (1 - sixthRoot (Real.cos x))) / Real.sin x ^ 2
def rootSum (x : ℝ) : ℝ :=
  (Finset.range 6).sum (fun k => sixthRoot ((Real.cos x) ^ k))
def rationalized (x : ℝ) : ℝ :=
  -((1 - Real.cos x) / Real.sin x ^ 2 *
    (cubeRoot (Real.cos x) / rootSum x))
def normalized (x : ℝ) : ℝ :=
  -((2 * Real.sin (x / 2) ^ 2) / (4 * (x / 2) ^ 2) *
    (x ^ 2 / Real.sin x ^ 2) * (cubeRoot (Real.cos x) / rootSum x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_501/1.txt`. -/
private theorem tendsto_cos_zero :
    Filter.Tendsto (fun x : ℝ => Real.cos x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hc :
      Filter.Tendsto (fun x : ℝ => Real.cos x) (nhds 0)
        (nhds (Real.cos 0)) :=
    Real.continuous_cos.continuousAt
  simpa using hc.mono_left inf_le_left

private theorem eventually_cos_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < Real.cos x := by
  apply tendsto_cos_zero.eventually
  exact Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)

private theorem tendsto_cos_rpow (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.rpow (Real.cos x) a)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (Real.cos x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hl :
        Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds (Real.log 1)) :=
      Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    simpa using hl.comp tendsto_cos_zero
  have harg :
      Filter.Tendsto (fun x : ℝ => Real.log (Real.cos x) * a)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hlog.mul_const a
  have hexpAt : ContinuousAt Real.exp 0 :=
    Real.continuous_exp.continuousAt
  have hexp0 :
      Filter.Tendsto Real.exp (nhds (0 : ℝ)) (nhds 1) := by
    simpa only [Real.exp_zero] using (ContinuousAt.tendsto hexpAt)
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (Real.cos x) * a))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hexp0.comp harg
  have heq :
      (fun x : ℝ => Real.rpow (Real.cos x) a) =ᶠ[
        nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ => Real.exp (Real.log (Real.cos x) * a)) := by
    filter_upwards [eventually_cos_pos] with x hx
    exact Real.rpow_def_of_pos hx a
  exact Filter.Tendsto.congr' heq.symm hexp

private theorem sixthRoot_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    sixthRoot (x ^ k) = sixthRoot x ^ k := by
  induction k with
  | zero => simp [sixthRoot]
  | succ k ih =>
      unfold sixthRoot at ih ⊢
      rw [pow_succ]
      calc
        Real.rpow (x ^ k * x) (1 / 6 : ℝ) =
            Real.rpow (x ^ k) (1 / 6 : ℝ) *
              Real.rpow x (1 / 6 : ℝ) := by
          exact Real.mul_rpow (pow_nonneg hx k) hx
        _ = Real.rpow x (1 / 6 : ℝ) ^ (k + 1) := by
          rw [ih, pow_succ]

private theorem sixthRoot_pow_six {x : ℝ} (hx : 0 ≤ x) :
    sixthRoot x ^ 6 = x := by
  unfold sixthRoot
  calc
    Real.rpow x (1 / 6 : ℝ) ^ 6 =
        Real.rpow (Real.rpow x (1 / 6 : ℝ)) (6 : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow x (1 / 6 : ℝ)) 6).symm
    _ = Real.rpow x ((1 / 6 : ℝ) * 6) := by
      exact (Real.rpow_mul hx (1 / 6 : ℝ) (6 : ℝ)).symm
    _ = x := by norm_num

private theorem rootSum_eq_of_pos {x : ℝ} (hx : 0 < Real.cos x) :
    rootSum x =
      1 + sixthRoot (Real.cos x) + sixthRoot (Real.cos x) ^ 2 +
      sixthRoot (Real.cos x) ^ 3 + sixthRoot (Real.cos x) ^ 4 +
      sixthRoot (Real.cos x) ^ 5 := by
  norm_num [rootSum, Finset.sum_range_succ,
    sixthRoot_pow (Real.cos x) hx.le]

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rewritten L := by
  unfold HasLimitAtZero
  have heq :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] rewritten := by
    filter_upwards [eventually_cos_pos] with x hx
    have hp :
        Real.sqrt (Real.cos x) =
          cubeRoot (Real.cos x) * sixthRoot (Real.cos x) := by
      unfold cubeRoot sixthRoot
      rw [Real.sqrt_eq_rpow]
      calc
        Real.rpow (Real.cos x) (1 / 2 : ℝ) =
            Real.rpow (Real.cos x) ((1 / 3 : ℝ) + (1 / 6 : ℝ)) := by
              norm_num
        _ = Real.rpow (Real.cos x) (1 / 3 : ℝ) *
              Real.rpow (Real.cos x) (1 / 6 : ℝ) := by
              exact Real.rpow_add hx (1 / 3 : ℝ) (1 / 6 : ℝ)
    unfold original rewritten
    rw [hp]
    ring
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_501/2.txt`; replace the six-term ellipsis by `rootSum`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rationalized L := by
  rw [gap1]
  unfold HasLimitAtZero
  have heq :
      rewritten =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] rationalized := by
    filter_upwards [eventually_cos_pos] with x hx
    have hsum :
        rootSum x =
          1 + sixthRoot (Real.cos x) + sixthRoot (Real.cos x) ^ 2 +
          sixthRoot (Real.cos x) ^ 3 + sixthRoot (Real.cos x) ^ 4 +
          sixthRoot (Real.cos x) ^ 5 :=
      rootSum_eq_of_pos hx
    have hsix : sixthRoot (Real.cos x) ^ 6 = Real.cos x :=
      sixthRoot_pow_six hx.le
    have hgeom :
        (1 - sixthRoot (Real.cos x)) * rootSum x = 1 - Real.cos x := by
      rw [hsum]
      calc
        (1 - sixthRoot (Real.cos x)) *
            (1 + sixthRoot (Real.cos x) + sixthRoot (Real.cos x) ^ 2 +
              sixthRoot (Real.cos x) ^ 3 + sixthRoot (Real.cos x) ^ 4 +
              sixthRoot (Real.cos x) ^ 5) =
            1 - sixthRoot (Real.cos x) ^ 6 := by ring_nf
        _ = 1 - Real.cos x := by rw [hsix]
    have ha : 0 ≤ sixthRoot (Real.cos x) := by
      unfold sixthRoot
      exact (Real.rpow_pos_of_pos hx _).le
    have hrspos : 0 < rootSum x := by
      rw [hsum]
      have h2 : 0 ≤ sixthRoot (Real.cos x) ^ 2 := pow_nonneg ha 2
      have h3 : 0 ≤ sixthRoot (Real.cos x) ^ 3 := pow_nonneg ha 3
      have h4 : 0 ≤ sixthRoot (Real.cos x) ^ 4 := pow_nonneg ha 4
      have h5 : 0 ≤ sixthRoot (Real.cos x) ^ 5 := pow_nonneg ha 5
      linarith
    have hrs : rootSum x ≠ 0 := ne_of_gt hrspos
    have hcancel :
        rootSum x * (cubeRoot (Real.cos x) / rootSum x) =
          cubeRoot (Real.cos x) := by
      field_simp [hrs]
    unfold rewritten rationalized
    rw [← hgeom]
    rw [div_mul_eq_mul_div]
    rw [mul_assoc, hcancel]
    ring_nf
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_501/3.txt`; replace the six-term ellipsis by `rootSum`. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  rw [gap2]
  unfold HasLimitAtZero
  have heq :
      rationalized =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    by_cases hs : Real.sin x = 0
    · simp [rationalized, normalized, hs]
    · have hc2 :
          Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
        convert Real.cos_two_mul (x / 2) using 1 <;> ring
      have hsc := Real.sin_sq_add_cos_sq (x / 2)
      have htrig :
          1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
        nlinarith
      unfold rationalized normalized
      rw [htrig]
      have hden : 4 * (x / 2) ^ 2 = x ^ 2 := by ring
      rw [hden]
      set q : ℝ := cubeRoot (Real.cos x) / rootSum x
      change
        -((2 * Real.sin (x / 2) ^ 2 / Real.sin x ^ 2) * q) =
          -((2 * Real.sin (x / 2) ^ 2 / x ^ 2) *
            (x ^ 2 / Real.sin x ^ 2) * q)
      field_simp [hx0, hs]
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_501/4.txt`. -/
theorem gap4 : HasLimitAtZero normalized (-1 / 12) := by
  unfold HasLimitAtZero
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hzero :
      Filter.Tendsto (fun x : ℝ => x / 2) F (nhds 0) := by
    have hi0 : ContinuousAt (fun x : ℝ => x) 0 := continuousAt_id
    have hi : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) :=
      hi0.mono_left inf_le_left
    simpa [div_eq_mul_inv] using hi.mul_const (2 : ℝ)⁻¹
  have hscale :
      Filter.Tendsto (fun x : ℝ => x / 2) F
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (div_ne_zero hx0 (by norm_num : (2 : ℝ) ≠ 0))
  have hsinc :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x) F (nhds 1) := by
    simpa [F, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hhalf :
      Filter.Tendsto (fun x : ℝ => Real.sin (x / 2) / (x / 2))
        F (nhds 1) :=
    hsinc.comp hscale
  have hcub :
      Filter.Tendsto (fun x : ℝ => cubeRoot (Real.cos x))
        F (nhds 1) := by
    simpa [F, cubeRoot] using tendsto_cos_rpow (1 / 3 : ℝ)
  have ha :
      Filter.Tendsto (fun x : ℝ => sixthRoot (Real.cos x))
        F (nhds 1) := by
    simpa [F, sixthRoot] using tendsto_cos_rpow (1 / 6 : ℝ)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) F (nhds 1) :=
    tendsto_const_nhds
  have hpoly :
      Filter.Tendsto
        (fun x : ℝ =>
          1 + sixthRoot (Real.cos x) + sixthRoot (Real.cos x) ^ 2 +
          sixthRoot (Real.cos x) ^ 3 + sixthRoot (Real.cos x) ^ 4 +
          sixthRoot (Real.cos x) ^ 5)
        F (nhds 6) := by
    convert (((((hone.add ha).add (ha.pow 2)).add (ha.pow 3)).add
      (ha.pow 4)).add (ha.pow 5)) using 1 <;> norm_num
  have hrootEq :
      rootSum =ᶠ[F]
        (fun x : ℝ =>
          1 + sixthRoot (Real.cos x) + sixthRoot (Real.cos x) ^ 2 +
          sixthRoot (Real.cos x) ^ 3 + sixthRoot (Real.cos x) ^ 4 +
          sixthRoot (Real.cos x) ^ 5) := by
    filter_upwards [eventually_cos_pos] with x hx
    exact rootSum_eq_of_pos hx
  have hroot : Filter.Tendsto rootSum F (nhds 6) :=
    Filter.Tendsto.congr' hrootEq.symm hpoly
  have hratio :
      Filter.Tendsto
        (fun x : ℝ => cubeRoot (Real.cos x) / rootSum x)
        F (nhds (1 / 6 : ℝ)) := by
    simpa using hcub.div hroot (by norm_num : (6 : ℝ) ≠ 0)
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        F (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hA :
      Filter.Tendsto
        (fun x : ℝ => (1 / 2 : ℝ) *
          (Real.sin (x / 2) / (x / 2)) ^ 2)
        F (nhds (1 / 2 : ℝ)) := by
    simpa using hconst.mul (hhalf.pow 2)
  have hB :
      Filter.Tendsto
        (fun x : ℝ => (1 : ℝ) / (Real.sin x / x) ^ 2)
        F (nhds (1 : ℝ)) := by
    convert hone.div (hsinc.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0) using 1 <;>
      norm_num
  have hF :
      Filter.Tendsto
        (fun x : ℝ =>
          -((((1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2) *
            ((1 : ℝ) / (Real.sin x / x) ^ 2)) *
            (cubeRoot (Real.cos x) / rootSum x)))
        F (nhds (-1 / 12 : ℝ)) := by
    convert ((hA.mul hB).mul hratio).neg using 1 <;> norm_num
  have heq :
      normalized =ᶠ[F]
        (fun x : ℝ =>
          -((((1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2) *
            ((1 : ℝ) / (Real.sin x / x) ^ 2)) *
            (cubeRoot (Real.cos x) / rootSum x))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    by_cases hs : Real.sin x = 0
    · simp [normalized, hs]
    · unfold normalized
      set q : ℝ := cubeRoot (Real.cos x) / rootSum x
      change
        -((2 * Real.sin (x / 2) ^ 2 / (4 * (x / 2) ^ 2) *
          (x ^ 2 / Real.sin x ^ 2)) * q) =
          -((((1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2) *
            ((1 : ℝ) / (Real.sin x / x) ^ 2)) * q)
      field_simp [hx0, hs]
      ring
  exact Filter.Tendsto.congr' heq.symm hF

/-- Source: `proof_gap/exercise_501/5.txt`. -/
theorem gap5 : HasLimitAtZero original (-1 / 12) := by
  exact (gap3 (-1 / 12)).mpr gap4

end

end ProofGap.Exercise501
