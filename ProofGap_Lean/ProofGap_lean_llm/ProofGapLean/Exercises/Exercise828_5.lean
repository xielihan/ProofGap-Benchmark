import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_5

noncomputable section

def y (x : ℝ) : ℝ := Real.cbrt x
def quotient (x h : ℝ) : ℝ := (y (x + h) - y x) / h
def rationalized (x h : ℝ) : ℝ :=
  1 / (Real.cbrt ((x + h) ^ 2) + Real.cbrt (x * (x + h)) + Real.cbrt (x ^ 2))

private theorem cbrt_cube_nonneg_local (a : ℝ) (ha : 0 ≤ a) :
    (Real.cbrt a) ^ 3 = a := by
  by_cases h0 : a = 0
  · subst a
    simp [Real.cbrt]
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    have hcbrt : Real.cbrt a = a ^ (1 / 3 : ℝ) := by
      simp [Real.cbrt, hpos, div_eq_mul_inv]
    rw [hcbrt]
    calc
      (a ^ (1 / 3 : ℝ)) ^ 3 =
          (a ^ (1 / 3 : ℝ) * a ^ (1 / 3 : ℝ)) *
            a ^ (1 / 3 : ℝ) := by ring
      _ = a ^ ((1 / 3 : ℝ) + (1 / 3 : ℝ)) *
            a ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hpos]
      _ = a ^ (((1 / 3 : ℝ) + (1 / 3 : ℝ)) + (1 / 3 : ℝ)) := by
        rw [← Real.rpow_add hpos]
      _ = a := by norm_num

private theorem cbrt_mul_nonneg_local (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.cbrt (a * b) = Real.cbrt a * Real.cbrt b := by
  have hc :
      (Real.cbrt (a * b)) ^ 3 =
        (Real.cbrt a * Real.cbrt b) ^ 3 := by
    calc
      (Real.cbrt (a * b)) ^ 3 = a * b :=
        cbrt_cube_nonneg_local (a * b) (mul_nonneg ha hb)
      _ = (Real.cbrt a) ^ 3 * (Real.cbrt b) ^ 3 := by
        rw [cbrt_cube_nonneg_local a ha, cbrt_cube_nonneg_local b hb]
      _ = (Real.cbrt a * Real.cbrt b) ^ 3 := by ring
  have hf :
      (Real.cbrt (a * b) - Real.cbrt a * Real.cbrt b) *
          ((Real.cbrt (a * b)) ^ 2 +
            Real.cbrt (a * b) * (Real.cbrt a * Real.cbrt b) +
            (Real.cbrt a * Real.cbrt b) ^ 2) = 0 := by
    calc
      _ = (Real.cbrt (a * b)) ^ 3 -
          (Real.cbrt a * Real.cbrt b) ^ 3 := by ring
      _ = 0 := by rw [hc]; ring
  rcases mul_eq_zero.mp hf with hd | hq
  · exact sub_eq_zero.mp hd
  · nlinarith
      [sq_nonneg (Real.cbrt (a * b) - Real.cbrt a * Real.cbrt b),
       sq_nonneg (Real.cbrt (a * b) + Real.cbrt a * Real.cbrt b)]

theorem gap1 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x) :
    Δy / h = quotient x h := by
  simpa [quotient] using congrArg (fun z : ℝ => z / h) hΔy
theorem gap2 (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ x + h) (hne : h ≠ 0) :
    quotient x h = rationalized x h := by
  unfold quotient rationalized y
  simp only [pow_two]
  rw [cbrt_mul_nonneg_local (x + h) (x + h) hh hh,
    cbrt_mul_nonneg_local x (x + h) hx hh,
    cbrt_mul_nonneg_local x x hx hx]
  have hprod :
      (Real.cbrt (x + h) - Real.cbrt x) *
          (Real.cbrt (x + h) * Real.cbrt (x + h) +
            Real.cbrt x * Real.cbrt (x + h) +
            Real.cbrt x * Real.cbrt x) = h := by
    calc
      _ = (Real.cbrt (x + h)) ^ 3 - (Real.cbrt x) ^ 3 := by ring
      _ = (x + h) - x := by
        rw [cbrt_cube_nonneg_local (x + h) hh,
          cbrt_cube_nonneg_local x hx]
      _ = h := by ring
  have hden :
      Real.cbrt (x + h) * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt x ≠ 0 := by
    intro hd
    rw [hd, mul_zero] at hprod
    exact hne hprod.symm
  apply (div_eq_iff hne).2
  calc
    Real.cbrt (x + h) - Real.cbrt x =
        h / (Real.cbrt (x + h) * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt x) :=
      (eq_div_iff hden).2 hprod
    _ = (1 / (Real.cbrt (x + h) * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt (x + h) +
          Real.cbrt x * Real.cbrt x)) * h := by ring
theorem gap3 (x h Δy : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ x + h)
    (hne : h ≠ 0) (hΔy : Δy = y (x + h) - y x) :
    Δy / h = rationalized x h := by
  calc
    Δy / h = quotient x h := gap1 x h Δy hΔy
    _ = rationalized x h := gap2 x h hx hh hne
theorem gap4 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (1 / (3 * Real.cbrt (x ^ 2))) x := by
  have hp0 :
      HasDerivAt (fun z : ℝ => z ^ (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1)) x := by
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hrel :
      x ^ ((1 / 3 : ℝ) - 1) * x = x ^ (1 / 3 : ℝ) := by
    calc
      x ^ ((1 / 3 : ℝ) - 1) * x =
          x ^ ((1 / 3 : ℝ) - 1) * x ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = x ^ (((1 / 3 : ℝ) - 1) + 1) := by
        rw [← Real.rpow_add hx]
      _ = x ^ (1 / 3 : ℝ) := by ring_nf
  have hdiv :
      x ^ ((1 / 3 : ℝ) - 1) = x ^ (1 / 3 : ℝ) / x :=
    (eq_div_iff hx.ne').2 hrel
  have hcoef :
      (1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1) =
        x ^ (1 / 3 : ℝ) * (1 / 3 : ℝ) / x := by
    rw [hdiv]
    ring
  have hp :
      HasDerivAt (fun z : ℝ => z ^ (1 / 3 : ℝ))
        (x ^ (1 / 3 : ℝ) * (1 / 3 : ℝ) / x) x := by
    rw [← hcoef]
    exact hp0
  have heq :
      Real.cbrt =ᶠ[nhds x] (fun z : ℝ => z ^ (1 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [Real.cbrt, hz, div_eq_mul_inv]
  have hc :
      HasDerivAt Real.cbrt
        (x ^ (1 / 3 : ℝ) * (1 / 3 : ℝ) / x) x :=
    hp.congr_of_eventuallyEq heq.symm
  have hroot : x ^ (1 / 3 : ℝ) = Real.cbrt x := by
    simp [Real.cbrt, hx, div_eq_mul_inv]
  have hsquare :
      Real.cbrt (x ^ 2) = Real.cbrt x * Real.cbrt x := by
    simpa only [pow_two] using cbrt_mul_nonneg_local x x hx.le hx.le
  have hcube : (Real.cbrt x) ^ 3 = x :=
    cbrt_cube_nonneg_local x hx.le
  have ha0 : Real.cbrt x ≠ 0 := by
    intro ha
    rw [ha] at hcube
    norm_num at hcube
    exact hx.ne' hcube.symm
  unfold y
  convert hc using 1
  rw [hsquare, hroot]
  field_simp [hx.ne', ha0]
  nlinarith [hcube]
theorem gap5 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 {0}ᶜ)
      (nhds (1 / (3 * Real.cbrt (x ^ 2)))) := by
  have hx0 : 0 < x + 0 := by simpa using hx
  have hg :
      HasDerivAt (fun h : ℝ => y (x + h))
        (1 / (3 * Real.cbrt (x ^ 2))) 0 := by
    simpa using
      (gap4 (x + 0) hx0).comp 0 ((hasDerivAt_id 0).const_add x)
  have ht := hg.tendsto_slope
  have hslope :
      slope (fun h : ℝ => y (x + h)) 0 = quotient x := by
    funext h
    simp [slope, quotient, div_eq_inv_mul]
  rw [hslope] at ht
  exact ht
theorem gap6 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (rationalized x) (nhds 0)
      (nhds (1 / (3 * Real.cbrt (x ^ 2)))) := by
  have hnear : ∀ᶠ h : ℝ in nhds 0, 0 ≤ x + h := by
    filter_upwards [eventually_gt_nhds (neg_lt_zero.mpr hx)] with h hh
    linarith
  have heq :
      quotient x =ᶠ[nhdsWithin 0 {0}ᶜ] rationalized x := by
    filter_upwards [hnear.filter_mono inf_le_left, self_mem_nhdsWithin]
      with h hh hmem
    have hne : h ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
    exact gap2 x h hx.le hh hne
  have hr :
      Filter.Tendsto (rationalized x) (nhdsWithin 0 {0}ᶜ)
        (nhds (1 / (3 * Real.cbrt (x ^ 2)))) :=
    (gap5 x hx).congr' heq
  have hval :
      rationalized x 0 = 1 / (3 * Real.cbrt (x ^ 2)) := by
    unfold rationalized
    simp only [add_zero, pow_two]
    congr 1
    ring
  rw [Filter.tendsto_def]
  intro s hs
  have hrs : rationalized x ⁻¹' s ∈ nhdsWithin 0 {0}ᶜ :=
    (Filter.tendsto_def.mp hr) s hs
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hrs with
    ⟨u, hu, hus⟩
  apply Filter.mem_of_superset hu
  intro h hhu
  by_cases hh : h = 0
  · subst h
    change rationalized x 0 ∈ s
    rw [hval]
    exact mem_of_mem_nhds hs
  · apply hus
    refine ⟨hhu, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
theorem gap7 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (1 / (3 * Real.cbrt (x ^ 2))) x := by
  exact gap4 x hx

end
end ProofGap.Exercise828_5
