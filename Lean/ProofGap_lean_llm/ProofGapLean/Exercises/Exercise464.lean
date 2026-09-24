import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise464

noncomputable section

def pow32 (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)
def original (x : ℝ) : ℝ :=
  pow32 x * (Real.sqrt (x + 2) - 2 * Real.sqrt (x + 1) + Real.sqrt x)
def conjugate (x : ℝ) : ℝ :=
  Real.sqrt (x + 2) + 2 * Real.sqrt (x + 1) + Real.sqrt x
def rationalized (x : ℝ) : ℝ :=
  original x * conjugate x / conjugate x
def normalized (x : ℝ) : ℝ :=
  -2 /
    ((Real.sqrt (1 + 2 / x) + 2 * Real.sqrt (1 + 1 / x) + 1) *
      (Real.sqrt (1 + 2 / x) + 1 + 1 / x))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_464/1.txt`; multiply by the displayed conjugate. -/
private theorem rationalized_eq_normalized_of_pos {x : ℝ} (hx : 0 < x) :
    rationalized x = normalized x := by
  let u : ℝ := Real.sqrt (1 + 2 / x)
  let v : ℝ := Real.sqrt (1 + 1 / x)
  have hx0 : 0 ≤ x := hx.le
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hu2 : u ^ 2 = 1 + 2 / x := by
    dsimp [u]
    apply Real.sq_sqrt
    positivity
  have hv2 : v ^ 2 = 1 + 1 / x := by
    dsimp [v]
    apply Real.sq_sqrt
    positivity
  have hrewrite2 : x + 2 = x * (1 + 2 / x) := by
    field_simp [hx.ne']
  have hrewrite1 : x + 1 = x * (1 + 1 / x) := by
    field_simp [hx.ne']
  have hsqrt2 : Real.sqrt (x + 2) = Real.sqrt x * u := by
    rw [hrewrite2, Real.sqrt_mul hx0]
  have hsqrt1 : Real.sqrt (x + 1) = Real.sqrt x * v := by
    rw [hrewrite1, Real.sqrt_mul hx0]
  have hpow : pow32 x = x * Real.sqrt x := by
    unfold pow32
    have hr1 : Real.rpow x (1 : ℝ) = x := by
      exact Real.rpow_one x
    have hrhalf : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
      change x ^ (1 / 2 : ℝ) = Real.sqrt x
      exact (Real.sqrt_eq_rpow x).symm
    calc
      Real.rpow x (3 / 2 : ℝ) = Real.rpow x (1 + 1 / 2 : ℝ) := by norm_num
      _ = Real.rpow x 1 * Real.rpow x (1 / 2 : ℝ) :=
        Real.rpow_add hx 1 (1 / 2 : ℝ)
      _ = x * Real.sqrt x := by rw [hr1, hrhalf]
  have hD1 : u + 2 * v + 1 ≠ 0 := by
    apply ne_of_gt
    dsimp [u, v]
    positivity
  have hD2 : u + 1 + 1 / x ≠ 0 := by
    apply ne_of_gt
    dsimp [u]
    positivity
  have hfirst :
      (u - 2 * v + 1) * (u + 2 * v + 1) =
        2 * (u - 1 - 1 / x) := by
    calc
      (u - 2 * v + 1) * (u + 2 * v + 1) =
          u ^ 2 + 2 * u + 1 - 4 * v ^ 2 := by ring
      _ = 2 * (u - 1 - 1 / x) := by
        rw [hu2, hv2]
        ring
  have hsecond :
      (u - 1 - 1 / x) * (u + 1 + 1 / x) = -(1 / x) ^ 2 := by
    calc
      (u - 1 - 1 / x) * (u + 1 + 1 / x) =
          u ^ 2 - (1 + 1 / x) ^ 2 := by ring
      _ = -(1 / x) ^ 2 := by
        rw [hu2]
        ring
  have hid :
      (u - 2 * v + 1) * (u + 2 * v + 1) * (u + 1 + 1 / x) =
        -2 * (1 / x) ^ 2 := by
    calc
      (u - 2 * v + 1) * (u + 2 * v + 1) * (u + 1 + 1 / x) =
          (2 * (u - 1 - 1 / x)) * (u + 1 + 1 / x) := by
            rw [hfirst]
      _ = 2 * ((u - 1 - 1 / x) * (u + 1 + 1 / x)) := by ring
      _ = 2 * (-(1 / x) ^ 2) := by rw [hsecond]
      _ = -2 * (1 / x) ^ 2 := by ring
  have horiginal : original x = x ^ 2 * (u - 2 * v + 1) := by
    rw [original, hpow, hsqrt2, hsqrt1]
    calc
      (x * Real.sqrt x) *
          (Real.sqrt x * u - 2 * (Real.sqrt x * v) + Real.sqrt x) =
          x * Real.sqrt x ^ 2 * (u - 2 * v + 1) := by ring
      _ = x ^ 2 * (u - 2 * v + 1) := by
        rw [hsx2]
        ring
  have hconj : conjugate x ≠ 0 := by
    apply ne_of_gt
    unfold conjugate
    have hs : 0 < Real.sqrt (x + 2) := Real.sqrt_pos.2 (by positivity)
    positivity
  calc
    rationalized x = original x := by simp [rationalized, hconj]
    _ = x ^ 2 * (u - 2 * v + 1) := horiginal
    _ = -2 / ((u + 2 * v + 1) * (u + 1 + 1 / x)) := by
      apply (eq_div_iff (mul_ne_zero hD1 hD2)).2
      calc
        x ^ 2 * (u - 2 * v + 1) *
            ((u + 2 * v + 1) * (u + 1 + 1 / x)) =
            x ^ 2 *
              ((u - 2 * v + 1) * (u + 2 * v + 1) *
                (u + 1 + 1 / x)) := by ring
        _ = x ^ 2 * (-2 * (1 / x) ^ 2) := by rw [hid]
        _ = -2 := by field_simp [hx.ne']
    _ = normalized x := by rfl

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  unfold HasLimitAtPosInfinity
  have heq : original =ᶠ[Filter.atTop] rationalized := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    have hconj : conjugate x ≠ 0 := by
      apply ne_of_gt
      unfold conjugate
      have hs : 0 < Real.sqrt (x + 2) := Real.sqrt_pos.2 (by positivity)
      positivity
    simp [rationalized, hconj]
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_464/2.txt`; perform the second rationalization and normalization. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity rationalized L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  have heq : rationalized =ᶠ[Filter.atTop] normalized := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    exact rationalized_eq_normalized_of_pos hx
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_464/3.txt`. -/
theorem gap3 : HasLimitAtPosInfinity normalized (-1 / 4) := by
  unfold HasLimitAtPosInfinity
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hb2 :
      Filter.Tendsto (fun x : ℝ => 1 + 2 / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
  have hb1 :
      Filter.Tendsto (fun x : ℝ => 1 + 1 / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add hinv)
  have hsqrt :
      Filter.Tendsto Real.sqrt (nhds (1 : ℝ)) (nhds (Real.sqrt 1)) :=
    Real.continuous_sqrt.tendsto 1
  have hs2 :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + 2 / x))
        Filter.atTop (nhds 1) := by
    simpa using Filter.Tendsto.comp hsqrt hb2
  have hs1 :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x))
        Filter.atTop (nhds 1) := by
    simpa using Filter.Tendsto.comp hsqrt hb1
  have hd1 :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sqrt (1 + 2 / x) + 2 * Real.sqrt (1 + 1 / x) + 1)
        Filter.atTop (nhds 4) := by
    convert (hs2.add (tendsto_const_nhds.mul hs1)).add tendsto_const_nhds using 1 <;>
      norm_num
  have hd2 :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 + 2 / x) + 1 + 1 / x)
        Filter.atTop (nhds 2) := by
    convert (hs2.add tendsto_const_nhds).add hinv using 1 <;> norm_num
  have hnum :
      Filter.Tendsto (fun _ : ℝ => (-2 : ℝ)) Filter.atTop (nhds (-2)) :=
    tendsto_const_nhds
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          (-2 : ℝ) /
            ((Real.sqrt (1 + 2 / x) + 2 * Real.sqrt (1 + 1 / x) + 1) *
              (Real.sqrt (1 + 2 / x) + 1 + 1 / x)))
        Filter.atTop (nhds ((-2 : ℝ) / ((4 : ℝ) * 2))) := by
    exact hnum.div (hd1.mul hd2) (by norm_num : (4 : ℝ) * 2 ≠ 0)
  change
    Filter.Tendsto
      (fun x : ℝ =>
        (-2 : ℝ) /
          ((Real.sqrt (1 + 2 / x) + 2 * Real.sqrt (1 + 1 / x) + 1) *
            (Real.sqrt (1 + 2 / x) + 1 + 1 / x)))
      Filter.atTop (nhds ((-1 : ℝ) / 4))
  convert hquot using 1 <;> norm_num

end

end ProofGap.Exercise464
