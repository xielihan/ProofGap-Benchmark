import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2172

noncomputable section

def floorR (x : ℝ) : ℝ := (Int.floor x : ℝ)
def frac (x : ℝ) := x - floorR x
def φ (x : ℝ) :=
  if frac x < 1 / 2 then frac x else 1 - frac x
def primitive (x : ℝ) :=
  x / 4 + 1 / 4 * (frac x - 1 / 2) *
    (1 - 2 * |frac x - 1 / 2|)
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, ∀ x, F x = p x + K}
def RawPiecewiseFormula
    (F : ℝ → ℝ) (C D : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, ∀ x : ℝ, (n : ℝ) ≤ x → x < (n : ℝ) + 1 →
    F x =
      if x < (n : ℝ) + 1 / 2
      then x ^ 2 / 2 - (n : ℝ) * x + C n
      else -x ^ 2 / 2 + ((n : ℝ) + 1) * x + D n
def PiecewiseFormula (F : ℝ → ℝ) (C : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, ∀ x : ℝ, (n : ℝ) ≤ x → x < (n : ℝ) + 1 →
    F x =
      if x < (n : ℝ) + 1 / 2
      then x ^ 2 / 2 - (n : ℝ) * x + C n
      else -x ^ 2 / 2 + ((n : ℝ) + 1) * x -
        ((n : ℝ) + 1 / 2) ^ 2 + C n
def explicitC (n : ℤ) : ℝ := 1 / 4 * (n : ℝ) * (2 * (n : ℝ) + 1)
def ExplicitPiecewiseFormula (F : ℝ → ℝ) : Prop :=
  ∀ n : ℤ, ∀ x : ℝ, (n : ℝ) ≤ x → x < (n : ℝ) + 1 →
    F x =
      if x < (n : ℝ) + 1 / 2
      then x ^ 2 / 2 - (n : ℝ) * x + explicitC n
      else -x ^ 2 / 2 + ((n : ℝ) + 1) * x -
        1 / 4 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1)

private theorem floor_eq_of_unit
    (n : ℤ) (x : ℝ) (h₁ : (n : ℝ) ≤ x) (h₂ : x < (n : ℝ) + 1) :
    Int.floor x = n := by
  rw [Int.floor_eq_iff]
  exact ⟨h₁, h₂⟩

private theorem primitive_piecewise : ExplicitPiecewiseFormula primitive := by
  intro n x hnx hxn
  have hf : Int.floor x = n := floor_eq_of_unit n x hnx hxn
  unfold primitive frac floorR explicitC
  rw [hf]
  by_cases h : x < (n : ℝ) + 1 / 2
  · rw [if_pos h, abs_of_neg (by linarith : x - (n : ℝ) - 1 / 2 < 0)]
    ring
  · rw [if_neg h, abs_of_nonneg (by linarith : 0 ≤ x - (n : ℝ) - 1 / 2)]
    ring

private theorem hasDerivAt_mul_abs_sub (a : ℝ) :
    HasDerivAt (fun y : ℝ => (y - a) * |y - a|) 0 a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hid : ContinuousAt (fun y : ℝ => y) a := continuousAt_id
  have hconst : ContinuousAt (fun _ : ℝ => a) a := continuousAt_const
  have habs : ContinuousAt (fun y : ℝ => |y - a|) a :=
    (hid.sub hconst).abs
  have hcont :
      Tendsto (fun y : ℝ => |y - a|) (nhds a)
        (nhds ((fun y : ℝ => |y - a|) a)) := by
    exact habs
  have hcont0 :
      Tendsto (fun y : ℝ => |y - a|) (nhds a) (nhds 0) := by
    simpa only [sub_self, abs_zero] using hcont
  have ht :
      Tendsto (fun y : ℝ => |y - a|) (nhdsWithin a {a}ᶜ) (nhds 0) :=
    hcont0.mono_left inf_le_left
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hya : y ≠ a := by simpa using hy
  have hsub : y - a ≠ 0 := sub_ne_zero.mpr hya
  simp [slope]
  field_simp [hsub] <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (φ x) x := by
  set n : ℤ := Int.floor x with hn
  clear_value n
  have hnx : (n : ℝ) ≤ x := by
    rw [hn]
    exact Int.floor_le x
  have hxn : x < (n : ℝ) + 1 := by
    rw [hn]
    exact Int.lt_floor_add_one x
  have hfloor : Int.floor x = n := hn.symm
  have hfloor_n : Int.floor (n : ℝ) = n := by
    apply floor_eq_of_unit n
    · exact le_rfl
    · linarith
  have hfrac_n : frac (n : ℝ) = 0 := by
    unfold frac floorR
    rw [hfloor_n]
    ring
  have hfloor_mid : Int.floor ((n : ℝ) + 1 / 2) = n := by
    apply floor_eq_of_unit n
    · linarith
    · linarith
  have hfrac_mid : frac ((n : ℝ) + 1 / 2) = 1 / 2 := by
    unfold frac floorR
    rw [hfloor_mid]
    ring
  by_cases hleft : x = (n : ℝ)
  · have hev :
        primitive =ᶠ[nhds (n : ℝ)]
          (fun y : ℝ => (n : ℝ) / 4 +
            (y - (n : ℝ)) * |y - (n : ℝ)| / 2) := by
      filter_upwards [Ioo_mem_nhds (by linarith : (n : ℝ) - 1 / 2 < (n : ℝ))
        (by linarith : (n : ℝ) < (n : ℝ) + 1 / 2)] with y hy
      by_cases hyn : y < (n : ℝ)
      · have hmem₁ : ((n - 1 : ℤ) : ℝ) ≤ y := by
          push_cast
          linarith [hy.1]
        have hmem₂ : y < ((n - 1 : ℤ) : ℝ) + 1 := by
          push_cast
          linarith
        rw [primitive_piecewise (n - 1) y hmem₁ hmem₂]
        have hbranch : ¬y < ((n - 1 : ℤ) : ℝ) + 1 / 2 := by
          push_cast
          linarith [hy.1]
        rw [if_neg hbranch, abs_of_neg (by linarith : y - (n : ℝ) < 0)]
        push_cast
        ring
      · have hmem₁ : (n : ℝ) ≤ y := by linarith
        have hmem₂ : y < (n : ℝ) + 1 := by linarith [hy.2]
        rw [primitive_piecewise n y hmem₁ hmem₂]
        rw [if_pos (by linarith [hy.2] : y < (n : ℝ) + 1 / 2)]
        rw [abs_of_nonneg (by linarith : 0 ≤ y - (n : ℝ))]
        unfold explicitC
        ring
    have hd : HasDerivAt
        (fun y : ℝ => (n : ℝ) / 4 +
          (y - (n : ℝ)) * |y - (n : ℝ)| / 2) 0 (n : ℝ) := by
      convert (hasDerivAt_const (n : ℝ) ((n : ℝ) / 4)).add
        ((hasDerivAt_mul_abs_sub (n : ℝ)).div_const 2) using 1 <;>
        simp [id] <;> ring
    have hp : HasDerivAt primitive 0 (n : ℝ) :=
      hev.hasDerivAt_iff.mpr hd
    have hphi : φ (n : ℝ) = 0 := by
      norm_num [φ, hfrac_n]
    rw [hleft, hphi]
    exact hp
  · have hxgt : (n : ℝ) < x := lt_of_le_of_ne hnx (Ne.symm hleft)
    by_cases hmid : x = (n : ℝ) + 1 / 2
    · have hev :
          primitive =ᶠ[nhds ((n : ℝ) + 1 / 2)]
            (fun y : ℝ =>
              ((n : ℝ) + 1 / 2) / 4 +
              (y - ((n : ℝ) + 1 / 2)) / 2 -
              (y - ((n : ℝ) + 1 / 2)) *
                |y - ((n : ℝ) + 1 / 2)| / 2) := by
        filter_upwards [Ioo_mem_nhds (by linarith : (n : ℝ) < (n : ℝ) + 1 / 2)
          (by linarith : (n : ℝ) + 1 / 2 < (n : ℝ) + 1)] with y hy
        rw [primitive_piecewise n y (le_of_lt hy.1) hy.2]
        by_cases hyhalf : y < (n : ℝ) + 1 / 2
        · rw [if_pos hyhalf,
            abs_of_neg (by linarith : y - ((n : ℝ) + 1 / 2) < 0)]
          unfold explicitC
          ring
        · rw [if_neg hyhalf,
            abs_of_nonneg (by linarith : 0 ≤ y - ((n : ℝ) + 1 / 2))]
          ring
      have hq := hasDerivAt_mul_abs_sub ((n : ℝ) + 1 / 2)
      have hd : HasDerivAt
          (fun y : ℝ =>
            ((n : ℝ) + 1 / 2) / 4 +
            (y - ((n : ℝ) + 1 / 2)) / 2 -
            (y - ((n : ℝ) + 1 / 2)) *
              |y - ((n : ℝ) + 1 / 2)| / 2)
          (1 / 2) ((n : ℝ) + 1 / 2) := by
        convert ((hasDerivAt_const ((n : ℝ) + 1 / 2)
          (((n : ℝ) + 1 / 2) / 4)).add
          (((hasDerivAt_id ((n : ℝ) + 1 / 2)).sub_const
            ((n : ℝ) + 1 / 2)).div_const 2)).sub
          (hq.div_const 2) using 1 <;> simp [id] <;> ring
      have hp := hev.hasDerivAt_iff.mpr hd
      have hphi : φ ((n : ℝ) + 1 / 2) = 1 / 2 := by
        norm_num [φ, hfrac_mid]
      rw [hmid, hphi]
      exact hp
    · by_cases hlo : x < (n : ℝ) + 1 / 2
      · have hev : primitive =ᶠ[nhds x]
            (fun y : ℝ => y ^ 2 / 2 - (n : ℝ) * y + explicitC n) := by
          filter_upwards [Ioo_mem_nhds hxgt hlo] with y hy
          rw [primitive_piecewise n y (le_of_lt hy.1)
            (lt_trans hy.2 (by linarith))]
          rw [if_pos hy.2]
        have hd : HasDerivAt
            (fun y : ℝ => y ^ 2 / 2 - (n : ℝ) * y + explicitC n)
            (x - (n : ℝ)) x := by
          convert ((((hasDerivAt_id x).pow 2).div_const 2).sub
            ((hasDerivAt_const x (n : ℝ)).mul (hasDerivAt_id x))).add_const
            (explicitC n) using 1 <;> simp [id] <;> ring
        have hp := hev.hasDerivAt_iff.mpr hd
        have hfrac : frac x < 1 / 2 := by
          simp only [frac, floorR, hfloor]
          linarith
        have hphi : φ x = x - (n : ℝ) := by
          rw [φ, if_pos hfrac]
          simp only [frac, floorR, hfloor]
        rw [hphi]
        exact hp
      · have hhi : (n : ℝ) + 1 / 2 < x :=
          lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm hmid)
        have hev : primitive =ᶠ[nhds x]
            (fun y : ℝ => -y ^ 2 / 2 + ((n : ℝ) + 1) * y -
              1 / 4 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) := by
          filter_upwards [Ioo_mem_nhds hhi hxn] with y hy
          rw [primitive_piecewise n y (by linarith [hy.1]) hy.2]
          rw [if_neg (by linarith [hy.1])]
        have hd : HasDerivAt
            (fun y : ℝ => -y ^ 2 / 2 + ((n : ℝ) + 1) * y -
              1 / 4 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1))
            ((n : ℝ) + 1 - x) x := by
          convert (((((hasDerivAt_id x).pow 2).neg).div_const 2).add
            ((hasDerivAt_const x ((n : ℝ) + 1)).mul (hasDerivAt_id x))).sub_const
            (1 / 4 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) using 1 <;>
            simp [id] <;> ring
        have hp := hev.hasDerivAt_iff.mpr hd
        have hfrac : ¬frac x < 1 / 2 := by
          simp only [frac, floorR, hfloor]
          linarith
        have hphi : φ x = (n : ℝ) + 1 - x := by
          rw [φ, if_neg hfrac]
          simp only [frac, floorR, hfloor]
          ring
        rw [hphi]
        exact hp

private theorem continuousAt_of_eventuallyEq
    {f g : ℝ → ℝ} {x : ℝ}
    (hfg : f =ᶠ[nhds x] g) (hpoint : f x = g x)
    (hg : ContinuousAt g x) : ContinuousAt f x := by
  change Tendsto f (nhds x) (nhds (f x))
  rw [hpoint]
  have htg : Tendsto g (nhds x) (nhds (g x)) := hg
  exact htg.congr' hfg.symm

private theorem continuous_phi : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro x
  set n : ℤ := Int.floor x with hn
  clear_value n
  have hnx : (n : ℝ) ≤ x := by
    rw [hn]
    exact Int.floor_le x
  have hxn : x < (n : ℝ) + 1 := by
    rw [hn]
    exact Int.lt_floor_add_one x
  have hfloor : Int.floor x = n := hn.symm
  have hfloor_n : Int.floor (n : ℝ) = n := by
    apply floor_eq_of_unit n
    · exact le_rfl
    · linarith
  have hfrac_n : frac (n : ℝ) = 0 := by
    unfold frac floorR
    rw [hfloor_n]
    ring
  have hfloor_mid : Int.floor ((n : ℝ) + 1 / 2) = n := by
    apply floor_eq_of_unit n
    · linarith
    · linarith
  have hfrac_mid : frac ((n : ℝ) + 1 / 2) = 1 / 2 := by
    unfold frac floorR
    rw [hfloor_mid]
    ring
  by_cases hleft : x = (n : ℝ)
  · have hev : φ =ᶠ[nhds (n : ℝ)] (fun y : ℝ => |y - (n : ℝ)|) := by
      filter_upwards [Ioo_mem_nhds (by linarith : (n : ℝ) - 1 / 2 < (n : ℝ))
        (by linarith : (n : ℝ) < (n : ℝ) + 1 / 2)] with y hy
      by_cases hyn : y < (n : ℝ)
      · have hf : Int.floor y = n - 1 := by
          apply floor_eq_of_unit
          · push_cast
            linarith [hy.1]
          · push_cast
            linarith
        have hb : ¬frac y < 1 / 2 := by
          simp [frac, floorR, hf]
          push_cast
          linarith [hy.1]
        change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
          |y - (n : ℝ)|
        rw [if_neg hb]
        simp [frac, floorR, hf, abs_of_neg (by linarith : y - (n : ℝ) < 0)]
        push_cast
        ring
      · have hf : Int.floor y = n :=
          floor_eq_of_unit n y (by linarith) (by linarith [hy.2])
        have hb : frac y < 1 / 2 := by
          simp [frac, floorR, hf]
          linarith [hy.2]
        change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
          |y - (n : ℝ)|
        rw [if_pos hb]
        simp [frac, floorR, hf,
          abs_of_nonneg (by linarith : 0 ≤ y - (n : ℝ))]
    rw [hleft]
    refine continuousAt_of_eventuallyEq hev ?_ ?_
    · calc
        φ (n : ℝ) = 0 := by norm_num [φ, hfrac_n]
        _ = |(n : ℝ) - (n : ℝ)| := by simp
    · have hid : ContinuousAt (fun y : ℝ => y) (n : ℝ) := continuousAt_id
      have hconst : ContinuousAt (fun _ : ℝ => (n : ℝ)) (n : ℝ) :=
        continuousAt_const
      exact (hid.sub hconst).abs
  · have hxgt : (n : ℝ) < x := lt_of_le_of_ne hnx (Ne.symm hleft)
    by_cases hmid : x = (n : ℝ) + 1 / 2
    · have hev : φ =ᶠ[nhds ((n : ℝ) + 1 / 2)]
          (fun y : ℝ => 1 / 2 - |y - ((n : ℝ) + 1 / 2)|) := by
        filter_upwards [Ioo_mem_nhds (by linarith : (n : ℝ) < (n : ℝ) + 1 / 2)
          (by linarith : (n : ℝ) + 1 / 2 < (n : ℝ) + 1)] with y hy
        have hf : Int.floor y = n :=
          floor_eq_of_unit n y (le_of_lt hy.1) hy.2
        by_cases hb : y < (n : ℝ) + 1 / 2
        · have hfrac : frac y < 1 / 2 := by
            simp [frac, floorR, hf]
            linarith
          change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
            1 / 2 - |y - ((n : ℝ) + 1 / 2)|
          rw [if_pos hfrac,
            abs_of_neg (by linarith : y - ((n : ℝ) + 1 / 2) < 0)]
          simp [frac, floorR, hf] <;> ring
        · have hfrac : ¬frac y < 1 / 2 := by
            simp [frac, floorR, hf]
            linarith
          change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
            1 / 2 - |y - ((n : ℝ) + 1 / 2)|
          rw [if_neg hfrac,
            abs_of_nonneg (by linarith : 0 ≤ y - ((n : ℝ) + 1 / 2))]
          simp [frac, floorR, hf] <;> ring
      rw [hmid]
      refine continuousAt_of_eventuallyEq hev ?_ ?_
      · calc
          φ ((n : ℝ) + 1 / 2) = 1 / 2 := by
            norm_num [φ, hfrac_mid]
          _ = 1 / 2 -
              |((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2)| := by simp
      · have hid : ContinuousAt (fun y : ℝ => y) ((n : ℝ) + 1 / 2) :=
          continuousAt_id
        have hcenter :
            ContinuousAt (fun _ : ℝ => (n : ℝ) + 1 / 2)
              ((n : ℝ) + 1 / 2) := continuousAt_const
        have hhalf :
            ContinuousAt (fun _ : ℝ => (1 / 2 : ℝ))
              ((n : ℝ) + 1 / 2) := continuousAt_const
        exact hhalf.sub ((hid.sub hcenter).abs)
    · by_cases hlo : x < (n : ℝ) + 1 / 2
      · have hev : φ =ᶠ[nhds x] (fun y : ℝ => y - (n : ℝ)) := by
          filter_upwards [Ioo_mem_nhds hxgt hlo] with y hy
          have hf : Int.floor y = n :=
            floor_eq_of_unit n y (le_of_lt hy.1) (by linarith [hy.2])
          have hb : frac y < 1 / 2 := by
            simp [frac, floorR, hf]
            linarith [hy.2]
          change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
            y - (n : ℝ)
          rw [if_pos hb]
          simp [frac, floorR, hf]
        have hfracx : frac x = x - (n : ℝ) := by
          simp only [frac, floorR, hfloor]
        have hb : frac x < 1 / 2 := by
          rw [hfracx]
          linarith
        have hpoint : φ x = x - (n : ℝ) := by
          rw [φ, if_pos hb, hfracx]
        have hid : ContinuousAt (fun y : ℝ => y) x := continuousAt_id
        have hconst : ContinuousAt (fun _ : ℝ => (n : ℝ)) x :=
          continuousAt_const
        exact continuousAt_of_eventuallyEq hev hpoint (hid.sub hconst)
      · have hhi : (n : ℝ) + 1 / 2 < x :=
          lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm hmid)
        have hev : φ =ᶠ[nhds x] (fun y : ℝ => (n : ℝ) + 1 - y) := by
          filter_upwards [Ioo_mem_nhds hhi hxn] with y hy
          have hf : Int.floor y = n :=
            floor_eq_of_unit n y (by linarith [hy.1]) hy.2
          have hb : ¬frac y < 1 / 2 := by
            simp [frac, floorR, hf]
            linarith [hy.1]
          change (if frac y < (1 / 2 : ℝ) then frac y else 1 - frac y) =
            (n : ℝ) + 1 - y
          rw [if_neg hb]
          simp [frac, floorR, hf]
          ring
        have hfracx : frac x = x - (n : ℝ) := by
          simp only [frac, floorR, hfloor]
        have hb : ¬frac x < 1 / 2 := by
          rw [hfracx]
          linarith
        have hpoint : φ x = (n : ℝ) + 1 - x := by
          rw [φ, if_neg hb, hfracx]
          ring
        have hconst : ContinuousAt (fun _ : ℝ => (n : ℝ) + 1) x :=
          continuousAt_const
        have hid : ContinuousAt (fun y : ℝ => y) x := continuousAt_id
        exact continuousAt_of_eventuallyEq hev hpoint (hconst.sub hid)

theorem gap1 :
    Continuous φ := by
  exact continuous_phi
theorem gap2 :
    ∃ F : ℝ → ℝ, Differentiable ℝ F ∧ Continuous (deriv F) ∧
      ∀ x, HasDerivAt F (φ x) x := by
  refine ⟨primitive, fun x => (hasDerivAt_primitive x).differentiableAt, ?_, hasDerivAt_primitive⟩
  have hd : deriv primitive = φ :=
    funext fun x => (hasDerivAt_primitive x).deriv
  rw [hd]
  exact continuous_phi
theorem gap3 :
    ∃ F : ℝ → ℝ, ∃ C D : ℤ → ℝ, RawPiecewiseFormula F C D := by
  refine ⟨primitive, explicitC,
    fun n => explicitC n - ((n : ℝ) + 1 / 2) ^ 2, ?_⟩
  intro n x hnx hxn
  rw [primitive_piecewise n x hnx hxn]
  split <;> unfold explicitC <;> ring
theorem gap4 :
    ∃ C D : ℤ → ℝ,
      ∀ n, D n = C n - ((n : ℝ) + 1 / 2) ^ 2 := by
  refine ⟨fun n => ((n : ℝ) + 1 / 2) ^ 2, fun _ => 0, ?_⟩
  intro n
  ring
theorem gap5 :
    ∃ F : ℝ → ℝ, ∃ C : ℤ → ℝ, PiecewiseFormula F C := by
  refine ⟨primitive, explicitC, ?_⟩
  intro n x hnx hxn
  rw [primitive_piecewise n x hnx hxn]
  split <;> unfold explicitC <;> ring
theorem gap6 :
    ∃ C : ℤ → ℝ,
      ∀ n, C (n + 1) = C n + (n : ℝ) + 3 / 4 := by
  refine ⟨explicitC, ?_⟩
  intro n
  simp [explicitC]
  ring
theorem gap7 :
    ∃ F ∈ Antiderivatives φ, F 0 = 0 := by
  refine ⟨primitive, ?_, ?_⟩
  · intro x
    exact hasDerivAt_primitive x
  · norm_num [primitive, frac, floorR]
theorem gap8 :
    ∃ F : ℝ → ℝ, ∃ C : ℤ → ℝ,
      PiecewiseFormula F C ∧ F 0 = C 0 := by
  rcases gap5 with ⟨F, C, hF⟩
  refine ⟨F, C, hF, ?_⟩
  simpa using hF 0 0 (by norm_num) (by norm_num)
theorem gap9 :
    ∃ C : ℤ → ℝ, C 0 = 0 := by
  exact ⟨fun _ => 0, rfl⟩
theorem gap10 :
    ∃ C : ℤ → ℝ, ∀ n, C n = explicitC n := by
  exact ⟨explicitC, fun _ => rfl⟩
theorem gap11 :
    ∃ F : ℝ → ℝ, ExplicitPiecewiseFormula F := by
  exact ⟨primitive, primitive_piecewise⟩
theorem gap12 :
    ∃ F : ℝ → ℝ, ∀ x, F x = primitive x := by
  exact ⟨primitive, fun _ => rfl⟩
theorem gap13 :
    Antiderivatives φ = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    refine ⟨F 0 - primitive 0, ?_⟩
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun y => (hF y).differentiableAt.sub
        (hasDerivAt_primitive y).differentiableAt
    have hzero : ∀ y, deriv (fun z => F z - primitive z) y = 0 := by
      intro y
      change deriv (F - primitive) y = 0
      simpa using ((hF y).sub (hasDerivAt_primitive y)).deriv
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith [hc]
  · rintro ⟨K, hK⟩
    intro x
    have hEq : F = fun y => primitive y + K := by
      funext y
      exact hK y
    rw [hEq]
    exact (hasDerivAt_primitive x).add_const K

end
end ProofGap.Exercise2172
