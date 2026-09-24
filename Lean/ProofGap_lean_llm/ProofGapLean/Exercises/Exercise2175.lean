import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2175
noncomputable section

open Set Filter

def f (x : ℝ) : ℝ :=
  if x < 0 then 1 else if x ≤ 1 then x + 1 else 2 * x

def leftPrimitive (x : ℝ) : ℝ := x
def middlePrimitive (x : ℝ) : ℝ := x ^ 2 / 2 + x
def rightPrimitive (x : ℝ) : ℝ := x ^ 2

def primitive (x : ℝ) : ℝ :=
  if x < 0 then x
  else if x ≤ 1 then x ^ 2 / 2 + x
  else x ^ 2 + 1 / 2

def FamilyOn (U : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ U, HasDerivAt F (g x) x}

def TranslatesOn (U : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem hasDerivAt_ite_of_eq
    (p : ℝ → Prop) [DecidablePred p]
    {u v : ℝ → ℝ} {u' x : ℝ}
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v u' x)
    (huv : u x = v x) :
    HasDerivAt (fun y => if p y then u y else v y) u' x := by
  rw [hasDerivAt_iff_tendsto_slope] at hu hv ⊢
  have hslope :
      slope (fun y => if p y then u y else v y) x =
        fun y => if p y then slope u x y else slope v x y := by
    funext y
    by_cases hy : p y <;> by_cases hx : p x <;>
      simp [slope, hy, hx, huv]
  rw [hslope]
  intro s hs
  have hu' := hu hs
  have hv' := hv hs
  change ∀ᶠ y in nhdsWithin x {x}ᶜ, slope u x y ∈ s at hu'
  change ∀ᶠ y in nhdsWithin x {x}ᶜ, slope v x y ∈ s at hv'
  change ∀ᶠ y in nhdsWithin x {x}ᶜ,
    (if p y then slope u x y else slope v x y) ∈ s
  filter_upwards [hu', hv'] with y hyu hyv
  by_cases hy : p y
  · simpa [hy] using hyu
  · simpa [hy] using hyv

private theorem familyOn_eq_translatesOn
    {U : Set ℝ} {g p : ℝ → ℝ}
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x)
    (hne : U.Nonempty) :
    FamilyOn U g = TranslatesOn U p := by
  ext F
  change (∀ x ∈ U, HasDerivAt F (g x) x) ↔
    ∃ C : ℝ, ∀ x ∈ U, F x = p x + C
  constructor
  · intro hF
    rcases hne with ⟨a, ha⟩
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) U := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      simpa using ((hF x hx).sub (hp x hx)).deriv
    refine ⟨F a - p a, ?_⟩
    intro x hx
    have heq : F x - p x = F a - p a :=
      hUo.is_const_of_deriv_eq_zero hUc hdiff hzero hx ha
    linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [hUo.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem middlePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt middlePrimitive (x + 1) x := by
  unfold middlePrimitive
  convert ((((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2).add
    (hasDerivAt_id x)) using 1 <;>
    norm_num <;> try ring
  funext y
  simp <;> ring

private theorem rightPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt rightPrimitive (2 * x) x := by
  unfold rightPrimitive
  convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
    norm_num <;> try ring
  funext y
  simp <;> ring

private theorem primitive_hasDerivAt (x : ℝ) : HasDerivAt primitive (f x) x := by
  have hmid : ∀ z : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2 / 2 + y) (z + 1) z := by
    intro z
    simpa [middlePrimitive] using middlePrimitive_hasDerivAt z
  have hright : ∀ z : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2) (2 * z) z := by
    intro z
    simpa [rightPrimitive] using (rightPrimitive_hasDerivAt z).add_const (1 / 2)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : primitive =ᶠ[nhds x] (fun y : ℝ => y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hylt : y < 0 := hy
      simp [primitive, hylt]
    have hd := (hasDerivAt_id x).congr_of_eventuallyEq heq
    simpa [f, hx] using hd
  · let q : ℝ → ℝ := fun y =>
      if y ≤ 1 then y ^ 2 / 2 + y else y ^ 2 + 1 / 2
    have hqeq : q =ᶠ[nhds (0 : ℝ)] (fun y : ℝ => y ^ 2 / 2 + y) := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
      have hylt : y < 1 := hy
      simp [q, hylt.le]
    have hm0 : HasDerivAt (fun y : ℝ => y ^ 2 / 2 + y) 1 0 := by
      simpa using hmid 0
    have hq : HasDerivAt q 1 0 :=
      hm0.congr_of_eventuallyEq hqeq
    have hout : HasDerivAt (fun y : ℝ => if y < 0 then y else q y) 1 0 :=
      hasDerivAt_ite_of_eq (p := fun y : ℝ => y < 0)
        (hasDerivAt_id 0) hq (by simp [q])
    have hf0 : f 0 = 1 := by
      norm_num [f]
    rw [hf0]
    change HasDerivAt
      (fun y : ℝ =>
        if y < 0 then y
        else if y ≤ 1 then y ^ 2 / 2 + y else y ^ 2 + 1 / 2) 1 0
    simpa [q] using hout
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have heq : primitive =ᶠ[nhds x]
          (fun y : ℝ => y ^ 2 / 2 + y) := by
        filter_upwards [Ioo_mem_nhds hx hx1] with y hy
        have hy0 : 0 < y := hy.1
        have hy1 : y < 1 := hy.2
        simp [primitive, not_lt.mpr hy0.le, hy1.le]
      have hd := (hmid x).congr_of_eventuallyEq heq
      simpa [f, not_lt.mpr hx.le, hx1.le] using hd
    · let q : ℝ → ℝ := fun y =>
        if y ≤ 1 then y ^ 2 / 2 + y else y ^ 2 + 1 / 2
      have hm1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2 + y) 2 1 := by
        convert hmid 1 using 1 <;> norm_num
      have hr1 : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2) 2 1 := by
        simpa using hright 1
      have hq : HasDerivAt q 2 1 := by
        dsimp [q]
        exact hasDerivAt_ite_of_eq (p := fun y : ℝ => y ≤ 1)
          hm1 hr1 (by norm_num)
      have heq : primitive =ᶠ[nhds (1 : ℝ)] q := by
        filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
        have hygt : 0 < y := hy
        simp [primitive, q, not_lt.mpr hygt.le]
      have hd := hq.congr_of_eventuallyEq heq
      have hf1 : f 1 = 2 := by
        norm_num [f]
      rw [hf1]
      exact hd
    · have heq : primitive =ᶠ[nhds x]
          (fun y : ℝ => y ^ 2 + 1 / 2) := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy
        have hygt : 1 < y := hy
        have h0 : ¬y < 0 := not_lt.mpr (le_trans (by norm_num) hygt.le)
        have h1 : ¬y ≤ 1 := not_le.mpr hygt
        simp [primitive, h0, h1]
      have hd := (hright x).congr_of_eventuallyEq heq
      have h0 : ¬x < 0 := not_lt.mpr (le_trans (by norm_num) hx1.le)
      have h1 : ¬x ≤ 1 := not_le.mpr hx1
      simpa [f, h0, h1] using hd

theorem gap1 :
    FamilyOn (Set.Iio (0 : ℝ)) f =
      FamilyOn (Set.Iio (0 : ℝ)) (fun _ => 1) := by
  ext F
  change (∀ x ∈ Set.Iio (0 : ℝ), HasDerivAt F (f x) x) ↔
    ∀ x ∈ Set.Iio (0 : ℝ), HasDerivAt F 1 x
  constructor <;> intro h x hx
  · have hxlt : x < 0 := hx
    simpa [f, hxlt] using h x hx
  · have hxlt : x < 0 := hx
    simpa [f, hxlt] using h x hx

theorem gap2 :
    FamilyOn (Set.Iio (0 : ℝ)) (fun _ => 1) =
      TranslatesOn (Set.Iio (0 : ℝ)) leftPrimitive := by
  apply familyOn_eq_translatesOn isOpen_Iio isPreconnected_Iio
  · intro x hx
    simpa [leftPrimitive] using hasDerivAt_id x
  · exact ⟨-1, by norm_num⟩

theorem gap3 :
    FamilyOn (Set.Iio (0 : ℝ)) f =
      TranslatesOn (Set.Iio (0 : ℝ)) leftPrimitive := by
  rw [gap1, gap2]

theorem gap4 :
    FamilyOn (Set.Ioo (0 : ℝ) 1) f =
      FamilyOn (Set.Ioo (0 : ℝ) 1) (fun x => x + 1) := by
  ext F
  change (∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) ↔
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (x + 1) x
  constructor <;> intro h x hx
  · have hx0 : ¬x < 0 := not_lt.mpr hx.1.le
    have hx1 : x ≤ 1 := hx.2.le
    simpa [f, hx0, hx1] using h x hx
  · have hx0 : ¬x < 0 := not_lt.mpr hx.1.le
    have hx1 : x ≤ 1 := hx.2.le
    simpa [f, hx0, hx1] using h x hx

theorem gap5 :
    FamilyOn (Set.Ioo (0 : ℝ) 1) (fun x => x + 1) =
      TranslatesOn (Set.Ioo (0 : ℝ) 1) middlePrimitive := by
  apply familyOn_eq_translatesOn isOpen_Ioo isPreconnected_Ioo
  · intro x hx
    exact middlePrimitive_hasDerivAt x
  · exact ⟨1 / 2, by norm_num⟩

theorem gap6 :
    FamilyOn (Set.Ioo (0 : ℝ) 1) f =
      TranslatesOn (Set.Ioo (0 : ℝ) 1) middlePrimitive := by
  rw [gap4, gap5]

theorem gap7 :
    FamilyOn (Set.Ioi (1 : ℝ)) f =
      FamilyOn (Set.Ioi (1 : ℝ)) (fun x => 2 * x) := by
  ext F
  change (∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F (f x) x) ↔
    ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F (2 * x) x
  constructor <;> intro h x hx
  · have hxgt : 1 < x := hx
    have h0 : ¬x < 0 := not_lt.mpr (le_trans (by norm_num) hxgt.le)
    have h1 : ¬x ≤ 1 := not_le.mpr hxgt
    simpa [f, h0, h1] using h x hx
  · have hxgt : 1 < x := hx
    have h0 : ¬x < 0 := not_lt.mpr (le_trans (by norm_num) hxgt.le)
    have h1 : ¬x ≤ 1 := not_le.mpr hxgt
    simpa [f, h0, h1] using h x hx

theorem gap8 :
    FamilyOn (Set.Ioi (1 : ℝ)) (fun x => 2 * x) =
      TranslatesOn (Set.Ioi (1 : ℝ)) rightPrimitive := by
  apply familyOn_eq_translatesOn isOpen_Ioi isPreconnected_Ioi
  · intro x hx
    exact rightPrimitive_hasDerivAt x
  · exact ⟨2, by norm_num⟩

theorem gap9 :
    FamilyOn (Set.Ioi (1 : ℝ)) f =
      TranslatesOn (Set.Ioi (1 : ℝ)) rightPrimitive := by
  rw [gap7, gap8]

theorem gap10 :
    ∃ F : ℝ → ℝ, F = primitive ∧ F 0 = 0 := by
  refine ⟨primitive, rfl, ?_⟩
  norm_num [primitive]

theorem gap11 :
    ∃ F : ℝ → ℝ, F = primitive ∧
      Tendsto F (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (F 0)) := by
  refine ⟨primitive, rfl, ?_⟩
  have heq : primitive =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)] (fun x : ℝ => x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxlt : x < 0 := hx
    simp [primitive, hxlt]
  have hid : Tendsto (fun x : ℝ => x) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hval : primitive 0 = 0 := by
    norm_num [primitive]
  rw [hval]
  exact (tendsto_congr' heq).2 hid

theorem gap12 :
    ∃ F : ℝ → ℝ, F = primitive ∧
      Tendsto F (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (F 1)) := by
  refine ⟨primitive, rfl, ?_⟩
  have heq : primitive =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun x : ℝ => x ^ 2 + 1 / 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxgt : 1 < x := hx
    have h0 : ¬x < 0 := not_lt.mpr (le_trans (by norm_num) hxgt.le)
    have h1 : ¬x ≤ 1 := not_le.mpr hxgt
    simp [primitive, h0, h1]
  have hfull : Tendsto (fun x : ℝ => x ^ 2 + 1 / 2) (nhds 1)
      (nhds ((1 : ℝ) ^ 2 + 1 / 2)) :=
    (continuousAt_id.pow 2).add continuousAt_const
  have hwithin : Tendsto (fun x : ℝ => x ^ 2 + 1 / 2)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds ((1 : ℝ) ^ 2 + 1 / 2)) :=
    hfull.mono_left inf_le_left
  have hval : primitive 1 = (1 : ℝ) ^ 2 + 1 / 2 := by
    norm_num [primitive]
  rw [hval]
  exact (tendsto_congr' heq).2 hwithin

theorem gap13 :
    ∃ F : ℝ → ℝ, ∀ x,
      F x =
        if x < 0 then x
        else if x ≤ 1 then x ^ 2 / 2 + x
        else x ^ 2 + 1 / 2 := by
  exact ⟨primitive, fun x => rfl⟩

theorem gap14 :
    FamilyOn Set.univ f = TranslatesOn Set.univ primitive := by
  apply familyOn_eq_translatesOn isOpen_univ isPreconnected_univ
  · intro x hx
    exact primitive_hasDerivAt x
  · exact ⟨0, Set.mem_univ 0⟩

end
end ProofGap.Exercise2175
