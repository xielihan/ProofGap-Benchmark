import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2174
noncomputable section

open Set Filter

def f (x : ℝ) : ℝ :=
  if |x| ≤ 1 then 1 - x ^ 2 else 1 - |x|

def innerPrimitive (x : ℝ) : ℝ :=
  x - x ^ 3 / 3

def outerPrimitive (x : ℝ) : ℝ :=
  x - x * |x| / 2

def primitive (x : ℝ) : ℝ :=
  if |x| ≤ 1 then innerPrimitive x
  else outerPrimitive x + (1 / 6 : ℝ) * SignType.sign x

def FamilyOn (U : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ U, HasDerivAt F (g x) x}

def TranslatesOn (U : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem familyOn_eq_translatesOn_of_isPreconnected
    {U : Set ℝ} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {g p : ℝ → ℝ} (a : ℝ) (ha : a ∈ U)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    FamilyOn U g = TranslatesOn U p := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (g x) x) ↔
      ∃ C : ℝ, ∀ x ∈ U, F x = p x + C
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - p y
    have hH : ∀ x ∈ U, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ H U := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv H x = 0 := by
      intro x hx
      exact (hH x hx).deriv
    refine ⟨H a, ?_⟩
    intro x hx
    have heq : H x = H a :=
      hUopen.is_const_of_deriv_eq_zero hUconn hdiff hzero hx ha
    dsimp [H] at heq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hmem : U ∈ nhds x := hUopen.mem_nhds hx
    have heq : (fun y => p y + C) =ᶠ[nhds x] F := by
      filter_upwards [hmem] with y hy
      exact (hFC y hy).symm
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq.symm

private theorem hasDerivAt_ite_of_eq
    {F G : ℝ → ℝ} {x d : ℝ} (hF : HasDerivAt F d x)
    (hG : HasDerivAt G d x) (heq : F x = G x)
    (p : ℝ → Prop) [DecidablePred p] :
    HasDerivAt (fun y => if p y then F y else G y) d x := by
  rw [hasDerivAt_iff_tendsto_slope] at hF hG ⊢
  apply tendsto_def.2
  intro s hs
  filter_upwards [hF hs, hG hs] with y hyF hyG
  by_cases hpy : p y
  · by_cases hpx : p x
    · simpa [slope, hpy, hpx] using hyF
    · simpa [slope, hpy, hpx, heq] using hyF
  · by_cases hpx : p x
    · simpa [slope, hpy, hpx, heq] using hyG
    · simpa [slope, hpy, hpx] using hyG

theorem gap1 :
    FamilyOn (Set.Ioo (-1 : ℝ) 1) f =
      FamilyOn (Set.Ioo (-1 : ℝ) 1) (fun x => 1 - x ^ 2) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt F (f x) x) ↔
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt F (1 - x ^ 2) x
  constructor <;> intro h x hx
  · have hle : |x| ≤ 1 := (abs_lt.2 hx).le
    simpa [f, hle] using h x hx
  · have hle : |x| ≤ 1 := (abs_lt.2 hx).le
    simpa [f, hle] using h x hx

theorem gap2 :
    FamilyOn (Set.Ioo (-1 : ℝ) 1) (fun x => 1 - x ^ 2) =
      TranslatesOn (Set.Ioo (-1 : ℝ) 1) innerPrimitive := by
  apply familyOn_eq_translatesOn_of_isPreconnected
    isOpen_Ioo isPreconnected_Ioo (0 : ℝ) (by norm_num)
  intro x hx
  unfold innerPrimitive
  convert (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 3) using 1 <;>
    simp [id] <;> ring

theorem gap3 :
    FamilyOn (Set.Ioo (-1 : ℝ) 1) f =
      TranslatesOn (Set.Ioo (-1 : ℝ) 1) innerPrimitive := by
  rw [gap1, gap2]

theorem gap4 :
    FamilyOn (Set.Ioi (1 : ℝ)) f =
      FamilyOn (Set.Ioi (1 : ℝ)) (fun x => 1 - |x|) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F (f x) x) ↔
      ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F (1 - |x|) x
  constructor <;> intro h x hx
  · have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx1
    have hnot : ¬ |x| ≤ 1 := by
      rw [abs_of_pos hx0]
      exact not_le.mpr hx1
    have hfx : f x = 1 - |x| := by simp only [f, hnot, ↓reduceIte]
    simpa only [hfx] using h x hx
  · have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx1
    have hnot : ¬ |x| ≤ 1 := by
      rw [abs_of_pos hx0]
      exact not_le.mpr hx1
    have hfx : f x = 1 - |x| := by simp only [f, hnot, ↓reduceIte]
    simpa only [hfx] using h x hx

theorem gap5 :
    FamilyOn (Set.Ioi (1 : ℝ)) (fun x => 1 - |x|) =
      TranslatesOn (Set.Ioi (1 : ℝ)) outerPrimitive := by
  apply familyOn_eq_translatesOn_of_isPreconnected
    isOpen_Ioi isPreconnected_Ioi (2 : ℝ) (by norm_num)
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx1
  have hp : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
    convert (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      simp [id] <;> ring
  have heq : (fun y : ℝ => y - y ^ 2 / 2) =ᶠ[nhds x] outerPrimitive := by
    filter_upwards [isOpen_Ioi.mem_nhds hx1] with y hy
    have hy0 : 0 < y := lt_trans (by norm_num) hy
    unfold outerPrimitive
    rw [abs_of_pos hy0]
    ring
  have hout : HasDerivAt outerPrimitive (1 - x) x :=
    hp.congr_of_eventuallyEq heq.symm
  simpa [abs_of_pos hx0] using hout

theorem gap6 :
    FamilyOn (Set.Ioi (1 : ℝ)) f =
      TranslatesOn (Set.Ioi (1 : ℝ)) outerPrimitive := by
  rw [gap4, gap5]

theorem gap7 :
    FamilyOn (Set.Iio (-1 : ℝ)) f =
      FamilyOn (Set.Iio (-1 : ℝ)) (fun x => 1 - |x|) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ Set.Iio (-1 : ℝ), HasDerivAt F (f x) x) ↔
      ∀ x ∈ Set.Iio (-1 : ℝ), HasDerivAt F (1 - |x|) x
  constructor <;> intro h x hx
  · have hx1 : x < (-1 : ℝ) := hx
    have hx0 : x < 0 := lt_trans hx1 (by norm_num)
    have hnot : ¬ |x| ≤ 1 := by
      rw [abs_of_neg hx0]
      linarith
    have hfx : f x = 1 - |x| := by simp only [f, hnot, ↓reduceIte]
    simpa only [hfx] using h x hx
  · have hx1 : x < (-1 : ℝ) := hx
    have hx0 : x < 0 := lt_trans hx1 (by norm_num)
    have hnot : ¬ |x| ≤ 1 := by
      rw [abs_of_neg hx0]
      linarith
    have hfx : f x = 1 - |x| := by simp only [f, hnot, ↓reduceIte]
    simpa only [hfx] using h x hx

theorem gap8 :
    FamilyOn (Set.Iio (-1 : ℝ)) (fun x => 1 - |x|) =
      TranslatesOn (Set.Iio (-1 : ℝ)) outerPrimitive := by
  apply familyOn_eq_translatesOn_of_isPreconnected
    isOpen_Iio isPreconnected_Iio (-2 : ℝ) (by norm_num)
  intro x hx
  have hx1 : x < (-1 : ℝ) := hx
  have hx0 : x < 0 := lt_trans hx1 (by norm_num)
  have hp : HasDerivAt (fun y : ℝ => y + y ^ 2 / 2) (1 + x) x := by
    convert (hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      simp [id] <;> ring
  have heq : (fun y : ℝ => y + y ^ 2 / 2) =ᶠ[nhds x] outerPrimitive := by
    filter_upwards [isOpen_Iio.mem_nhds hx1] with y hy
    have hy0 : y < 0 := lt_trans hy (by norm_num)
    unfold outerPrimitive
    rw [abs_of_neg hy0]
    ring
  have hout : HasDerivAt outerPrimitive (1 + x) x :=
    hp.congr_of_eventuallyEq heq.symm
  simpa [abs_of_neg hx0] using hout

theorem gap9 :
    FamilyOn (Set.Iio (-1 : ℝ)) f =
      TranslatesOn (Set.Iio (-1 : ℝ)) outerPrimitive := by
  rw [gap7, gap8]

theorem gap10 :
    ∃ F : ℝ → ℝ, F = primitive ∧ F 0 = 0 := by
  refine ⟨primitive, rfl, ?_⟩
  norm_num [primitive, innerPrimitive]

theorem gap11 :
    ∃ F : ℝ → ℝ, F = primitive ∧
      Tendsto F (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (F 1)) := by
  refine ⟨primitive, rfl, ?_⟩
  let q : ℝ → ℝ := fun x => x - x ^ 2 / 2 + (1 / 6 : ℝ)
  have hq : ContinuousAt q (1 : ℝ) := by
    dsimp [q]
    exact (continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)).add continuousAt_const
  have htq : Tendsto q (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (q 1)) :=
    hq.mono_left inf_le_left
  have heq : primitive =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx1
    have hnot : ¬ |x| ≤ 1 := by
      rw [abs_of_pos hx0]
      exact not_le.mpr hx1
    simp only [primitive, hnot, ↓reduceIte]
    dsimp [q, outerPrimitive]
    rw [abs_of_pos hx0]
    simp [SignType.sign, hx0]
    ring
  have hval : q 1 = primitive 1 := by
    norm_num [q, primitive, innerPrimitive]
  rw [← hval]
  exact htq.congr' heq.symm

theorem gap12 :
    ∃ F : ℝ → ℝ, F = primitive ∧ ContinuousAt F (-1 : ℝ) := by
  refine ⟨primitive, rfl, ?_⟩
  let q : ℝ → ℝ := fun x => x + x ^ 2 / 2 - (1 / 6 : ℝ)
  have hin0 : ContinuousAt innerPrimitive (-1 : ℝ) := by
    unfold innerPrimitive
    exact continuousAt_id.sub ((continuousAt_id.pow 3).div_const 3)
  have hvalin : innerPrimitive (-1 : ℝ) = primitive (-1 : ℝ) := by
    norm_num [primitive, innerPrimitive]
  have hin : Tendsto innerPrimitive (nhds (-1 : ℝ)) (nhds (primitive (-1))) := by
    rw [← hvalin]
    exact hin0
  have hq0 : ContinuousAt q (-1 : ℝ) := by
    dsimp [q]
    exact (continuousAt_id.add ((continuousAt_id.pow 2).div_const 2)).sub continuousAt_const
  have hvalq : q (-1 : ℝ) = primitive (-1 : ℝ) := by
    norm_num [q, primitive, innerPrimitive]
  have hout : Tendsto q (nhds (-1 : ℝ)) (nhds (primitive (-1))) := by
    rw [← hvalq]
    exact hq0
  apply tendsto_def.2
  intro s hs
  have hn : Set.Iio (0 : ℝ) ∈ nhds (-1 : ℝ) :=
    isOpen_Iio.mem_nhds (by norm_num)
  filter_upwards [hin hs, hout hs, hn] with x hix hox hx
  change innerPrimitive x ∈ s at hix
  change q x ∈ s at hox
  change x < 0 at hx
  change primitive x ∈ s
  by_cases hcond : |x| ≤ 1
  · have heqx : primitive x = innerPrimitive x := by
      simp only [primitive, hcond, ↓reduceIte]
    rw [heqx]
    exact hix
  · have hnpos : ¬ 0 < x := not_lt_of_ge hx.le
    have heqx : primitive x = q x := by
      simp only [primitive, hcond, ↓reduceIte]
      dsimp [outerPrimitive, q]
      rw [abs_of_neg hx]
      simp [SignType.sign, hnpos, hx]
      ring
    rw [heqx]
    exact hox

theorem gap13 :
    ∃ F : ℝ → ℝ, ∀ x,
      F x =
        if |x| ≤ 1 then x - x ^ 3 / 3
        else x - x * |x| / 2 + (1 / 6 : ℝ) * SignType.sign x := by
  refine ⟨primitive, ?_⟩
  intro x
  rfl

theorem gap14 :
    FamilyOn Set.univ f = TranslatesOn Set.univ primitive := by
  apply familyOn_eq_translatesOn_of_isPreconnected
    isOpen_univ isPreconnected_univ (0 : ℝ) (Set.mem_univ 0)
  intro x hx
  rcases lt_trichotomy x (-1 : ℝ) with hneg | hneg | hgtneg
  · have hx0 : x < 0 := lt_trans hneg (by norm_num)
    have hp : HasDerivAt (fun y : ℝ => y + y ^ 2 / 2 - (1 / 6 : ℝ)) (1 + x) x := by
      convert ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).div_const 2)).sub_const
          (1 / 6 : ℝ) using 1 <;> simp [id] <;> ring
    have heq :
        (fun y : ℝ => y + y ^ 2 / 2 - (1 / 6 : ℝ)) =ᶠ[nhds x] primitive := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
      have hylt : y < (-1 : ℝ) := hy
      have hy0 : y < 0 := lt_trans hylt (by norm_num)
      have hnot : ¬ |y| ≤ 1 := by
        rw [abs_of_neg hy0]
        exact not_le.mpr (by linarith [hylt])
      have hynpos : ¬ 0 < y := not_lt_of_ge hy0.le
      simp only [primitive, hnot, ↓reduceIte]
      dsimp [outerPrimitive]
      rw [abs_of_neg hy0]
      simp [SignType.sign, hynpos, hy0]
      ring
    have hprim : HasDerivAt primitive (1 + x) x :=
      hp.congr_of_eventuallyEq heq.symm
    have hnotx : ¬ |x| ≤ 1 := by
      rw [abs_of_neg hx0]
      exact not_le.mpr (by linarith [hneg])
    have hfx : f x = 1 + x := by
      simp only [f, hnotx, ↓reduceIte]
      rw [abs_of_neg hx0]
      ring
    simpa only [hfx] using hprim
  · subst x
    have hin : HasDerivAt innerPrimitive 0 (-1 : ℝ) := by
      unfold innerPrimitive
      convert (hasDerivAt_id (-1 : ℝ)).sub
          (((hasDerivAt_id (-1 : ℝ)).pow 3).div_const 3) using 1 <;> norm_num
    let B : ℝ → ℝ := fun y => outerPrimitive y + (1 / 6 : ℝ) * SignType.sign y
    have hq : HasDerivAt (fun y : ℝ => y + y ^ 2 / 2 - (1 / 6 : ℝ)) 0 (-1 : ℝ) := by
      convert (((hasDerivAt_id (-1 : ℝ)).add
          (((hasDerivAt_id (-1 : ℝ)).pow 2).div_const 2)).sub_const (1 / 6 : ℝ)) using 1 <;>
        norm_num
    have heqB :
        (fun y : ℝ => y + y ^ 2 / 2 - (1 / 6 : ℝ)) =ᶠ[nhds (-1 : ℝ)] B := by
      filter_upwards [isOpen_Iio.mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with y hy
      change y < 0 at hy
      have hynpos : ¬ 0 < y := not_lt_of_ge hy.le
      dsimp [B, outerPrimitive]
      rw [abs_of_neg hy]
      simp [SignType.sign, hynpos, hy]
      ring
    have hB : HasDerivAt B 0 (-1 : ℝ) := hq.congr_of_eventuallyEq heqB.symm
    have heq : innerPrimitive (-1 : ℝ) = B (-1 : ℝ) := by
      norm_num [innerPrimitive, B, outerPrimitive, SignType.sign]
    have hprim : HasDerivAt primitive 0 (-1 : ℝ) := by
      simpa only [primitive, B] using
        (hasDerivAt_ite_of_eq hin hB heq (fun y : ℝ => |y| ≤ 1))
    simpa [f] using hprim
  · rcases lt_trichotomy x (1 : ℝ) with hinner | hpos | houter
    · have habslt : |x| < 1 := abs_lt.2 ⟨hgtneg, hinner⟩
      have hp : HasDerivAt innerPrimitive (1 - x ^ 2) x := by
        unfold innerPrimitive
        convert (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 3) using 1 <;>
          simp [id] <;> ring
      have heq : innerPrimitive =ᶠ[nhds x] primitive := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hgtneg, hinner⟩] with y hy
        have hle : |y| ≤ 1 := (abs_lt.2 hy).le
        simp only [primitive, hle, ↓reduceIte]
      have hprim : HasDerivAt primitive (1 - x ^ 2) x :=
        hp.congr_of_eventuallyEq heq.symm
      have hfx : f x = 1 - x ^ 2 := by
        simp only [f, habslt.le, ↓reduceIte]
      simpa only [hfx] using hprim
    · subst x
      have hin : HasDerivAt innerPrimitive 0 (1 : ℝ) := by
        unfold innerPrimitive
        convert (hasDerivAt_id (1 : ℝ)).sub
            (((hasDerivAt_id (1 : ℝ)).pow 3).div_const 3) using 1 <;> norm_num
      let B : ℝ → ℝ := fun y => outerPrimitive y + (1 / 6 : ℝ) * SignType.sign y
      have hq : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + (1 / 6 : ℝ)) 0 (1 : ℝ) := by
        convert (((hasDerivAt_id (1 : ℝ)).sub
            (((hasDerivAt_id (1 : ℝ)).pow 2).div_const 2)).add_const (1 / 6 : ℝ)) using 1 <;>
          norm_num
      have heqB :
          (fun y : ℝ => y - y ^ 2 / 2 + (1 / 6 : ℝ)) =ᶠ[nhds (1 : ℝ)] B := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
        change 0 < y at hy
        dsimp [B, outerPrimitive]
        rw [abs_of_pos hy]
        simp [SignType.sign, hy]
        ring
      have hB : HasDerivAt B 0 (1 : ℝ) := hq.congr_of_eventuallyEq heqB.symm
      have heq : innerPrimitive (1 : ℝ) = B (1 : ℝ) := by
        norm_num [innerPrimitive, B, outerPrimitive, SignType.sign]
      have hprim : HasDerivAt primitive 0 (1 : ℝ) := by
        simpa only [primitive, B] using
          (hasDerivAt_ite_of_eq hin hB heq (fun y : ℝ => |y| ≤ 1))
      simpa [f] using hprim
    · have hx0 : 0 < x := lt_trans (by norm_num) houter
      have hp : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + (1 / 6 : ℝ)) (1 - x) x := by
        convert (((hasDerivAt_id x).sub
            (((hasDerivAt_id x).pow 2).div_const 2)).add_const (1 / 6 : ℝ)) using 1 <;>
          simp [id] <;> ring
      have heq :
          (fun y : ℝ => y - y ^ 2 / 2 + (1 / 6 : ℝ)) =ᶠ[nhds x] primitive := by
        filter_upwards [isOpen_Ioi.mem_nhds houter] with y hy
        have hy0 : 0 < y := lt_trans (by norm_num) hy
        have hnot : ¬ |y| ≤ 1 := by
          rw [abs_of_pos hy0]
          exact not_le.mpr hy
        simp only [primitive, hnot, ↓reduceIte]
        dsimp [outerPrimitive]
        rw [abs_of_pos hy0]
        simp [SignType.sign, hy0]
        ring
      have hprim : HasDerivAt primitive (1 - x) x :=
        hp.congr_of_eventuallyEq heq.symm
      have hnotx : ¬ |x| ≤ 1 := by
        rw [abs_of_pos hx0]
        exact not_le.mpr houter
      have hfx : f x = 1 - x := by
        simp only [f, hnotx, ↓reduceIte]
        rw [abs_of_pos hx0]
      simpa only [hfx] using hprim

end
end ProofGap.Exercise2174
