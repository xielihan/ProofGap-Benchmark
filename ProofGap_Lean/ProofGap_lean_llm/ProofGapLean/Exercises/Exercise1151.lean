import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1151

open Filter

noncomputable section

def F (f : ℝ → ℝ) (a b c x₀ x : ℝ) : ℝ :=
  if x ≤ x₀ then f x else a * (x - x₀) ^ 2 + b * (x - x₀) + c

def ClassK2At (g : ℝ → ℝ) (x₀ : ℝ) : Prop := ContDiffAt ℝ 2 g x₀

theorem gap1 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    ∃ L, Tendsto (F f a b c x₀) (nhdsWithin x₀ (Set.Iio x₀)) (nhds L) ∧
      Tendsto (F f a b c x₀) (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L) := by
  refine ⟨F f a b c x₀ x₀, ?_, ?_⟩
  · exact h.continuousAt.mono_left inf_le_left
  · exact h.continuousAt.mono_left inf_le_left

theorem gap2 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    Tendsto (F f a b c x₀) (nhdsWithin x₀ (Set.Ioi x₀))
      (nhds (F f a b c x₀ x₀)) := by
  exact h.continuousAt.mono_left inf_le_left

theorem gap3 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    Tendsto (F f a b c x₀) (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (F f a b c x₀ x₀)) := by
  exact h.continuousAt.mono_left inf_le_left

theorem gap4 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    ∃ L,
      Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds L) ∧
      Tendsto (fun x => a * (x - x₀) ^ 2 + b * (x - x₀) + c)
        (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L) := by
  rcases gap1 f a b c x₀ h with ⟨L, hleft, hright⟩
  have heqLeft :
      F f a b c x₀ =ᶠ[nhdsWithin x₀ (Set.Iio x₀)] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z < x₀ at hz
    simp [F, le_of_lt hz]
  have heqRight :
      F f a b c x₀ =ᶠ[nhdsWithin x₀ (Set.Ioi x₀)]
        (fun z => a * (z - x₀) ^ 2 + b * (z - x₀) + c) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change x₀ < z at hz
    simp [F, not_le.mpr hz]
  exact ⟨L, hleft.congr' heqLeft, hright.congr' heqRight⟩

theorem gap5 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    Tendsto (fun x => a * (x - x₀) ^ 2 + b * (x - x₀) + c)
      (nhdsWithin x₀ (Set.Ioi x₀)) (nhds (f x₀)) := by
  have hlim := gap2 f a b c x₀ h
  have heqRight :
      F f a b c x₀ =ᶠ[nhdsWithin x₀ (Set.Ioi x₀)]
        (fun z => a * (z - x₀) ^ 2 + b * (z - x₀) + c) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change x₀ < z at hz
    simp [F, not_le.mpr hz]
  simpa [F] using hlim.congr' heqRight

theorem gap6 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) := by
  have hlim := gap3 f a b c x₀ h
  have heqLeft :
      F f a b c x₀ =ᶠ[nhdsWithin x₀ (Set.Iio x₀)] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z < x₀ at hz
    simp [F, le_of_lt hz]
  simpa [F] using hlim.congr' heqLeft

theorem gap7 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (h : ClassK2At (F f a b c x₀) x₀) :
    c = f x₀ := by
  have hpolyAt :
      ContinuousAt
        (fun z : ℝ => a * (z - x₀) ^ 2 + b * (z - x₀) + c) x₀ := by
    fun_prop
  have hpoly :
      Tendsto (fun z : ℝ => a * (z - x₀) ^ 2 + b * (z - x₀) + c)
        (nhdsWithin x₀ (Set.Ioi x₀)) (nhds c) := by
    convert hpolyAt.mono_left inf_le_left using 1 <;> ring
  exact tendsto_nhds_unique hpoly (gap5 f a b c x₀ h)

theorem gap8 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (h : ClassK2At (F f a b c x₀) x₀) :
    deriv f x₀ = 2 * a * (x₀ - x₀) + b := by
  let P : ℝ → ℝ :=
    fun z => a * (z - x₀) ^ 2 + b * (z - x₀) + c
  have hfAt : DifferentiableAt ℝ f x₀ :=
    hf.differentiableAt (by decide)
  have hFAt : DifferentiableAt ℝ (F f a b c x₀) x₀ :=
    h.differentiableAt (by decide)
  have hP :
      HasDerivAt P (2 * a * (x₀ - x₀) + b) x₀ := by
    dsimp [P]
    have hsub := (hasDerivAt_id x₀).sub_const x₀
    convert ((hsub.pow 2).const_mul a).add
      (hsub.const_mul b) |>.add_const c using 1 <;>
      simp only [id_eq] <;> ring
  have hc : c = f x₀ := gap7 f a b c x₀ h
  have heqLeft : ∀ z ∈ Set.Iic x₀, F f a b c x₀ z = f z := by
    intro z hz
    change z ≤ x₀ at hz
    simp [F, hz]
  have heqRight : ∀ z ∈ Set.Ici x₀, F f a b c x₀ z = P z := by
    intro z hz
    change x₀ ≤ z at hz
    by_cases hzx : z = x₀
    · subst z
      simp [F, P, hc]
    · have hgt : x₀ < z := lt_of_le_of_ne hz (Ne.symm hzx)
      simp [F, P, not_le.mpr hgt]
  have hleft :
      deriv (F f a b c x₀) x₀ = deriv f x₀ :=
    (uniqueDiffOn_Iic x₀ x₀ Set.self_mem_Iic).eq_deriv _
      hFAt.hasDerivAt.hasDerivWithinAt
      (hfAt.hasDerivAt.hasDerivWithinAt.congr_of_mem
        (fun z hz => heqLeft z hz) Set.self_mem_Iic)
  have hright :
      deriv (F f a b c x₀) x₀ = 2 * a * (x₀ - x₀) + b :=
    (uniqueDiffOn_Ici x₀ x₀ Set.self_mem_Ici).eq_deriv _
      hFAt.hasDerivAt.hasDerivWithinAt
      (hP.hasDerivWithinAt.congr_of_mem
        (fun z hz => heqRight z hz) Set.self_mem_Ici)
  linarith

theorem gap9 (a b x₀ : ℝ) :
    2 * a * (x₀ - x₀) + b = b := by
  ring

theorem gap10 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (h : ClassK2At (F f a b c x₀) x₀) :
    deriv f x₀ = b := by
  calc
    deriv f x₀ = 2 * a * (x₀ - x₀) + b := gap8 f a b c x₀ hf h
    _ = b := gap9 a b x₀

theorem gap11 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (h : ClassK2At (F f a b c x₀) x₀) :
    deriv (deriv f) x₀ = 2 * a := by
  let P : ℝ → ℝ :=
    fun z => a * (z - x₀) ^ 2 + b * (z - x₀) + c
  let Q : ℝ → ℝ := fun z => 2 * a * (z - x₀) + b
  have hfDerSmooth : ContDiffAt ℝ 1 (deriv f) x₀ :=
    hf.derivWithin (m := 1) (by norm_num)
  have hFDerSmooth : ContDiffAt ℝ 1 (deriv (F f a b c x₀)) x₀ :=
    h.derivWithin (m := 1) (by norm_num)
  have hfDerAt : DifferentiableAt ℝ (deriv f) x₀ :=
    hfDerSmooth.differentiableAt (by decide)
  have hFDerAt : DifferentiableAt ℝ (deriv (F f a b c x₀)) x₀ :=
    hFDerSmooth.differentiableAt (by decide)
  have hQ : HasDerivAt Q (2 * a) x₀ := by
    dsimp [Q]
    convert ((hasDerivAt_id x₀).sub_const x₀).const_mul (2 * a) |>.add_const b
      using 1 <;> ring
  have hFfAt :
      deriv (F f a b c x₀) x₀ = deriv f x₀ := by
    have hFAt : DifferentiableAt ℝ (F f a b c x₀) x₀ :=
      h.differentiableAt (by decide)
    have hfAt : DifferentiableAt ℝ f x₀ :=
      hf.differentiableAt (by decide)
    exact
      (uniqueDiffOn_Iic x₀ x₀ Set.self_mem_Iic).eq_deriv _
        hFAt.hasDerivAt.hasDerivWithinAt
        (hfAt.hasDerivAt.hasDerivWithinAt.congr_of_mem
          (fun z hz => by
            change z ≤ x₀ at hz
            simp [F, hz]) Set.self_mem_Iic)
  have hc : c = f x₀ := gap7 f a b c x₀ h
  have hFPAt :
      deriv (F f a b c x₀) x₀ = Q x₀ := by
    have hFAt : DifferentiableAt ℝ (F f a b c x₀) x₀ :=
      h.differentiableAt (by decide)
    have hP :
        HasDerivAt P (Q x₀) x₀ := by
      dsimp [P, Q]
      have hsub := (hasDerivAt_id x₀).sub_const x₀
      convert ((hsub.pow 2).const_mul a).add
        (hsub.const_mul b) |>.add_const c using 1 <;>
        simp only [id_eq] <;> ring
    apply (uniqueDiffOn_Ici x₀ x₀ Set.self_mem_Ici).eq_deriv _
      hFAt.hasDerivAt.hasDerivWithinAt
    apply hP.hasDerivWithinAt.congr_of_mem _ Set.self_mem_Ici
    intro z hz
    change x₀ ≤ z at hz
    by_cases hzx : z = x₀
    · subst z
      simp [F, P, hc]
    · have hgt : x₀ < z := lt_of_le_of_ne hz (Ne.symm hzx)
      simp [F, P, not_le.mpr hgt]
  have hDerivLeft :
      ∀ z ∈ Set.Iic x₀,
        deriv (F f a b c x₀) z = deriv f z := by
    intro z hz
    change z ≤ x₀ at hz
    by_cases hzx : z = x₀
    · subst z
      exact hFfAt
    · have hlt : z < x₀ := lt_of_le_of_ne hz hzx
      have heq : F f a b c x₀ =ᶠ[nhds z] f := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        change w < x₀ at hw
        simp [F, le_of_lt hw]
      exact heq.deriv_eq
  have hDerivRight :
      ∀ z ∈ Set.Ici x₀,
        deriv (F f a b c x₀) z = Q z := by
    intro z hz
    change x₀ ≤ z at hz
    by_cases hzx : z = x₀
    · subst z
      exact hFPAt
    · have hgt : x₀ < z := lt_of_le_of_ne hz (Ne.symm hzx)
      have heq : F f a b c x₀ =ᶠ[nhds z] P := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        change x₀ < w at hw
        simp [F, P, not_le.mpr hw]
      have hPz :
          HasDerivAt P (Q z) z := by
        dsimp [P, Q]
        have hsub := (hasDerivAt_id z).sub_const x₀
        convert ((hsub.pow 2).const_mul a).add
          (hsub.const_mul b) |>.add_const c using 1 <;>
          simp only [id_eq] <;> ring
      calc
        deriv (F f a b c x₀) z = deriv P z := heq.deriv_eq
        _ = Q z := hPz.deriv
  have hleft :
      deriv (deriv (F f a b c x₀)) x₀ = deriv (deriv f) x₀ :=
    (uniqueDiffOn_Iic x₀ x₀ Set.self_mem_Iic).eq_deriv _
      hFDerAt.hasDerivAt.hasDerivWithinAt
      (hfDerAt.hasDerivAt.hasDerivWithinAt.congr_of_mem
        (fun z hz => hDerivLeft z hz) Set.self_mem_Iic)
  have hright :
      deriv (deriv (F f a b c x₀)) x₀ = 2 * a :=
    (uniqueDiffOn_Ici x₀ x₀ Set.self_mem_Ici).eq_deriv _
      hFDerAt.hasDerivAt.hasDerivWithinAt
      (hQ.hasDerivWithinAt.congr_of_mem
        (fun z hz => hDerivRight z hz) Set.self_mem_Ici)
  linarith

theorem gap12 (f : ℝ → ℝ) (a x₀ : ℝ)
    (h : deriv (deriv f) x₀ = 2 * a) :
    a = (1 / 2 : ℝ) * deriv (deriv f) x₀ := by
  rw [h]
  ring

theorem gap13 (f : ℝ → ℝ) (a b c x₀ : ℝ)
    (hf : ContDiff ℝ 2 f)
    (habc : (a, b, c) =
      ((1 / 2 : ℝ) * deriv (deriv f) x₀, deriv f x₀, f x₀)) :
    ClassK2At (F f a b c x₀) x₀ := by
  have ha :
      a = (1 / 2 : ℝ) * deriv (deriv f) x₀ :=
    congrArg Prod.fst habc
  have hbc :
      (b, c) = (deriv f x₀, f x₀) :=
    congrArg Prod.snd habc
  have hb : b = deriv f x₀ := congrArg Prod.fst hbc
  have hc : c = f x₀ := congrArg Prod.snd hbc
  have ha2 : 2 * a = deriv (deriv f) x₀ := by
    rw [ha]
    ring
  let P : ℝ → ℝ :=
    fun z => a * (z - x₀) ^ 2 + b * (z - x₀) + c
  let Q : ℝ → ℝ := fun z => 2 * a * (z - x₀) + b
  let H : ℝ → ℝ :=
    fun z => if z ≤ x₀ then deriv (deriv f) z else 2 * a
  have hfDiff : Differentiable ℝ f :=
    hf.differentiable (by decide)
  have hfDerSmooth : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  have hfDerDiff : Differentiable ℝ (deriv f) :=
    hfDerSmooth.differentiable (by decide)
  have hfSecondCont : Continuous (deriv (deriv f)) :=
    hfDerSmooth.continuous_deriv_one
  have hP : ∀ z, HasDerivAt P (Q z) z := by
    intro z
    dsimp [P, Q]
    have hsub := (hasDerivAt_id z).sub_const x₀
    convert ((hsub.pow 2).const_mul a).add
      (hsub.const_mul b) |>.add_const c using 1 <;>
      simp only [id_eq] <;> ring
  have hQ : ∀ z, HasDerivAt Q (2 * a) z := by
    intro z
    dsimp [Q]
    convert ((hasDerivAt_id z).sub_const x₀).const_mul (2 * a) |>.add_const b
      using 1 <;> ring
  let G : ℝ → ℝ :=
    fun z => if z ≤ x₀ then deriv f z else Q z
  have hFder : ∀ z, HasDerivAt (F f a b c x₀) (G z) z := by
    intro z
    rcases lt_trichotomy z x₀ with hlt | heq | hgt
    · have hevent : F f a b c x₀ =ᶠ[nhds z] f := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        change w < x₀ at hw
        simp [F, le_of_lt hw]
      simpa [G, le_of_lt hlt] using
        (hfDiff z).hasDerivAt.congr_of_eventuallyEq hevent
    · subst z
      have hleft :
          HasDerivWithinAt (F f a b c x₀) (deriv f x₀)
            (Set.Iic x₀) x₀ := by
        apply (hfDiff x₀).hasDerivAt.hasDerivWithinAt.congr_of_mem _
          Set.self_mem_Iic
        intro w hw
        change w ≤ x₀ at hw
        simp [F, hw]
      have hQx : Q x₀ = deriv f x₀ := by
        dsimp [Q]
        rw [hb]
        ring
      have hright :
          HasDerivWithinAt (F f a b c x₀) (deriv f x₀)
            (Set.Ici x₀) x₀ := by
        apply ((hP x₀).congr_deriv hQx).hasDerivWithinAt.congr_of_mem _
          Set.self_mem_Ici
        intro w hw
        change x₀ ≤ w at hw
        by_cases hwx : w = x₀
        · subst w
          simp [F, P, hc]
        · have hwgt : x₀ < w := lt_of_le_of_ne hw (Ne.symm hwx)
          simp [F, P, not_le.mpr hwgt]
      have hunion := hleft.union hright
      simpa [G, Set.Iic_union_Ici] using hunion
    · have hevent : F f a b c x₀ =ᶠ[nhds z] P := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        change x₀ < w at hw
        simp [F, P, not_le.mpr hw]
      simpa [G, not_le.mpr hgt] using
        (hP z).congr_of_eventuallyEq hevent
  have hGder : ∀ z, HasDerivAt G (H z) z := by
    intro z
    rcases lt_trichotomy z x₀ with hlt | heq | hgt
    · have hevent : G =ᶠ[nhds z] deriv f := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        change w < x₀ at hw
        simp [G, le_of_lt hw]
      simpa [H, le_of_lt hlt] using
        (hfDerDiff z).hasDerivAt.congr_of_eventuallyEq hevent
    · subst z
      have hleft :
          HasDerivWithinAt G (deriv (deriv f) x₀)
            (Set.Iic x₀) x₀ := by
        apply (hfDerDiff x₀).hasDerivAt.hasDerivWithinAt.congr_of_mem _
          Set.self_mem_Iic
        intro w hw
        change w ≤ x₀ at hw
        simp [G, hw]
      have hright :
          HasDerivWithinAt G (deriv (deriv f) x₀)
            (Set.Ici x₀) x₀ := by
        apply ((hQ x₀).congr_deriv ha2).hasDerivWithinAt.congr_of_mem _
          Set.self_mem_Ici
        intro w hw
        change x₀ ≤ w at hw
        by_cases hwx : w = x₀
        · subst w
          simp [G, Q, hb]
        · have hwgt : x₀ < w := lt_of_le_of_ne hw (Ne.symm hwx)
          simp [G, not_le.mpr hwgt]
      have hunion := hleft.union hright
      simpa [H, Set.Iic_union_Ici] using hunion
    · have hevent : G =ᶠ[nhds z] Q := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        change x₀ < w at hw
        simp [G, not_le.mpr hw]
      simpa [H, not_le.mpr hgt] using
        (hQ z).congr_of_eventuallyEq hevent
  have hHCont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro z
    rcases lt_trichotomy z x₀ with hlt | heq | hgt
    · have hevent : H =ᶠ[nhds z] deriv (deriv f) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        change w < x₀ at hw
        simp [H, le_of_lt hw]
      exact hfSecondCont.continuousAt.congr_of_eventuallyEq hevent
    · subst z
      rw [continuousAt_iff_continuous_left_right]
      constructor
      · change Tendsto H (nhdsWithin x₀ (Set.Iic x₀)) (nhds (H x₀))
        have ht :=
          hfSecondCont.continuousAt.mono_left
            (show nhdsWithin x₀ (Set.Iic x₀) ≤ nhds x₀ from inf_le_left)
        have hevent :
            H =ᶠ[nhdsWithin x₀ (Set.Iic x₀)] deriv (deriv f) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          change w ≤ x₀ at hw
          simp [H, hw]
        simpa [H] using ht.congr' hevent.symm
      · change Tendsto H (nhdsWithin x₀ (Set.Ici x₀)) (nhds (H x₀))
        have ht :
            Tendsto (fun _ : ℝ => 2 * a)
              (nhdsWithin x₀ (Set.Ici x₀)) (nhds (2 * a)) :=
          tendsto_const_nhds
        have hevent :
            H =ᶠ[nhdsWithin x₀ (Set.Ici x₀)] (fun _ : ℝ => 2 * a) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          change x₀ ≤ w at hw
          by_cases hwx : w = x₀
          · subst w
            simp [H, ha2]
          · have hwgt : x₀ < w := lt_of_le_of_ne hw (Ne.symm hwx)
            simp [H, not_le.mpr hwgt]
        simpa [H, ha2] using ht.congr' hevent.symm
    · have hevent : H =ᶠ[nhds z] (fun _ : ℝ => 2 * a) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        change x₀ < w at hw
        simp [H, not_le.mpr hw]
      exact continuousAt_const.congr_of_eventuallyEq hevent
  have hFdiff : Differentiable ℝ (F f a b c x₀) :=
    fun z => (hFder z).differentiableAt
  have hGdiff : Differentiable ℝ G :=
    fun z => (hGder z).differentiableAt
  have hDerivF : deriv (F f a b c x₀) = G := by
    funext z
    exact (hFder z).deriv
  have hDerivG : deriv G = H := by
    funext z
    exact (hGder z).deriv
  have hGContDiff : ContDiff ℝ 1 G := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hGdiff, ?_⟩
    simpa only [hDerivG] using hHCont
  have hDerivFContDiff : ContDiff ℝ 1 (deriv (F f a b c x₀)) := by
    simpa only [hDerivF] using hGContDiff
  have hFContDiff : ContDiff ℝ 2 (F f a b c x₀) := by
    change ContDiff ℝ (1 + 1) (F f a b c x₀)
    apply contDiff_succ_iff_deriv.mpr
    exact ⟨hFdiff, by norm_num, hDerivFContDiff⟩
  exact hFContDiff.contDiffAt

end

end ProofGap.Exercise1151
