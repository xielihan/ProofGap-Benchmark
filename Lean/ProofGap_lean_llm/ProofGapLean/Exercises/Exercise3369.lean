import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Real.Lemmas

namespace ProofGap.Exercise3369

noncomputable section

def F (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x - y - φ y

def partialX (G : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => G t y) x

def partialY (G : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => G x t) y

def productDomain (a : ℝ) : Set (ℝ × ℝ) :=
  Set.univ ×ˢ Set.Ioo (-a) a

def Admissible (φ : ℝ → ℝ) (a k : ℝ) : Prop :=
  0 < a ∧
    DifferentiableOn ℝ φ (Set.Ioo (-a) a) ∧
      ContinuousOn (deriv φ) (Set.Ioo (-a) a) ∧
        (∀ y ∈ Set.Ioo (-a) a, |deriv φ y| ≤ k) ∧ k < 1

def IsLocalInverse (φ : ℝ → ℝ) (a ε : ℝ) (y : ℝ → ℝ) : Prop :=
  DifferentiableOn ℝ y (Set.Ioo (-ε) ε) ∧
    y 0 = 0 ∧
      ∀ x ∈ Set.Ioo (-ε) ε,
        y x ∈ Set.Ioo (-a) a ∧ x = y x + φ (y x)

def HasUniqueLocalInverse (φ : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ y : ℝ → ℝ, IsLocalInverse φ a ε y ∧
      ∀ y₁ : ℝ → ℝ, IsLocalInverse φ a ε y₁ →
        Set.EqOn y₁ y (Set.Ioo (-ε) ε)

theorem gap1 (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) :
    F φ 0 0 = 0 := by simp [F, hφ0]

theorem gap2 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ0 : φ 0 = 0) (hφ : Admissible φ a k) :
    ContinuousOn (fun p : ℝ × ℝ => F φ p.1 p.2)
      (productDomain a) := by
  have hφc : ContinuousOn φ (Set.Ioo (-a) a) :=
    hφ.2.1.continuousOn
  have hc : ContinuousOn (fun p : ℝ × ℝ => φ p.2)
      (productDomain a) :=
    hφc.comp continuous_snd.continuousOn (by
      intro p hp
      exact hp.2)
  simpa [F] using
    (continuous_fst.continuousOn.sub continuous_snd.continuousOn).sub hc

theorem gap3 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    ContinuousOn (fun p : ℝ × ℝ => partialX (F φ) p.1 p.2)
      (productDomain a) := by
  have heq : (fun p : ℝ × ℝ => partialX (F φ) p.1 p.2) =
      fun _ => 1 := by
    funext p
    unfold partialX F
    have h : HasDerivAt
        (fun t => t - p.2 - φ p.2) 1 p.1 := by
      convert ((hasDerivAt_id p.1).sub_const p.2).sub_const (φ p.2)
        using 1 <;> simp [id]
    exact h.deriv
  rw [heq]
  exact continuous_const.continuousOn

theorem gap4 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    ContinuousOn (fun p : ℝ × ℝ => partialY (F φ) p.1 p.2)
      (productDomain a) := by
  have heq : ∀ p ∈ productDomain a,
      partialY (F φ) p.1 p.2 = -1 - deriv φ p.2 := by
    intro p hp
    have hφy : HasDerivAt φ (deriv φ p.2) p.2 :=
      (hφ.2.1.differentiableAt (isOpen_Ioo.mem_nhds hp.2)).hasDerivAt
    unfold partialY F
    have h := ((hasDerivAt_const p.2 p.1).sub
      (hasDerivAt_id p.2)).sub hφy
    convert h.deriv using 1 <;> simp [id] <;> ring
  have hder : ContinuousOn (fun p : ℝ × ℝ => deriv φ p.2)
      (productDomain a) :=
    hφ.2.2.1.comp continuous_snd.continuousOn (by
      intro p hp
      exact hp.2)
  have hrhs : ContinuousOn (fun p : ℝ × ℝ => -1 - deriv φ p.2)
      (productDomain a) :=
    continuous_const.continuousOn.sub hder
  exact hrhs.congr (fun p hp => heq p hp)

theorem gap5 (φ : ℝ → ℝ) (a k x y : ℝ)
    (hφ : Admissible φ a k) (hy : y ∈ Set.Ioo (-a) a) :
    partialY (F φ) x y = -1 - deriv φ y := by
  have hφy : HasDerivAt φ (deriv φ y) y :=
    (hφ.2.1.differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  unfold partialY F
  have h := ((hasDerivAt_const y x).sub (hasDerivAt_id y)).sub hφy
  convert h.deriv using 1 <;> simp [id] <;> ring

theorem gap6 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    partialY (F φ) 0 0 = -1 - deriv φ 0 := by
  apply gap5 φ a k 0 0 hφ
  constructor <;> linarith [hφ.1]

theorem gap7 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    -1 - deriv φ 0 < 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-a) a := by
    constructor <;> linarith [hφ.1]
  have hb := hφ.2.2.2.1 0 h0
  have hl : -k ≤ deriv φ 0 := (abs_le.mp hb).1
  linarith [hφ.2.2.2.2]

theorem gap8 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    partialY (F φ) 0 0 < 0 := by
  rw [gap6 φ a k hφ]
  exact gap7 φ a k hφ

theorem gap9 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ : Admissible φ a k) :
    partialY (F φ) 0 0 ≠ 0 :=
  ne_of_lt (gap8 φ a k hφ)

theorem gap10 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ0 : φ 0 = 0) (hφ : Admissible φ a k) :
    HasUniqueLocalInverse φ a := by
  let g : ℝ → ℝ := fun y => y + φ y
  have hzero : (0 : ℝ) ∈ Set.Ioo (-a) a := by
    constructor <;> linarith [hφ.1]
  have hg0 : g 0 = 0 := by simp [g, hφ0]
  have hder (q : ℝ) (hq : q ∈ Set.Ioo (-a) a) :
      HasDerivAt g (1 + deriv φ q) q := by
    have hφq : HasDerivAt φ (deriv φ q) q :=
      (hφ.2.1.differentiableAt (isOpen_Ioo.mem_nhds hq)).hasDerivAt
    simpa [g] using (hasDerivAt_id q).add hφq
  have hpos (q : ℝ) (hq : q ∈ Set.Ioo (-a) a) :
      0 < 1 + deriv φ q := by
    have hb := hφ.2.2.2.1 q hq
    have hl : -k ≤ deriv φ q := (abs_le.mp hb).1
    linarith [hφ.2.2.2.2]
  have hderEv : ∀ᶠ q : ℝ in nhds 0,
      HasDerivAt g (1 + deriv φ q) q := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with q hq
    exact hder q hq
  have hderCont : ContinuousAt (fun q => 1 + deriv φ q) 0 := by
    exact continuousAt_const.add
      (hφ.2.2.1.continuousAt (isOpen_Ioo.mem_nhds hzero))
  have hs0 : HasStrictDerivAt g (1 + deriv φ 0) 0 :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt hderEv hderCont
  have hne : 1 + deriv φ 0 ≠ 0 := (hpos 0 hzero).ne'
  let y : ℝ → ℝ := hs0.localInverse g (1 + deriv φ 0) 0 hne
  have hy0 : y 0 = 0 := by
    have h := (hs0.hasStrictFDerivAt_equiv hne).localInverse_apply_image
    simpa [y, HasStrictDerivAt.localInverse, hg0] using h
  have hright : ∀ᶠ x : ℝ in nhds 0, g (y x) = x := by
    simpa [y, hg0] using
      (hs0.eventually_right_inverse (f := g) (f' := 1 + deriv φ 0)
        (a := 0) hne)
  have hleft : ∀ᶠ q : ℝ in nhds 0, y (g q) = q := by
    simpa [y] using
      (hs0.eventually_left_inverse (f := g) (f' := 1 + deriv φ 0)
        (a := 0) hne)
  have hyCont : ContinuousAt y 0 := by
    simpa [y, hg0] using
      (hs0.to_localInverse (f := g) (f' := 1 + deriv φ 0)
        (a := 0) hne).hasDerivAt.differentiableAt.continuousAt
  have hyRange : ∀ᶠ x : ℝ in nhds 0, y x ∈ Set.Ioo (-a) a :=
    hyCont.eventually (isOpen_Ioo.mem_nhds (by simpa [hy0] using hzero))
  rcases mem_nhds_iff.mp hleft with ⟨U, hUsub, hUopen, hU0⟩
  have hyU : ∀ᶠ x : ℝ in nhds 0, y x ∈ U :=
    hyCont.eventually (hUopen.mem_nhds (by simpa [hy0] using hU0))
  have hyDiff : ∀ᶠ x : ℝ in nhds 0, DifferentiableAt ℝ y x := by
    filter_upwards [hyRange, hyU, hright] with x hya hyu hr
    have hloc : ∀ᶠ q : ℝ in nhds (y x), y (g q) = q :=
      Filter.mem_of_superset (hUopen.mem_nhds hyu) hUsub
    have hqEv : ∀ᶠ q : ℝ in nhds (y x),
        HasDerivAt g (1 + deriv φ q) q := by
      filter_upwards [isOpen_Ioo.mem_nhds hya] with q hq
      exact hder q hq
    have hqCont : ContinuousAt (fun q => 1 + deriv φ q) (y x) :=
      continuousAt_const.add
        (hφ.2.2.1.continuousAt (isOpen_Ioo.mem_nhds hya))
    have hs := hasStrictDerivAt_of_hasDerivAt_of_continuousAt hqEv hqCont
    have hi := hs.to_local_left_inverse (hpos (y x) hya).ne' hloc
    rw [hr] at hi
    exact hi.hasDerivAt.differentiableAt
  have hgCont : ContinuousOn g (Set.Ioo (-a) a) := by
    simpa [g] using continuous_id.continuousOn.add hφ.2.1.continuousOn
  have hgStrict : StrictMonoOn g (Set.Ioo (-a) a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-a) a) hgCont
    intro q hq
    rw [interior_Ioo] at hq
    rw [(hder q hq).deriv]
    exact hpos q hq
  have hall : ∀ᶠ x : ℝ in nhds 0,
      DifferentiableAt ℝ y x ∧ y x ∈ Set.Ioo (-a) a ∧ g (y x) = x := by
    filter_upwards [hyDiff, hyRange, hright] with x hd hrange heq
    exact ⟨hd, hrange, heq⟩
  rcases Metric.mem_nhds_iff.mp hall with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, y, ?_, ?_⟩
  · refine ⟨?_, hy0, ?_⟩
    · intro x hx
      have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
        simpa [Real.dist_eq] using (abs_lt.mpr hx)
      exact (hball hxball).1.differentiableWithinAt
    · intro x hx
      have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
        simpa [Real.dist_eq] using (abs_lt.mpr hx)
      have hh := hball hxball
      exact ⟨hh.2.1, by simpa [g] using hh.2.2.symm⟩
  · intro y₁ hy₁ x hx
    have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Real.dist_eq] using (abs_lt.mpr hx)
    have hyx := (hball hxball).2.1
    have h1 := (hy₁.2.2 x hx).1
    have heq1 := (hy₁.2.2 x hx).2
    have heqy := (hball hxball).2.2
    apply hgStrict.injOn h1 hyx
    simpa [g] using heq1.symm.trans heqy.symm

theorem gap11 (φ : ℝ → ℝ) (a k : ℝ)
    (hφ0 : φ 0 = 0) (hφ : Admissible φ a k) :
    HasUniqueLocalInverse φ a :=
  gap10 φ a k hφ0 hφ

end

end ProofGap.Exercise3369
