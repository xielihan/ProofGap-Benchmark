import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3731

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def radiusSq (x y z ξ : ℝ) : ℝ :=
  (x - ξ) ^ 2 + y ^ 2 + z ^ 2

def potential (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..l, f ξ / Real.sqrt (radiusSq x y z ξ)

def AwayFromSegment (l x y z : ℝ) : Prop :=
  ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 < radiusSq x y z ξ

def partialX (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => potential l f s y z) x

def partialXX (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX l f s y z) x

def partialY (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => potential l f x t z) y

def partialYY (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY l f x t z) y

def partialZ (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun r => potential l f x y r) z

def partialZZ (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun r => partialZ l f x y r) z

def powerThreeHalves (r : ℝ) : ℝ :=
  r * Real.sqrt r

def powerFiveHalves (r : ℝ) : ℝ :=
  r ^ 2 * Real.sqrt r

private def coordQ (shift rest : ℝ → ℝ) (s ξ : ℝ) : ℝ :=
  (s - shift ξ) ^ 2 + rest ξ

private def coordKernel
    (f shift rest : ℝ → ℝ) (s ξ : ℝ) : ℝ :=
  f ξ / Real.sqrt (coordQ shift rest s ξ)

private def coordFirst
    (f shift rest : ℝ → ℝ) (s ξ : ℝ) : ℝ :=
  -(s - shift ξ) * f ξ /
    (coordQ shift rest s ξ * Real.sqrt (coordQ shift rest s ξ))

private def coordSecond
    (f shift rest : ℝ → ℝ) (s ξ : ℝ) : ℝ :=
  f ξ * (2 * (s - shift ξ) ^ 2 - rest ξ) /
    (coordQ shift rest s ξ ^ 2 *
      Real.sqrt (coordQ shift rest s ξ))

private def coordIntegral
    (l : ℝ) (f shift rest : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..l, coordKernel f shift rest s ξ

private def coordFirstIntegral
    (l : ℝ) (f shift rest : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..l, coordFirst f shift rest s ξ

private theorem hasDerivAt_coordQ
    (shift rest : ℝ → ℝ) (s ξ : ℝ) :
    HasDerivAt (fun q => coordQ shift rest q ξ)
      (2 * (s - shift ξ)) s := by
  unfold coordQ
  convert
    (((hasDerivAt_id s).sub
      (hasDerivAt_const s (shift ξ))).pow 2).add
        (hasDerivAt_const s (rest ξ)) using 1
  simp only [Pi.sub_apply, id_eq]
  ring

private theorem hasDerivAt_coordKernel
    (f shift rest : ℝ → ℝ) (s ξ : ℝ)
    (hq : 0 < coordQ shift rest s ξ) :
    HasDerivAt (fun q => coordKernel f shift rest q ξ)
      (coordFirst f shift rest s ξ) s := by
  have hQ := hasDerivAt_coordQ shift rest s ξ
  have hroot :
      HasDerivAt
        (fun q => Real.sqrt (coordQ shift rest q ξ))
        ((s - shift ξ) / Real.sqrt (coordQ shift rest s ξ)) s := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp s hQ using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hq] <;> ring
  have hsqrt0 :
      Real.sqrt (coordQ shift rest s ξ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hq
  unfold coordKernel coordFirst
  convert (hasDerivAt_const s (f ξ)).div hroot hsqrt0 using 1
  simp only [zero_mul, zero_sub]
  field_simp [hsqrt0, hq.ne']
  rw [Real.sq_sqrt hq.le]

private theorem hasDerivAt_coordFirst
    (f shift rest : ℝ → ℝ) (s ξ : ℝ)
    (hq : 0 < coordQ shift rest s ξ) :
    HasDerivAt (fun q => coordFirst f shift rest q ξ)
      (coordSecond f shift rest s ξ) s := by
  have hQ := hasDerivAt_coordQ shift rest s ξ
  have hroot :
      HasDerivAt
        (fun q => Real.sqrt (coordQ shift rest q ξ))
        ((s - shift ξ) / Real.sqrt (coordQ shift rest s ξ)) s := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp s hQ using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hq] <;> ring
  have hnum :
      HasDerivAt (fun q : ℝ => -(q - shift ξ) * f ξ)
        (-f ξ) s := by
    convert
      (((hasDerivAt_id s).sub
        (hasDerivAt_const s (shift ξ))).neg.mul_const (f ξ)) using 1 <;>
      ring
  have hden :
      HasDerivAt
        (fun q =>
          coordQ shift rest q ξ *
            Real.sqrt (coordQ shift rest q ξ))
        (3 * (s - shift ξ) *
          Real.sqrt (coordQ shift rest s ξ)) s := by
    convert hQ.mul hroot using 1
    have hsquare :
        Real.sqrt (coordQ shift rest s ξ) ^ 2 =
          coordQ shift rest s ξ :=
      Real.sq_sqrt hq.le
    field_simp [Real.sqrt_ne_zero'.mpr hq]
    rw [hsquare]
    ring
  have hden0 :
      coordQ shift rest s ξ *
          Real.sqrt (coordQ shift rest s ξ) ≠ 0 :=
    mul_ne_zero hq.ne' (Real.sqrt_ne_zero'.mpr hq)
  unfold coordFirst coordSecond
  convert hnum.div hden hden0 using 1
  have hsqrt0 : Real.sqrt (coordQ shift rest s ξ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hq
  field_simp [hq.ne', hsqrt0]
  unfold coordQ
  ring

private theorem coord_continuousOn_product
    (l : ℝ) (f shift rest : ℝ → ℝ) (S : Set ℝ)
    (hf : ContinuousOn f (Set.Icc 0 l))
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hpos :
      ∀ s ∈ S, ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        0 < coordQ shift rest s ξ) :
    ContinuousOn
        (fun p : ℝ × ℝ =>
          coordKernel f shift rest p.1 p.2)
        (S ×ˢ Set.Icc (0 : ℝ) l) ∧
      ContinuousOn
        (fun p : ℝ × ℝ =>
          coordFirst f shift rest p.1 p.2)
        (S ×ˢ Set.Icc (0 : ℝ) l) ∧
      ContinuousOn
        (fun p : ℝ × ℝ =>
          coordSecond f shift rest p.1 p.2)
        (S ×ˢ Set.Icc (0 : ℝ) l) := by
  let K : Set (ℝ × ℝ) := S ×ˢ Set.Icc (0 : ℝ) l
  have hsnd :
      Set.MapsTo (fun p : ℝ × ℝ => p.2) K (Set.Icc (0 : ℝ) l) := by
    intro p hp
    exact hp.2
  have hfP : ContinuousOn (fun p : ℝ × ℝ => f p.2) K :=
    hf.comp continuous_snd.continuousOn hsnd
  have hshiftP : ContinuousOn (fun p : ℝ × ℝ => shift p.2) K :=
    hshift.comp continuous_snd.continuousOn hsnd
  have hrestP : ContinuousOn (fun p : ℝ × ℝ => rest p.2) K :=
    hrest.comp continuous_snd.continuousOn hsnd
  have hv :
      ContinuousOn (fun p : ℝ × ℝ => p.1 - shift p.2) K :=
    continuous_fst.continuousOn.sub hshiftP
  have hQ :
      ContinuousOn
        (fun p : ℝ × ℝ => coordQ shift rest p.1 p.2) K := by
    simpa only [coordQ] using (hv.pow 2).add hrestP
  have hsqrt :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          Real.sqrt (coordQ shift rest p.1 p.2)) K :=
    hQ.sqrt
  have hsqrt0 :
      ∀ p ∈ K, Real.sqrt (coordQ shift rest p.1 p.2) ≠ 0 := by
    intro p hp
    exact Real.sqrt_ne_zero'.mpr (hpos p.1 hp.1 p.2 hp.2)
  have hQ0 :
      ∀ p ∈ K, coordQ shift rest p.1 p.2 ≠ 0 := by
    intro p hp
    exact (hpos p.1 hp.1 p.2 hp.2).ne'
  have hk :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          coordKernel f shift rest p.1 p.2) K := by
    simpa only [coordKernel] using hfP.div hsqrt hsqrt0
  have hfirst :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          coordFirst f shift rest p.1 p.2) K := by
    have hnum := hv.neg.mul hfP
    have hden := hQ.mul hsqrt
    have hden0 :
        ∀ p ∈ K,
          coordQ shift rest p.1 p.2 *
            Real.sqrt (coordQ shift rest p.1 p.2) ≠ 0 := by
      intro p hp
      exact mul_ne_zero (hQ0 p hp) (hsqrt0 p hp)
    simpa only [coordFirst] using hnum.div hden hden0
  have hsecond :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          coordSecond f shift rest p.1 p.2) K := by
    have hnum := hfP.mul ((hv.pow 2).const_mul 2 |>.sub hrestP)
    have hden := (hQ.pow 2).mul hsqrt
    have hden0 :
        ∀ p ∈ K,
          coordQ shift rest p.1 p.2 ^ 2 *
            Real.sqrt (coordQ shift rest p.1 p.2) ≠ 0 := by
      intro p hp
      exact mul_ne_zero (pow_ne_zero 2 (hQ0 p hp)) (hsqrt0 p hp)
    simpa only [coordSecond] using hnum.div hden hden0
  exact ⟨hk, hfirst, hsecond⟩

private theorem coordIntegral_hasDerivAt_on
    (l : ℝ) (f shift rest : ℝ → ℝ) (c ε s : ℝ)
    (hl : 0 < l) (hε : 0 < ε)
    (hf : ContinuousOn f (Set.Icc 0 l))
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hpos :
      ∀ q ∈ Set.Icc (c - ε) (c + ε),
        ∀ ξ ∈ Set.Icc (0 : ℝ) l,
          0 < coordQ shift rest q ξ)
    (hsleft : c - ε < s) (hsright : s < c + ε) :
    HasDerivAt (coordIntegral l f shift rest)
      (coordFirstIntegral l f shift rest s) s := by
  let S : Set ℝ := Set.Icc (c - ε) (c + ε)
  let T : Set ℝ := Set.Icc 0 l
  let K : Set (ℝ × ℝ) := S ×ˢ T
  have hScompact : IsCompact S := isCompact_Icc
  have hTcompact : IsCompact T := isCompact_Icc
  have hKcompact : IsCompact K := hScompact.prod hTcompact
  have hcont :=
    coord_continuousOn_product l f shift rest S hf hshift hrest
      (by
        intro q hq ξ hξ
        exact hpos q hq ξ hξ)
  have hkernelCont := hcont.1
  have hfirstCont := hcont.2.1
  have hsection
      (H : ℝ × ℝ → ℝ) (hH : ContinuousOn H K)
      (q : ℝ) (hq : q ∈ S) :
      ContinuousOn (fun ξ : ℝ => H (q, ξ)) T := by
    apply hH.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro ξ hξ
    exact ⟨hq, hξ⟩
  have hsS : S ∈ 𝓝 s := by
    dsimp [S]
    exact Icc_mem_nhds hsleft hsright
  have hF_meas :
      ∀ᶠ q in 𝓝 s,
        AEStronglyMeasurable
          (fun ξ : ℝ => coordKernel f shift rest q ξ)
          (volume.restrict (Set.uIoc 0 l)) := by
    filter_upwards [hsS] with q hq
    have hc :=
      hsection
        (fun p : ℝ × ℝ => coordKernel f shift rest p.1 p.2)
        hkernelCont q hq
    have hi : IntervalIntegrable
        (fun ξ : ℝ => coordKernel f shift rest q ξ)
        volume 0 l := by
      apply ContinuousOn.intervalIntegrable
      simpa only [T, Set.uIcc_of_le hl.le] using hc
    simpa [Set.uIoc_of_le hl.le] using hi.aestronglyMeasurable
  have hs_mem : s ∈ S := by
    dsimp [S]
    exact ⟨hsleft.le, hsright.le⟩
  have hF_int :
      IntervalIntegrable
        (fun ξ : ℝ => coordKernel f shift rest s ξ)
        volume 0 l := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le hl.le] using
      (hsection
        (fun p : ℝ × ℝ => coordKernel f shift rest p.1 p.2)
        hkernelCont s hs_mem)
  have hF'_int :
      IntervalIntegrable
        (fun ξ : ℝ => coordFirst f shift rest s ξ)
        volume 0 l := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le hl.le] using
      (hsection
        (fun p : ℝ × ℝ => coordFirst f shift rest p.1 p.2)
        hfirstCont s hs_mem)
  have hF'_meas :
      AEStronglyMeasurable
        (fun ξ : ℝ => coordFirst f shift rest s ξ)
        (volume.restrict (Set.uIoc 0 l)) := by
    simpa [Set.uIoc_of_le hl.le] using hF'_int.aestronglyMeasurable
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hfirstCont
  have hbound :
      ∀ᵐ ξ ∂volume, ξ ∈ Set.uIoc (0 : ℝ) l →
        ∀ q ∈ S, ‖coordFirst f shift rest q ξ‖ ≤ C := by
    filter_upwards [] with ξ hξ q hq
    rw [Set.uIoc_of_le hl.le] at hξ
    exact hC (q, ξ) ⟨hq, ⟨hξ.1.le, hξ.2⟩⟩
  have hbound_int :
      IntervalIntegrable (fun _ : ℝ => C) volume 0 l :=
    continuous_const.intervalIntegrable 0 l
  have hdiff :
      ∀ᵐ ξ ∂volume, ξ ∈ Set.uIoc (0 : ℝ) l →
        ∀ q ∈ S,
          HasDerivAt
            (fun q => coordKernel f shift rest q ξ)
            (coordFirst f shift rest q ξ) q := by
    filter_upwards [] with ξ hξ q hq
    rw [Set.uIoc_of_le hl.le] at hξ
    exact hasDerivAt_coordKernel f shift rest q ξ
      (hpos q hq ξ ⟨hξ.1.le, hξ.2⟩)
  unfold coordIntegral coordFirstIntegral
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun q ξ => coordKernel f shift rest q ξ)
      (F' := fun q ξ => coordFirst f shift rest q ξ)
      (bound := fun _ => C) (s := S)
      hsS hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

private theorem coordFirstIntegral_hasDerivAt_on
    (l : ℝ) (f shift rest : ℝ → ℝ) (c ε s : ℝ)
    (hl : 0 < l) (hε : 0 < ε)
    (hf : ContinuousOn f (Set.Icc 0 l))
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hpos :
      ∀ q ∈ Set.Icc (c - ε) (c + ε),
        ∀ ξ ∈ Set.Icc (0 : ℝ) l,
          0 < coordQ shift rest q ξ)
    (hsleft : c - ε < s) (hsright : s < c + ε) :
    HasDerivAt (coordFirstIntegral l f shift rest)
      (∫ ξ in (0 : ℝ)..l, coordSecond f shift rest s ξ) s := by
  let S : Set ℝ := Set.Icc (c - ε) (c + ε)
  let T : Set ℝ := Set.Icc 0 l
  let K : Set (ℝ × ℝ) := S ×ˢ T
  have hScompact : IsCompact S := isCompact_Icc
  have hTcompact : IsCompact T := isCompact_Icc
  have hKcompact : IsCompact K := hScompact.prod hTcompact
  have hcont :=
    coord_continuousOn_product l f shift rest S hf hshift hrest
      (by
        intro q hq ξ hξ
        exact hpos q hq ξ hξ)
  have hfirstCont := hcont.2.1
  have hsecondCont := hcont.2.2
  have hsection
      (H : ℝ × ℝ → ℝ) (hH : ContinuousOn H K)
      (q : ℝ) (hq : q ∈ S) :
      ContinuousOn (fun ξ : ℝ => H (q, ξ)) T := by
    apply hH.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro ξ hξ
    exact ⟨hq, hξ⟩
  have hsS : S ∈ 𝓝 s := by
    dsimp [S]
    exact Icc_mem_nhds hsleft hsright
  have hF_meas :
      ∀ᶠ q in 𝓝 s,
        AEStronglyMeasurable
          (fun ξ : ℝ => coordFirst f shift rest q ξ)
          (volume.restrict (Set.uIoc 0 l)) := by
    filter_upwards [hsS] with q hq
    have hc :=
      hsection
        (fun p : ℝ × ℝ => coordFirst f shift rest p.1 p.2)
        hfirstCont q hq
    have hi : IntervalIntegrable
        (fun ξ : ℝ => coordFirst f shift rest q ξ)
        volume 0 l := by
      apply ContinuousOn.intervalIntegrable
      simpa only [T, Set.uIcc_of_le hl.le] using hc
    simpa [Set.uIoc_of_le hl.le] using hi.aestronglyMeasurable
  have hs_mem : s ∈ S := by
    dsimp [S]
    exact ⟨hsleft.le, hsright.le⟩
  have hF_int :
      IntervalIntegrable
        (fun ξ : ℝ => coordFirst f shift rest s ξ)
        volume 0 l := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le hl.le] using
      (hsection
        (fun p : ℝ × ℝ => coordFirst f shift rest p.1 p.2)
        hfirstCont s hs_mem)
  have hF'_int :
      IntervalIntegrable
        (fun ξ : ℝ => coordSecond f shift rest s ξ)
        volume 0 l := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le hl.le] using
      (hsection
        (fun p : ℝ × ℝ => coordSecond f shift rest p.1 p.2)
        hsecondCont s hs_mem)
  have hF'_meas :
      AEStronglyMeasurable
        (fun ξ : ℝ => coordSecond f shift rest s ξ)
        (volume.restrict (Set.uIoc 0 l)) := by
    simpa [Set.uIoc_of_le hl.le] using hF'_int.aestronglyMeasurable
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hsecondCont
  have hbound :
      ∀ᵐ ξ ∂volume, ξ ∈ Set.uIoc (0 : ℝ) l →
        ∀ q ∈ S, ‖coordSecond f shift rest q ξ‖ ≤ C := by
    filter_upwards [] with ξ hξ q hq
    rw [Set.uIoc_of_le hl.le] at hξ
    exact hC (q, ξ) ⟨hq, ⟨hξ.1.le, hξ.2⟩⟩
  have hbound_int :
      IntervalIntegrable (fun _ : ℝ => C) volume 0 l :=
    continuous_const.intervalIntegrable 0 l
  have hdiff :
      ∀ᵐ ξ ∂volume, ξ ∈ Set.uIoc (0 : ℝ) l →
        ∀ q ∈ S,
          HasDerivAt
            (fun q => coordFirst f shift rest q ξ)
            (coordSecond f shift rest q ξ) q := by
    filter_upwards [] with ξ hξ q hq
    rw [Set.uIoc_of_le hl.le] at hξ
    exact hasDerivAt_coordFirst f shift rest q ξ
      (hpos q hq ξ ⟨hξ.1.le, hξ.2⟩)
  unfold coordFirstIntegral
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun q ξ => coordFirst f shift rest q ξ)
      (F' := fun q ξ => coordSecond f shift rest q ξ)
      (bound := fun _ => C) (s := S)
      hsS hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

private theorem coordIntegral_second_deriv
    (l : ℝ) (f shift rest : ℝ → ℝ) (c ε : ℝ)
    (hl : 0 < l) (hε : 0 < ε)
    (hf : ContinuousOn f (Set.Icc 0 l))
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hpos :
      ∀ q ∈ Set.Icc (c - ε) (c + ε),
        ∀ ξ ∈ Set.Icc (0 : ℝ) l,
          0 < coordQ shift rest q ξ) :
    deriv (deriv (coordIntegral l f shift rest)) c =
      ∫ ξ in (0 : ℝ)..l, coordSecond f shift rest c ξ := by
  have heq :
      deriv (coordIntegral l f shift rest) =ᶠ[𝓝 c]
        coordFirstIntegral l f shift rest := by
    filter_upwards
      [Ioo_mem_nhds
        (by linarith : c - ε < c)
        (by linarith : c < c + ε)] with s hs
    exact
      (coordIntegral_hasDerivAt_on l f shift rest c ε s
        hl hε hf hshift hrest hpos hs.1 hs.2).deriv
  rw [heq.deriv_eq]
  exact
    (coordFirstIntegral_hasDerivAt_on l f shift rest c ε c
      hl hε hf hshift hrest hpos
      (by linarith) (by linarith)).deriv

private theorem exists_coord_positive_neighborhood
    (l : ℝ) (shift rest : ℝ → ℝ) (c : ℝ)
    (hl : 0 < l)
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hrest0 : ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 ≤ rest ξ)
    (haway :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        coordQ shift rest c ξ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ Set.Icc (c - ε) (c + ε),
        ∀ ξ ∈ Set.Icc (0 : ℝ) l,
          0 < coordQ shift rest q ξ := by
  let T : Set ℝ := Set.Icc 0 l
  have hTcompact : IsCompact T := isCompact_Icc
  have hTne : T.Nonempty := by
    exact ⟨0, by simp [T, hl.le]⟩
  have hqcont :
      ContinuousOn (fun ξ => coordQ shift rest c ξ) T := by
    dsimp [T]
    simpa only [coordQ] using
      ((continuous_const.continuousOn.sub hshift).pow 2).add hrest
  obtain ⟨ξ₀, hξ₀, hmin⟩ :=
    hTcompact.exists_isMinOn hTne hqcont
  let m : ℝ := coordQ shift rest c ξ₀
  have hmpos : 0 < m := by
    have hmne : m ≠ 0 := by
      dsimp [m]
      exact haway ξ₀ hξ₀
    have hm0 : 0 ≤ m := by
      dsimp [m, coordQ]
      exact add_nonneg (sq_nonneg _) (hrest0 ξ₀ hξ₀)
    exact lt_of_le_of_ne hm0 (Ne.symm hmne)
  have hvcont :
      ContinuousOn (fun ξ => c - shift ξ) T := by
    dsimp [T]
    exact continuous_const.continuousOn.sub hshift
  obtain ⟨B, hB⟩ :=
    hTcompact.exists_bound_of_continuousOn hvcont
  have hB0 : 0 ≤ B := by
    have hb := hB ξ₀ hξ₀
    linarith [norm_nonneg (c - shift ξ₀)]
  let ε : ℝ := min 1 (m / (8 * (B + 1)))
  have hden : 0 < 8 * (B + 1) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hmpos hden)
  refine ⟨ε, hεpos, ?_⟩
  intro q hq ξ hξ
  let v : ℝ := c - shift ξ
  let d : ℝ := q - c
  have hvabs : |v| ≤ B := by
    have hb := hB ξ hξ
    rw [Real.norm_eq_abs] at hb
    simpa only [v] using hb
  have hdabs : |d| ≤ ε := by
    apply abs_le.mpr
    dsimp [d]
    constructor <;> linarith [hq.1, hq.2]
  have hvdabs : |v * d| ≤ B * ε := by
    rw [abs_mul]
    exact mul_le_mul hvabs hdabs (abs_nonneg d) hB0
  have hvdlower : -(B * ε) ≤ v * d :=
    (abs_le.mp hvdabs).1
  have hεupper : ε ≤ m / (8 * (B + 1)) :=
    min_le_right _ _
  have hsmall : 2 * B * ε < m := by
    have hmul :
        2 * B * ε ≤ 2 * B * (m / (8 * (B + 1))) := by
      gcongr
    have hstrict :
        2 * B * (m / (8 * (B + 1))) < m := by
      field_simp [ne_of_gt hden]
      nlinarith [mul_pos hmpos (show 0 < B + 1 by linarith)]
    exact hmul.trans_lt hstrict
  have hbase : m ≤ v ^ 2 + rest ξ := by
    have hm := hmin hξ
    simpa only [m, coordQ, v] using hm
  have hshiftEq : q - shift ξ = v + d := by
    dsimp [v, d]
    ring
  unfold coordQ
  rw [hshiftEq]
  nlinarith [sq_nonneg d]

private theorem coordSecond_intervalIntegrable_at
    (l : ℝ) (f shift rest : ℝ → ℝ) (c : ℝ)
    (hl : 0 < l)
    (hf : ContinuousOn f (Set.Icc 0 l))
    (hshift : ContinuousOn shift (Set.Icc 0 l))
    (hrest : ContinuousOn rest (Set.Icc 0 l))
    (hpos :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        0 < coordQ shift rest c ξ) :
    IntervalIntegrable
      (fun ξ => coordSecond f shift rest c ξ)
      volume 0 l := by
  let S : Set ℝ := {c}
  let T : Set ℝ := Set.Icc 0 l
  let K : Set (ℝ × ℝ) := S ×ˢ T
  have hcont :=
    coord_continuousOn_product l f shift rest S hf hshift hrest
      (by
        intro q hq ξ hξ
        have hqc : q = c := by simpa [S] using hq
        subst q
        exact hpos ξ hξ)
  have hsec :
      ContinuousOn
        (fun ξ => coordSecond f shift rest c ξ) T := by
    apply hcont.2.2.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro ξ hξ
    exact ⟨by simp [S], hξ⟩
  apply ContinuousOn.intervalIntegrable
  simpa only [T, Set.uIcc_of_le hl.le] using hsec

private def xShift (ξ : ℝ) : ℝ := ξ

private def xRest (y z : ℝ) (_ξ : ℝ) : ℝ := y ^ 2 + z ^ 2

private def zeroShift (_ξ : ℝ) : ℝ := 0

private def yRest (x z ξ : ℝ) : ℝ := (x - ξ) ^ 2 + z ^ 2

private def zRest (x y ξ : ℝ) : ℝ := (x - ξ) ^ 2 + y ^ 2

private theorem potential_eq_coordX
    (l : ℝ) (f : ℝ → ℝ) (y z : ℝ) :
    (fun s => potential l f s y z) =
      coordIntegral l f xShift (xRest y z) := by
  funext s
  unfold potential coordIntegral coordKernel coordQ
  unfold radiusSq xShift xRest
  apply intervalIntegral.integral_congr
  intro ξ _
  apply congrArg (fun r : ℝ => f ξ / Real.sqrt r)
  ring

private theorem potential_eq_coordY
    (l : ℝ) (f : ℝ → ℝ) (x z : ℝ) :
    (fun s => potential l f x s z) =
      coordIntegral l f zeroShift (yRest x z) := by
  funext s
  unfold potential coordIntegral coordKernel coordQ
  unfold radiusSq zeroShift yRest
  apply intervalIntegral.integral_congr
  intro ξ _
  apply congrArg (fun r : ℝ => f ξ / Real.sqrt r)
  ring

private theorem potential_eq_coordZ
    (l : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    (fun s => potential l f x y s) =
      coordIntegral l f zeroShift (zRest x y) := by
  funext s
  unfold potential coordIntegral coordKernel coordQ
  unfold radiusSq zeroShift zRest
  apply intervalIntegral.integral_congr
  intro ξ _
  apply congrArg (fun r : ℝ => f ξ / Real.sqrt r)
  ring

private theorem partialX_eq_coord
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) :
    partialX l f x y z =
      deriv (coordIntegral l f xShift (xRest y z)) x := by
  unfold partialX
  rw [potential_eq_coordX l f y z]

private theorem partialXX_eq_coord
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) :
    partialXX l f x y z =
      deriv (deriv (coordIntegral l f xShift (xRest y z))) x := by
  unfold partialXX partialX
  rw [potential_eq_coordX l f y z]

private theorem partialYY_eq_coord
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) :
    partialYY l f x y z =
      deriv (deriv (coordIntegral l f zeroShift (yRest x z))) y := by
  unfold partialYY partialY
  rw [potential_eq_coordY l f x z]

private theorem partialZZ_eq_coord
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ) :
    partialZZ l f x y z =
      deriv (deriv (coordIntegral l f zeroShift (zRest x y))) z := by
  unfold partialZZ partialZ
  rw [potential_eq_coordZ l f x y]

private theorem partialX_coord_formula
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 < l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialX l f x y z =
      coordFirstIntegral l f xShift (xRest y z) x := by
  have hshift :
      ContinuousOn xShift (Set.Icc (0 : ℝ) l) :=
    continuous_id.continuousOn
  have hrest :
      ContinuousOn (xRest y z) (Set.Icc (0 : ℝ) l) := by
    unfold xRest
    fun_prop
  have hrest0 :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 ≤ xRest y z ξ := by
    intro ξ _
    unfold xRest
    positivity
  have haway' :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        coordQ xShift (xRest y z) x ξ ≠ 0 := by
    intro ξ hξ
    have h := (haway ξ hξ).ne'
    convert h using 1 <;>
      unfold coordQ xShift xRest radiusSq <;> ring
  obtain ⟨ε, hε, hpos⟩ :=
    exists_coord_positive_neighborhood
      l xShift (xRest y z) x hl hshift hrest hrest0 haway'
  rw [partialX_eq_coord]
  exact
    (coordIntegral_hasDerivAt_on
      l f xShift (xRest y z) x ε x
      hl hε hf hshift hrest hpos
      (by linarith) (by linarith)).deriv

private theorem partialXX_coord_formula
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 < l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialXX l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        coordSecond f xShift (xRest y z) x ξ := by
  have hshift :
      ContinuousOn xShift (Set.Icc (0 : ℝ) l) :=
    continuous_id.continuousOn
  have hrest :
      ContinuousOn (xRest y z) (Set.Icc (0 : ℝ) l) := by
    unfold xRest
    fun_prop
  have hrest0 :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 ≤ xRest y z ξ := by
    intro ξ _
    unfold xRest
    positivity
  have haway' :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        coordQ xShift (xRest y z) x ξ ≠ 0 := by
    intro ξ hξ
    have h := (haway ξ hξ).ne'
    convert h using 1 <;>
      unfold coordQ xShift xRest radiusSq <;> ring
  obtain ⟨ε, hε, hpos⟩ :=
    exists_coord_positive_neighborhood
      l xShift (xRest y z) x hl hshift hrest hrest0 haway'
  rw [partialXX_eq_coord]
  exact coordIntegral_second_deriv
    l f xShift (xRest y z) x ε
    hl hε hf hshift hrest hpos

private theorem partialYY_coord_formula
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 < l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialYY l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        coordSecond f zeroShift (yRest x z) y ξ := by
  have hshift :
      ContinuousOn zeroShift (Set.Icc (0 : ℝ) l) := by
    unfold zeroShift
    fun_prop
  have hrest :
      ContinuousOn (yRest x z) (Set.Icc (0 : ℝ) l) := by
    unfold yRest
    fun_prop
  have hrest0 :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 ≤ yRest x z ξ := by
    intro ξ _
    unfold yRest
    positivity
  have haway' :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        coordQ zeroShift (yRest x z) y ξ ≠ 0 := by
    intro ξ hξ
    have h := (haway ξ hξ).ne'
    convert h using 1 <;>
      unfold coordQ zeroShift yRest radiusSq <;> ring
  obtain ⟨ε, hε, hpos⟩ :=
    exists_coord_positive_neighborhood
      l zeroShift (yRest x z) y hl hshift hrest hrest0 haway'
  rw [partialYY_eq_coord]
  exact coordIntegral_second_deriv
    l f zeroShift (yRest x z) y ε
    hl hε hf hshift hrest hpos

private theorem partialZZ_coord_formula
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 < l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialZZ l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        coordSecond f zeroShift (zRest x y) z ξ := by
  have hshift :
      ContinuousOn zeroShift (Set.Icc (0 : ℝ) l) := by
    unfold zeroShift
    fun_prop
  have hrest :
      ContinuousOn (zRest x y) (Set.Icc (0 : ℝ) l) := by
    unfold zRest
    fun_prop
  have hrest0 :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l, 0 ≤ zRest x y ξ := by
    intro ξ _
    unfold zRest
    positivity
  have haway' :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        coordQ zeroShift (zRest x y) z ξ ≠ 0 := by
    intro ξ hξ
    have h := (haway ξ hξ).ne'
    convert h using 1 <;>
      unfold coordQ zeroShift zRest radiusSq <;> ring
  obtain ⟨ε, hε, hpos⟩ :=
    exists_coord_positive_neighborhood
      l zeroShift (zRest x y) z hl hshift hrest hrest0 haway'
  rw [partialZZ_eq_coord]
  exact coordIntegral_second_deriv
    l f zeroShift (zRest x y) z ε
    hl hε hf hshift hrest hpos

theorem gap1 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialX l f x y z =
      -(∫ ξ in (0 : ℝ)..l,
          (x - ξ) * f ξ /
            powerThreeHalves (radiusSq x y z ξ)) := by
  rcases hl.eq_or_lt with rfl | hlpos
  · simp [partialX, potential]
  · rw [partialX_coord_formula l f x y z hlpos hf haway]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro ξ _
    unfold coordFirst
    have hq :
        coordQ xShift (xRest y z) x ξ =
          radiusSq x y z ξ := by
      unfold coordQ xShift xRest radiusSq
      ring
    rw [hq]
    unfold xShift powerThreeHalves
    ring

theorem gap2 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialXX l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        f ξ * (2 * (x - ξ) ^ 2 - y ^ 2 - z ^ 2) /
          powerFiveHalves (radiusSq x y z ξ) := by
  rcases hl.eq_or_lt with rfl | hlpos
  · simp [partialXX, partialX, potential]
  · rw [partialXX_coord_formula l f x y z hlpos hf haway]
    apply intervalIntegral.integral_congr
    intro ξ _
    unfold coordSecond
    have hq :
        coordQ xShift (xRest y z) x ξ =
          radiusSq x y z ξ := by
      unfold coordQ xShift xRest radiusSq
      ring
    rw [hq]
    unfold xShift xRest powerFiveHalves
    ring

theorem gap3 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialYY l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        f ξ * (-(x - ξ) ^ 2 + 2 * y ^ 2 - z ^ 2) /
          powerFiveHalves (radiusSq x y z ξ) := by
  rcases hl.eq_or_lt with rfl | hlpos
  · simp [partialYY, partialY, potential]
  · rw [partialYY_coord_formula l f x y z hlpos hf haway]
    apply intervalIntegral.integral_congr
    intro ξ _
    unfold coordSecond
    have hq :
        coordQ zeroShift (yRest x z) y ξ =
          radiusSq x y z ξ := by
      unfold coordQ zeroShift yRest radiusSq
      ring
    rw [hq]
    unfold zeroShift yRest powerFiveHalves
    ring

theorem gap4 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialZZ l f x y z =
      ∫ ξ in (0 : ℝ)..l,
        f ξ * (-(x - ξ) ^ 2 - y ^ 2 + 2 * z ^ 2) /
          powerFiveHalves (radiusSq x y z ξ) := by
  rcases hl.eq_or_lt with rfl | hlpos
  · simp [partialZZ, partialZ, potential]
  · rw [partialZZ_coord_formula l f x y z hlpos hf haway]
    apply intervalIntegral.integral_congr
    intro ξ _
    unfold coordSecond
    have hq :
        coordQ zeroShift (zRest x y) z ξ =
          radiusSq x y z ξ := by
      unfold coordQ zeroShift zRest radiusSq
      ring
    rw [hq]
    unfold zeroShift zRest powerFiveHalves
    ring

private theorem laplacian_eq_zero_of_pos_length
    (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 < l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialXX l f x y z + partialYY l f x y z +
        partialZZ l f x y z = 0 := by
  rw [partialXX_coord_formula l f x y z hl hf haway,
    partialYY_coord_formula l f x y z hl hf haway,
    partialZZ_coord_formula l f x y z hl hf haway]
  have hxshift :
      ContinuousOn xShift (Set.Icc (0 : ℝ) l) :=
    continuous_id.continuousOn
  have hzeroShift :
      ContinuousOn zeroShift (Set.Icc (0 : ℝ) l) := by
    unfold zeroShift
    fun_prop
  have hxrest :
      ContinuousOn (xRest y z) (Set.Icc (0 : ℝ) l) := by
    unfold xRest
    fun_prop
  have hyrest :
      ContinuousOn (yRest x z) (Set.Icc (0 : ℝ) l) := by
    unfold yRest
    fun_prop
  have hzrest :
      ContinuousOn (zRest x y) (Set.Icc (0 : ℝ) l) := by
    unfold zRest
    fun_prop
  have hxpos :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        0 < coordQ xShift (xRest y z) x ξ := by
    intro ξ hξ
    have h := haway ξ hξ
    change 0 < (x - ξ) ^ 2 + y ^ 2 + z ^ 2 at h
    unfold coordQ xShift xRest
    linarith
  have hypos :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        0 < coordQ zeroShift (yRest x z) y ξ := by
    intro ξ hξ
    have h := haway ξ hξ
    change 0 < (x - ξ) ^ 2 + y ^ 2 + z ^ 2 at h
    unfold coordQ zeroShift yRest
    nlinarith
  have hzpos :
      ∀ ξ ∈ Set.Icc (0 : ℝ) l,
        0 < coordQ zeroShift (zRest x y) z ξ := by
    intro ξ hξ
    have h := haway ξ hξ
    change 0 < (x - ξ) ^ 2 + y ^ 2 + z ^ 2 at h
    unfold coordQ zeroShift zRest
    nlinarith
  have hxint :=
    coordSecond_intervalIntegrable_at
      l f xShift (xRest y z) x hl hf hxshift hxrest hxpos
  have hyint :=
    coordSecond_intervalIntegrable_at
      l f zeroShift (yRest x z) y hl hf hzeroShift hyrest hypos
  have hzint :=
    coordSecond_intervalIntegrable_at
      l f zeroShift (zRest x y) z hl hf hzeroShift hzrest hzpos
  rw [← intervalIntegral.integral_add hxint hyint,
    ← intervalIntegral.integral_add (hxint.add hyint) hzint]
  calc
    (∫ ξ in (0 : ℝ)..l,
        (coordSecond f xShift (xRest y z) x ξ +
          coordSecond f zeroShift (yRest x z) y ξ) +
          coordSecond f zeroShift (zRest x y) z ξ) =
        ∫ _ξ in (0 : ℝ)..l, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro ξ hξ
      rw [Set.uIcc_of_le hl.le] at hξ
      let R : ℝ := radiusSq x y z ξ
      have hR : 0 < R := haway ξ hξ
      have hqx :
          coordQ xShift (xRest y z) x ξ = R := by
        unfold coordQ xShift xRest R radiusSq
        ring
      have hqy :
          coordQ zeroShift (yRest x z) y ξ = R := by
        unfold coordQ zeroShift yRest R radiusSq
        ring
      have hqz :
          coordQ zeroShift (zRest x y) z ξ = R := by
        unfold coordQ zeroShift zRest R radiusSq
        ring
      unfold coordSecond
      change
        f ξ * (2 * (x - xShift ξ) ^ 2 - xRest y z ξ) /
              (coordQ xShift (xRest y z) x ξ ^ 2 *
                Real.sqrt (coordQ xShift (xRest y z) x ξ)) +
            f ξ * (2 * (y - zeroShift ξ) ^ 2 - yRest x z ξ) /
              (coordQ zeroShift (yRest x z) y ξ ^ 2 *
                Real.sqrt (coordQ zeroShift (yRest x z) y ξ)) +
          f ξ * (2 * (z - zeroShift ξ) ^ 2 - zRest x y ξ) /
            (coordQ zeroShift (zRest x y) z ξ ^ 2 *
              Real.sqrt (coordQ zeroShift (zRest x y) z ξ)) = 0
      rw [hqx, hqy, hqz]
      unfold xShift xRest zeroShift yRest zRest
      field_simp [hR.ne', Real.sqrt_ne_zero'.mpr hR]
      ring
    _ = 0 := by simp

theorem gap5 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialXX l f x y z + partialYY l f x y z +
      partialZZ l f x y z = 0 := by
  rcases hl.eq_or_lt with rfl | hlpos
  · simp [partialXX, partialX, partialYY, partialY,
      partialZZ, partialZ, potential]
  · exact laplacian_eq_zero_of_pos_length l f x y z hlpos hf haway

theorem gap6 (l : ℝ) (f : ℝ → ℝ) (x y z : ℝ)
    (hl : 0 ≤ l) (hf : ContinuousOn f (Set.Icc 0 l))
    (haway : AwayFromSegment l x y z) :
    partialXX l f x y z + partialYY l f x y z +
      partialZZ l f x y z = 0 :=
  gap5 l f x y z hl hf haway

end

end ProofGap.Exercise3731
