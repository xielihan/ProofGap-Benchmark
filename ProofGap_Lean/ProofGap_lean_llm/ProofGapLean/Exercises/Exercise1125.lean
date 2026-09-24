import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1125

noncomputable section

def d₂ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => deriv f t) x
def d₃ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => d₂ f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def ThreeTimesDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => d₂ f t) x

def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x ^ 2)

private lemma twiceDifferentiableAt_of_on
    (f : ℝ → ℝ) (s L U : ℝ) (hs : s ∈ Set.Ioo L U)
    (hf : DifferentiableOn ℝ f (Set.Ioo L U))
    (hdf : DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo L U)) :
    TwiceDifferentiableAt f s := by
  let ε := min (s - L) (U - s)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)
  refine ⟨ε, hε, ?_, ?_⟩
  · apply hf.mono
    intro z hz
    constructor
    · have hle : ε ≤ s - L := min_le_left _ _
      linarith [hz.1]
    · have hle : ε ≤ U - s := min_le_right _ _
      linarith [hz.2]
  · exact (hdf s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f (x ^ 2)) :
    deriv (y f) x = 2 * x * deriv f (x ^ 2) := by
  have hsq :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hchain :
      HasDerivAt (f ∘ fun t : ℝ => t ^ 2)
        (deriv f (x ^ 2) * (2 * x)) x :=
    HasDerivAt.comp x hf.hasDerivAt hsq
  unfold y
  simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using
    hchain.deriv

theorem gap2 (f : ℝ → ℝ) (x : ℝ)
    (hf : TwiceDifferentiableAt f (x ^ 2)) :
    d₂ (y f) x = 2 * deriv f (x ^ 2) + 4 * x ^ 2 * d₂ f (x ^ 2) := by
  rcases hf with ⟨ε, hε, hfon, hdf⟩
  have hmem : x ^ 2 ∈ Set.Ioo (x ^ 2 - ε) (x ^ 2 + ε) := by
    constructor <;> linarith
  have hev : ∀ᶠ t in nhds x,
      t ^ 2 ∈ Set.Ioo (x ^ 2 - ε) (x ^ 2 + ε) :=
    (continuousAt_id.pow 2).eventually (isOpen_Ioo.mem_nhds hmem)
  have heq :
      (fun t : ℝ => deriv (y f) t) =ᶠ[nhds x]
        (fun t : ℝ => 2 * t * deriv f (t ^ 2)) := by
    filter_upwards [hev] with t ht
    have hfat : DifferentiableAt ℝ f (t ^ 2) :=
      (hfon (t ^ 2) ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
    exact gap1 f t hfat
  have hsq :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hcomp :
      HasDerivAt (fun t : ℝ => deriv f (t ^ 2))
        (d₂ f (x ^ 2) * (2 * x)) x := by
    have hc :
        HasDerivAt ((fun s : ℝ => deriv f s) ∘
          (fun t : ℝ => t ^ 2))
          (deriv (fun s : ℝ => deriv f s) (x ^ 2) * (2 * x)) x :=
      HasDerivAt.comp x hdf.hasDerivAt hsq
    unfold d₂
    simpa only [Function.comp_apply] using hc
  have hlin :
      HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hformula :
      HasDerivAt (fun t : ℝ => 2 * t * deriv f (t ^ 2))
        (2 * deriv f (x ^ 2) + 4 * x ^ 2 * d₂ f (x ^ 2)) x := by
    convert HasDerivAt.mul hlin hcomp using 1 <;> ring
  unfold d₂
  exact (hformula.congr_of_eventuallyEq heq).deriv

theorem gap3 (f : ℝ → ℝ) (x : ℝ)
    (hf : ThreeTimesDifferentiableAt f (x ^ 2)) :
    d₃ (y f) x =
      4 * x * d₂ f (x ^ 2) + 8 * x * d₂ f (x ^ 2) +
        8 * x ^ 3 * d₃ f (x ^ 2) := by
  rcases hf with ⟨ε, hε, hfon, hdfon, hd2⟩
  have hmem : x ^ 2 ∈ Set.Ioo (x ^ 2 - ε) (x ^ 2 + ε) := by
    constructor <;> linarith
  have hev : ∀ᶠ t in nhds x,
      t ^ 2 ∈ Set.Ioo (x ^ 2 - ε) (x ^ 2 + ε) :=
    (continuousAt_id.pow 2).eventually (isOpen_Ioo.mem_nhds hmem)
  have heq :
      (fun t : ℝ => d₂ (y f) t) =ᶠ[nhds x]
        (fun t : ℝ =>
          2 * deriv f (t ^ 2) + 4 * t ^ 2 * d₂ f (t ^ 2)) := by
    filter_upwards [hev] with t ht
    exact gap2 f t
      (twiceDifferentiableAt_of_on f (t ^ 2)
        (x ^ 2 - ε) (x ^ 2 + ε) ht hfon hdfon)
  have hsq :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hdf :
      DifferentiableAt ℝ (fun t => deriv f t) (x ^ 2) :=
    (hdfon (x ^ 2) hmem).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)
  have hcomp1 :
      HasDerivAt (fun t : ℝ => deriv f (t ^ 2))
        (d₂ f (x ^ 2) * (2 * x)) x := by
    have hc :
        HasDerivAt ((fun s : ℝ => deriv f s) ∘
          (fun t : ℝ => t ^ 2))
          (deriv (fun s : ℝ => deriv f s) (x ^ 2) * (2 * x)) x :=
      HasDerivAt.comp x hdf.hasDerivAt hsq
    unfold d₂
    simpa only [Function.comp_apply] using hc
  have hcomp2 :
      HasDerivAt (fun t : ℝ => d₂ f (t ^ 2))
        (d₃ f (x ^ 2) * (2 * x)) x := by
    have hc :
        HasDerivAt ((fun s : ℝ => d₂ f s) ∘
          (fun t : ℝ => t ^ 2))
          (deriv (fun s : ℝ => d₂ f s) (x ^ 2) * (2 * x)) x :=
      HasDerivAt.comp x hd2.hasDerivAt hsq
    unfold d₃
    simpa only [Function.comp_apply] using hc
  have hfirst :
      HasDerivAt (fun t : ℝ => 2 * deriv f (t ^ 2))
        (4 * x * d₂ f (x ^ 2)) x := by
    convert hcomp1.const_mul 2 using 1 <;> ring
  have hfactor :
      HasDerivAt (fun t : ℝ => 4 * t ^ 2) (8 * x) x := by
    convert hsq.const_mul 4 using 1 <;> ring
  have hsecond :
      HasDerivAt (fun t : ℝ => 4 * t ^ 2 * d₂ f (t ^ 2))
        (8 * x * d₂ f (x ^ 2) +
          8 * x ^ 3 * d₃ f (x ^ 2)) x := by
    convert HasDerivAt.mul hfactor hcomp2 using 1 <;> ring
  have hformula :
      HasDerivAt
        (fun t : ℝ =>
          2 * deriv f (t ^ 2) + 4 * t ^ 2 * d₂ f (t ^ 2))
        (4 * x * d₂ f (x ^ 2) + 8 * x * d₂ f (x ^ 2) +
          8 * x ^ 3 * d₃ f (x ^ 2)) x := by
    convert HasDerivAt.add hfirst hsecond using 1 <;> ring
  unfold d₃
  exact (hformula.congr_of_eventuallyEq heq).deriv

theorem gap4 (f : ℝ → ℝ) (x : ℝ) :
    4 * x * d₂ f (x ^ 2) + 8 * x * d₂ f (x ^ 2) +
        8 * x ^ 3 * d₃ f (x ^ 2) =
      12 * x * d₂ f (x ^ 2) + 8 * x ^ 3 * d₃ f (x ^ 2) := by ring

theorem gap5 (f : ℝ → ℝ) (x : ℝ)
    (hf : ThreeTimesDifferentiableAt f (x ^ 2)) :
    d₃ (y f) x =
      12 * x * d₂ f (x ^ 2) + 8 * x ^ 3 * d₃ f (x ^ 2) := by
  rw [gap3 f x hf, gap4 f x]

end

end ProofGap.Exercise1125
