import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3387

noncomputable section

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z x t) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY z x t) y

def IsC2Surface (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ) : Prop :=
  IsOpen D ∧ ContDiffOn ℝ 2 (Function.uncurry z) D ∧
    ∀ p ∈ D,
      p.1 + p.2 + z p.1 p.2 =
        Real.exp (-(p.1 + p.2 + z p.1 p.2))

private theorem differentiableAt_const.prodMk {a b : ℝ}
    (h : DifferentiableAt ℝ (fun t : ℝ => t) b) :
    DifferentiableAt ℝ (fun t : ℝ => (a, t)) b :=
  (differentiableAt_const a).prodMk h

theorem gap1 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      1 + partialX z p.1 p.2 =
        Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
          (-1 - partialX z p.1 p.2) := by
  intro p hp
  rcases h with ⟨hD, hzC2, hEqn⟩
  have hzPair : DifferentiableAt ℝ (Function.uncurry z) p :=
    ((hzC2 p hp).differentiableWithinAt (by decide)).differentiableAt
      (hD.mem_nhds hp)
  have hzX : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    have hcurve : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
      differentiableAt_id.prodMk (differentiableAt_const p.2)
    simpa [Function.uncurry] using hzPair.comp p.1 hcurve
  have hleft :
      HasDerivAt (fun t : ℝ => t + p.2 + z t p.2)
        (1 + partialX z p.1 p.2) p.1 := by
    simpa [partialX] using
      (((hasDerivAt_id p.1).add (hasDerivAt_const p.1 p.2)).add
        hzX.hasDerivAt)
  have hright :
      HasDerivAt
        (fun t : ℝ => Real.exp (-(t + p.2 + z t p.2)))
        (Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
          (-1 - partialX z p.1 p.2)) p.1 := by
    simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
      (Real.hasDerivAt_exp (-(p.1 + p.2 + z p.1 p.2))).comp p.1
        hleft.neg
  have hcurve : ContinuousAt (fun t : ℝ => (t, p.2)) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hmem : ∀ᶠ t in nhds p.1, (t, p.2) ∈ D :=
    hcurve.eventually (hD.mem_nhds hp)
  have heq :
      (fun t : ℝ => t + p.2 + z t p.2) =ᶠ[nhds p.1]
        (fun t : ℝ => Real.exp (-(t + p.2 + z t p.2))) :=
    hmem.mono (fun t ht => hEqn (t, p.2) ht)
  calc
    1 + partialX z p.1 p.2 =
        deriv (fun t : ℝ => t + p.2 + z t p.2) p.1 := hleft.deriv.symm
    _ = deriv (fun t : ℝ => Real.exp (-(t + p.2 + z t p.2))) p.1 :=
      Filter.EventuallyEq.deriv_eq heq
    _ = Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
        (-1 - partialX z p.1 p.2) := hright.deriv

theorem gap2 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, partialX z p.1 p.2 = -1 := by
  intro p hp
  have hd := gap1 D z h p hp
  have hpos : 0 < Real.exp (-(p.1 + p.2 + z p.1 p.2)) :=
    Real.exp_pos _
  nlinarith

theorem gap3 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, partialY z p.1 p.2 = -1 := by
  intro p hp
  rcases h with ⟨hD, hzC2, hEqn⟩
  have hzPair : DifferentiableAt ℝ (Function.uncurry z) p :=
    ((hzC2 p hp).differentiableWithinAt (by decide)).differentiableAt
      (hD.mem_nhds hp)
  have hzY : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    have hcurve : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2 :=
      differentiableAt_const.prodMk differentiableAt_id
    simpa [Function.uncurry] using hzPair.comp p.2 hcurve
  have hleft :
      HasDerivAt (fun t : ℝ => p.1 + t + z p.1 t)
        (1 + partialY z p.1 p.2) p.2 := by
    simpa [partialY] using
      (((hasDerivAt_const p.2 p.1).add (hasDerivAt_id p.2)).add
        hzY.hasDerivAt)
  have hright :
      HasDerivAt
        (fun t : ℝ => Real.exp (-(p.1 + t + z p.1 t)))
        (Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
          (-1 - partialY z p.1 p.2)) p.2 := by
    simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
      (Real.hasDerivAt_exp (-(p.1 + p.2 + z p.1 p.2))).comp p.2
        hleft.neg
  have hcurve : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hmem : ∀ᶠ t in nhds p.2, (p.1, t) ∈ D :=
    hcurve.eventually (hD.mem_nhds hp)
  have heq :
      (fun t : ℝ => p.1 + t + z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => Real.exp (-(p.1 + t + z p.1 t))) :=
    hmem.mono (fun t ht => hEqn (p.1, t) ht)
  have hd :
      1 + partialY z p.1 p.2 =
        Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
          (-1 - partialY z p.1 p.2) := by
    calc
      1 + partialY z p.1 p.2 =
          deriv (fun t : ℝ => p.1 + t + z p.1 t) p.2 := hleft.deriv.symm
      _ = deriv (fun t : ℝ => Real.exp (-(p.1 + t + z p.1 t))) p.2 :=
        Filter.EventuallyEq.deriv_eq heq
      _ = Real.exp (-(p.1 + p.2 + z p.1 p.2)) *
          (-1 - partialY z p.1 p.2) := hright.deriv
  have hpos : 0 < Real.exp (-(p.1 + p.2 + z p.1 p.2)) :=
    Real.exp_pos _
  nlinarith

theorem gap4 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 = partialXY z p.1 p.2 := by
  intro p hp
  have hD : IsOpen D := h.1
  have hmemX : ∀ᶠ t in nhds p.1, (t, p.2) ∈ D :=
    (continuousAt_id.prodMk continuousAt_const).eventually
      (hD.mem_nhds hp)
  have hxxEv :
      (fun t : ℝ => partialX z t p.2) =ᶠ[nhds p.1]
        (fun _ : ℝ => (-1 : ℝ)) :=
    hmemX.mono (fun t ht => by
      simpa using gap2 D z h (t, p.2) ht)
  have hxx : partialXX z p.1 p.2 = 0 := by
    unfold partialXX
    rw [Filter.EventuallyEq.deriv_eq hxxEv]
    simp
  have hmemY : ∀ᶠ t in nhds p.2, (p.1, t) ∈ D :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (hD.mem_nhds hp)
  have hxyEv :
      (fun t : ℝ => partialX z p.1 t) =ᶠ[nhds p.2]
        (fun _ : ℝ => (-1 : ℝ)) :=
    hmemY.mono (fun t ht => by
      simpa using gap2 D z h (p.1, t) ht)
  have hxy : partialXY z p.1 p.2 = 0 := by
    unfold partialXY
    rw [Filter.EventuallyEq.deriv_eq hxyEv]
    simp
  rw [hxx, hxy]

theorem gap5 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXY z p.1 p.2 = partialYY z p.1 p.2 := by
  intro p hp
  have hD : IsOpen D := h.1
  have hmemY : ∀ᶠ t in nhds p.2, (p.1, t) ∈ D :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (hD.mem_nhds hp)
  have hxyEv :
      (fun t : ℝ => partialX z p.1 t) =ᶠ[nhds p.2]
        (fun _ : ℝ => (-1 : ℝ)) :=
    hmemY.mono (fun t ht => by
      simpa using gap2 D z h (p.1, t) ht)
  have hxy : partialXY z p.1 p.2 = 0 := by
    unfold partialXY
    rw [Filter.EventuallyEq.deriv_eq hxyEv]
    simp
  have hyyEv :
      (fun t : ℝ => partialY z p.1 t) =ᶠ[nhds p.2]
        (fun _ : ℝ => (-1 : ℝ)) :=
    hmemY.mono (fun t ht => by
      simpa using gap3 D z h (p.1, t) ht)
  have hyy : partialYY z p.1 p.2 = 0 := by
    unfold partialYY
    rw [Filter.EventuallyEq.deriv_eq hyyEv]
    simp
  rw [hxy, hyy]

theorem gap6 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, partialYY z p.1 p.2 = 0 := by
  intro p hp
  have hD : IsOpen D := h.1
  have hmemY : ∀ᶠ t in nhds p.2, (p.1, t) ∈ D :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (hD.mem_nhds hp)
  have hyyEv :
      (fun t : ℝ => partialY z p.1 t) =ᶠ[nhds p.2]
        (fun _ : ℝ => (-1 : ℝ)) :=
    hmemY.mono (fun t ht => by
      simpa using gap3 D z h (p.1, t) ht)
  unfold partialYY
  rw [Filter.EventuallyEq.deriv_eq hyyEv]
  simp

theorem gap7 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, partialXX z p.1 p.2 = 0 := by
  intro p hp
  calc
    partialXX z p.1 p.2 = partialXY z p.1 p.2 := gap4 D z h p hp
    _ = partialYY z p.1 p.2 := gap5 D z h p hp
    _ = 0 := gap6 D z h p hp

end

end ProofGap.Exercise3387
