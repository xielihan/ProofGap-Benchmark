import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1140

noncomputable section

def xCoord (t : ℝ) : ℝ := 2 * t - t ^ 2
def yCoord (t : ℝ) : ℝ := 3 * t - t ^ 3

def firstParamDeriv (t : ℝ) : ℝ :=
  deriv yCoord t / deriv xCoord t

def secondParamDeriv (t : ℝ) : ℝ :=
  deriv firstParamDeriv t / deriv xCoord t

def thirdParamDeriv (t : ℝ) : ℝ :=
  deriv secondParamDeriv t / deriv xCoord t

private theorem coordDerivs (t : ℝ) :
    HasDerivAt xCoord (2 - 2 * t) t ∧
      HasDerivAt yCoord (3 - 3 * t ^ 2) t := by
  constructor
  · unfold xCoord
    convert (((hasDerivAt_const (x := t) (c := (2 : ℝ))).mul
      (hasDerivAt_id t)).sub ((hasDerivAt_id t).pow 2)) using 1 <;>
      simp only [id_eq] <;> ring
  · unfold yCoord
    convert (((hasDerivAt_const (x := t) (c := (3 : ℝ))).mul
      (hasDerivAt_id t)).sub ((hasDerivAt_id t).pow 3)) using 1 <;>
      simp only [id_eq] <;> ring

theorem gap1 (t : ℝ) (ht : t ≠ 1) :
    firstParamDeriv t = deriv yCoord t / deriv xCoord t := by
  rfl

theorem gap2 (t : ℝ) (ht : t ≠ 1) :
    deriv yCoord t / deriv xCoord t =
      (3 - 3 * t ^ 2) / (2 - 2 * t) := by
  rw [(coordDerivs t).2.deriv, (coordDerivs t).1.deriv]

theorem gap3 (t : ℝ) (ht : t ≠ 1) :
    (3 - 3 * t ^ 2) / (2 - 2 * t) = (3 / 2 : ℝ) * (t + 1) := by
  have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 2 - 2 * t ≠ 0 := by
    rw [show 2 - 2 * t = 2 * (1 - t) by ring]
    exact mul_ne_zero (by norm_num) h1
  field_simp [hden, h1] <;> ring

theorem gap4 (t : ℝ) (ht : t ≠ 1) :
    firstParamDeriv t = (3 / 2 : ℝ) * (t + 1) := by
  calc
    firstParamDeriv t = deriv yCoord t / deriv xCoord t := gap1 t ht
    _ = (3 - 3 * t ^ 2) / (2 - 2 * t) := gap2 t ht
    _ = (3 / 2 : ℝ) * (t + 1) := gap3 t ht

theorem gap5 (t : ℝ) (ht : t ≠ 1) :
    secondParamDeriv t =
      deriv firstParamDeriv t / deriv xCoord t := by
  rfl

theorem gap6 (t : ℝ) (ht : t ≠ 1) :
    deriv firstParamDeriv t / deriv xCoord t =
      (3 / 2 : ℝ) / (2 - 2 * t) := by
  have hEq : firstParamDeriv =ᶠ[nhds t]
      (fun s : ℝ => (3 / 2 : ℝ) * (s + 1)) := by
    exact (eventually_ne_nhds ht).mono (fun s hs => gap4 s hs)
  have hlin : HasDerivAt (fun s : ℝ => (3 / 2 : ℝ) * (s + 1)) (3 / 2) t := by
    convert (((hasDerivAt_id t).add_const 1).const_mul (3 / 2 : ℝ)) using 1 <;>
      (try simp only [id_eq]) <;> ring
  have hfirst : deriv firstParamDeriv t = (3 / 2 : ℝ) := by
    calc
      deriv firstParamDeriv t =
          deriv (fun s : ℝ => (3 / 2 : ℝ) * (s + 1)) t := hEq.deriv_eq
      _ = (3 / 2 : ℝ) := hlin.deriv
  rw [hfirst, (coordDerivs t).1.deriv]

theorem gap7 (t : ℝ) (ht : t ≠ 1) :
    (3 / 2 : ℝ) / (2 - 2 * t) = 3 / (4 * (1 - t)) := by
  have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 2 - 2 * t ≠ 0 := by
    rw [show 2 - 2 * t = 2 * (1 - t) by ring]
    exact mul_ne_zero (by norm_num) h1
  field_simp [hden, h1] <;> ring

theorem gap8 (t : ℝ) (ht : t ≠ 1) :
    secondParamDeriv t = 3 / (4 * (1 - t)) := by
  calc
    secondParamDeriv t = deriv firstParamDeriv t / deriv xCoord t := gap5 t ht
    _ = (3 / 2 : ℝ) / (2 - 2 * t) := gap6 t ht
    _ = 3 / (4 * (1 - t)) := gap7 t ht

theorem gap9 (t : ℝ) (ht : t ≠ 1) :
    thirdParamDeriv t =
      deriv secondParamDeriv t / deriv xCoord t := by
  rfl

theorem gap10 (t : ℝ) (ht : t ≠ 1) :
    deriv secondParamDeriv t / deriv xCoord t =
      (3 / (4 * (1 - t) ^ 2)) / (2 - 2 * t) := by
  have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 4 * (1 - t) ≠ 0 := mul_ne_zero (by norm_num) h1
  have hEq : secondParamDeriv =ᶠ[nhds t]
      (fun s : ℝ => 3 / (4 * (1 - s))) := by
    exact (eventually_ne_nhds ht).mono (fun s hs => gap8 s hs)
  have hdenDeriv : HasDerivAt (fun s : ℝ => 4 * (1 - s)) (-4) t := by
    convert (((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (hasDerivAt_id t)).const_mul 4) using 1 <;>
      (try simp only [id_eq]) <;> ring
  have hratRaw :=
    (hasDerivAt_const (x := t) (c := (3 : ℝ))).div hdenDeriv hden
  have hrat : HasDerivAt (fun s : ℝ => 3 / (4 * (1 - s)))
      (3 / (4 * (1 - t) ^ 2)) t := by
    convert hratRaw using 1 <;> field_simp [h1] <;> ring
  have hsecond : deriv secondParamDeriv t = 3 / (4 * (1 - t) ^ 2) := by
    calc
      deriv secondParamDeriv t =
          deriv (fun s : ℝ => 3 / (4 * (1 - s))) t := hEq.deriv_eq
      _ = 3 / (4 * (1 - t) ^ 2) := hrat.deriv
  rw [hsecond, (coordDerivs t).1.deriv]

theorem gap11 (t : ℝ) (ht : t ≠ 1) :
    (3 / (4 * (1 - t) ^ 2)) / (2 - 2 * t) =
      3 / (8 * (1 - t) ^ 3) := by
  have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 2 - 2 * t ≠ 0 := by
    rw [show 2 - 2 * t = 2 * (1 - t) by ring]
    exact mul_ne_zero (by norm_num) h1
  field_simp [hden, h1] <;> ring

theorem gap12 (t : ℝ) (ht : t ≠ 1) :
    thirdParamDeriv t = 3 / (8 * (1 - t) ^ 3) := by
  calc
    thirdParamDeriv t = deriv secondParamDeriv t / deriv xCoord t := gap9 t ht
    _ = (3 / (4 * (1 - t) ^ 2)) / (2 - 2 * t) := gap10 t ht
    _ = 3 / (8 * (1 - t) ^ 3) := gap11 t ht

end

end ProofGap.Exercise1140
