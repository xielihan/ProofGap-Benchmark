import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3406

noncomputable section

def xCoord (t : ℝ) := t + 1 / t
def yCoord (t : ℝ) := t ^ 2 + 1 / t ^ 2
def zCoord (t : ℝ) := t ^ 3 + 1 / t ^ 3

def Admissible (t : ℝ) : Prop :=
  t ≠ 0 ∧ 1 - 1 / t ^ 2 ≠ 0

def dyDx (t : ℝ) := deriv yCoord t / deriv xCoord t
def dzDx (t : ℝ) := deriv zCoord t / deriv xCoord t
def d2yDx2 (t : ℝ) := deriv dyDx t / deriv xCoord t
def d2zDx2 (t : ℝ) := deriv dzDx t / deriv xCoord t

private theorem eventually_admissible {t : ℝ} (ht : Admissible t) :
    ∀ᶠ s in nhds t, Admissible s := by
  have hden : ContinuousAt (fun s : ℝ => 1 - 1 / s ^ 2) t :=
    continuousAt_const.sub
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht.1))
  simpa [Admissible] using
    (continuousAt_id.eventually_ne ht.1).and (hden.eventually_ne ht.2)

private theorem hasDerivAt_coords {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt xCoord (1 - 1 / t ^ 2) t ∧
      HasDerivAt yCoord (2 * t - 2 / t ^ 3) t ∧
        HasDerivAt zCoord (3 * t ^ 2 - 3 / t ^ 4) t := by
  have hx : HasDerivAt xCoord (1 - 1 / t ^ 2) t := by
    unfold xCoord
    convert (hasDerivAt_id t).add ((hasDerivAt_id t).inv ht) using 1
    · funext s
      simp [one_div]
    · simp [id, one_div] <;> field_simp [ht] <;> ring
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).mul (hasDerivAt_id t) using 1
    · funext s
      simp [pow_two]
    · simp [id] <;> ring
  have hcub : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    convert hsq.mul (hasDerivAt_id t) using 1
    change 3 * t ^ 2 = 2 * t * t + t ^ 2 * 1
    ring
  have hy : HasDerivAt yCoord (2 * t - 2 / t ^ 3) t := by
    unfold yCoord
    convert hsq.add (hsq.inv (pow_ne_zero 2 ht)) using 1
    · funext s
      simp [one_div]
    · field_simp [ht] <;> ring
  have hz : HasDerivAt zCoord (3 * t ^ 2 - 3 / t ^ 4) t := by
    unfold zCoord
    convert hcub.add (hcub.inv (pow_ne_zero 3 ht)) using 1
    · funext s
      simp [one_div]
    · field_simp [ht] <;> ring
  exact ⟨hx, hy, hz⟩

theorem gap1 (t : ℝ) (ht : Admissible t) :
    dyDx t = deriv yCoord t / deriv xCoord t := by
  rfl

theorem gap2 (t : ℝ) (ht : Admissible t) :
    deriv yCoord t / deriv xCoord t =
      (2 * t - 2 / t ^ 3) / (1 - 1 / t ^ 2) := by
  have h := hasDerivAt_coords ht.1
  rw [h.2.1.deriv, h.1.deriv]

theorem gap3 (t : ℝ) (ht : Admissible t) :
    (2 * t - 2 / t ^ 3) / (1 - 1 / t ^ 2) =
      2 * (t + 1 / t) := by
  apply (div_eq_iff ht.2).2
  field_simp [ht.1]
  ring

theorem gap4 (t : ℝ) (ht : Admissible t)
    (h1 : dyDx t = deriv yCoord t / deriv xCoord t)
    (h2 : deriv yCoord t / deriv xCoord t =
      (2 * t - 2 / t ^ 3) / (1 - 1 / t ^ 2))
    (h3 : (2 * t - 2 / t ^ 3) / (1 - 1 / t ^ 2) =
      2 * (t + 1 / t)) :
    dyDx t = 2 * (t + 1 / t) := by
  exact h1.trans (h2.trans h3)

theorem gap5 (t : ℝ) (ht : Admissible t) :
    dzDx t = deriv zCoord t / deriv xCoord t := by
  rfl

theorem gap6 (t : ℝ) (ht : Admissible t) :
    deriv zCoord t / deriv xCoord t =
      (3 * t ^ 2 - 3 / t ^ 4) / (1 - 1 / t ^ 2) := by
  have h := hasDerivAt_coords ht.1
  rw [h.2.2.deriv, h.1.deriv]

theorem gap7 (t : ℝ) (ht : Admissible t) :
    (3 * t ^ 2 - 3 / t ^ 4) / (1 - 1 / t ^ 2) =
      3 * (t ^ 2 + 1 / t ^ 2 + 1) := by
  apply (div_eq_iff ht.2).2
  field_simp [ht.1]
  ring

theorem gap8 (t : ℝ) (ht : Admissible t)
    (h1 : dzDx t = deriv zCoord t / deriv xCoord t)
    (h2 : deriv zCoord t / deriv xCoord t =
      (3 * t ^ 2 - 3 / t ^ 4) / (1 - 1 / t ^ 2))
    (h3 : (3 * t ^ 2 - 3 / t ^ 4) / (1 - 1 / t ^ 2) =
      3 * (t ^ 2 + 1 / t ^ 2 + 1)) :
    dzDx t = 3 * (t ^ 2 + 1 / t ^ 2 + 1) := by
  exact h1.trans (h2.trans h3)

theorem gap9 (t : ℝ) (ht : Admissible t) :
    d2yDx2 t = deriv dyDx t / deriv xCoord t := by
  rfl

theorem gap10 (t : ℝ) (ht : Admissible t)
    (hFirst : ∀ᶠ s in nhds t, dyDx s = 2 * (s + 1 / s)) :
    deriv dyDx t / deriv xCoord t =
      (2 * (1 - 1 / t ^ 2)) / (1 - 1 / t ^ 2) := by
  have hcoords := hasDerivAt_coords ht.1
  have hg : HasDerivAt (fun s : ℝ => 2 * (s + 1 / s))
      (2 * (1 - 1 / t ^ 2)) t := by
    convert (hasDerivAt_const t (2 : ℝ)).mul hcoords.1 using 1 <;>
      simp [xCoord] <;> ring
  have hFirst' :
      dyDx =ᶠ[nhds t] (fun s : ℝ => 2 * (s + 1 / s)) := hFirst
  calc
    deriv dyDx t / deriv xCoord t =
        deriv (fun s : ℝ => 2 * (s + 1 / s)) t / deriv xCoord t := by
      rw [hFirst'.deriv_eq]
    _ = (2 * (1 - 1 / t ^ 2)) / (1 - 1 / t ^ 2) := by
      rw [hg.deriv, hcoords.1.deriv]

theorem gap11 (t : ℝ) (ht : Admissible t) :
    (2 * (1 - 1 / t ^ 2)) / (1 - 1 / t ^ 2) = 2 := by
  apply (div_eq_iff ht.2).2
  ring

theorem gap12 (t : ℝ) (ht : Admissible t)
    (h1 : d2yDx2 t = deriv dyDx t / deriv xCoord t)
    (h2 : deriv dyDx t / deriv xCoord t =
      (2 * (1 - 1 / t ^ 2)) / (1 - 1 / t ^ 2))
    (h3 : (2 * (1 - 1 / t ^ 2)) / (1 - 1 / t ^ 2) = 2) :
    d2yDx2 t = 2 := by
  exact h1.trans (h2.trans h3)

theorem gap13 (t : ℝ) (ht : Admissible t) :
    d2zDx2 t = deriv dzDx t / deriv xCoord t := by
  rfl

theorem gap14 (t : ℝ) (ht : Admissible t)
    (hFirst : ∀ᶠ s in nhds t,
      dzDx s = 3 * (s ^ 2 + 1 / s ^ 2 + 1)) :
    deriv dzDx t / deriv xCoord t =
      (3 * (2 * t - 2 / t ^ 3)) / (1 - 1 / t ^ 2) := by
  have hcoords := hasDerivAt_coords ht.1
  have hg : HasDerivAt
      (fun s : ℝ => 3 * (s ^ 2 + 1 / s ^ 2 + 1))
      (3 * (2 * t - 2 / t ^ 3)) t := by
    convert (hasDerivAt_const t (3 : ℝ)).mul
      (hcoords.2.1.add (hasDerivAt_const t (1 : ℝ))) using 1 <;>
      simp [yCoord] <;> ring
  have hFirst' :
      dzDx =ᶠ[nhds t]
        (fun s : ℝ => 3 * (s ^ 2 + 1 / s ^ 2 + 1)) := hFirst
  calc
    deriv dzDx t / deriv xCoord t =
        deriv (fun s : ℝ => 3 * (s ^ 2 + 1 / s ^ 2 + 1)) t /
          deriv xCoord t := by
      rw [hFirst'.deriv_eq]
    _ = (3 * (2 * t - 2 / t ^ 3)) / (1 - 1 / t ^ 2) := by
      rw [hg.deriv, hcoords.1.deriv]

theorem gap15 (t : ℝ) (ht : Admissible t) :
    (3 * (2 * t - 2 / t ^ 3)) / (1 - 1 / t ^ 2) =
      6 * (t + 1 / t) := by
  apply (div_eq_iff ht.2).2
  field_simp [ht.1]
  ring

theorem gap16 (t : ℝ) (ht : Admissible t)
    (h1 : d2zDx2 t = deriv dzDx t / deriv xCoord t)
    (h2 : deriv dzDx t / deriv xCoord t =
      (3 * (2 * t - 2 / t ^ 3)) / (1 - 1 / t ^ 2))
    (h3 : (3 * (2 * t - 2 / t ^ 3)) / (1 - 1 / t ^ 2) =
      6 * (t + 1 / t)) :
    d2zDx2 t = 6 * (t + 1 / t) := by
  exact h1.trans (h2.trans h3)

theorem gap17 (t : ℝ) (ht : t ≠ 0) :
    yCoord t = (t + 1 / t) ^ 2 - 2 := by
  unfold yCoord
  field_simp [ht] <;> ring

theorem gap18 (t : ℝ) (ht : t ≠ 0) :
    (t + 1 / t) ^ 2 - 2 = (xCoord t) ^ 2 - 2 := by
  rfl

theorem gap19 (t : ℝ) (ht : t ≠ 0)
    (h1 : yCoord t = (t + 1 / t) ^ 2 - 2)
    (h2 : (t + 1 / t) ^ 2 - 2 = (xCoord t) ^ 2 - 2) :
    yCoord t = (xCoord t) ^ 2 - 2 := by
  exact h1.trans h2

theorem gap20 (t : ℝ) (ht : t ≠ 0) :
    zCoord t = (t + 1 / t) * (t ^ 2 - 1 + 1 / t ^ 2) := by
  unfold zCoord
  field_simp [ht] <;> ring

theorem gap21 (t : ℝ) (ht : t ≠ 0) :
    (t + 1 / t) * (t ^ 2 - 1 + 1 / t ^ 2) =
      xCoord t * ((xCoord t) ^ 2 - 3) := by
  unfold xCoord
  field_simp [ht] <;> ring

theorem gap22 (t : ℝ) :
    xCoord t * ((xCoord t) ^ 2 - 3) =
      (xCoord t) ^ 3 - 3 * xCoord t := by
  ring

theorem gap23 (t : ℝ) (ht : t ≠ 0)
    (h1 : zCoord t = (t + 1 / t) * (t ^ 2 - 1 + 1 / t ^ 2))
    (h2 : (t + 1 / t) * (t ^ 2 - 1 + 1 / t ^ 2) =
      xCoord t * ((xCoord t) ^ 2 - 3))
    (h3 : xCoord t * ((xCoord t) ^ 2 - 3) =
      (xCoord t) ^ 3 - 3 * xCoord t) :
    zCoord t = (xCoord t) ^ 3 - 3 * xCoord t := by
  exact h1.trans (h2.trans h3)

theorem gap24 (t : ℝ) (ht : Admissible t) :
    dyDx t = 2 * xCoord t := by
  simpa [xCoord] using
    gap4 t ht (gap1 t ht) (gap2 t ht) (gap3 t ht)

theorem gap25 (t : ℝ) (ht : Admissible t) :
    dzDx t = 3 * (xCoord t) ^ 2 - 3 := by
  rw [gap8 t ht (gap5 t ht) (gap6 t ht) (gap7 t ht)]
  unfold xCoord
  field_simp [ht.1] <;> ring

theorem gap26 (t : ℝ) (ht : Admissible t) :
    d2yDx2 t = 2 := by
  have hFirst : ∀ᶠ s in nhds t, dyDx s = 2 * (s + 1 / s) := by
    exact (eventually_admissible ht).mono fun s hs =>
      gap4 s hs (gap1 s hs) (gap2 s hs) (gap3 s hs)
  exact gap12 t ht (gap9 t ht) (gap10 t ht hFirst) (gap11 t ht)

theorem gap27 (t : ℝ) (ht : Admissible t) :
    d2zDx2 t = 6 * xCoord t := by
  have hFirst : ∀ᶠ s in nhds t,
      dzDx s = 3 * (s ^ 2 + 1 / s ^ 2 + 1) := by
    exact (eventually_admissible ht).mono fun s hs =>
      gap8 s hs (gap5 s hs) (gap6 s hs) (gap7 s hs)
  simpa [xCoord] using
    gap16 t ht (gap13 t ht) (gap14 t ht hFirst) (gap15 t ht)

theorem gap28 (t : ℝ) (ht : Admissible t)
    (h : dyDx t = 2 * xCoord t) :
    dyDx t = 2 * (t + 1 / t) := by
  simpa [xCoord] using h

theorem gap29 (t : ℝ) (ht : Admissible t)
    (h : dzDx t = 3 * (xCoord t) ^ 2 - 3) :
    dzDx t = 3 * (t ^ 2 + 1 / t ^ 2 + 1) := by
  rw [h]
  unfold xCoord
  field_simp [ht.1] <;> ring

theorem gap30 (t : ℝ) (ht : Admissible t)
    (h : d2yDx2 t = 2) :
    d2yDx2 t = 2 := by
  exact h

theorem gap31 (t : ℝ) (ht : Admissible t)
    (h : d2zDx2 t = 6 * xCoord t) :
    d2zDx2 t = 6 * (t + 1 / t) := by
  simpa [xCoord] using h

end

end ProofGap.Exercise3406
