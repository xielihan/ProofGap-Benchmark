import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3854

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def ell (a b c : ℝ) : ℝ :=
  (b - a) / (b + c)

def xOfT (a b c t : ℝ) : ℝ :=
  (a + ell a b c * c * t) / (1 - ell a b c * t)

def integrand (a b c m n x : ℝ) : ℝ :=
  Real.rpow (x - a) m * Real.rpow (b - x) n /
    Real.rpow (x + c) (m + n + 2)

private theorem bc_pos (a b c : ℝ) (hab : a < b) (hac : 0 < a + c) :
    0 < b + c := by
  linarith

private theorem ell_pos (a b c : ℝ) (hab : a < b) (hac : 0 < a + c) :
    0 < ell a b c := by
  unfold ell
  exact div_pos (sub_pos.mpr hab) (bc_pos a b c hab hac)

private theorem ell_lt_one (a b c : ℝ) (hab : a < b) (hac : 0 < a + c) :
    ell a b c < 1 := by
  unfold ell
  apply (div_lt_one (bc_pos a b c hab hac)).2
  linarith

private theorem denom_pos (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - ell a b c * t := by
  have he0 := (ell_pos a b c hab hac).le
  have he1 := ell_lt_one a b c hab hac
  have hprod : ell a b c * t ≤ ell a b c := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr ht.2)]
  linarith

theorem gap1 (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xOfT a b c t =
      (a + ell a b c * c * t) / (1 - ell a b c * t) := by
  rfl

theorem gap2 (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xOfT a b c t - a =
      ((a + c) * ell a b c * t) /
        (1 - ell a b c * t) := by
  have hden : 1 - ell a b c * t ≠ 0 :=
    ne_of_gt (denom_pos a b c t hab hac ht)
  unfold xOfT
  field_simp [hden]
  ring

theorem gap3 (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xOfT a b c t - b =
      (a - b + (b + c) * ell a b c * t) /
        (1 - ell a b c * t) := by
  have hden : 1 - ell a b c * t ≠ 0 :=
    ne_of_gt (denom_pos a b c t hab hac ht)
  unfold xOfT
  field_simp [hden]
  ring

theorem gap4 (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xOfT a b c t + c =
      (a + c) / (1 - ell a b c * t) := by
  have hden : 1 - ell a b c * t ≠ 0 :=
    ne_of_gt (denom_pos a b c t hab hac ht)
  unfold xOfT
  field_simp [hden]
  ring

theorem gap5 (a b c t : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (xOfT a b c)
      (((a + c) * ell a b c) /
        (1 - ell a b c * t) ^ 2) t := by
  have hden : 1 - ell a b c * t ≠ 0 :=
    ne_of_gt (denom_pos a b c t hab hac ht)
  have hnum :
      HasDerivAt
        (fun s : ℝ => a + ell a b c * c * s)
        (ell a b c * c) t := by
    convert (hasDerivAt_const t a).add
      ((hasDerivAt_id t).const_mul (ell a b c * c)) using 1 <;>
      simp [id_eq] <;> ring
  have hdenDeriv :
      HasDerivAt
        (fun s : ℝ => 1 - ell a b c * s)
        (-ell a b c) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (ell a b c)) using 1 <;>
      simp [id_eq]
  unfold xOfT
  convert (hnum.div hdenDeriv hden) using 1 <;>
    (try simp [id_eq]) <;>
    field_simp [hden] <;> ring

private theorem beta_intervalIntegrable (m n : ℝ)
    (hm : -1 < m) (hn : -1 < n) :
    IntervalIntegrable
      (fun t : ℝ => Real.rpow t m * Real.rpow (1 - t) n)
      volume 0 1 := by
  have hmLeft :
      IntervalIntegrable (fun t : ℝ => Real.rpow t m)
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hm
  have hnContLeft :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) n)
        [[(0 : ℝ), 1 / 2]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : 1 - t ≠ 0 := by linarith
    simpa [Function.comp_def] using
      (Real.continuousAt_rpow_const (1 - t) n (Or.inl hbase)).comp
        (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow t m * Real.rpow (1 - t) n)
        volume 0 (1 / 2 : ℝ) :=
    hmLeft.mul_continuousOn hnContLeft
  have hnRight :
      IntervalIntegrable (fun t : ℝ => Real.rpow (1 - t) n)
        volume (1 / 2 : ℝ) 1 := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := 1 / 2) hn).comp_sub_left 1
    convert h.symm using 1 <;> norm_num
  have hmContRight :
      ContinuousOn (fun t : ℝ => Real.rpow t m)
        [[(1 / 2 : ℝ), 1]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : t ≠ 0 := by linarith
    exact Real.continuousAt_rpow_const t m (Or.inl hbase)
  have hright :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow t m * Real.rpow (1 - t) n)
        volume (1 / 2 : ℝ) 1 :=
    hnRight.continuousOn_mul hmContRight
  exact hleft.trans hright

private theorem integrand_intervalIntegrable
    (a b c m n : ℝ) (hab : a < b) (hac : 0 < a + c)
    (hm : -1 < m) (hn : -1 < n) :
    IntervalIntegrable (integrand a b c m n) volume a b := by
  let d : ℝ := (a + b) / 2
  have had : a < d := by dsimp [d]; linarith
  have hdb : d < b := by dsimp [d]; linarith
  have hmShift :
      IntervalIntegrable (fun x : ℝ => Real.rpow (x - a) m)
        volume a d := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := d - a) hm).comp_sub_right a
    convert h using 1 <;> ring
  have hcontLeft :
      ContinuousOn
        (fun x : ℝ =>
          Real.rpow (b - x) n *
            (Real.rpow (x + c) (m + n + 2))⁻¹)
        [[a, d]] := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx' : x ∈ Set.Icc a d := by
      simpa [Set.uIcc_of_le had.le] using hx
    have hbx : b - x ≠ 0 := by linarith [hx'.2, hdb]
    have hxcpos : 0 < x + c := by linarith [hx'.1, hac]
    have hxc : x + c ≠ 0 := ne_of_gt hxcpos
    have hleft :
        ContinuousAt (fun y : ℝ => Real.rpow (b - y) n) x := by
      simpa [Function.comp_def] using
        (Real.continuousAt_rpow_const (b - x) n (Or.inl hbx)).comp
          (continuous_const.sub continuous_id).continuousAt
    have hright :
        ContinuousAt
          (fun y : ℝ => (Real.rpow (y + c) (m + n + 2))⁻¹) x := by
      have hr :
          ContinuousAt (fun y : ℝ => Real.rpow (y + c) (m + n + 2)) x := by
        have hinner : ContinuousAt (fun y : ℝ => y + c) x :=
          continuousAt_id.add continuousAt_const
        simpa using
          hinner.rpow continuousAt_const (Or.inl hxc)
      exact hr.inv₀ (ne_of_gt (Real.rpow_pos_of_pos hxcpos (m + n + 2)))
    exact hleft.mul hright
  have hleft0 := hmShift.mul_continuousOn hcontLeft
  have hleft :
      IntervalIntegrable (integrand a b c m n) volume a d := by
    change IntervalIntegrable
      (fun x : ℝ =>
        Real.rpow (x - a) m * Real.rpow (b - x) n /
          Real.rpow (x + c) (m + n + 2)) volume a d
    simpa only [div_eq_mul_inv, mul_assoc] using hleft0
  have hnShift :
      IntervalIntegrable (fun x : ℝ => Real.rpow (b - x) n)
        volume d b := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := b - d) hn).comp_sub_left b
    convert h.symm using 1 <;> ring
  have hcontRight :
      ContinuousOn
        (fun x : ℝ =>
          Real.rpow (x - a) m *
            (Real.rpow (x + c) (m + n + 2))⁻¹)
        [[d, b]] := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx' : x ∈ Set.Icc d b := by
      simpa [Set.uIcc_of_le hdb.le] using hx
    have hxa : x - a ≠ 0 := by linarith [hx'.1, had]
    have hxcpos : 0 < x + c := by linarith [hx'.1, had, hac]
    have hxc : x + c ≠ 0 := ne_of_gt hxcpos
    have hleft :
        ContinuousAt (fun y : ℝ => Real.rpow (y - a) m) x := by
      have hinner : ContinuousAt (fun y : ℝ => y - a) x :=
        continuousAt_id.sub continuousAt_const
      simpa using hinner.rpow continuousAt_const (Or.inl hxa)
    have hright :
        ContinuousAt
          (fun y : ℝ => (Real.rpow (y + c) (m + n + 2))⁻¹) x := by
      have hr :
          ContinuousAt (fun y : ℝ => Real.rpow (y + c) (m + n + 2)) x := by
        have hinner : ContinuousAt (fun y : ℝ => y + c) x :=
          continuousAt_id.add continuousAt_const
        simpa using
          hinner.rpow continuousAt_const (Or.inl hxc)
      exact hr.inv₀ (ne_of_gt (Real.rpow_pos_of_pos hxcpos (m + n + 2)))
    exact hleft.mul hright
  have hright0 := hnShift.continuousOn_mul hcontRight
  have hright :
      IntervalIntegrable (integrand a b c m n) volume d b := by
    change IntervalIntegrable
      (fun x : ℝ =>
        Real.rpow (x - a) m * Real.rpow (b - x) n /
          Real.rpow (x + c) (m + n + 2)) volume d b
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hright0
  exact hleft.trans hright

private theorem change_identity
    (a b c m n t : ℝ) (hab : a < b) (hac : 0 < a + c)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    integrand a b c m n (xOfT a b c t) *
        (((a + c) * ell a b c) /
          (1 - ell a b c * t) ^ 2) =
      Real.rpow (ell a b c) (m + 1) /
          Real.rpow (a + c) (n + 1) *
        (Real.rpow t m *
          Real.rpow
            (b - a - (b + c) * ell a b c * t) n) := by
  have hbc : 0 < b + c := bc_pos a b c hab hac
  have he : 0 < ell a b c := ell_pos a b c hab hac
  have hD : 0 < 1 - ell a b c * t :=
    denom_pos a b c t hab hac ht
  have hq :
      b - a - (b + c) * ell a b c * t =
        (b - a) * (1 - t) := by
    unfold ell
    field_simp [ne_of_gt hbc]
  have hq0 :
      0 ≤ b - a - (b + c) * ell a b c * t := by
    rw [hq]
    exact mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr ht.2)
  have hxa :
      xOfT a b c t - a =
        ((a + c) * ell a b c * t) /
          (1 - ell a b c * t) :=
    gap2 a b c t hab hac ht
  have hbx :
      b - xOfT a b c t =
        (b - a - (b + c) * ell a b c * t) /
          (1 - ell a b c * t) := by
    unfold xOfT
    field_simp [ne_of_gt hD]
    ring
  have hxc :
      xOfT a b c t + c =
        (a + c) / (1 - ell a b c * t) :=
    gap4 a b c t hab hac ht
  have hepow :
      Real.rpow (ell a b c) (m + 1) =
        Real.rpow (ell a b c) m * ell a b c := by
    calc
      Real.rpow (ell a b c) (m + 1) =
          Real.rpow (ell a b c) m *
            Real.rpow (ell a b c) 1 :=
        Real.rpow_add he m 1
      _ = _ := by simp
  have hApow :
      Real.rpow (a + c) (m + n + 2) =
        Real.rpow (a + c) m * Real.rpow (a + c) (n + 1) *
          (a + c) := by
    calc
      Real.rpow (a + c) (m + n + 2) =
          Real.rpow (a + c) (m + (n + 1) + 1) := by ring
      _ = Real.rpow (a + c) (m + (n + 1)) *
            Real.rpow (a + c) 1 :=
        Real.rpow_add hac (m + (n + 1)) 1
      _ = _ := by
        have hmn :
            Real.rpow (a + c) (m + (n + 1)) =
              Real.rpow (a + c) m * Real.rpow (a + c) (n + 1) :=
          Real.rpow_add hac m (n + 1)
        rw [hmn]
        simp
  have hDpow :
      Real.rpow (1 - ell a b c * t) (m + n + 2) =
        Real.rpow (1 - ell a b c * t) m *
            Real.rpow (1 - ell a b c * t) n *
          (1 - ell a b c * t) ^ 2 := by
    calc
      Real.rpow (1 - ell a b c * t) (m + n + 2) =
        Real.rpow (1 - ell a b c * t) ((m + n) + 2) := by ring
      _ = Real.rpow (1 - ell a b c * t) (m + n) *
          Real.rpow (1 - ell a b c * t) 2 :=
        Real.rpow_add hD (m + n) 2
      _ = _ := by
        have hmn :
            Real.rpow (1 - ell a b c * t) (m + n) =
              Real.rpow (1 - ell a b c * t) m *
                Real.rpow (1 - ell a b c * t) n :=
          Real.rpow_add hD m n
        rw [hmn]
        norm_num [Real.rpow_natCast]
  have hfirstDiv :
      Real.rpow
          (((a + c) * ell a b c * t) /
            (1 - ell a b c * t)) m =
        Real.rpow ((a + c) * ell a b c * t) m /
          Real.rpow (1 - ell a b c * t) m :=
    Real.div_rpow
      (mul_nonneg (mul_nonneg hac.le he.le) ht.1) hD.le m
  have hfirstMul1 :
      Real.rpow ((a + c) * ell a b c * t) m =
        Real.rpow ((a + c) * ell a b c) m *
          Real.rpow t m :=
    Real.mul_rpow (mul_nonneg hac.le he.le) ht.1
  have hfirstMul2 :
      Real.rpow ((a + c) * ell a b c) m =
        Real.rpow (a + c) m * Real.rpow (ell a b c) m :=
    Real.mul_rpow hac.le he.le
  have hsecondDiv :
      Real.rpow
          ((b - a - (b + c) * ell a b c * t) /
            (1 - ell a b c * t)) n =
        Real.rpow (b - a - (b + c) * ell a b c * t) n /
          Real.rpow (1 - ell a b c * t) n :=
    Real.div_rpow hq0 hD.le n
  have hthirdDiv :
      Real.rpow
          ((a + c) / (1 - ell a b c * t)) (m + n + 2) =
        Real.rpow (a + c) (m + n + 2) /
          Real.rpow (1 - ell a b c * t) (m + n + 2) :=
    Real.div_rpow hac.le hD.le (m + n + 2)
  unfold integrand
  rw [hxa, hbx, hxc]
  rw [hfirstDiv, hfirstMul1, hfirstMul2, hsecondDiv, hthirdDiv]
  rw [hepow, hApow, hDpow]
  have hAm : Real.rpow (a + c) m ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hac m)
  have hAn : Real.rpow (a + c) (n + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hac (n + 1))
  have hDm : Real.rpow (1 - ell a b c * t) m ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hD m)
  have hDn : Real.rpow (1 - ell a b c * t) n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hD n)
  have hD2 : (1 - ell a b c * t) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt hD)
  field_simp [hAm, hAn, hDm, hDn, hD2]

theorem gap6 (a b c m n : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (hm : -1 < m) (hn : -1 < n) :
    (∫ x in a..b, integrand a b c m n x) =
      Real.rpow (ell a b c) (m + 1) /
          Real.rpow (a + c) (n + 1) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t m *
            Real.rpow
              (b - a - (b + c) * ell a b c * t) n := by
  have hbc : 0 < b + c := bc_pos a b c hab hac
  have he : 0 < ell a b c := ell_pos a b c hab hac
  have he1 : ell a b c < 1 := ell_lt_one a b c hab hac
  have hden (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      0 < 1 - ell a b c * t :=
    denom_pos a b c t hab hac ht
  have hq (t : ℝ) :
      b - a - (b + c) * ell a b c * t =
        (b - a) * (1 - t) := by
    unfold ell
    field_simp [ne_of_gt hbc]
  have hf :
      ContinuousOn (xOfT a b c) [[(0 : ℝ), 1]] := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact (gap5 a b c t hab hac ht01).continuousAt.continuousWithinAt
  have hff' :
      ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt (xOfT a b c)
          (((a + c) * ell a b c) /
            (1 - ell a b c * t) ^ 2)
          (Set.Ioi t) t := by
    intro t ht
    norm_num at ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    exact (gap5 a b c t hab hac ht01).hasDerivWithinAt
  have hg_cont :
      ContinuousOn
        (integrand a b c m n)
        (xOfT a b c ''
          Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) := by
    rintro x ⟨t, ht, rfl⟩
    norm_num at ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hxa : 0 < xOfT a b c t - a := by
      rw [gap2 a b c t hab hac ht01]
      exact div_pos (mul_pos (mul_pos hac he) ht.1) (hden t ht01)
    have hbx : 0 < b - xOfT a b c t := by
      have hbxEq :
          b - xOfT a b c t =
            (b - a - (b + c) * ell a b c * t) /
              (1 - ell a b c * t) := by
        unfold xOfT
        field_simp [ne_of_gt (hden t ht01)]
        ring
      rw [hbxEq, hq t]
      exact div_pos
        (mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2))
        (hden t ht01)
    have hxc : 0 < xOfT a b c t + c := by
      rw [gap4 a b c t hab hac ht01]
      exact div_pos hac (hden t ht01)
    have hleft :
        ContinuousAt
          (fun y : ℝ => Real.rpow (y - a) m)
          (xOfT a b c t) := by
      have hinner :
          ContinuousAt (fun y : ℝ => y - a) (xOfT a b c t) :=
        continuousAt_id.sub continuousAt_const
      simpa using
        hinner.rpow continuousAt_const (Or.inl (ne_of_gt hxa))
    have hmiddle :
        ContinuousAt
          (fun y : ℝ => Real.rpow (b - y) n)
          (xOfT a b c t) := by
      have hinner :
          ContinuousAt (fun y : ℝ => b - y) (xOfT a b c t) :=
        continuousAt_const.sub continuousAt_id
      simpa using
        hinner.rpow continuousAt_const (Or.inl (ne_of_gt hbx))
    have hright :
        ContinuousAt
          (fun y : ℝ => Real.rpow (y + c) (m + n + 2))
          (xOfT a b c t) := by
      have hinner :
          ContinuousAt (fun y : ℝ => y + c) (xOfT a b c t) :=
        continuousAt_id.add continuousAt_const
      simpa using
        hinner.rpow continuousAt_const (Or.inl (ne_of_gt hxc))
    unfold integrand
    exact
      ((hleft.mul hmiddle).div hright
        (ne_of_gt (Real.rpow_pos_of_pos hxc (m + n + 2)))).continuousWithinAt
  have himage :
      xOfT a b c '' [[(0 : ℝ), 1]] ⊆ Set.Icc a b := by
    rintro x ⟨t, ht, rfl⟩
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hxa : 0 ≤ xOfT a b c t - a := by
      rw [gap2 a b c t hab hac ht01]
      exact div_nonneg
        (mul_nonneg (mul_nonneg hac.le he.le) ht01.1)
        (hden t ht01).le
    have hbx : 0 ≤ b - xOfT a b c t := by
      have hbxEq :
          b - xOfT a b c t =
            (b - a - (b + c) * ell a b c * t) /
              (1 - ell a b c * t) := by
        unfold xOfT
        field_simp [ne_of_gt (hden t ht01)]
        ring
      rw [hbxEq, hq t]
      exact div_nonneg
        (mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr ht01.2))
        (hden t ht01).le
    constructor <;> linarith
  have hg1 :
      IntegrableOn
        (integrand a b c m n)
        (xOfT a b c '' [[(0 : ℝ), 1]])
        volume := by
    have hIcc :
        IntegrableOn (integrand a b c m n) (Set.Icc a b) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp
        (integrand_intervalIntegrable a b c m n hab hac hm hn)
    exact hIcc.mono_set himage
  have hqInt :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t m *
            Real.rpow
              (b - a - (b + c) * ell a b c * t) n)
        volume 0 1 := by
    have hscaled :
        IntervalIntegrable
          (fun t : ℝ =>
            Real.rpow (b - a) n *
              (Real.rpow t m * Real.rpow (1 - t) n))
          volume 0 1 :=
      (beta_intervalIntegrable m n hm hn).continuousOn_mul continuousOn_const
    apply hscaled.congr
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact ⟨ht'.1.le, ht'.2⟩
    have hrp :
        Real.rpow ((b - a) * (1 - t)) n =
          Real.rpow (b - a) n * Real.rpow (1 - t) n :=
      Real.mul_rpow (sub_pos.mpr hab).le (sub_nonneg.mpr ht01.2)
    dsimp only
    rw [hq t, hrp]
    ring
  have hg2 :
      IntegrableOn
        (fun t : ℝ =>
          ((integrand a b c m n) ∘ (xOfT a b c)) t *
            (((a + c) * ell a b c) /
              (1 - ell a b c * t) ^ 2))
        [[(0 : ℝ), 1]] volume := by
    have hscaled :
        IntervalIntegrable
          (fun t : ℝ =>
            (Real.rpow (ell a b c) (m + 1) /
                Real.rpow (a + c) (n + 1)) *
              (Real.rpow t m *
                Real.rpow
                  (b - a - (b + c) * ell a b c * t) n))
          volume 0 1 :=
      hqInt.continuousOn_mul continuousOn_const
    have htrans :
        IntervalIntegrable
          (fun t : ℝ =>
            ((integrand a b c m n) ∘ (xOfT a b c)) t *
              (((a + c) * ell a b c) /
                (1 - ell a b c * t) ^ 2))
          volume 0 1 := by
      apply hscaled.congr
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
        have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ⟨ht'.1.le, ht'.2⟩
      simpa [Function.comp_def] using
        (change_identity a b c m n t hab hac ht01).symm
    exact (intervalIntegrable_iff').mp htrans
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'''
      hf hff' hg_cont hg1 hg2
  have hf0 : xOfT a b c 0 = a := by
    simp [xOfT]
  have hf1 : xOfT a b c 1 = b := by
    have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hnum :
        a - b + (b + c) * ell a b c * 1 = 0 := by
      unfold ell
      field_simp [ne_of_gt hbc]
      ring
    apply sub_eq_zero.mp
    rw [gap3 a b c 1 hab hac ht1, hnum]
    simp
  rw [hf0, hf1] at hsub
  calc
    (∫ x in a..b, integrand a b c m n x) =
        ∫ t in (0 : ℝ)..1,
          ((integrand a b c m n) ∘ (xOfT a b c)) t *
            (((a + c) * ell a b c) /
              (1 - ell a b c * t) ^ 2) :=
      hsub.symm
    _ =
        ∫ t in (0 : ℝ)..1,
          (Real.rpow (ell a b c) (m + 1) /
              Real.rpow (a + c) (n + 1)) *
            (Real.rpow t m *
              Real.rpow
                (b - a - (b + c) * ell a b c * t) n) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      simpa [Function.comp_def] using
        change_identity a b c m n t hab hac ht01
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]

theorem gap7 (a b c m n : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (hm : -1 < m) (hn : -1 < n) :
    (∫ x in a..b, integrand a b c m n x) =
      Real.rpow (b - a) (m + n + 1) /
          (Real.rpow (a + c) (n + 1) *
            Real.rpow (b + c) (m + 1)) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t m * Real.rpow (1 - t) n := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hbc : 0 < b + c := bc_pos a b c hab hac
  have hq (t : ℝ) :
      b - a - (b + c) * ell a b c * t =
        (b - a) * (1 - t) := by
    unfold ell
    field_simp [ne_of_gt hbc]
  have hint :
      (∫ t in (0 : ℝ)..1,
          Real.rpow t m *
            Real.rpow
              (b - a - (b + c) * ell a b c * t) n) =
        Real.rpow (b - a) n *
          ∫ t in (0 : ℝ)..1,
            Real.rpow t m * Real.rpow (1 - t) n := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hrp :
        Real.rpow ((b - a) * (1 - t)) n =
          Real.rpow (b - a) n * Real.rpow (1 - t) n :=
      Real.mul_rpow hba.le (sub_nonneg.mpr ht01.2)
    rw [hq t, hrp]
    ring
  have hellpow :
      Real.rpow (ell a b c) (m + 1) =
        Real.rpow (b - a) (m + 1) /
          Real.rpow (b + c) (m + 1) := by
    unfold ell
    exact Real.div_rpow hba.le hbc.le (m + 1)
  have hbapow :
      Real.rpow (b - a) (m + n + 1) =
        Real.rpow (b - a) (m + 1) * Real.rpow (b - a) n := by
    calc
      Real.rpow (b - a) (m + n + 1) =
          Real.rpow (b - a) ((m + 1) + n) := by ring
      _ = Real.rpow (b - a) (m + 1) * Real.rpow (b - a) n :=
        Real.rpow_add hba (m + 1) n
  have hcoef :
      Real.rpow (ell a b c) (m + 1) /
            Real.rpow (a + c) (n + 1) *
          Real.rpow (b - a) n =
        Real.rpow (b - a) (m + n + 1) /
          (Real.rpow (a + c) (n + 1) *
            Real.rpow (b + c) (m + 1)) := by
    rw [hellpow, hbapow]
    have hacpow :
        Real.rpow (a + c) (n + 1) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hac (n + 1))
    have hbcpow :
        Real.rpow (b + c) (m + 1) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hbc (m + 1))
    field_simp [hacpow, hbcpow]
  rw [gap6 a b c m n hab hac hm hn, hint]
  rw [← mul_assoc, hcoef]

theorem gap8 (a b c m n : ℝ)
    (hab : a < b) (hac : 0 < a + c)
    (hm : -1 < m) (hn : -1 < n) :
    (∫ x in a..b, integrand a b c m n x) =
      Real.rpow (b - a) (m + n + 1) /
          (Real.rpow (a + c) (n + 1) *
            Real.rpow (b + c) (m + 1)) *
        betaFn (m + 1) (n + 1) := by
  rw [gap7 a b c m n hab hac hm hn]
  simp [betaFn]

theorem gap9 (m : ℝ) (hm : -1 < m) :
    -1 < m := by
  exact hm

theorem gap10 (n : ℝ) (hn : -1 < n) :
    -1 < n := by
  exact hn

end

end ProofGap.Exercise3854
