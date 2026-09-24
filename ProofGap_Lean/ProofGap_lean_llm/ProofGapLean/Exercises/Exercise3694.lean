import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3694

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def feasible (R : ℝ) (p : Point3) : Prop :=
  0 ≤ p.x ∧ 0 ≤ p.y ∧ 0 ≤ p.z ∧
    p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = R ^ 2

def volume (p : Point3) : ℝ :=
  4 * p.x * p.y * p.z

def critical (R : ℝ) (p : Point3) (μ : ℝ) : Prop :=
  p.y * p.z - 2 * μ * p.x = 0 ∧
    p.x * p.z - 2 * μ * p.y = 0 ∧
    p.x * p.y - 2 * μ * p.z = 0 ∧
    p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = R ^ 2

def candidate (R : ℝ) : Point3 :=
  ⟨R / Real.sqrt 3, R / Real.sqrt 3, R / Real.sqrt 3⟩

def maximizers (R : ℝ) : Set Point3 :=
  {p | feasible R p ∧ ∀ q, feasible R q → volume q ≤ volume p}

private theorem critical_coordinates_eq (R : ℝ) (p : Point3) (μ : ℝ)
    (hp : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z)
    (hcrit : critical R p μ) :
    p.x = p.y ∧ p.y = p.z := by
  have hμ : 0 < μ := by
    have heq : p.y * p.z = 2 * μ * p.x :=
      sub_eq_zero.mp hcrit.1
    have hprod : 0 < 2 * μ * p.x := by
      rw [← heq]
      exact mul_pos hp.2.1 hp.2.2
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · nlinarith [hpos.1]
    · nlinarith [hp.1, hneg.2]
  constructor
  · have hfactor : (p.y - p.x) * (p.z + 2 * μ) = 0 := by
      calc
        (p.y - p.x) * (p.z + 2 * μ) =
            (p.y * p.z - 2 * μ * p.x) -
              (p.x * p.z - 2 * μ * p.y) := by ring
        _ = 0 := by
          rw [hcrit.1, hcrit.2.1]
          ring
    rcases mul_eq_zero.mp hfactor with hdiff | hsum
    · nlinarith [hdiff]
    · nlinarith [hsum, hp.2.2, hμ]
  · have hfactor : (p.z - p.y) * (p.x + 2 * μ) = 0 := by
      calc
        (p.z - p.y) * (p.x + 2 * μ) =
            (p.x * p.z - 2 * μ * p.y) -
              (p.x * p.y - 2 * μ * p.z) := by ring
        _ = 0 := by
          rw [hcrit.2.1, hcrit.2.2.1]
          ring
    rcases mul_eq_zero.mp hfactor with hdiff | hsum
    · nlinarith [hdiff]
    · nlinarith [hsum, hp.1, hμ]

private theorem point3_eq_of_fields {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      change px = qx at hx
      change py = qy at hy
      change pz = qz at hz
      subst qx
      subst qy
      subst qz
      rfl

theorem gap1 (R : ℝ) (p : Point3) (μ : ℝ)
    (hp : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z)
    (hcrit : critical R p μ) :
    p.x = p.y := by
  exact (critical_coordinates_eq R p μ hp hcrit).1

theorem gap2 (R : ℝ) (p : Point3) (μ : ℝ)
    (hp : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z)
    (hcrit : critical R p μ) :
    p.y = p.z := by
  exact (critical_coordinates_eq R p μ hp hcrit).2

theorem gap3 (R : ℝ) (hR : 0 < R) (p : Point3) (μ : ℝ)
    (hp : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z)
    (hcrit : critical R p μ) :
    p.z = R / Real.sqrt 3 := by
  have hxy : p.x = p.y := gap1 R p μ hp hcrit
  have hyz : p.y = p.z := gap2 R p μ hp hcrit
  have hsphere := hcrit.2.2.2
  rw [hxy, hyz] at hsphere
  have hsqrt_pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hmul_sq : (p.z * Real.sqrt 3) ^ 2 = R ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    nlinarith [hsphere]
  have hfactor :
      (p.z * Real.sqrt 3 - R) * (p.z * Real.sqrt 3 + R) = 0 := by
    calc
      (p.z * Real.sqrt 3 - R) * (p.z * Real.sqrt 3 + R) =
          (p.z * Real.sqrt 3) ^ 2 - R ^ 2 := by ring
      _ = 0 := by
        rw [hmul_sq]
        ring
  have hmul : p.z * Real.sqrt 3 = R := by
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · linarith
    · have hpositive : 0 < p.z * Real.sqrt 3 + R :=
        add_pos (mul_pos hp.2.2 hsqrt_pos) hR
      exfalso
      exact (ne_of_gt hpositive) hplus
  exact (eq_div_iff (ne_of_gt hsqrt_pos)).2 hmul

theorem gap4 (R : ℝ) (hR : 0 < R) (p : Point3) (μ : ℝ)
    (hp : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z)
    (hcrit : critical R p μ) :
    p.x = R / Real.sqrt 3 := by
  calc
    p.x = p.y := gap1 R p μ hp hcrit
    _ = p.z := gap2 R p μ hp hcrit
    _ = R / Real.sqrt 3 := gap3 R hR p μ hp hcrit

theorem gap5 (R : ℝ) (hR : 0 < R) :
    {p : Point3 | 0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
      ∃ μ, critical R p μ} = ({candidate R} : Set Point3) := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    rcases hp with ⟨hx, hy, hz, μ, hcrit⟩
    have hpos : 0 < p.x ∧ 0 < p.y ∧ 0 < p.z := ⟨hx, hy, hz⟩
    have hp_eq : p = candidate R := by
      apply point3_eq_of_fields
      · simpa [candidate] using (gap4 R hR p μ hpos hcrit)
      · simpa [candidate] using
          ((gap2 R p μ hpos hcrit).trans (gap3 R hR p μ hpos hcrit))
      · simpa [candidate] using (gap3 R hR p μ hpos hcrit)
    simpa using hp_eq
  · intro hp
    have hp_eq : p = candidate R := by simpa using hp
    subst p
    have hsqrt_pos : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.2 (by norm_num)
    have hcoord_pos : 0 < R / Real.sqrt 3 := div_pos hR hsqrt_pos
    change 0 < R / Real.sqrt 3 ∧ 0 < R / Real.sqrt 3 ∧
      0 < R / Real.sqrt 3 ∧ ∃ μ, critical R (candidate R) μ
    refine ⟨hcoord_pos, hcoord_pos, hcoord_pos, ?_⟩
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hcoord_sq :
        (R / Real.sqrt 3) ^ 2 = R ^ 2 / 3 := by
      rw [div_pow, hsqrt_sq]
    refine ⟨(R / Real.sqrt 3) / 2, ?_⟩
    unfold critical candidate
    refine ⟨?_, ?_, ?_, ?_⟩
    · ring
    · ring
    · ring
    · calc
        (R / Real.sqrt 3) ^ 2 + (R / Real.sqrt 3) ^ 2 +
            (R / Real.sqrt 3) ^ 2 =
          3 * (R / Real.sqrt 3) ^ 2 := by ring
        _ = 3 * (R ^ 2 / 3) := by rw [hcoord_sq]
        _ = R ^ 2 := by ring

theorem gap6 (R : ℝ) (p : Point3) (hfeas : feasible R p)
    (hboundary : p.x = 0 ∨ p.y = 0 ∨ p.z = 0) :
    volume p = 0 := by
  rcases hboundary with hx | hy | hz
  · simp [volume, hx]
  · simp [volume, hy]
  · simp [volume, hz]

theorem gap7 (R : ℝ) (hR : 0 < R) :
    maximizers R = ({candidate R} : Set Point3) := by
  set_option maxHeartbeats 2000000 in
  exact by
    let a : ℝ := R / Real.sqrt 3
    have hc_mem :
        candidate R ∈
          {p : Point3 | 0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
            ∃ μ, critical R p μ} := by
      rw [gap5 R hR]
      simp
    rcases hc_mem with ⟨hcx, hcy, hcz, μ, hcritc⟩
    have hcfeas : feasible R (candidate R) := by
      unfold feasible
      exact ⟨le_of_lt hcx, le_of_lt hcy, le_of_lt hcz, hcritc.2.2.2⟩
    have ha_pos : 0 < a := by
      simpa [candidate, a] using hcx
    have ha_sq : 3 * a ^ 2 = R ^ 2 := by
      have hsphere := hcritc.2.2.2
      change a ^ 2 + a ^ 2 + a ^ 2 = R ^ 2 at hsphere
      calc
        3 * a ^ 2 = a ^ 2 + a ^ 2 + a ^ 2 := by ring
        _ = R ^ 2 := hsphere
    have hbound : ∀ q : Point3, feasible R q →
        volume q ≤ volume (candidate R) ∧
          (volume q = volume (candidate R) → q = candidate R) := by
      intro q hq
      unfold feasible at hq
      rcases hq with ⟨hx, hy, hz, hsphere⟩
      have hrel : q.x ^ 2 + q.y ^ 2 + q.z ^ 2 = 3 * a ^ 2 :=
        hsphere.trans ha_sq.symm
      have hdecomp :
          (q.z - a) ^ 2 * (q.z + 2 * a) +
              q.z * (q.x - q.y) ^ 2 =
            2 * (a ^ 3 - q.x * q.y * q.z) := by
        calc
          (q.z - a) ^ 2 * (q.z + 2 * a) +
                q.z * (q.x - q.y) ^ 2 =
              2 * a ^ 3 - 2 * q.x * q.y * q.z +
                q.z * (q.x ^ 2 + q.y ^ 2 + q.z ^ 2 - 3 * a ^ 2) := by
                  ring
          _ = 2 * (a ^ 3 - q.x * q.y * q.z) := by
            rw [hrel]
            ring
      have hzplus : 0 < q.z + 2 * a := by
        have htwoa : 0 < 2 * a := mul_pos (by norm_num) ha_pos
        exact add_pos_of_nonneg_of_pos hz htwoa
      have ht1_nonneg :
          0 ≤ (q.z - a) ^ 2 * (q.z + 2 * a) :=
        mul_nonneg (sq_nonneg (q.z - a)) (le_of_lt hzplus)
      have ht2_nonneg : 0 ≤ q.z * (q.x - q.y) ^ 2 :=
        mul_nonneg hz (sq_nonneg (q.x - q.y))
      have hsum_nonneg :
          0 ≤ (q.z - a) ^ 2 * (q.z + 2 * a) +
              q.z * (q.x - q.y) ^ 2 :=
        add_nonneg ht1_nonneg ht2_nonneg
      have hprod_le : q.x * q.y * q.z ≤ a ^ 3 := by
        rw [hdecomp] at hsum_nonneg
        nlinarith only [hsum_nonneg]
      have hvol_le : volume q ≤ volume (candidate R) := by
        change 4 * q.x * q.y * q.z ≤ 4 * a * a * a
        nlinarith only [hprod_le]
      refine ⟨hvol_le, ?_⟩
      intro hvol_eq
      have hprod_eq : q.x * q.y * q.z = a ^ 3 := by
        change 4 * q.x * q.y * q.z = 4 * a * a * a at hvol_eq
        nlinarith only [hvol_eq]
      have hsum_zero :
          (q.z - a) ^ 2 * (q.z + 2 * a) +
              q.z * (q.x - q.y) ^ 2 = 0 := by
        rw [hdecomp, hprod_eq]
        ring
      have ht1_zero : (q.z - a) ^ 2 * (q.z + 2 * a) = 0 := by
        apply le_antisymm
        · calc
            (q.z - a) ^ 2 * (q.z + 2 * a) ≤
                (q.z - a) ^ 2 * (q.z + 2 * a) +
                  q.z * (q.x - q.y) ^ 2 :=
              le_add_of_nonneg_right ht2_nonneg
            _ = 0 := hsum_zero
        · exact ht1_nonneg
      have ht2_zero : q.z * (q.x - q.y) ^ 2 = 0 := by
        simpa [ht1_zero] using hsum_zero
      have hsquare_z : (q.z - a) ^ 2 = 0 :=
        (mul_eq_zero.mp ht1_zero).resolve_right (ne_of_gt hzplus)
      have hz_eq : q.z = a := by
        nlinarith only [hsquare_z]
      have hz_ne : q.z ≠ 0 := by
        rw [hz_eq]
        exact ne_of_gt ha_pos
      have hsquare_xy : (q.x - q.y) ^ 2 = 0 :=
        (mul_eq_zero.mp ht2_zero).resolve_left hz_ne
      have hxy : q.x = q.y := by
        nlinarith only [hsquare_xy]
      have hrel' := hrel
      rw [← hxy, hz_eq] at hrel'
      have hx_sq : q.x ^ 2 = a ^ 2 := by
        nlinarith only [hrel']
      have hx_factor : (q.x - a) * (q.x + a) = 0 := by
        calc
          (q.x - a) * (q.x + a) = q.x ^ 2 - a ^ 2 := by ring
          _ = 0 := by
            rw [hx_sq]
            ring
      have hx_eq : q.x = a := by
        rcases mul_eq_zero.mp hx_factor with hminus | hplus
        · linarith only [hminus]
        · linarith only [hplus, hx, ha_pos]
      have hy_eq : q.y = a := by
        calc
          q.y = q.x := hxy.symm
          _ = a := hx_eq
      apply point3_eq_of_fields
      · simpa [candidate, a] using hx_eq
      · simpa [candidate, a] using hy_eq
      · simpa [candidate, a] using hz_eq
    apply Set.ext
    intro p
    constructor
    · intro hp
      change feasible R p ∧
        (∀ q, feasible R q → volume q ≤ volume p) at hp
      rcases hp with ⟨hpfeas, hpmax⟩
      have hpdata := hbound p hpfeas
      have hc_le : volume (candidate R) ≤ volume p :=
        hpmax (candidate R) hcfeas
      have hvol_eq : volume p = volume (candidate R) :=
        le_antisymm hpdata.1 hc_le
      simpa using (hpdata.2 hvol_eq)
    · intro hp
      have hp_eq : p = candidate R := by simpa using hp
      subst p
      change feasible R (candidate R) ∧
        ∀ q, feasible R q → volume q ≤ volume (candidate R)
      exact ⟨hcfeas, fun q hq => (hbound q hq).1⟩

end

end ProofGap.Exercise3694
