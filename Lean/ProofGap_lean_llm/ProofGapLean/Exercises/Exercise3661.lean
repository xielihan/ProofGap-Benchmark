import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3661

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def objective (q : Point3) : ℝ :=
  q.x ^ 2 + q.y ^ 2 + q.z ^ 2

def ellipsoid (a b c : ℝ) : Set Point3 :=
  {q | q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2 = 1}

def critical (a b c : ℝ) (q : Point3) (lambda : ℝ) : Prop :=
  2 * q.x * (1 + lambda / a ^ 2) = 0 ∧
    2 * q.y * (1 + lambda / b ^ 2) = 0 ∧
    2 * q.z * (1 + lambda / c ^ 2) = 0 ∧
    q ∈ ellipsoid a b c

def P₁ (a : ℝ) : Point3 := ⟨a, 0, 0⟩
def P₂ (a : ℝ) : Point3 := ⟨-a, 0, 0⟩
def P₃ (b : ℝ) : Point3 := ⟨0, b, 0⟩
def P₄ (b : ℝ) : Point3 := ⟨0, -b, 0⟩
def P₅ (c : ℝ) : Point3 := ⟨0, 0, c⟩
def P₆ (c : ℝ) : Point3 := ⟨0, 0, -c⟩

def maximizers (a b c : ℝ) : Set Point3 :=
  {q | q ∈ ellipsoid a b c ∧
    ∀ r ∈ ellipsoid a b c, objective r ≤ objective q}

def minimizers (a b c : ℝ) : Set Point3 :=
  {q | q ∈ ellipsoid a b c ∧
    ∀ r ∈ ellipsoid a b c, objective q ≤ objective r}

def secondVariationAtY (a b c dx dz : ℝ) : ℝ :=
  2 * (1 - b ^ 2 / a ^ 2) * dx ^ 2 +
    2 * (1 - b ^ 2 / c ^ 2) * dz ^ 2

private theorem point3_eq_of_coords
    (p q : Point3) (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
      cases q with
      | mk qx qy qz =>
          simp only at hx hy hz
          subst qx
          subst qy
          subst qz
          rfl

private theorem square_lt_square_of_pos_lt
    (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    x ^ 2 < y ^ 2 := by
  nlinarith

private theorem lambda_eq_neg_square
    (d lambda : ℝ) (hd : d ≠ 0)
    (h : 1 + lambda / d ^ 2 = 0) :
    lambda = -d ^ 2 := by
  have hdiv : lambda / d ^ 2 = -1 := by
    linarith only [h]
  have hmul : lambda = (-1 : ℝ) * d ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 hd)).mp hdiv
  simpa using hmul

private theorem square_eq_square_of_div_eq_one
    (u d : ℝ) (hd : d ≠ 0)
    (h : u ^ 2 / d ^ 2 = 1) :
    u ^ 2 = d ^ 2 := by
  have hmul : u ^ 2 = (1 : ℝ) * d ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 hd)).mp h
  simpa using hmul

private theorem eq_or_eq_neg_of_square_eq_square
    (u d : ℝ) (h : u ^ 2 = d ^ 2) :
    u = d ∨ u = -d := by
  have hprod : (u - d) * (u + d) = 0 := by
    nlinarith only [h]
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · left
    linarith only [hminus]
  · right
    linarith only [hplus]

private theorem critical_mem_axis_set
    (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) (q : Point3) :
    (∃ lambda, critical a b c q lambda) →
      q ∈ ({P₁ a, P₂ a, P₃ b, P₄ b, P₅ c, P₆ c} : Set Point3) := by
  intro h
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have habsq : b ^ 2 < a ^ 2 :=
    square_lt_square_of_pos_lt b a hb hab
  have hbcsq : c ^ 2 < b ^ 2 :=
    square_lt_square_of_pos_lt c b hc hbc
  have hacsq : c ^ 2 < a ^ 2 := lt_trans hbcsq habsq
  rcases h with ⟨lambda, hcrit⟩
  change
    2 * q.x * (1 + lambda / a ^ 2) = 0 ∧
      2 * q.y * (1 + lambda / b ^ 2) = 0 ∧
      2 * q.z * (1 + lambda / c ^ 2) = 0 ∧
      q ∈ ellipsoid a b c at hcrit
  rcases hcrit with ⟨hx, hy, hz, he⟩
  change q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2 = 1 at he
  by_cases hx0 : q.x = 0
  · by_cases hy0 : q.y = 0
    · have hzdiv : q.z ^ 2 / c ^ 2 = 1 := by
        simpa [hx0, hy0] using he
      have hzs : q.z ^ 2 = c ^ 2 :=
        square_eq_square_of_div_eq_one q.z c hc0 hzdiv
      rcases eq_or_eq_neg_of_square_eq_square q.z c hzs with hzval | hzval
      · have hq : q = P₅ c := by
          apply point3_eq_of_coords
          · exact hx0
          · exact hy0
          · exact hzval
        simp [hq]
      · have hq : q = P₆ c := by
          apply point3_eq_of_coords
          · exact hx0
          · exact hy0
          · exact hzval
        simp [hq]
    · have hfb : 1 + lambda / b ^ 2 = 0 := by
        exact (mul_eq_zero.mp hy).resolve_left (mul_ne_zero (by norm_num) hy0)
      have hlamb : lambda = -b ^ 2 :=
        lambda_eq_neg_square b lambda hb0 hfb
      have hz0 : q.z = 0 := by
        by_contra hz0
        have hfc : 1 + lambda / c ^ 2 = 0 := by
          exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hz0)
        have hlamc : lambda = -c ^ 2 :=
          lambda_eq_neg_square c lambda hc0 hfc
        linarith only [hlamb, hlamc, hbcsq]
      have hydiv : q.y ^ 2 / b ^ 2 = 1 := by
        simpa [hx0, hz0] using he
      have hys : q.y ^ 2 = b ^ 2 :=
        square_eq_square_of_div_eq_one q.y b hb0 hydiv
      rcases eq_or_eq_neg_of_square_eq_square q.y b hys with hyval | hyval
      · have hq : q = P₃ b := by
          apply point3_eq_of_coords
          · exact hx0
          · exact hyval
          · exact hz0
        simp [hq]
      · have hq : q = P₄ b := by
          apply point3_eq_of_coords
          · exact hx0
          · exact hyval
          · exact hz0
        simp [hq]
  · have hfa : 1 + lambda / a ^ 2 = 0 := by
      exact (mul_eq_zero.mp hx).resolve_left (mul_ne_zero (by norm_num) hx0)
    have hlama : lambda = -a ^ 2 :=
      lambda_eq_neg_square a lambda ha0 hfa
    have hy0 : q.y = 0 := by
      by_contra hy0
      have hfb : 1 + lambda / b ^ 2 = 0 := by
        exact (mul_eq_zero.mp hy).resolve_left (mul_ne_zero (by norm_num) hy0)
      have hlamb : lambda = -b ^ 2 :=
        lambda_eq_neg_square b lambda hb0 hfb
      linarith only [hlama, hlamb, habsq]
    have hz0 : q.z = 0 := by
      by_contra hz0
      have hfc : 1 + lambda / c ^ 2 = 0 := by
        exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hz0)
      have hlamc : lambda = -c ^ 2 :=
        lambda_eq_neg_square c lambda hc0 hfc
      linarith only [hlama, hlamc, hacsq]
    have hxdiv : q.x ^ 2 / a ^ 2 = 1 := by
      simpa [hy0, hz0] using he
    have hxs : q.x ^ 2 = a ^ 2 :=
      square_eq_square_of_div_eq_one q.x a ha0 hxdiv
    rcases eq_or_eq_neg_of_square_eq_square q.x a hxs with hxval | hxval
    · have hq : q = P₁ a := by
        apply point3_eq_of_coords
        · exact hxval
        · exact hy0
        · exact hz0
      simp [hq]
    · have hq : q = P₂ a := by
        apply point3_eq_of_coords
        · exact hxval
        · exact hy0
        · exact hz0
      simp [hq]

private theorem axis_set_mem_critical
    (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) (q : Point3) :
    q ∈ ({P₁ a, P₂ a, P₃ b, P₄ b, P₅ c, P₆ c} : Set Point3) →
      ∃ lambda, critical a b c q lambda := by
  intro h
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨-a ^ 2, ?_⟩
    simp [critical, ellipsoid, P₁, ha0]
  · refine ⟨-a ^ 2, ?_⟩
    simp [critical, ellipsoid, P₂, ha0]
  · refine ⟨-b ^ 2, ?_⟩
    simp [critical, ellipsoid, P₃, hb0]
  · refine ⟨-b ^ 2, ?_⟩
    simp [critical, ellipsoid, P₄, hb0]
  · refine ⟨-c ^ 2, ?_⟩
    simp [critical, ellipsoid, P₅, hc0]
  · refine ⟨-c ^ 2, ?_⟩
    simp [critical, ellipsoid, P₆, hc0]

private theorem objective_axis_bounds
    (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0)
    (q : Point3) (hq : q ∈ ellipsoid a b c) :
    c ^ 2 ≤ objective q ∧ objective q ≤ a ^ 2 := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have habsq : b ^ 2 < a ^ 2 := by nlinarith
  have hbcsq : c ^ 2 < b ^ 2 := by nlinarith
  have hacsq : c ^ 2 < a ^ 2 := by nlinarith
  have he := hq
  change q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2 = 1 at he
  have hu :
      a ^ 2 - objective q =
        (a ^ 2 / b ^ 2 - 1) * q.y ^ 2 +
          (a ^ 2 / c ^ 2 - 1) * q.z ^ 2 := by
    unfold objective
    field_simp [ha0, hb0, hc0] at he ⊢
    nlinarith [he]
  have habdiv : 0 ≤ a ^ 2 / b ^ 2 - 1 := by
    have h : 1 ≤ a ^ 2 / b ^ 2 :=
      (le_div_iff₀ hb2).2 (by nlinarith)
    nlinarith
  have hacdiv : 0 ≤ a ^ 2 / c ^ 2 - 1 := by
    have h : 1 ≤ a ^ 2 / c ^ 2 :=
      (le_div_iff₀ hc2).2 (by nlinarith)
    nlinarith
  have huy : 0 ≤ (a ^ 2 / b ^ 2 - 1) * q.y ^ 2 :=
    mul_nonneg habdiv (sq_nonneg q.y)
  have huz : 0 ≤ (a ^ 2 / c ^ 2 - 1) * q.z ^ 2 :=
    mul_nonneg hacdiv (sq_nonneg q.z)
  have hl :
      objective q - c ^ 2 =
        (1 - c ^ 2 / a ^ 2) * q.x ^ 2 +
          (1 - c ^ 2 / b ^ 2) * q.y ^ 2 := by
    unfold objective
    field_simp [ha0, hb0, hc0] at he ⊢
    nlinarith [he]
  have hcadiv : 0 ≤ 1 - c ^ 2 / a ^ 2 := by
    have h : c ^ 2 / a ^ 2 ≤ 1 :=
      (div_le_iff₀ ha2).2 (by nlinarith)
    nlinarith
  have hcbdiv : 0 ≤ 1 - c ^ 2 / b ^ 2 := by
    have h : c ^ 2 / b ^ 2 ≤ 1 :=
      (div_le_iff₀ hb2).2 (by nlinarith)
    nlinarith
  have hlx : 0 ≤ (1 - c ^ 2 / a ^ 2) * q.x ^ 2 :=
    mul_nonneg hcadiv (sq_nonneg q.x)
  have hly : 0 ≤ (1 - c ^ 2 / b ^ 2) * q.y ^ 2 :=
    mul_nonneg hcbdiv (sq_nonneg q.y)
  constructor <;> nlinarith

private theorem point_eq_major_axis
    (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0)
    (q : Point3) (hq : q ∈ ellipsoid a b c)
    (hobj : objective q = a ^ 2) :
    q = P₁ a ∨ q = P₂ a := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have habsq : b ^ 2 < a ^ 2 := by nlinarith
  have hacsq : c ^ 2 < a ^ 2 := by nlinarith
  have he := hq
  change q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2 = 1 at he
  have hu :
      a ^ 2 - objective q =
        (a ^ 2 / b ^ 2 - 1) * q.y ^ 2 +
          (a ^ 2 / c ^ 2 - 1) * q.z ^ 2 := by
    unfold objective
    field_simp [ha0, hb0, hc0] at he ⊢
    nlinarith [he]
  have habdiv : 0 < a ^ 2 / b ^ 2 - 1 := by
    have h : 1 < a ^ 2 / b ^ 2 :=
      (lt_div_iff₀ hb2).2 (by nlinarith)
    nlinarith
  have hacdiv : 0 < a ^ 2 / c ^ 2 - 1 := by
    have h : 1 < a ^ 2 / c ^ 2 :=
      (lt_div_iff₀ hc2).2 (by nlinarith)
    nlinarith
  have hy : q.y = 0 := by
    by_contra hy0
    have hpos : 0 < (a ^ 2 / b ^ 2 - 1) * q.y ^ 2 :=
      mul_pos habdiv (sq_pos_of_ne_zero hy0)
    have hnonneg : 0 ≤ (a ^ 2 / c ^ 2 - 1) * q.z ^ 2 :=
      mul_nonneg (le_of_lt hacdiv) (sq_nonneg q.z)
    nlinarith
  have hz : q.z = 0 := by
    by_contra hz0
    have hpos : 0 < (a ^ 2 / c ^ 2 - 1) * q.z ^ 2 :=
      mul_pos hacdiv (sq_pos_of_ne_zero hz0)
    have hnonneg : 0 ≤ (a ^ 2 / b ^ 2 - 1) * q.y ^ 2 :=
      mul_nonneg (le_of_lt habdiv) (sq_nonneg q.y)
    nlinarith
  have hxs : q.x ^ 2 = a ^ 2 := by
    simp [objective, hy, hz] at hobj
    exact hobj
  rcases le_total 0 q.x with hxnonneg | hxnonpos
  · left
    have hx : q.x = a := by nlinarith
    apply point3_eq_of_coords
    · exact hx
    · exact hy
    · exact hz
  · right
    have hx : q.x = -a := by nlinarith
    apply point3_eq_of_coords
    · exact hx
    · exact hy
    · exact hz

private theorem point_eq_minor_axis
    (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0)
    (q : Point3) (hq : q ∈ ellipsoid a b c)
    (hobj : objective q = c ^ 2) :
    q = P₅ c ∨ q = P₆ c := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hbcsq : c ^ 2 < b ^ 2 := by nlinarith
  have hacsq : c ^ 2 < a ^ 2 := by nlinarith
  have he := hq
  change q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2 = 1 at he
  have hl :
      objective q - c ^ 2 =
        (1 - c ^ 2 / a ^ 2) * q.x ^ 2 +
          (1 - c ^ 2 / b ^ 2) * q.y ^ 2 := by
    unfold objective
    field_simp [ha0, hb0, hc0] at he ⊢
    nlinarith [he]
  have hcadiv : 0 < 1 - c ^ 2 / a ^ 2 := by
    have h : c ^ 2 / a ^ 2 < 1 :=
      (div_lt_iff₀ ha2).2 (by nlinarith)
    nlinarith
  have hcbdiv : 0 < 1 - c ^ 2 / b ^ 2 := by
    have h : c ^ 2 / b ^ 2 < 1 :=
      (div_lt_iff₀ hb2).2 (by nlinarith)
    nlinarith
  have hx : q.x = 0 := by
    by_contra hx0
    have hpos : 0 < (1 - c ^ 2 / a ^ 2) * q.x ^ 2 :=
      mul_pos hcadiv (sq_pos_of_ne_zero hx0)
    have hnonneg : 0 ≤ (1 - c ^ 2 / b ^ 2) * q.y ^ 2 :=
      mul_nonneg (le_of_lt hcbdiv) (sq_nonneg q.y)
    nlinarith
  have hy : q.y = 0 := by
    by_contra hy0
    have hpos : 0 < (1 - c ^ 2 / b ^ 2) * q.y ^ 2 :=
      mul_pos hcbdiv (sq_pos_of_ne_zero hy0)
    have hnonneg : 0 ≤ (1 - c ^ 2 / a ^ 2) * q.x ^ 2 :=
      mul_nonneg (le_of_lt hcadiv) (sq_nonneg q.x)
    nlinarith
  have hzs : q.z ^ 2 = c ^ 2 := by
    simp [objective, hx, hy] at hobj
    exact hobj
  rcases le_total 0 q.z with hznonneg | hznonpos
  · left
    have hz : q.z = c := by nlinarith
    apply point3_eq_of_coords
    · exact hx
    · exact hy
    · exact hz
  · right
    have hz : q.z = -c := by nlinarith
    apply point3_eq_of_coords
    · exact hx
    · exact hy
    · exact hz

theorem gap1 (a : ℝ) :
    ∃ P : Point3, P = P₁ a := by
  exact ⟨P₁ a, rfl⟩

theorem gap2 (a : ℝ) :
    ∃ P : Point3, P = P₂ a := by
  exact ⟨P₂ a, rfl⟩

theorem gap3 (b : ℝ) :
    ∃ P : Point3, P = P₃ b := by
  exact ⟨P₃ b, rfl⟩

theorem gap4 (b : ℝ) :
    ∃ P : Point3, P = P₄ b := by
  exact ⟨P₄ b, rfl⟩

theorem gap5 (c : ℝ) :
    ∃ P : Point3, P = P₅ c := by
  exact ⟨P₅ c, rfl⟩

theorem gap6 (c : ℝ) :
    ∃ P : Point3, P = P₆ c := by
  exact ⟨P₆ c, rfl⟩

theorem gap7 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    {q | ∃ lambda, critical a b c q lambda} =
      ({P₁ a, P₂ a, P₃ b, P₄ b, P₅ c, P₆ c} : Set Point3) := by
  ext q
  constructor
  · exact critical_mem_axis_set a b c hab hbc hc q
  · exact axis_set_mem_critical a b c hab hbc hc q

theorem gap8 (a : ℝ) :
    objective (P₁ a) = objective (P₂ a) := by
  simp [objective, P₁, P₂]

theorem gap9 (a : ℝ) :
    objective (P₂ a) = a ^ 2 := by
  simp [objective, P₂]

theorem gap10 (a : ℝ) :
    objective (P₁ a) = a ^ 2 := by
  simp [objective, P₁]

theorem gap11 (b : ℝ) :
    objective (P₃ b) = objective (P₄ b) := by
  simp [objective, P₃, P₄]

theorem gap12 (b : ℝ) :
    objective (P₄ b) = b ^ 2 := by
  simp [objective, P₄]

theorem gap13 (b : ℝ) :
    objective (P₃ b) = b ^ 2 := by
  simp [objective, P₃]

theorem gap14 (c : ℝ) :
    objective (P₅ c) = objective (P₆ c) := by
  simp [objective, P₅, P₆]

theorem gap15 (c : ℝ) :
    objective (P₆ c) = c ^ 2 := by
  simp [objective, P₆]

theorem gap16 (c : ℝ) :
    objective (P₅ c) = c ^ 2 := by
  simp [objective, P₅]

theorem gap17 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    maximizers a b c = ({P₁ a, P₂ a} : Set Point3) := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  ext q
  constructor
  · intro h
    change q ∈ ellipsoid a b c ∧
      ∀ r ∈ ellipsoid a b c, objective r ≤ objective q at h
    rcases h with ⟨hq, hmax⟩
    have hp : P₁ a ∈ ellipsoid a b c := by
      simp [ellipsoid, P₁, ha0]
    have hcomp := hmax (P₁ a) hp
    rw [gap10 a] at hcomp
    have hu := (objective_axis_bounds a b c hab hbc hc q hq).2
    have heq : objective q = a ^ 2 := le_antisymm hu hcomp
    rcases point_eq_major_axis a b c hab hbc hc q hq heq with hq1 | hq2
    · simp [hq1]
    · simp [hq2]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · change P₁ a ∈ ellipsoid a b c ∧
        ∀ r ∈ ellipsoid a b c, objective r ≤ objective (P₁ a)
      constructor
      · simp [ellipsoid, P₁, ha0]
      · intro r hr
        have hu := (objective_axis_bounds a b c hab hbc hc r hr).2
        simpa [objective, P₁] using hu
    · change P₂ a ∈ ellipsoid a b c ∧
        ∀ r ∈ ellipsoid a b c, objective r ≤ objective (P₂ a)
      constructor
      · simp [ellipsoid, P₂, ha0]
      · intro r hr
        have hu := (objective_axis_bounds a b c hab hbc hc r hr).2
        simpa [objective, P₂] using hu

theorem gap18 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    minimizers a b c = ({P₅ c, P₆ c} : Set Point3) := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have hc0 : c ≠ 0 := ne_of_gt hc
  ext q
  constructor
  · intro h
    change q ∈ ellipsoid a b c ∧
      ∀ r ∈ ellipsoid a b c, objective q ≤ objective r at h
    rcases h with ⟨hq, hmin⟩
    have hp : P₅ c ∈ ellipsoid a b c := by
      simp [ellipsoid, P₅, hc0]
    have hcomp := hmin (P₅ c) hp
    rw [gap16 c] at hcomp
    have hl := (objective_axis_bounds a b c hab hbc hc q hq).1
    have heq : objective q = c ^ 2 := le_antisymm hcomp hl
    rcases point_eq_minor_axis a b c hab hbc hc q hq heq with hq1 | hq2
    · simp [hq1]
    · simp [hq2]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · change P₅ c ∈ ellipsoid a b c ∧
        ∀ r ∈ ellipsoid a b c, objective (P₅ c) ≤ objective r
      constructor
      · simp [ellipsoid, P₅, hc0]
      · intro r hr
        have hl := (objective_axis_bounds a b c hab hbc hc r hr).1
        simpa [objective, P₅] using hl
    · change P₆ c ∈ ellipsoid a b c ∧
        ∀ r ∈ ellipsoid a b c, objective (P₆ c) ≤ objective r
      constructor
      · simp [ellipsoid, P₆, hc0]
      · intro r hr
        have hl := (objective_axis_bounds a b c hab hbc hc r hr).1
        simpa [objective, P₆] using hl

theorem gap19 (a b c dx dz : ℝ) :
    secondVariationAtY a b c dx dz =
      2 * (1 - b ^ 2 / a ^ 2) * dx ^ 2 +
        2 * (1 - b ^ 2 / c ^ 2) * dz ^ 2 := by
  rfl

theorem gap20 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    secondVariationAtY a b c 1 0 > 0 := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have habsq : b ^ 2 < a ^ 2 := by nlinarith
  have hratio : b ^ 2 / a ^ 2 < 1 := by
    exact (div_lt_iff₀ ha2).2 (by nlinarith)
  unfold secondVariationAtY
  norm_num
  nlinarith

theorem gap21 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    secondVariationAtY a b c 0 1 < 0 := by
  have hb : 0 < b := lt_trans hc hbc
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hbcsq : c ^ 2 < b ^ 2 := by nlinarith
  have hratio : 1 < b ^ 2 / c ^ 2 := by
    exact (lt_div_iff₀ hc2).2 (by nlinarith)
  unfold secondVariationAtY
  norm_num
  nlinarith

theorem gap22 (a b c : ℝ) (hab : a > b) (hbc : b > c) (hc : c > 0) :
    P₃ b ∉ maximizers a b c ∧ P₃ b ∉ minimizers a b c ∧
      P₄ b ∉ maximizers a b c ∧ P₄ b ∉ minimizers a b c := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [gap17 a b c hab hbc hc, gap18 a b c hab hbc hc]
  simp [P₁, P₂, P₃, P₄, P₅, P₆, ha0, hb0, hc0]

end

end ProofGap.Exercise3661
