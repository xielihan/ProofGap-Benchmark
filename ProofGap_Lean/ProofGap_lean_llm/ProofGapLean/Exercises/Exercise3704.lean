import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3704

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def distanceSq (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2

def sectionSet (a b A B C : ℝ) : Set Point3 :=
  {p | A * p.x + B * p.y + C * p.z = 0 ∧
    p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 ≤ 1}

def sectionBoundary (a b A B C : ℝ) : Set Point3 :=
  {p | A * p.x + B * p.y + C * p.z = 0 ∧
    p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 = 1}

def critical (a b A B C : ℝ) (p : Point3) (lam mu : ℝ) : Prop :=
  (1 - mu / a ^ 2) * p.x + lam * A = 0 ∧
    (1 - mu / b ^ 2) * p.y + lam * B = 0 ∧
    p.z + lam * C = 0 ∧
    A * p.x + B * p.y + C * p.z = 0 ∧
    p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 = 1

def characteristic (a b A B C mu : ℝ) : Prop :=
  C ^ 2 / (a ^ 2 * b ^ 2) * mu ^ 2 -
      (B ^ 2 / a ^ 2 + A ^ 2 / b ^ 2 +
        C ^ 2 / a ^ 2 + C ^ 2 / b ^ 2) * mu +
      A ^ 2 + B ^ 2 + C ^ 2 = 0

def majorSq (a b A B C : ℝ) : ℝ :=
  sSup (distanceSq '' sectionBoundary a b A B C)

def minorSq (a b A B C : ℝ) : ℝ :=
  sInf (distanceSq '' sectionBoundary a b A B C)

def majorRadius (a b A B C : ℝ) : ℝ :=
  Real.sqrt (majorSq a b A B C)

def minorRadius (a b A B C : ℝ) : ℝ :=
  Real.sqrt (minorSq a b A B C)

def sectionArea (a b A B C : ℝ) : ℝ :=
  Real.pi * majorRadius a b A B C * minorRadius a b A B C

private def quadValues (q r s : ℝ) : Set ℝ :=
  {w | ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧
    w = q * x ^ 2 + 2 * r * x * y + s * y ^ 2}

private theorem exists_unit_pair (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ x ^ 2 - y ^ 2 = u ∧ 2 * x * y = v := by
  have hu_lower : -1 ≤ u := by nlinarith [sq_nonneg v, sq_nonneg (u + 1)]
  by_cases hzero : 1 + u = 0
  · have hu : u = -1 := by linarith
    have hv : v = 0 := by nlinarith [sq_nonneg v]
    refine ⟨0, 1, ?_⟩
    simp [hu, hv]
  · have harg : 0 ≤ (1 + u) / 2 := by linarith
    let x : ℝ := Real.sqrt ((1 + u) / 2)
    have hx_sq : x ^ 2 = (1 + u) / 2 := by
      dsimp [x]
      exact Real.sq_sqrt harg
    have hnum_pos : 0 < 1 + u := by
      apply lt_of_le_of_ne
      · linarith
      · exact Ne.symm hzero
    have hx_pos : 0 < x := by
      apply Real.sqrt_pos.2
      exact div_pos hnum_pos (by norm_num)
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    let y : ℝ := v / (2 * x)
    have hy_sq : y ^ 2 = (1 - u) / 2 := by
      dsimp [y]
      field_simp [hx_ne]
      nlinarith [huv, hx_sq]
    have hxy : 2 * x * y = v := by
      dsimp [y]
      field_simp [hx_ne]
    refine ⟨x, y, ?_, ?_, hxy⟩
    · nlinarith
    · nlinarith

private theorem quadValues_extrema (q r s : ℝ) :
    let t := (q + s) / 2
    let d := (q - s) / 2
    let R := Real.sqrt (d ^ 2 + r ^ 2)
    sSup (quadValues q r s) = t + R ∧
      sInf (quadValues q r s) = t - R := by
  dsimp only
  let t : ℝ := (q + s) / 2
  let d : ℝ := (q - s) / 2
  let R : ℝ := Real.sqrt (d ^ 2 + r ^ 2)
  have hrad : 0 ≤ d ^ 2 + r ^ 2 := by positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = d ^ 2 + r ^ 2 := by
    dsimp [R]
    exact Real.sq_sqrt hrad
  have hbound (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) :
      t - R ≤ q * x ^ 2 + 2 * r * x * y + s * y ^ 2 ∧
        q * x ^ 2 + 2 * r * x * y + s * y ^ 2 ≤ t + R := by
    let u : ℝ := x ^ 2 - y ^ 2
    let v : ℝ := 2 * x * y
    have huv : u ^ 2 + v ^ 2 = 1 := by
      dsimp [u, v]
      calc
        (x ^ 2 - y ^ 2) ^ 2 + (2 * x * y) ^ 2 =
            (x ^ 2 + y ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hunit]; norm_num
    have hcauchy : (d * u + r * v) ^ 2 ≤ R ^ 2 := by
      have hn : 0 ≤ (d * v - r * u) ^ 2 := sq_nonneg _
      rw [hRsq]
      nlinarith
    have hform :
        q * x ^ 2 + 2 * r * x * y + s * y ^ 2 = t + (d * u + r * v) := by
      calc
        q * x ^ 2 + 2 * r * x * y + s * y ^ 2 =
            t + (d * u + r * v) +
              (q + s) / 2 * (x ^ 2 + y ^ 2 - 1) := by
                dsimp [t, d, u, v]
                ring
        _ = t + (d * u + r * v) := by rw [hunit]; ring
    rw [hform]
    constructor <;> nlinarith [sq_nonneg (d * u + r * v + R),
      sq_nonneg (d * u + r * v - R)]
  have hendpoints :
      t + R ∈ quadValues q r s ∧ t - R ∈ quadValues q r s := by
    by_cases hRzero : R = 0
    · have hd : d = 0 := by nlinarith [sq_nonneg d, sq_nonneg r]
      have hr : r = 0 := by nlinarith [sq_nonneg d, sq_nonneg r]
      constructor
      · refine ⟨1, 0, by norm_num, ?_⟩
        dsimp [t, d] at hd ⊢
        rw [hRzero]
        nlinarith
      · refine ⟨1, 0, by norm_num, ?_⟩
        dsimp [t, d] at hd ⊢
        rw [hRzero]
        nlinarith
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
      have huvPlus : (d / R) ^ 2 + (r / R) ^ 2 = 1 := by
        field_simp [hRzero]
        nlinarith
      have huvMinus : (-d / R) ^ 2 + (-r / R) ^ 2 = 1 := by
        field_simp [hRzero]
        nlinarith
      rcases exists_unit_pair (d / R) (r / R) huvPlus with
        ⟨xp, yp, hpunit, hpu, hpv⟩
      rcases exists_unit_pair (-d / R) (-r / R) huvMinus with
        ⟨xm, ym, hmunit, hmu, hmv⟩
      constructor
      · refine ⟨xp, yp, hpunit, ?_⟩
        have hform :
            q * xp ^ 2 + 2 * r * xp * yp + s * yp ^ 2 =
              t + d * (xp ^ 2 - yp ^ 2) + r * (2 * xp * yp) := by
          calc
            q * xp ^ 2 + 2 * r * xp * yp + s * yp ^ 2 =
                (t + d * (xp ^ 2 - yp ^ 2) + r * (2 * xp * yp)) +
                  (q + s) / 2 * (xp ^ 2 + yp ^ 2 - 1) := by
                    dsimp [t, d]
                    ring
            _ = t + d * (xp ^ 2 - yp ^ 2) + r * (2 * xp * yp) := by
              rw [hpunit]
              ring
        rw [hform, hpu, hpv]
        field_simp [hRzero]
        nlinarith
      · refine ⟨xm, ym, hmunit, ?_⟩
        have hform :
            q * xm ^ 2 + 2 * r * xm * ym + s * ym ^ 2 =
              t + d * (xm ^ 2 - ym ^ 2) + r * (2 * xm * ym) := by
          calc
            q * xm ^ 2 + 2 * r * xm * ym + s * ym ^ 2 =
                (t + d * (xm ^ 2 - ym ^ 2) + r * (2 * xm * ym)) +
                  (q + s) / 2 * (xm ^ 2 + ym ^ 2 - 1) := by
                    dsimp [t, d]
                    ring
            _ = t + d * (xm ^ 2 - ym ^ 2) + r * (2 * xm * ym) := by
              rw [hmunit]
              ring
        rw [hform, hmu, hmv]
        field_simp [hRzero]
        nlinarith
  have hnonempty : (quadValues q r s).Nonempty := ⟨t + R, hendpoints.1⟩
  have hupper : ∀ w ∈ quadValues q r s, w ≤ t + R := by
    intro w hw
    rcases hw with ⟨x, y, hunit, rfl⟩
    exact (hbound x y hunit).2
  have hlower : ∀ w ∈ quadValues q r s, t - R ≤ w := by
    intro w hw
    rcases hw with ⟨x, y, hunit, rfl⟩
    exact (hbound x y hunit).1
  have hbddAbove : BddAbove (quadValues q r s) := ⟨t + R, hupper⟩
  have hbddBelow : BddBelow (quadValues q r s) := ⟨t - R, hlower⟩
  constructor
  · exact le_antisymm (csSup_le hnonempty hupper)
      (le_csSup hbddAbove hendpoints.1)
  · exact le_antisymm (csInf_le hbddBelow hendpoints.2)
      (le_csInf hnonempty hlower)

private theorem section_values_eq (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    distanceSq '' sectionBoundary a b A B C =
      quadValues
        (a ^ 2 + (A * a / C) ^ 2)
        ((A * a / C) * (B * b / C))
        (b ^ 2 + (B * b / C) ^ 2) := by
  ext w
  constructor
  · rintro ⟨p, ⟨hplane, hunit⟩, rfl⟩
    refine ⟨p.x / a, p.y / b, ?_, ?_⟩
    · simpa [div_pow] using hunit
    · have hz : p.z = -(A * p.x + B * p.y) / C := by
        field_simp [hC]
        nlinarith [hplane]
      unfold distanceSq
      rw [hz]
      field_simp [ne_of_gt ha, ne_of_gt hb, hC]
      ring
  · rintro ⟨u, v, huv, rfl⟩
    let p : Point3 :=
      ⟨a * u, b * v, -(A * (a * u) + B * (b * v)) / C⟩
    refine ⟨p, ?_, ?_⟩
    · constructor
      · dsimp [p]
        field_simp [hC]
        ring
      · dsimp [p]
        field_simp [ne_of_gt ha, ne_of_gt hb]
        nlinarith
    · dsimp [p, distanceSq]
      field_simp [hC]
      ring

private theorem section_product (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    majorSq a b A B C * minorSq a b A B C =
      a ^ 2 * b ^ 2 * (A ^ 2 + B ^ 2 + C ^ 2) / C ^ 2 := by
  let q : ℝ := a ^ 2 + (A * a / C) ^ 2
  let r : ℝ := (A * a / C) * (B * b / C)
  let s : ℝ := b ^ 2 + (B * b / C) ^ 2
  let t : ℝ := (q + s) / 2
  let d : ℝ := (q - s) / 2
  let R : ℝ := Real.sqrt (d ^ 2 + r ^ 2)
  have hrad : 0 ≤ d ^ 2 + r ^ 2 := by positivity
  have hRsq : R ^ 2 = d ^ 2 + r ^ 2 := by
    dsimp [R]
    exact Real.sq_sqrt hrad
  have hext := quadValues_extrema q r s
  change sSup (quadValues q r s) = t + R ∧
    sInf (quadValues q r s) = t - R at hext
  have hvalues :
      distanceSq '' sectionBoundary a b A B C = quadValues q r s := by
    simpa [q, r, s] using section_values_eq a b A B C ha hb hC
  unfold majorSq minorSq
  rw [hvalues, hext.1, hext.2]
  have halg : (t + R) * (t - R) = q * s - r ^ 2 := by
    calc
      (t + R) * (t - R) = t ^ 2 - R ^ 2 := by ring
      _ = q * s - r ^ 2 := by
        rw [hRsq]
        dsimp [t, d]
        ring
  rw [halg]
  dsimp [q, r, s]
  field_simp [hC]
  ring

private theorem section_sq_nonneg (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    0 ≤ majorSq a b A B C ∧ 0 ≤ minorSq a b A B C := by
  let q : ℝ := a ^ 2 + (A * a / C) ^ 2
  let r : ℝ := (A * a / C) * (B * b / C)
  let s : ℝ := b ^ 2 + (B * b / C) ^ 2
  let t : ℝ := (q + s) / 2
  let d : ℝ := (q - s) / 2
  let R : ℝ := Real.sqrt (d ^ 2 + r ^ 2)
  have hrad : 0 ≤ d ^ 2 + r ^ 2 := by positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = d ^ 2 + r ^ 2 := by
    dsimp [R]
    exact Real.sq_sqrt hrad
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hsum : 0 < A ^ 2 + B ^ 2 + C ^ 2 := by
    have hC2 : 0 < C ^ 2 := sq_pos_of_ne_zero hC
    nlinarith [sq_nonneg A, sq_nonneg B]
  have hdet_formula :
      q * s - r ^ 2 =
        a ^ 2 * b ^ 2 * (A ^ 2 + B ^ 2 + C ^ 2) / C ^ 2 := by
    dsimp [q, r, s]
    field_simp [hC]
    ring
  have hdet : 0 < q * s - r ^ 2 := by
    rw [hdet_formula]
    exact div_pos
      (mul_pos (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb)) hsum)
      (sq_pos_of_ne_zero hC)
  have htd : t ^ 2 - R ^ 2 = q * s - r ^ 2 := by
    calc
      t ^ 2 - R ^ 2 = t ^ 2 - (d ^ 2 + r ^ 2) := by rw [hRsq]
      _ = q * s - r ^ 2 := by
        dsimp [t, d]
        ring
  have hminor : 0 ≤ t - R := by nlinarith
  have hext := quadValues_extrema q r s
  change sSup (quadValues q r s) = t + R ∧
    sInf (quadValues q r s) = t - R at hext
  have hvalues :
      distanceSq '' sectionBoundary a b A B C = quadValues q r s := by
    simpa [q, r, s] using section_values_eq a b A B C ha hb hC
  unfold majorSq minorSq
  rw [hvalues, hext.1, hext.2]
  exact ⟨by linarith, hminor⟩

theorem gap1 (a b A B C lam mu : ℝ) (p : Point3)
    (hcrit : critical a b A B C p lam mu) :
    distanceSq p = mu := by
  rcases hcrit with ⟨hx, hy, hz, hp, hbnd⟩
  have hsum :
      (1 - mu / a ^ 2) * p.x ^ 2 +
          (1 - mu / b ^ 2) * p.y ^ 2 + p.z ^ 2 = 0 := by
    calc
      (1 - mu / a ^ 2) * p.x ^ 2 +
            (1 - mu / b ^ 2) * p.y ^ 2 + p.z ^ 2 =
          p.x * ((1 - mu / a ^ 2) * p.x + lam * A) +
            p.y * ((1 - mu / b ^ 2) * p.y + lam * B) +
            p.z * (p.z + lam * C) -
            lam * (A * p.x + B * p.y + C * p.z) := by ring
      _ = 0 := by rw [hx, hy, hz, hp]; ring
  unfold distanceSq
  calc
    p.x ^ 2 + p.y ^ 2 + p.z ^ 2 =
        ((1 - mu / a ^ 2) * p.x ^ 2 +
          (1 - mu / b ^ 2) * p.y ^ 2 + p.z ^ 2) +
          mu * (p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2) := by ring
    _ = mu := by rw [hsum, hbnd]; ring

theorem gap2 (a b A B C lam mu : ℝ) (p : Point3)
    (hcrit : critical a b A B C p lam mu) :
    (1 - mu / a ^ 2) * p.x + lam * A = 0 ∧
      (1 - mu / b ^ 2) * p.y + lam * B = 0 ∧
      p.z + lam * C = 0 ∧
      p ∈ sectionBoundary a b A B C := by
  rcases hcrit with ⟨hx, hy, hz, hp, hbnd⟩
  exact ⟨hx, hy, hz, hp, hbnd⟩

theorem gap3 (a b A B C lam mu : ℝ) (p : Point3)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcrit : critical a b A B C p lam mu) :
    characteristic a b A B C mu := by
  rcases hcrit with ⟨hx, hy, hz, hp, hbnd⟩
  let alpha : ℝ := 1 - mu / a ^ 2
  let beta : ℝ := 1 - mu / b ^ 2
  let K : ℝ := alpha * beta * C ^ 2 + alpha * B ^ 2 + beta * A ^ 2
  have hchar :
      C ^ 2 / (a ^ 2 * b ^ 2) * mu ^ 2 -
          (B ^ 2 / a ^ 2 + A ^ 2 / b ^ 2 +
            C ^ 2 / a ^ 2 + C ^ 2 / b ^ 2) * mu +
          A ^ 2 + B ^ 2 + C ^ 2 = K := by
    dsimp [K, alpha, beta]
    field_simp [ha, hb]
    <;> ring
  have hKx : K * p.x = 0 := by
    calc
      K * p.x =
          beta * A * (A * p.x + B * p.y + C * p.z) -
            A * B * (beta * p.y + lam * B) -
            beta * A * C * (p.z + lam * C) +
            (beta * C ^ 2 + B ^ 2) * (alpha * p.x + lam * A) := by
              dsimp [K]
              ring
      _ = 0 := by
        change
          beta * A * (A * p.x + B * p.y + C * p.z) -
              A * B * ((1 - mu / b ^ 2) * p.y + lam * B) -
              beta * A * C * (p.z + lam * C) +
              (beta * C ^ 2 + B ^ 2) *
                ((1 - mu / a ^ 2) * p.x + lam * A) = 0
        rw [hp, hy, hz, hx]
        ring
  have hKy : K * p.y = 0 := by
    calc
      K * p.y =
          alpha * B * (A * p.x + B * p.y + C * p.z) -
            A * B * (alpha * p.x + lam * A) -
            alpha * B * C * (p.z + lam * C) +
            (alpha * C ^ 2 + A ^ 2) * (beta * p.y + lam * B) := by
              dsimp [K]
              ring
      _ = 0 := by
        change
          alpha * B * (A * p.x + B * p.y + C * p.z) -
              A * B * ((1 - mu / a ^ 2) * p.x + lam * A) -
              alpha * B * C * (p.z + lam * C) +
              (alpha * C ^ 2 + A ^ 2) *
                ((1 - mu / b ^ 2) * p.y + lam * B) = 0
        rw [hp, hx, hz, hy]
        ring
  have hxy : p.x ≠ 0 ∨ p.y ≠ 0 := by
    by_cases hpx : p.x = 0
    · right
      intro hpy
      rw [hpx, hpy] at hbnd
      norm_num at hbnd
    · exact Or.inl hpx
  have hK : K = 0 := by
    rcases hxy with hpx | hpy
    · exact (mul_eq_zero.mp hKx).resolve_right hpx
    · exact (mul_eq_zero.mp hKy).resolve_right hpy
  change
    C ^ 2 / (a ^ 2 * b ^ 2) * mu ^ 2 -
        (B ^ 2 / a ^ 2 + A ^ 2 / b ^ 2 +
          C ^ 2 / a ^ 2 + C ^ 2 / b ^ 2) * mu +
        A ^ 2 + B ^ 2 + C ^ 2 = 0
  exact hchar.trans hK

theorem gap4 (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    majorSq a b A B C * minorSq a b A B C =
      a ^ 2 * b ^ 2 * (A ^ 2 + B ^ 2 + C ^ 2) / C ^ 2 := by
  exact section_product a b A B C ha hb hC

theorem gap5 (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    Real.pi * majorRadius a b A B C * minorRadius a b A B C =
      Real.pi * a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C| := by
  rcases section_sq_nonneg a b A B C ha hb hC with ⟨hmajor, hminor⟩
  have hsum : 0 ≤ A ^ 2 + B ^ 2 + C ^ 2 := by positivity
  have habs : 0 < |C| := abs_pos.mpr hC
  have hsmajor : (Real.sqrt (majorSq a b A B C)) ^ 2 = majorSq a b A B C :=
    Real.sq_sqrt hmajor
  have hsminor : (Real.sqrt (minorSq a b A B C)) ^ 2 = minorSq a b A B C :=
    Real.sq_sqrt hminor
  have hssum : (Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2)) ^ 2 =
      A ^ 2 + B ^ 2 + C ^ 2 := Real.sq_sqrt hsum
  have hleftsq :
      (majorRadius a b A B C * minorRadius a b A B C) ^ 2 =
        majorSq a b A B C * minorSq a b A B C := by
    simp only [majorRadius, minorRadius, mul_pow, hsmajor, hsminor]
  have hrightsq :
      (a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C|) ^ 2 =
        majorSq a b A B C * minorSq a b A B C := by
    rw [section_product a b A B C ha hb hC]
    field_simp [hC, ne_of_gt habs]
    rw [hssum, sq_abs]
    ring
  have hleft : 0 ≤ majorRadius a b A B C * minorRadius a b A B C := by
    unfold majorRadius minorRadius
    positivity
  have hright :
      0 ≤ a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C| := by
    positivity
  have hradius :
      majorRadius a b A B C * minorRadius a b A B C =
        a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C| := by
    nlinarith
  calc
    Real.pi * majorRadius a b A B C * minorRadius a b A B C =
        Real.pi * (majorRadius a b A B C * minorRadius a b A B C) := by ring
    _ = Real.pi * a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C| := by
      rw [hradius]
      ring

theorem gap6 (a b A B C : ℝ) (hC : C = 0) :
    (⟨0, 0, 0⟩ : Point3) ∈ sectionSet a b A B C := by
  simp [sectionSet, hC]

theorem gap7 (a b A B C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : C ≠ 0) :
    sectionArea a b A B C =
      Real.pi * a * b * Real.sqrt (A ^ 2 + B ^ 2 + C ^ 2) / |C| := by
  simpa [sectionArea] using gap5 a b A B C ha hb hC

end

end ProofGap.Exercise3704
