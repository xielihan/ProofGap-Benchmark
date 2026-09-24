import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3550

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def levelFunction (a b c : ℝ) (p : Point3) : ℝ :=
  p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2

def ellipsoid (a b c : ℝ) : Set Point3 :=
  {p | levelFunction a b c p = 1}

def normalVector (a b c : ℝ) (p : Point3) : Point3 :=
  ⟨deriv (fun t => levelFunction a b c ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => levelFunction a b c ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => levelFunction a b c ⟨p.x, p.y, t⟩) p.z⟩

def reducedNormal (a b c : ℝ) (p : Point3) : Point3 :=
  ⟨p.x / a ^ 2, p.y / b ^ 2, p.z / c ^ 2⟩

def reducedNormalLength (a b c : ℝ) (p : Point3) : ℝ :=
  Real.sqrt
    (p.x ^ 2 / a ^ 4 + p.y ^ 2 / b ^ 4 + p.z ^ 2 / c ^ 4)

def equalDirectionCosines (a b c : ℝ) (p : Point3) : Prop :=
  (p.x / a ^ 2) / reducedNormalLength a b c p =
      (p.y / b ^ 2) / reducedNormalLength a b c p ∧
    (p.y / b ^ 2) / reducedNormalLength a b c p =
      (p.z / c ^ 2) / reducedNormalLength a b c p

def commonRatio (a b c : ℝ) (p : Point3) (lam : ℝ) : Prop :=
  p.x / a ^ 2 = lam ∧ p.y / b ^ 2 = lam ∧ p.z / c ^ 2 = lam

def denominator (a b c : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)

def solutionSet (a b c : ℝ) : Set Point3 :=
  {p | p ∈ ellipsoid a b c ∧ ∃ lam : ℝ, commonRatio a b c p lam}

def answerPoints (a b c : ℝ) : Set Point3 :=
  {p |
    p = ⟨a ^ 2 / denominator a b c,
      b ^ 2 / denominator a b c, c ^ 2 / denominator a b c⟩ ∨
    p = ⟨-(a ^ 2 / denominator a b c),
      -(b ^ 2 / denominator a b c),
      -(c ^ 2 / denominator a b c)⟩}

theorem gap1 (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ p : Point3,
      normalVector a b c p =
        ⟨2 * (p.x / a ^ 2), 2 * (p.y / b ^ 2),
          2 * (p.z / c ^ 2)⟩ := by
  intro p
  have hx :
      deriv
          (fun t : ℝ =>
            t ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2)
          p.x =
        2 * (p.x / a ^ 2) := by
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (p.x + p.x) p.x := by
      simpa [pow_two] using
        (hasDerivAt_id p.x).mul (hasDerivAt_id p.x)
    have h :=
      ((hsq.div_const (a ^ 2)).add_const
        (p.y ^ 2 / b ^ 2)).add_const (p.z ^ 2 / c ^ 2)
    convert h.deriv using 1 <;> ring
  have hy :
      deriv
          (fun t : ℝ =>
            p.x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2)
          p.y =
        2 * (p.y / b ^ 2) := by
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (p.y + p.y) p.y := by
      simpa [pow_two] using
        (hasDerivAt_id p.y).mul (hasDerivAt_id p.y)
    have h :=
      ((hsq.div_const (b ^ 2)).const_add
        (p.x ^ 2 / a ^ 2)).add_const (p.z ^ 2 / c ^ 2)
    convert h.deriv using 1 <;> ring
  have hz :
      deriv
          (fun t : ℝ =>
            p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + t ^ 2 / c ^ 2)
          p.z =
        2 * (p.z / c ^ 2) := by
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (p.z + p.z) p.z := by
      simpa [pow_two] using
        (hasDerivAt_id p.z).mul (hasDerivAt_id p.z)
    have h :=
      (hsq.div_const (c ^ 2)).const_add
        (p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2)
    convert h.deriv using 1 <;> ring
  change
    Point3.mk
        (deriv
          (fun t : ℝ =>
            t ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2)
          p.x)
        (deriv
          (fun t : ℝ =>
            p.x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2)
          p.y)
        (deriv
          (fun t : ℝ =>
            p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + t ^ 2 / c ^ 2)
          p.z) =
      Point3.mk
        (2 * (p.x / a ^ 2))
        (2 * (p.y / b ^ 2))
        (2 * (p.z / c ^ 2))
  rw [hx, hy, hz]

theorem gap2 (a b c : ℝ) (p : Point3)
    (hEqual : equalDirectionCosines a b c p) :
    (p.x / a ^ 2) / reducedNormalLength a b c p =
      (p.y / b ^ 2) / reducedNormalLength a b c p := by
  exact hEqual.1

theorem gap3 (a b c : ℝ) (p : Point3)
    (hEqual : equalDirectionCosines a b c p) :
    (p.y / b ^ 2) / reducedNormalLength a b c p =
      (p.z / c ^ 2) / reducedNormalLength a b c p := by
  exact hEqual.2

theorem gap4 (a b c : ℝ) (p : Point3)
    (hXY :
      (p.x / a ^ 2) / reducedNormalLength a b c p =
        (p.y / b ^ 2) / reducedNormalLength a b c p)
    (hYZ :
      (p.y / b ^ 2) / reducedNormalLength a b c p =
        (p.z / c ^ 2) / reducedNormalLength a b c p) :
    (p.x / a ^ 2) / reducedNormalLength a b c p =
      (p.z / c ^ 2) / reducedNormalLength a b c p := by
  exact hXY.trans hYZ

theorem gap5 (a b c : ℝ) (p : Point3)
    (hLength : reducedNormalLength a b c p ≠ 0)
    (hXY :
      (p.x / a ^ 2) / reducedNormalLength a b c p =
        (p.y / b ^ 2) / reducedNormalLength a b c p) :
    p.x / a ^ 2 = p.y / b ^ 2 := by
  calc
    p.x / a ^ 2 =
        ((p.x / a ^ 2) / reducedNormalLength a b c p) *
          reducedNormalLength a b c p := by
            field_simp [hLength]
    _ =
        ((p.y / b ^ 2) / reducedNormalLength a b c p) *
          reducedNormalLength a b c p := by
            rw [hXY]
    _ = p.y / b ^ 2 := by
      field_simp [hLength]

theorem gap6 (a b c : ℝ) (p : Point3)
    (hLength : reducedNormalLength a b c p ≠ 0)
    (hYZ :
      (p.y / b ^ 2) / reducedNormalLength a b c p =
        (p.z / c ^ 2) / reducedNormalLength a b c p) :
    p.y / b ^ 2 = p.z / c ^ 2 := by
  calc
    p.y / b ^ 2 =
        ((p.y / b ^ 2) / reducedNormalLength a b c p) *
          reducedNormalLength a b c p := by
            field_simp [hLength]
    _ =
        ((p.z / c ^ 2) / reducedNormalLength a b c p) *
          reducedNormalLength a b c p := by
            rw [hYZ]
    _ = p.z / c ^ 2 := by
      field_simp [hLength]

theorem gap7 (a b c : ℝ) (p : Point3)
    (hYZ : p.y / b ^ 2 = p.z / c ^ 2) :
    ∃ lam : ℝ, p.y / b ^ 2 = lam ∧ p.z / c ^ 2 = lam := by
  refine ⟨p.y / b ^ 2, rfl, ?_⟩
  exact hYZ.symm

theorem gap8 (a b c : ℝ) (p : Point3)
    (hXY : p.x / a ^ 2 = p.y / b ^ 2)
    (hCommonYZ :
      ∃ lam : ℝ, p.y / b ^ 2 = lam ∧ p.z / c ^ 2 = lam) :
    ∃ lam : ℝ, commonRatio a b c p lam := by
  rcases hCommonYZ with ⟨lam, hy, hz⟩
  refine ⟨lam, ?_⟩
  exact ⟨hXY.trans hy, hy, hz⟩

theorem gap9 (a b c : ℝ) (p : Point3)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hSurface : p ∈ ellipsoid a b c)
    (hCommon : ∃ lam : ℝ, commonRatio a b c p lam) :
    ∃ lam : ℝ, commonRatio a b c p lam ∧
      (lam = 1 / denominator a b c ∨
        lam = -(1 / denominator a b c)) := by
  rcases hCommon with ⟨lam, hx, hy, hz⟩
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hx' : p.x = lam * a ^ 2 := (div_eq_iff ha2).mp hx
  have hy' : p.y = lam * b ^ 2 := (div_eq_iff hb2).mp hy
  have hz' : p.z = lam * c ^ 2 := (div_eq_iff hc2).mp hz
  change
    p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2 = 1
    at hSurface
  have hlam_sq : lam ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1 := by
    calc
      lam ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) =
          (lam * a ^ 2) ^ 2 / a ^ 2 +
            (lam * b ^ 2) ^ 2 / b ^ 2 +
              (lam * c ^ 2) ^ 2 / c ^ 2 := by
                field_simp [ha2, hb2, hc2] <;> ring
      _ = p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2 := by
        rw [hx', hy', hz']
      _ = 1 := hSurface
  have hsum : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    positivity
  have hden_pos : 0 < denominator a b c := by
    unfold denominator
    exact Real.sqrt_pos.2 hsum
  have hden_ne : denominator a b c ≠ 0 := ne_of_gt hden_pos
  have hden_sq :
      denominator a b c ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    unfold denominator
    exact Real.sq_sqrt (le_of_lt hsum)
  have hprod_sq : (lam * denominator a b c) ^ 2 = 1 := by
    calc
      (lam * denominator a b c) ^ 2 =
          lam ^ 2 * denominator a b c ^ 2 := by ring
      _ = lam ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by rw [hden_sq]
      _ = 1 := hlam_sq
  have hfactor :
      (lam * denominator a b c - 1) *
          (lam * denominator a b c + 1) = 0 := by
    nlinarith [hprod_sq]
  refine ⟨lam, ⟨hx, hy, hz⟩, ?_⟩
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · left
    apply (eq_div_iff hden_ne).2
    linarith
  · right
    have hvalue : lam = (-1) / denominator a b c :=
      (eq_div_iff hden_ne).2 (by linarith)
    calc
      lam = (-1) / denominator a b c := hvalue
      _ = -(1 / denominator a b c) := by ring

theorem gap10 (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    solutionSet a b c = answerPoints a b c := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hsum : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    positivity
  have hden_pos : 0 < denominator a b c := by
    unfold denominator
    exact Real.sqrt_pos.2 hsum
  have hden_ne : denominator a b c ≠ 0 := ne_of_gt hden_pos
  have hden_sq :
      denominator a b c ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    unfold denominator
    exact Real.sq_sqrt (le_of_lt hsum)
  apply Set.ext
  intro p
  constructor
  · intro hp
    rcases hp with ⟨hSurface, hCommon⟩
    rcases gap9 a b c p ha hb hc hSurface hCommon with
      ⟨lam, hratio, hlam⟩
    rcases hratio with ⟨hx, hy, hz⟩
    have hx' : p.x = lam * a ^ 2 := (div_eq_iff ha2).mp hx
    have hy' : p.y = lam * b ^ 2 := (div_eq_iff hb2).mp hy
    have hz' : p.z = lam * c ^ 2 := (div_eq_iff hc2).mp hz
    change
      p =
          ⟨a ^ 2 / denominator a b c,
            b ^ 2 / denominator a b c,
            c ^ 2 / denominator a b c⟩ ∨
        p =
          ⟨-(a ^ 2 / denominator a b c),
            -(b ^ 2 / denominator a b c),
            -(c ^ 2 / denominator a b c)⟩
    rcases hlam with hlam | hlam
    · left
      rcases p with ⟨x, y, z⟩
      dsimp at hx' hy' hz' ⊢
      have hxv : x = a ^ 2 / denominator a b c := by
        calc
          x = lam * a ^ 2 := hx'
          _ = a ^ 2 / denominator a b c := by rw [hlam]; ring
      have hyv : y = b ^ 2 / denominator a b c := by
        calc
          y = lam * b ^ 2 := hy'
          _ = b ^ 2 / denominator a b c := by rw [hlam]; ring
      have hzv : z = c ^ 2 / denominator a b c := by
        calc
          z = lam * c ^ 2 := hz'
          _ = c ^ 2 / denominator a b c := by rw [hlam]; ring
      rw [hxv, hyv, hzv]
    · right
      rcases p with ⟨x, y, z⟩
      dsimp at hx' hy' hz' ⊢
      have hxv : x = -(a ^ 2 / denominator a b c) := by
        calc
          x = lam * a ^ 2 := hx'
          _ = -(a ^ 2 / denominator a b c) := by rw [hlam]; ring
      have hyv : y = -(b ^ 2 / denominator a b c) := by
        calc
          y = lam * b ^ 2 := hy'
          _ = -(b ^ 2 / denominator a b c) := by rw [hlam]; ring
      have hzv : z = -(c ^ 2 / denominator a b c) := by
        calc
          z = lam * c ^ 2 := hz'
          _ = -(c ^ 2 / denominator a b c) := by rw [hlam]; ring
      rw [hxv, hyv, hzv]
  · intro hp
    change
      p =
          ⟨a ^ 2 / denominator a b c,
            b ^ 2 / denominator a b c,
            c ^ 2 / denominator a b c⟩ ∨
        p =
          ⟨-(a ^ 2 / denominator a b c),
            -(b ^ 2 / denominator a b c),
            -(c ^ 2 / denominator a b c)⟩
      at hp
    change p ∈ ellipsoid a b c ∧ ∃ lam : ℝ, commonRatio a b c p lam
    rcases hp with hp | hp
    · subst p
      constructor
      · change
          (a ^ 2 / denominator a b c) ^ 2 / a ^ 2 +
                (b ^ 2 / denominator a b c) ^ 2 / b ^ 2 +
              (c ^ 2 / denominator a b c) ^ 2 / c ^ 2 =
            1
        calc
          (a ^ 2 / denominator a b c) ^ 2 / a ^ 2 +
                  (b ^ 2 / denominator a b c) ^ 2 / b ^ 2 +
                (c ^ 2 / denominator a b c) ^ 2 / c ^ 2 =
              (a ^ 2 + b ^ 2 + c ^ 2) / denominator a b c ^ 2 := by
                field_simp [ha2, hb2, hc2, hden_ne] <;> ring
          _ = 1 := by
            rw [← hden_sq]
            field_simp [hden_ne]
      · refine ⟨1 / denominator a b c, ?_⟩
        unfold commonRatio
        dsimp
        constructor
        · field_simp [ha2, hden_ne] <;> ring
        · constructor
          · field_simp [hb2, hden_ne] <;> ring
          · field_simp [hc2, hden_ne] <;> ring
    · subst p
      constructor
      · change
          (-(a ^ 2 / denominator a b c)) ^ 2 / a ^ 2 +
                (-(b ^ 2 / denominator a b c)) ^ 2 / b ^ 2 +
              (-(c ^ 2 / denominator a b c)) ^ 2 / c ^ 2 =
            1
        calc
          (-(a ^ 2 / denominator a b c)) ^ 2 / a ^ 2 +
                  (-(b ^ 2 / denominator a b c)) ^ 2 / b ^ 2 +
                (-(c ^ 2 / denominator a b c)) ^ 2 / c ^ 2 =
              (a ^ 2 + b ^ 2 + c ^ 2) / denominator a b c ^ 2 := by
                field_simp [ha2, hb2, hc2, hden_ne] <;> ring
          _ = 1 := by
            rw [← hden_sq]
            field_simp [hden_ne]
      · refine ⟨-(1 / denominator a b c), ?_⟩
        unfold commonRatio
        dsimp
        constructor
        · field_simp [ha2, hden_ne] <;> ring
        · constructor
          · field_simp [hb2, hden_ne] <;> ring
          · field_simp [hc2, hden_ne] <;> ring

end

end ProofGap.Exercise3550
