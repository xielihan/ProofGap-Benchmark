import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3657

noncomputable section

def quadraticForm (A B C : ℝ) (q : ℝ × ℝ) : ℝ :=
  A * q.1 ^ 2 + 2 * B * q.1 * q.2 + C * q.2 ^ 2

def circle : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 = 1}

def critical (A B C lambda : ℝ) (q : ℝ × ℝ) : Prop :=
  (A - lambda) * q.1 + B * q.2 = 0 ∧
    B * q.1 + (C - lambda) * q.2 = 0 ∧
    q ∈ circle

def discriminant (A B C : ℝ) : ℝ :=
  (A - C) ^ 2 + 4 * B ^ 2

def highEigenvalue (A B C : ℝ) : ℝ :=
  (A + C + Real.sqrt (discriminant A B C)) / 2

def lowEigenvalue (A B C : ℝ) : ℝ :=
  (A + C - Real.sqrt (discriminant A B C)) / 2

def maximizers (A B C : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ circle ∧
    ∀ r ∈ circle, quadraticForm A B C r ≤ quadraticForm A B C q}

def minimizers (A B C : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ circle ∧
    ∀ r ∈ circle, quadraticForm A B C q ≤ quadraticForm A B C r}

private theorem critical_eq_or_eq_neg (A B C lambda : ℝ)
    {p q : ℝ × ℝ} (hdisc : discriminant A B C ≠ 0)
    (hp : critical A B C lambda p) (hq : critical A B C lambda q) :
    q = p ∨ q = (-p.1, -p.2) := by
  rcases hp with ⟨hp₁, hp₂, hpc⟩
  rcases hq with ⟨hq₁, hq₂, hqc⟩
  let d : ℝ := p.1 * q.2 - p.2 * q.1
  have hAd : (A - lambda) * d = 0 := by
    dsimp [d]
    calc
      (A - lambda) * (p.1 * q.2 - p.2 * q.1) =
          q.2 * ((A - lambda) * p.1 + B * p.2) -
            p.2 * ((A - lambda) * q.1 + B * q.2) := by ring
      _ = 0 := by rw [hp₁, hq₁]; ring
  have hBd : B * d = 0 := by
    dsimp [d]
    calc
      B * (p.1 * q.2 - p.2 * q.1) =
          q.2 * (B * p.1 + (C - lambda) * p.2) -
            p.2 * (B * q.1 + (C - lambda) * q.2) := by ring
      _ = 0 := by rw [hp₂, hq₂]; ring
  have hCd : (C - lambda) * d = 0 := by
    dsimp [d]
    calc
      (C - lambda) * (p.1 * q.2 - p.2 * q.1) =
          p.1 * (B * q.1 + (C - lambda) * q.2) -
            q.1 * (B * p.1 + (C - lambda) * p.2) := by ring
      _ = 0 := by rw [hp₂, hq₂]; ring
  have hd : d = 0 := by
    by_contra hdn
    have hA : A - lambda = 0 :=
      (mul_eq_zero.mp hAd).resolve_right hdn
    have hB : B = 0 :=
      (mul_eq_zero.mp hBd).resolve_right hdn
    have hC : C - lambda = 0 :=
      (mul_eq_zero.mp hCd).resolve_right hdn
    have hAe : A = lambda := by linarith only [hA]
    have hCe : C = lambda := by linarith only [hC]
    apply hdisc
    simp [discriminant, hAe, hCe, hB]
  change p.1 ^ 2 + p.2 ^ 2 = 1 at hpc
  change q.1 ^ 2 + q.2 ^ 2 = 1 at hqc
  let t : ℝ := p.1 * q.1 + p.2 * q.2
  have hlagrange : d ^ 2 + t ^ 2 =
      (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by
    dsimp [d, t]
    ring
  have ht : t ^ 2 = 1 := by
    calc
      t ^ 2 = d ^ 2 + t ^ 2 := by rw [hd]; ring
      _ = (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := hlagrange
      _ = 1 := by rw [hpc, hqc]; ring
  by_cases hsign : 0 ≤ t
  · have htone : t = 1 := by
      nlinarith only [ht, hsign]
    dsimp [t] at htone
    have hsum : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = 0 := by
      nlinarith only [hpc, hqc, htone]
    have he₁ : q.1 = p.1 := by
      nlinarith only [hsum, sq_nonneg (q.1 - p.1),
        sq_nonneg (q.2 - p.2)]
    have he₂ : q.2 = p.2 := by
      nlinarith only [hsum, sq_nonneg (q.1 - p.1),
        sq_nonneg (q.2 - p.2)]
    exact Or.inl (Prod.ext he₁ he₂)
  · have hneg : t < 0 := lt_of_not_ge hsign
    have htmone : t = -1 := by
      nlinarith only [ht, hneg]
    dsimp [t] at htmone
    have hsum : (q.1 + p.1) ^ 2 + (q.2 + p.2) ^ 2 = 0 := by
      nlinarith only [hpc, hqc, htmone]
    have he₁ : q.1 = -p.1 := by
      nlinarith only [hsum, sq_nonneg (q.1 + p.1),
        sq_nonneg (q.2 + p.2)]
    have he₂ : q.2 = -p.2 := by
      nlinarith only [hsum, sq_nonneg (q.1 + p.1),
        sq_nonneg (q.2 + p.2)]
    exact Or.inr (Prod.ext he₁ he₂)

theorem gap1 (A B C lambda : ℝ) :
    (∃ q, critical A B C lambda q) ↔
      lambda ^ 2 - (A + C) * lambda + A * C - B ^ 2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    rcases hq with ⟨h₁, h₂, hc⟩
    change q.1 ^ 2 + q.2 ^ 2 = 1 at hc
    have hu : ((A - lambda) * (C - lambda) - B ^ 2) * q.1 = 0 := by
      calc
        ((A - lambda) * (C - lambda) - B ^ 2) * q.1 =
            (C - lambda) * ((A - lambda) * q.1 + B * q.2) -
              B * (B * q.1 + (C - lambda) * q.2) := by ring
        _ = 0 := by rw [h₁, h₂]; ring
    have hv : ((A - lambda) * (C - lambda) - B ^ 2) * q.2 = 0 := by
      calc
        ((A - lambda) * (C - lambda) - B ^ 2) * q.2 =
            (A - lambda) * (B * q.1 + (C - lambda) * q.2) -
              B * ((A - lambda) * q.1 + B * q.2) := by ring
        _ = 0 := by rw [h₁, h₂]; ring
    have hdet : (A - lambda) * (C - lambda) - B ^ 2 = 0 := by
      by_cases hx : q.1 = 0
      · have hy : q.2 ≠ 0 := by
          intro hy
          rw [hx, hy] at hc
          norm_num at hc
        exact (mul_eq_zero.mp hv).resolve_right hy
      · exact (mul_eq_zero.mp hu).resolve_right hx
    calc
      lambda ^ 2 - (A + C) * lambda + A * C - B ^ 2 =
          (A - lambda) * (C - lambda) - B ^ 2 := by ring
      _ = 0 := hdet
  · intro hpoly
    have hdet : (A - lambda) * (C - lambda) - B ^ 2 = 0 := by
      calc
        (A - lambda) * (C - lambda) - B ^ 2 =
            lambda ^ 2 - (A + C) * lambda + A * C - B ^ 2 := by ring
        _ = 0 := hpoly
    by_cases hB : B = 0
    · have hxz : (A - lambda) * (C - lambda) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hxz with hx | hz
      · exact ⟨(1, 0), by simp [critical, circle, hB, hx]⟩
      · exact ⟨(0, 1), by simp [critical, circle, hB, hz]⟩
    · let S : ℝ := B ^ 2 + (A - lambda) ^ 2
      have hS : 0 < S := by
        dsimp [S]
        have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
        nlinarith [sq_nonneg (A - lambda)]
      have hd : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
      have hd2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt (le_of_lt hS)
      refine ⟨(B / Real.sqrt S, -(A - lambda) / Real.sqrt S), ?_⟩
      unfold critical circle
      dsimp
      refine ⟨?_, ?_, ?_⟩
      · field_simp [hd] <;> ring
      · field_simp [hd] <;> nlinarith [hdet]
      · field_simp [hd] <;> nlinarith [hd2]

theorem gap2 (A B C : ℝ) (hdisc : discriminant A B C = 0) :
    ∀ q ∈ circle, quadraticForm A B C q = A := by
  have hAC : A = C := by
    unfold discriminant at hdisc
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  have hB : B = 0 := by
    unfold discriminant at hdisc
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 = 1 at hq
  unfold quadraticForm
  rw [hAC, hB]
  calc
    C * q.1 ^ 2 + 2 * 0 * q.1 * q.2 + C * q.2 ^ 2 =
        C * (q.1 ^ 2 + q.2 ^ 2) := by ring
    _ = C := by rw [hq]; ring

theorem gap3 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    highEigenvalue A B C > lowEigenvalue A B C := by
  have hnonneg : 0 ≤ discriminant A B C := by
    unfold discriminant
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  have hpos : 0 < discriminant A B C :=
    lt_of_le_of_ne hnonneg (Ne.symm hdisc)
  have hspos : 0 < Real.sqrt (discriminant A B C) :=
    Real.sqrt_pos.2 hpos
  unfold highEigenvalue lowEigenvalue
  nlinarith

theorem gap4 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    highEigenvalue A B C =
      (A + C + Real.sqrt ((A - C) ^ 2 + 4 * B ^ 2)) / 2 := by
  rfl

theorem gap5 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    lowEigenvalue A B C =
      (A + C - Real.sqrt ((A - C) ^ 2 + 4 * B ^ 2)) / 2 := by
  rfl

theorem gap6 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    {lambda | ∃ q, critical A B C lambda q} =
      ({highEigenvalue A B C, lowEigenvalue A B C} : Set ℝ) := by
  ext lambda
  change (∃ q, critical A B C lambda q) ↔
    lambda = highEigenvalue A B C ∨ lambda = lowEigenvalue A B C
  rw [gap1]
  have hD : 0 ≤ discriminant A B C := by
    unfold discriminant
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  have hsq : Real.sqrt (discriminant A B C) ^ 2 =
      (A - C) ^ 2 + 4 * B ^ 2 := by
    simpa [discriminant] using Real.sq_sqrt hD
  have hsnonneg : 0 ≤ Real.sqrt (discriminant A B C) :=
    Real.sqrt_nonneg _
  constructor
  · intro h
    have heq : (2 * lambda - (A + C)) ^ 2 =
        (A - C) ^ 2 + 4 * B ^ 2 := by
      nlinarith
    by_cases hsign : 0 ≤ 2 * lambda - (A + C)
    · left
      unfold highEigenvalue
      nlinarith
    · right
      have hsign' : 2 * lambda - (A + C) < 0 := lt_of_not_ge hsign
      unfold lowEigenvalue
      nlinarith
  · rintro (h | h)
    · rw [h]
      unfold highEigenvalue
      nlinarith
    · rw [h]
      unfold lowEigenvalue
      nlinarith

theorem gap7 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₁, critical A B C (highEigenvalue A B C) P₁ := by
  have hmem : highEigenvalue A B C ∈
      {lambda | ∃ q, critical A B C lambda q} := by
    rw [gap6 A B C hdisc]
    simp
  exact hmem

theorem gap8 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₁ P₂, critical A B C (highEigenvalue A B C) P₁ ∧
      critical A B C (highEigenvalue A B C) P₂ ∧
      P₂ = (-P₁.1, -P₁.2) := by
  rcases gap7 A B C hdisc with ⟨P₁, hP₁⟩
  refine ⟨P₁, (-P₁.1, -P₁.2), hP₁, ?_, rfl⟩
  rcases hP₁ with ⟨h₁, h₂, hc⟩
  unfold critical
  refine ⟨?_, ?_, ?_⟩
  · dsimp
    nlinarith
  · dsimp
    nlinarith
  · simpa [circle] using hc

theorem gap9 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₃, critical A B C (lowEigenvalue A B C) P₃ := by
  have hmem : lowEigenvalue A B C ∈
      {lambda | ∃ q, critical A B C lambda q} := by
    rw [gap6 A B C hdisc]
    simp
  exact hmem

theorem gap10 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₃ P₄, critical A B C (lowEigenvalue A B C) P₃ ∧
      critical A B C (lowEigenvalue A B C) P₄ ∧
      P₄ = (-P₃.1, -P₃.2) := by
  rcases gap9 A B C hdisc with ⟨P₃, hP₃⟩
  refine ⟨P₃, (-P₃.1, -P₃.2), hP₃, ?_, rfl⟩
  rcases hP₃ with ⟨h₁, h₂, hc⟩
  unfold critical
  refine ⟨?_, ?_, ?_⟩
  · dsimp
    nlinarith
  · dsimp
    nlinarith
  · simpa [circle] using hc

theorem gap11 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₁ P₂, critical A B C (highEigenvalue A B C) P₁ ∧
      critical A B C (highEigenvalue A B C) P₂ ∧
      quadraticForm A B C P₁ = quadraticForm A B C P₂ := by
  rcases gap8 A B C hdisc with ⟨P₁, P₂, hP₁, hP₂, hneg⟩
  refine ⟨P₁, P₂, hP₁, hP₂, ?_⟩
  rw [hneg]
  unfold quadraticForm
  dsimp
  ring

theorem gap12 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₂, critical A B C (highEigenvalue A B C) P₂ ∧
      quadraticForm A B C P₂ = highEigenvalue A B C := by
  rcases gap7 A B C hdisc with ⟨P₂, hP₂⟩
  refine ⟨P₂, hP₂, ?_⟩
  rcases hP₂ with ⟨h₁, h₂, hc⟩
  change P₂.1 ^ 2 + P₂.2 ^ 2 = 1 at hc
  calc
    quadraticForm A B C P₂ =
        highEigenvalue A B C * (P₂.1 ^ 2 + P₂.2 ^ 2) +
          P₂.1 * ((A - highEigenvalue A B C) * P₂.1 + B * P₂.2) +
          P₂.2 * (B * P₂.1 + (C - highEigenvalue A B C) * P₂.2) := by
            unfold quadraticForm
            ring
    _ = highEigenvalue A B C := by rw [h₁, h₂, hc]; ring

theorem gap13 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₁, critical A B C (highEigenvalue A B C) P₁ ∧
      quadraticForm A B C P₁ = highEigenvalue A B C := by
  exact gap12 A B C hdisc

theorem gap14 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₃ P₄, critical A B C (lowEigenvalue A B C) P₃ ∧
      critical A B C (lowEigenvalue A B C) P₄ ∧
      quadraticForm A B C P₃ = quadraticForm A B C P₄ := by
  rcases gap10 A B C hdisc with ⟨P₃, P₄, hP₃, hP₄, hneg⟩
  refine ⟨P₃, P₄, hP₃, hP₄, ?_⟩
  rw [hneg]
  unfold quadraticForm
  dsimp
  ring

theorem gap15 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₄, critical A B C (lowEigenvalue A B C) P₄ ∧
      quadraticForm A B C P₄ = lowEigenvalue A B C := by
  rcases gap9 A B C hdisc with ⟨P₄, hP₄⟩
  refine ⟨P₄, hP₄, ?_⟩
  rcases hP₄ with ⟨h₁, h₂, hc⟩
  change P₄.1 ^ 2 + P₄.2 ^ 2 = 1 at hc
  calc
    quadraticForm A B C P₄ =
        lowEigenvalue A B C * (P₄.1 ^ 2 + P₄.2 ^ 2) +
          P₄.1 * ((A - lowEigenvalue A B C) * P₄.1 + B * P₄.2) +
          P₄.2 * (B * P₄.1 + (C - lowEigenvalue A B C) * P₄.2) := by
            unfold quadraticForm
            ring
    _ = lowEigenvalue A B C := by rw [h₁, h₂, hc]; ring

theorem gap16 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₃, critical A B C (lowEigenvalue A B C) P₃ ∧
      quadraticForm A B C P₃ = lowEigenvalue A B C := by
  exact gap15 A B C hdisc

theorem gap17 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₁ P₂, critical A B C (highEigenvalue A B C) P₁ ∧
      P₂ = (-P₁.1, -P₁.2) ∧
      maximizers A B C = ({P₁, P₂} : Set (ℝ × ℝ)) := by
  rcases gap13 A B C hdisc with ⟨P₁, hP₁, hP₁val⟩
  let s : ℝ := Real.sqrt (discriminant A B C)
  have hD : 0 ≤ discriminant A B C := by
    unfold discriminant
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  have hDpos : 0 < discriminant A B C :=
    lt_of_le_of_ne hD (Ne.symm hdisc)
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hDpos
  have hsq : s ^ 2 = (A - C) ^ 2 + 4 * B ^ 2 := by
    dsimp [s]
    simpa [discriminant] using Real.sq_sqrt hD
  have hidentity (r : ℝ × ℝ) (hr : r ∈ circle) :
      ((s - (A - C)) * r.1 - 2 * B * r.2) ^ 2 +
          (2 * B * r.1 - (s + (A - C)) * r.2) ^ 2 =
        4 * s * (highEigenvalue A B C - quadraticForm A B C r) := by
    change r.1 ^ 2 + r.2 ^ 2 = 1 at hr
    change
      ((s - (A - C)) * r.1 - 2 * B * r.2) ^ 2 +
          (2 * B * r.1 - (s + (A - C)) * r.2) ^ 2 =
        4 * s * ((A + C + s) / 2 -
          (A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2))
    have hz : (A - C) ^ 2 + 4 * B ^ 2 - s ^ 2 = 0 := by
      nlinarith only [hsq]
    calc
      ((s - (A - C)) * r.1 - 2 * B * r.2) ^ 2 +
          (2 * B * r.1 - (s + (A - C)) * r.2) ^ 2 =
          2 * s * ((s - (A - C)) * r.1 ^ 2 -
            4 * B * r.1 * r.2 + (s + (A - C)) * r.2 ^ 2) := by
              apply sub_eq_zero.mp
              calc
                (((s - (A - C)) * r.1 - 2 * B * r.2) ^ 2 +
                    (2 * B * r.1 - (s + (A - C)) * r.2) ^ 2) -
                    2 * s * ((s - (A - C)) * r.1 ^ 2 -
                      4 * B * r.1 * r.2 + (s + (A - C)) * r.2 ^ 2) =
                    ((A - C) ^ 2 + 4 * B ^ 2 - s ^ 2) *
                      (r.1 ^ 2 + r.2 ^ 2) := by ring
                _ = 0 := by rw [hz]; ring
      _ = 4 * s * ((A + C + s) / 2 -
          (A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2)) := by
            apply sub_eq_zero.mp
            calc
              2 * s * ((s - (A - C)) * r.1 ^ 2 -
                    4 * B * r.1 * r.2 + (s + (A - C)) * r.2 ^ 2) -
                  4 * s * ((A + C + s) / 2 -
                    (A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2)) =
                  2 * s * (s + A + C) * (r.1 ^ 2 + r.2 ^ 2 - 1) := by ring
              _ = 0 := by rw [hr]; ring
  have hupper : ∀ r ∈ circle,
      quadraticForm A B C r ≤ highEigenvalue A B C := by
    intro r hr
    have hid := hidentity r hr
    nlinarith [sq_nonneg ((s - (A - C)) * r.1 - 2 * B * r.2),
      sq_nonneg (2 * B * r.1 - (s + (A - C)) * r.2)]
  have hP₁max : P₁ ∈ maximizers A B C := by
    change P₁ ∈ circle ∧ ∀ r ∈ circle,
      quadraticForm A B C r ≤ quadraticForm A B C P₁
    refine ⟨hP₁.2.2, ?_⟩
    intro r hr
    calc
      quadraticForm A B C r ≤ highEigenvalue A B C := hupper r hr
      _ = quadraticForm A B C P₁ := hP₁val.symm
  have hnegCircle : (-P₁.1, -P₁.2) ∈ circle := by
    simpa [circle] using hP₁.2.2
  have hnegVal : quadraticForm A B C (-P₁.1, -P₁.2) =
      highEigenvalue A B C := by
    calc
      quadraticForm A B C (-P₁.1, -P₁.2) =
          quadraticForm A B C P₁ := by
            unfold quadraticForm
            dsimp
            ring
      _ = highEigenvalue A B C := hP₁val
  have hnegMax : (-P₁.1, -P₁.2) ∈ maximizers A B C := by
    change (-P₁.1, -P₁.2) ∈ circle ∧ ∀ r ∈ circle,
      quadraticForm A B C r ≤ quadraticForm A B C (-P₁.1, -P₁.2)
    refine ⟨hnegCircle, ?_⟩
    intro r hr
    calc
      quadraticForm A B C r ≤ highEigenvalue A B C := hupper r hr
      _ = quadraticForm A B C (-P₁.1, -P₁.2) := hnegVal.symm
  refine ⟨P₁, (-P₁.1, -P₁.2), hP₁, rfl, ?_⟩
  ext r
  constructor
  · intro hr
    change r ∈ circle ∧ ∀ t ∈ circle,
      quadraticForm A B C t ≤ quadraticForm A B C r at hr
    rcases hr with ⟨hrc, hrmax⟩
    have hrle := hupper r hrc
    have hrge := hrmax P₁ hP₁.2.2
    have hrval : quadraticForm A B C r = highEigenvalue A B C := by
      nlinarith [hP₁val]
    have hid := hidentity r hrc
    rw [hrval] at hid
    have he₁ : (s - (A - C)) * r.1 - 2 * B * r.2 = 0 := by
      nlinarith [sq_nonneg ((s - (A - C)) * r.1 - 2 * B * r.2),
        sq_nonneg (2 * B * r.1 - (s + (A - C)) * r.2)]
    have he₂ : 2 * B * r.1 - (s + (A - C)) * r.2 = 0 := by
      nlinarith [sq_nonneg ((s - (A - C)) * r.1 - 2 * B * r.2),
        sq_nonneg (2 * B * r.1 - (s + (A - C)) * r.2)]
    have hrcrit : critical A B C (highEigenvalue A B C) r := by
      unfold critical
      refine ⟨?_, ?_, hrc⟩
      · dsimp [highEigenvalue, s] at he₁ ⊢
        nlinarith
      · dsimp [highEigenvalue, s] at he₂ ⊢
        nlinarith
    have hor := critical_eq_or_eq_neg A B C (highEigenvalue A B C)
      hdisc hP₁ hrcrit
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hor
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hP₁max
    · exact hnegMax

theorem gap18 (A B C : ℝ) (hdisc : discriminant A B C ≠ 0) :
    ∃ P₃ P₄, critical A B C (lowEigenvalue A B C) P₃ ∧
      P₄ = (-P₃.1, -P₃.2) ∧
      minimizers A B C = ({P₃, P₄} : Set (ℝ × ℝ)) := by
  rcases gap16 A B C hdisc with ⟨P₃, hP₃, hP₃val⟩
  let s : ℝ := Real.sqrt (discriminant A B C)
  have hD : 0 ≤ discriminant A B C := by
    unfold discriminant
    nlinarith [sq_nonneg (A - C), sq_nonneg B]
  have hDpos : 0 < discriminant A B C :=
    lt_of_le_of_ne hD (Ne.symm hdisc)
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hDpos
  have hsq : s ^ 2 = (A - C) ^ 2 + 4 * B ^ 2 := by
    dsimp [s]
    simpa [discriminant] using Real.sq_sqrt hD
  have hidentity (r : ℝ × ℝ) (hr : r ∈ circle) :
      ((s + (A - C)) * r.1 + 2 * B * r.2) ^ 2 +
          (2 * B * r.1 + (s - (A - C)) * r.2) ^ 2 =
        4 * s * (quadraticForm A B C r - lowEigenvalue A B C) := by
    change r.1 ^ 2 + r.2 ^ 2 = 1 at hr
    change
      ((s + (A - C)) * r.1 + 2 * B * r.2) ^ 2 +
          (2 * B * r.1 + (s - (A - C)) * r.2) ^ 2 =
        4 * s * ((A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2) -
          (A + C - s) / 2)
    have hz : (A - C) ^ 2 + 4 * B ^ 2 - s ^ 2 = 0 := by
      nlinarith only [hsq]
    calc
      ((s + (A - C)) * r.1 + 2 * B * r.2) ^ 2 +
          (2 * B * r.1 + (s - (A - C)) * r.2) ^ 2 =
          2 * s * ((s + (A - C)) * r.1 ^ 2 +
            4 * B * r.1 * r.2 + (s - (A - C)) * r.2 ^ 2) := by
              apply sub_eq_zero.mp
              calc
                (((s + (A - C)) * r.1 + 2 * B * r.2) ^ 2 +
                    (2 * B * r.1 + (s - (A - C)) * r.2) ^ 2) -
                    2 * s * ((s + (A - C)) * r.1 ^ 2 +
                      4 * B * r.1 * r.2 + (s - (A - C)) * r.2 ^ 2) =
                    ((A - C) ^ 2 + 4 * B ^ 2 - s ^ 2) *
                      (r.1 ^ 2 + r.2 ^ 2) := by ring
                _ = 0 := by rw [hz]; ring
      _ = 4 * s * ((A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2) -
          (A + C - s) / 2) := by
            apply sub_eq_zero.mp
            calc
              2 * s * ((s + (A - C)) * r.1 ^ 2 +
                    4 * B * r.1 * r.2 + (s - (A - C)) * r.2 ^ 2) -
                  4 * s * ((A * r.1 ^ 2 + 2 * B * r.1 * r.2 + C * r.2 ^ 2) -
                    (A + C - s) / 2) =
                  2 * s * (s - A - C) * (r.1 ^ 2 + r.2 ^ 2 - 1) := by ring
              _ = 0 := by rw [hr]; ring
  have hlower : ∀ r ∈ circle,
      lowEigenvalue A B C ≤ quadraticForm A B C r := by
    intro r hr
    have hid := hidentity r hr
    nlinarith [sq_nonneg ((s + (A - C)) * r.1 + 2 * B * r.2),
      sq_nonneg (2 * B * r.1 + (s - (A - C)) * r.2)]
  have hP₃min : P₃ ∈ minimizers A B C := by
    change P₃ ∈ circle ∧ ∀ r ∈ circle,
      quadraticForm A B C P₃ ≤ quadraticForm A B C r
    refine ⟨hP₃.2.2, ?_⟩
    intro r hr
    calc
      quadraticForm A B C P₃ = lowEigenvalue A B C := hP₃val
      _ ≤ quadraticForm A B C r := hlower r hr
  have hnegCircle : (-P₃.1, -P₃.2) ∈ circle := by
    simpa [circle] using hP₃.2.2
  have hnegVal : quadraticForm A B C (-P₃.1, -P₃.2) =
      lowEigenvalue A B C := by
    calc
      quadraticForm A B C (-P₃.1, -P₃.2) =
          quadraticForm A B C P₃ := by
            unfold quadraticForm
            dsimp
            ring
      _ = lowEigenvalue A B C := hP₃val
  have hnegMin : (-P₃.1, -P₃.2) ∈ minimizers A B C := by
    change (-P₃.1, -P₃.2) ∈ circle ∧ ∀ r ∈ circle,
      quadraticForm A B C (-P₃.1, -P₃.2) ≤ quadraticForm A B C r
    refine ⟨hnegCircle, ?_⟩
    intro r hr
    calc
      quadraticForm A B C (-P₃.1, -P₃.2) = lowEigenvalue A B C := hnegVal
      _ ≤ quadraticForm A B C r := hlower r hr
  refine ⟨P₃, (-P₃.1, -P₃.2), hP₃, rfl, ?_⟩
  ext r
  constructor
  · intro hr
    change r ∈ circle ∧ ∀ t ∈ circle,
      quadraticForm A B C r ≤ quadraticForm A B C t at hr
    rcases hr with ⟨hrc, hrmin⟩
    have hrge := hlower r hrc
    have hrle := hrmin P₃ hP₃.2.2
    have hrval : quadraticForm A B C r = lowEigenvalue A B C := by
      nlinarith [hP₃val]
    have hid := hidentity r hrc
    rw [hrval] at hid
    have he₁ : (s + (A - C)) * r.1 + 2 * B * r.2 = 0 := by
      nlinarith [sq_nonneg ((s + (A - C)) * r.1 + 2 * B * r.2),
        sq_nonneg (2 * B * r.1 + (s - (A - C)) * r.2)]
    have he₂ : 2 * B * r.1 + (s - (A - C)) * r.2 = 0 := by
      nlinarith [sq_nonneg ((s + (A - C)) * r.1 + 2 * B * r.2),
        sq_nonneg (2 * B * r.1 + (s - (A - C)) * r.2)]
    have hrcrit : critical A B C (lowEigenvalue A B C) r := by
      unfold critical
      refine ⟨?_, ?_, hrc⟩
      · dsimp [lowEigenvalue, s] at he₁ ⊢
        nlinarith
      · dsimp [lowEigenvalue, s] at he₂ ⊢
        nlinarith
    have hor := critical_eq_or_eq_neg A B C (lowEigenvalue A B C)
      hdisc hP₃ hrcrit
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hor
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hP₃min
    · exact hnegMin

end

end ProofGap.Exercise3657
