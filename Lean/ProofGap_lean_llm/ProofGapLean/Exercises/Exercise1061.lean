import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1061

noncomputable section

def C1 : Set (ℝ × ℝ) := {p | p.2 = p.1 ^ 2}
def C2 : Set (ℝ × ℝ) := {p | p.1 = p.2 ^ 2}
def y1 (x : ℝ) : ℝ := x ^ 2
def y2 (x : ℝ) : ℝ := Real.sqrt x
def θ0 : ℝ := Real.pi / 2
def k1 : ℝ := 2
def k2 : ℝ := 1 / 2
def θ1 : ℝ := Real.arctan (3 / 4)

theorem gap1 :
    C1 ∩ C2 = ({((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))} :
      Set (ℝ × ℝ)) := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [C1, C2, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hy, hx⟩
    have hx0 : 0 ≤ x := by
      rw [hx]
      positivity
    have hy0 : 0 ≤ y := by
      rw [hy]
      positivity
    have hprod : (x - y) * (1 + x + y) = 0 := by
      calc
        (x - y) * (1 + x + y) = (x - y) + (x ^ 2 - y ^ 2) := by ring
        _ = 0 := by rw [← hy, ← hx]; ring
    have hpos : 0 < 1 + x + y := by nlinarith
    have hxy : x = y := by
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpos))
    have hfix : x = x ^ 2 := by
      calc
        x = y := hxy
        _ = x ^ 2 := hy
    have hfactor : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with hxz | hxo
    · left
      constructor
      · exact hxz
      · nlinarith [hxy]
    · right
      constructor <;> nlinarith [hxy]
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num

theorem gap2 (x : ℝ) : deriv y1 x = 2 * x := by
  unfold y1
  have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      ((hasDerivAt_id x).pow 2)
  exact h.deriv

theorem gap3 (x : ℝ) (hx : 0 < x) :
    deriv y2 x = 1 / (2 * y2 x) := by
  simpa [y2] using (Real.hasDerivAt_sqrt (ne_of_gt hx)).deriv

theorem gap4 : θ0 = Real.pi / 2 := by
  rfl
theorem gap5 : k1 = 2 := by
  rfl
theorem gap6 : k2 = 1 / 2 := by
  rfl

theorem gap7 :
    Real.tan θ1 = (k1 - k2) / (1 + k1 * k2) := by
  norm_num [θ1, k1, k2, Real.tan_arctan]

theorem gap8 :
    (k1 - k2) / (1 + k1 * k2) =
      (2 - 1 / 2) / (1 + 2 * (1 / 2 : ℝ)) := by
  rfl

theorem gap9 :
    ((2 - 1 / 2) / (1 + 2 * (1 / 2 : ℝ))) = 3 / 4 := by
  norm_num

theorem gap10 : Real.tan θ1 = 3 / 4 := by
  calc
    Real.tan θ1 = (k1 - k2) / (1 + k1 * k2) := gap7
    _ = (2 - 1 / 2) / (1 + 2 * (1 / 2 : ℝ)) := gap8
    _ = 3 / 4 := gap9
theorem gap11 : θ1 = Real.arctan (3 / 4) := by
  rfl

theorem gap12 :
    |Real.arctan (3 / 4) - 37 * Real.pi / 180| < 1 / 100 := by
  let a : ℝ := 13 / 100
  have ha0 : 0 ≤ a := by norm_num [a]
  have ha_mem : a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcospos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ha_mem
  have habs : |Real.sin a| ≤ a := by
    simpa [abs_of_nonneg ha0] using (Real.abs_sin_le_abs (x := a))
  have hslo : -a ≤ Real.sin a := (abs_le.mp habs).1
  have hshi : Real.sin a ≤ a := (abs_le.mp habs).2
  have hsums_nonneg : 0 ≤ (a - Real.sin a) * (a + Real.sin a) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hsin_sq : Real.sin a ^ 2 ≤ a ^ 2 := by
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq a
  have hcos_sq_lower : (9831 / 10000 : ℝ) ≤ Real.cos a ^ 2 := by
    calc
      (9831 / 10000 : ℝ) = 1 - a ^ 2 := by norm_num [a]
      _ ≤ 1 - Real.sin a ^ 2 := sub_le_sub_left hsin_sq 1
      _ = Real.cos a ^ 2 := by linarith [htrig]
  have hcos_sq : (91 / 100 : ℝ) ^ 2 < Real.cos a ^ 2 := by
    exact lt_of_lt_of_le (by norm_num) hcos_sq_lower
  have hcos : (91 / 100 : ℝ) < Real.cos a := by
    by_contra h
    have hle : Real.cos a ≤ 91 / 100 := le_of_not_gt h
    have hprod :
        0 ≤ ((91 / 100 : ℝ) - Real.cos a) *
          ((91 / 100 : ℝ) + Real.cos a) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hle
      · nlinarith
    nlinarith [hcos_sq, hprod]
  have htan : Real.tan a < (1 / 7 : ℝ) := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ hcospos).2
    calc
      Real.sin a ≤ a := hshi
      _ < (1 / 7 : ℝ) * Real.cos a := by nlinarith [hcos]
  have hata : Real.arctan (Real.tan a) = a :=
    Real.arctan_tan ha_mem.1 ha_mem.2
  have hatan_lower : a < Real.arctan (1 / 7 : ℝ) := by
    calc
      a = Real.arctan (Real.tan a) := hata.symm
      _ < Real.arctan (1 / 7 : ℝ) := Real.arctan_strictMono htan
  have hb_mem : (1 / 7 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_gt_three]
  have htan_self : (1 / 7 : ℝ) < Real.tan (1 / 7 : ℝ) := by
    exact Real.lt_tan (by norm_num) hb_mem.2
  have hatan_upper : Real.arctan (1 / 7 : ℝ) ≤ 1 / 7 := by
    have h := Real.arctan_lt_arctan htan_self
    rw [Real.arctan_tan hb_mem.1 hb_mem.2] at h
    exact h.le
  have hadd :
      Real.arctan (3 / 4 : ℝ) + Real.arctan (1 / 7 : ℝ) =
        Real.pi / 4 := by
    calc
      Real.arctan (3 / 4 : ℝ) + Real.arctan (1 / 7 : ℝ) =
          Real.arctan (((3 / 4 : ℝ) + 1 / 7) /
            (1 - (3 / 4 : ℝ) * (1 / 7))) :=
        Real.arctan_add (x := (3 / 4 : ℝ)) (y := (1 / 7 : ℝ)) (by norm_num)
      _ = Real.arctan 1 := by norm_num
      _ = Real.pi / 4 := Real.arctan_one
  have hpi_upper : Real.pi < 22 / 7 := by
    nlinarith [Real.pi_lt_d20]
  rw [abs_lt]
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [hpi_upper]

theorem gap13 :
    |θ1 - 37 * Real.pi / 180| < 1 / 100 := by
  simpa [θ1] using gap12

end

end ProofGap.Exercise1061
