import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2173

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def interval (n : ℕ) : Set ℝ := Set.Ioo (n : ℝ) ((n : ℝ) + 1)
def floorR (x : ℝ) : ℝ := (Int.floor x : ℝ)
def floorSign (x : ℝ) := Real.cos (Real.pi * floorR x)
def integrand (x : ℝ) :=
  floorR x * |Real.sin (Real.pi * x)|
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def localPrimitive (n : ℕ) (x : ℝ) :=
  -Real.cos (Real.pi * (n : ℝ)) * (n : ℝ) / Real.pi *
    Real.cos (Real.pi * x)
def primitive (x : ℝ) :=
  floorR x / Real.pi *
    (floorR x - floorSign x * Real.cos (Real.pi * x))
def expandedPrimitive (x : ℝ) :=
  floorR x * (floorR x - 1) / Real.pi +
    floorR x / Real.pi *
      (1 - floorSign x * Real.cos (Real.pi * x))
def algebraicPrimitive (x : ℝ) :=
  floorR x * (floorR x - 1) / Real.pi +
    floorSign x * floorR x * floorSign x / Real.pi -
    floorSign x * floorR x * Real.cos (Real.pi * x) / Real.pi

private theorem sin_pi_mul_nat (n : ℕ) :
    Real.sin (Real.pi * (n : ℝ)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show Real.pi * ((n : ℝ) + 1) =
          Real.pi * (n : ℝ) + Real.pi by ring]
      rw [Real.sin_add, ih, Real.sin_pi, Real.cos_pi]
      ring

private theorem cos_pi_mul_nat_sq (n : ℕ) :
    Real.cos (Real.pi * (n : ℝ)) * Real.cos (Real.pi * (n : ℝ)) = 1 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi * (n : ℝ))
  rw [sin_pi_mul_nat n] at h
  nlinarith

private theorem cos_pi_mul_nat_succ (n : ℕ) :
    Real.cos (Real.pi * ((n + 1 : ℕ) : ℝ)) =
      -Real.cos (Real.pi * (n : ℝ)) := by
  rw [Nat.cast_add, Nat.cast_one]
  rw [show Real.pi * ((n : ℝ) + 1) =
      Real.pi * (n : ℝ) + Real.pi by ring]
  rw [Real.cos_add, sin_pi_mul_nat n, Real.cos_pi, Real.sin_pi]
  ring

private theorem floorR_eq_nat_of_mem_interval (n : ℕ) (x : ℝ)
    (hx : x ∈ interval n) : floorR x = (n : ℝ) := by
  have hf : Int.floor x = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using le_of_lt hx.1
    · simpa using hx.2
  simp [floorR, hf]

private theorem floorSign_sq (x : ℝ) : floorSign x * floorSign x = 1 := by
  unfold floorSign floorR
  have hs : Real.sin (Real.pi * (Int.floor x : ℝ)) = 0 := by
    rw [mul_comm]
    exact Real.sin_int_mul_pi (Int.floor x)
  have h := Real.sin_sq_add_cos_sq (Real.pi * (Int.floor x : ℝ))
  rw [hs] at h
  nlinarith

private theorem localPrimitive_hasDerivAt_formula (n : ℕ) (x : ℝ) :
    HasDerivAt (localPrimitive n)
      ((-Real.cos (Real.pi * (n : ℝ)) * (n : ℝ) / Real.pi) *
        (-Real.sin (Real.pi * x) * Real.pi)) x := by
  have harg : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul Real.pi
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (Real.pi * y))
      (-Real.sin (Real.pi * x) * Real.pi) x := by
    convert (Real.hasDerivAt_cos (Real.pi * x)).comp x harg using 1 <;> ring
  simpa only [localPrimitive] using
    hcos.const_mul
      (-Real.cos (Real.pi * (n : ℝ)) * (n : ℝ) / Real.pi)

private theorem localPrimitive_hasDerivAt (n : ℕ) (x : ℝ)
    (hx : x ∈ interval n) :
    HasDerivAt (localPrimitive n) (integrand x) x := by
  let c : ℝ := Real.cos (Real.pi * (n : ℝ))
  have hc : c * c = 1 := by
    simpa [c] using cos_pi_mul_nat_sq n
  have hfloor : floorR x = (n : ℝ) :=
    floorR_eq_nat_of_mem_interval n x hx
  have hdelta0 : 0 < Real.pi * (x - (n : ℝ)) := by
    nlinarith [Real.pi_pos, hx.1]
  have hdeltapi : Real.pi * (x - (n : ℝ)) < Real.pi := by
    nlinarith [Real.pi_pos, hx.2]
  have hspos : 0 < Real.sin (Real.pi * (x - (n : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hdelta0 hdeltapi
  have hsin : Real.sin (Real.pi * x) =
      c * Real.sin (Real.pi * (x - (n : ℝ))) := by
    rw [show Real.pi * x = Real.pi * (n : ℝ) +
        Real.pi * (x - (n : ℝ)) by ring]
    rw [Real.sin_add, sin_pi_mul_nat n]
    simp [c]
  have habsc : |c| = 1 := by
    have hnonneg : 0 ≤ |c| := abs_nonneg c
    have hsq : |c| * |c| = 1 := by
      rw [← abs_mul, hc, abs_one]
    nlinarith
  have habs : |Real.sin (Real.pi * x)| =
      c * Real.sin (Real.pi * x) := by
    rw [hsin, abs_mul, habsc, abs_of_pos hspos, one_mul]
    rw [← mul_assoc, hc, one_mul]
  convert localPrimitive_hasDerivAt_formula n x using 1 <;> try rfl
  rw [integrand, hfloor, habs]
  dsimp only [c]
  field_simp [Real.pi_ne_zero] <;> ring

private theorem antiderivativesOn_Ioo_characterization
    (n : ℕ) (z : ℝ) (hz : z ∈ interval n) (p : ℝ → ℝ)
    (hp : ∀ x ∈ interval n, HasDerivAt p (integrand x) x) :
    AntiderivativesOn (interval n) integrand =
      PrimitiveFamilyOn (interval n) p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨F z - p z, ?_⟩
    intro x hx
    have hd : ∀ y ∈ interval n,
        HasDerivAt (fun t => F t - p t) 0 y := by
      intro y hy
      convert (hF y hy).sub (hp y hy) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun t => F t - p t) (interval n) := by
      intro y hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ interval n,
        deriv (fun t => F t - p t) y = 0 := by
      intro y hy
      exact (hd y hy).deriv
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hzero hx hz
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent

private theorem primitive_eq_branch_on_closed_unit (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    primitive x =
      (n : ℝ) / Real.pi *
        ((n : ℝ) - Real.cos (Real.pi * (n : ℝ)) *
          Real.cos (Real.pi * x)) := by
  rcases eq_or_lt_of_le hx.2 with hright | hlt
  · subst x
    have hfloor : floorR ((n : ℝ) + 1) = ((n : ℝ) + 1) := by
      simp [floorR]
    have hcosnext :
        Real.cos (Real.pi * ((n : ℝ) + 1)) =
          -Real.cos (Real.pi * (n : ℝ)) := by
      simpa using cos_pi_mul_nat_succ n
    have hc := cos_pi_mul_nat_sq n
    have hsq : Real.cos ((n : ℝ) * Real.pi) ^ 2 = 1 := by
      rw [mul_comm]
      simpa [pow_two] using hc
    simp only [primitive, floorSign]
    rw [hfloor, hcosnext]
    field_simp [Real.pi_ne_zero]
    simp [hsq]
    ring
  · have hf : Int.floor x = (n : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa using hx.1
      · simpa using hlt
    simp [primitive, floorR, floorSign, hf]

private theorem primitive_eq_shiftedLocal_on_closed_unit
    (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    primitive x =
      localPrimitive n x + (n : ℝ) * (n : ℝ) / Real.pi := by
  rw [primitive_eq_branch_on_closed_unit n x hx]
  simp only [localPrimitive]
  ring

private theorem primitive_hasDerivAt_nat (m : ℕ) (hm : 0 < m) :
    HasDerivAt primitive 0 (m : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hcastpred : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    norm_cast
    exact Nat.sub_add_cancel hm1
  have hleftlt : ((m - 1 : ℕ) : ℝ) < (m : ℝ) := by
    have hnat : m - 1 < m := by omega
    exact_mod_cast hnat
  let leftSet : Set ℝ := Set.Icc ((m - 1 : ℕ) : ℝ) (m : ℝ)
  let rightSet : Set ℝ := Set.Icc (m : ℝ) ((m : ℝ) + 1)
  let leftShift : ℝ → ℝ := fun y =>
    localPrimitive (m - 1) y +
      ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) / Real.pi
  let rightShift : ℝ → ℝ := fun y =>
    localPrimitive m y + (m : ℝ) * (m : ℝ) / Real.pi
  have hleftBase : HasDerivAt leftShift 0 (m : ℝ) := by
    dsimp only [leftShift]
    simpa [sin_pi_mul_nat m] using
      (localPrimitive_hasDerivAt_formula (m - 1) (m : ℝ)).add_const
        (((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) / Real.pi)
  have hrightBase : HasDerivAt rightShift 0 (m : ℝ) := by
    dsimp only [rightShift]
    simpa [sin_pi_mul_nat m] using
      (localPrimitive_hasDerivAt_formula m (m : ℝ)).add_const
        ((m : ℝ) * (m : ℝ) / Real.pi)
  have hleftEq : Set.EqOn primitive leftShift leftSet := by
    intro y hy
    have hy' : y ∈ Set.Icc ((m - 1 : ℕ) : ℝ)
        (((m - 1 : ℕ) : ℝ) + 1) := by
      exact ⟨hy.1, by simpa [hcastpred] using hy.2⟩
    simpa only [leftShift] using
      primitive_eq_shiftedLocal_on_closed_unit (m - 1) y hy'
  have hrightEq : Set.EqOn primitive rightShift rightSet := by
    intro y hy
    simpa only [rightShift] using
      primitive_eq_shiftedLocal_on_closed_unit m y hy
  have hmleft : (m : ℝ) ∈ leftSet := by
    exact ⟨hleftlt.le, le_rfl⟩
  have hmright : (m : ℝ) ∈ rightSet := by
    constructor <;> norm_num
  have hleft : HasDerivWithinAt primitive 0 leftSet (m : ℝ) := by
    exact hleftBase.hasDerivWithinAt.congr hleftEq (hleftEq hmleft)
  have hright : HasDerivWithinAt primitive 0 rightSet (m : ℝ) := by
    exact hrightBase.hasDerivWithinAt.congr hrightEq (hrightEq hmright)
  have hopen : Set.Ioo ((m - 1 : ℕ) : ℝ) ((m : ℝ) + 1) ∈
      nhds (m : ℝ) := by
    exact Ioo_mem_nhds hleftlt (by norm_num)
  have hmem : leftSet ∪ rightSet ∈ nhds (m : ℝ) := by
    apply Filter.mem_of_superset hopen
    intro y hy
    by_cases hle : y ≤ (m : ℝ)
    · left
      exact ⟨le_of_lt hy.1, hle⟩
    · right
      exact ⟨le_of_not_ge hle, le_of_lt hy.2⟩
  exact (hleft.union hright).hasDerivAt hmem

private theorem primitive_hasDerivAt_on_domain (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxpos : 0 < x := hx
  have hb :
      (Int.floor x : ℝ) ≤ x ∧
        x < (Int.floor x : ℝ) + 1 := by
    rw [← Int.floor_eq_iff]
  have hz0 : 0 ≤ Int.floor x := by
    by_contra hz
    have hzle : Int.floor x ≤ -1 := by omega
    have hzleR : (Int.floor x : ℝ) ≤ (-1 : ℝ) := by
      exact_mod_cast hzle
    nlinarith [hb.2]
  let n : ℕ := (Int.floor x).toNat
  have hnint : (n : ℤ) = Int.floor x := by
    simp [n, Int.toNat_of_nonneg hz0]
  have hncast : (n : ℝ) = floorR x := by
    rw [floorR, ← hnint]
    norm_num
  have hxlo : (n : ℝ) ≤ x := by
    rw [hncast]
    exact hb.1
  have hxhi : x < (n : ℝ) + 1 := by
    rw [hncast]
    exact hb.2
  by_cases heq : x = (n : ℝ)
  · have hnposR : 0 < (n : ℝ) := by
      simpa [heq] using hxpos
    have hnpos : 0 < n := by
      exact_mod_cast hnposR
    have hbder := primitive_hasDerivAt_nat n hnpos
    have hint0 : integrand (n : ℝ) = 0 := by
      simp [integrand, sin_pi_mul_nat n]
    rw [heq, hint0]
    exact hbder
  · have hxstrict : (n : ℝ) < x :=
      lt_of_le_of_ne hxlo (Ne.symm heq)
    have hxint : x ∈ interval n := ⟨hxstrict, hxhi⟩
    have hbase :=
      (localPrimitive_hasDerivAt n x hxint).add_const
        ((n : ℝ) * (n : ℝ) / Real.pi)
    have hevent : primitive =ᶠ[nhds x]
        fun y => localPrimitive n y +
          (n : ℝ) * (n : ℝ) / Real.pi := by
      filter_upwards [isOpen_Ioo.mem_nhds hxint] with y hy
      exact primitive_eq_shiftedLocal_on_closed_unit n y
        ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    exact hbase.congr_of_eventuallyEq hevent

private theorem antiderivativesOn_domain_eq_primitive :
    AntiderivativesOn domain integrand =
      PrimitiveFamilyOn domain primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hz : (1 : ℝ) ∈ domain := by
      norm_num [domain]
    have hd : ∀ y ∈ domain,
        HasDerivAt (fun t => F t - primitive t) 0 y := by
      intro y hy
      convert (hF y hy).sub (primitive_hasDerivAt_on_domain y hy) using 1 <;>
        ring
    have hdiff : DifferentiableOn ℝ
        (fun t => F t - primitive t) domain := by
      intro y hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ domain,
        deriv (fun t => F t - primitive t) y = 0 := by
      intro y hy
      exact (hd y hy).deriv
    have heq := isOpen_Ioi.is_const_of_deriv_eq_zero
      isPreconnected_Ioi hdiff hzero hx hz
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt_on_domain x hx).add_const C).congr_of_eventuallyEq
      hevent

theorem gap1 :
    ∀ x ∈ domain, 0 ≤ x := by
  intro x hx
  exact le_of_lt hx
theorem gap2 :
    AntiderivativesOn (interval 0) integrand =
      PrimitiveFamilyOn (interval 0) (fun _ => 0) := by
  apply antiderivativesOn_Ioo_characterization (z := (1 / 2 : ℝ))
  · norm_num [interval]
  · intro x hx
    have hfloor : floorR x = 0 := by
      simpa using floorR_eq_nat_of_mem_interval 0 x hx
    have hint : integrand x = 0 := by
      simp [integrand, hfloor]
    rw [hint]
    simpa using (hasDerivAt_const x (0 : ℝ))
theorem gap3 :
    primitive 1 - primitive 0 = 0 := by
  norm_num [primitive, floorR, floorSign, Real.pi_ne_zero]
theorem gap4 :
    AntiderivativesOn (interval 1) integrand =
      PrimitiveFamilyOn (interval 1) (localPrimitive 1) := by
  apply antiderivativesOn_Ioo_characterization (z := (3 / 2 : ℝ))
  · norm_num [interval]
  · exact localPrimitive_hasDerivAt 1
theorem gap5 :
    primitive 2 - primitive 1 = 2 / Real.pi := by
  have h2 :
      Real.cos (Real.pi * (2 : ℝ)) * Real.cos (Real.pi * (2 : ℝ)) = 1 := by
    simpa using cos_pi_mul_nat_sq 2
  norm_num [primitive, floorR, floorSign, Real.pi_ne_zero]
  rw [h2]
  norm_num
theorem gap6 :
    AntiderivativesOn (interval 2) integrand =
      PrimitiveFamilyOn (interval 2) (localPrimitive 2) := by
  apply antiderivativesOn_Ioo_characterization (z := (5 / 2 : ℝ))
  · norm_num [interval]
  · exact localPrimitive_hasDerivAt 2
theorem gap7 :
    primitive 3 - primitive 2 = 2 * 2 / Real.pi := by
  have h2 :
      Real.cos (Real.pi * (2 : ℝ)) * Real.cos (Real.pi * (2 : ℝ)) = 1 := by
    simpa using cos_pi_mul_nat_sq 2
  have h3 :
      Real.cos (Real.pi * (3 : ℝ)) * Real.cos (Real.pi * (3 : ℝ)) = 1 := by
    simpa using cos_pi_mul_nat_sq 3
  norm_num [primitive, floorR, floorSign, Real.pi_ne_zero]
  rw [h3, h2]
  ring
theorem gap8 (n : ℕ) :
    AntiderivativesOn (interval n) integrand =
      PrimitiveFamilyOn (interval n) (localPrimitive n) := by
  apply antiderivativesOn_Ioo_characterization
    (z := (n : ℝ) + 1 / 2)
  · constructor <;> norm_num [interval]
  · exact localPrimitive_hasDerivAt n
theorem gap9 (n : ℕ) (x : ℝ)
    (hx0 : (n : ℝ) ≤ x) (hx1 : x ≤ (n : ℝ) + 1) :
    primitive x - primitive n =
      Real.cos (Real.pi * (n : ℝ)) * (n : ℝ) / Real.pi *
        (Real.cos (Real.pi * (n : ℝ)) - Real.cos (Real.pi * x)) := by
  have hxmem : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := ⟨hx0, hx1⟩
  have hnmem : (n : ℝ) ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
    constructor <;> norm_num
  rw [primitive_eq_branch_on_closed_unit n x hxmem]
  rw [primitive_eq_branch_on_closed_unit n (n : ℝ) hnmem]
  ring
theorem gap10 :
    ∃ F : ℝ → ℝ,
      AntiderivativesOn domain integrand = PrimitiveFamilyOn domain F := by
  refine ⟨primitive, ?_⟩
  exact antiderivativesOn_domain_eq_primitive
theorem gap11 :
    AntiderivativesOn domain integrand =
      PrimitiveFamilyOn domain expandedPrimitive := by
  have heq : expandedPrimitive = primitive := by
    funext x
    simp only [expandedPrimitive, primitive]
    ring
  rw [heq]
  exact antiderivativesOn_domain_eq_primitive
theorem gap12 :
    AntiderivativesOn domain integrand =
      PrimitiveFamilyOn domain algebraicPrimitive := by
  have heq : ∀ x ∈ domain, algebraicPrimitive x = primitive x := by
    intro x hx
    have hs := floorSign_sq x
    have hmid :
        floorSign x * floorR x * floorSign x = floorR x := by
      calc
        floorSign x * floorR x * floorSign x =
            floorR x * (floorSign x * floorSign x) := by ring
        _ = floorR x := by rw [hs]; ring
    simp only [algebraicPrimitive, primitive]
    rw [hmid]
    ring
  rw [antiderivativesOn_domain_eq_primitive]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [heq x hx]; exact hC x hx⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [← heq x hx]; exact hC x hx⟩
theorem gap13 :
    AntiderivativesOn domain integrand =
      PrimitiveFamilyOn domain primitive := by
  exact antiderivativesOn_domain_eq_primitive

end
end ProofGap.Exercise2173
