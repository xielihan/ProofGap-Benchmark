import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3349

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def vec3 (x y z : ℝ) : Vec3 :=
  (x, y, z)

def dot (r s : Vec3) : ℝ :=
  r.1 * s.1 + r.2.1 * s.2.1 + r.2.2 * s.2.2

def norm (r : Vec3) : ℝ :=
  Real.sqrt (dot r r)

def angle (r s : Vec3) : ℝ :=
  Real.arccos (dot r s / (norm r * norm s))

structure AsymptoticData where
  a : ℝ
  b : ℝ
  c : ℝ
  m : ℝ
  n : ℝ
  p : ℝ
  x₀ : ℕ → ℝ
  y₀ : ℕ → ℝ
  z₀ : ℕ → ℝ
  habc : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0
  hx : Tendsto x₀ atTop atTop
  hy : Tendsto y₀ atTop atTop
  hz : Tendsto z₀ atTop atTop

def u (D : AsymptoticData) (x y z : ℝ) : ℝ :=
  D.a * x ^ 2 + D.b * y ^ 2 + D.c * z ^ 2

def v (D : AsymptoticData) (x y z : ℝ) : ℝ :=
  u D x y z + 2 * D.m * x + 2 * D.n * y + 2 * D.p * z

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def grad (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Vec3 :=
  vec3 (partialX f x y z) (partialY f x y z) (partialZ f x y z)

def M₀ (D : AsymptoticData) (k : ℕ) : Vec3 :=
  vec3 (D.x₀ k) (D.y₀ k) (D.z₀ k)

def gradAt (f : ℝ → ℝ → ℝ → ℝ) (r : Vec3) : Vec3 :=
  grad f r.1 r.2.1 r.2.2

def α (D : AsymptoticData) (k : ℕ) : ℝ :=
  D.a * D.x₀ k

def β (D : AsymptoticData) (k : ℕ) : ℝ :=
  D.b * D.y₀ k

def γ (D : AsymptoticData) (k : ℕ) : ℝ :=
  D.c * D.z₀ k

def α₁ (D : AsymptoticData) (k : ℕ) : ℝ :=
  α D k + D.m

def β₁ (D : AsymptoticData) (k : ℕ) : ℝ :=
  β D k + D.n

def γ₁ (D : AsymptoticData) (k : ℕ) : ℝ :=
  γ D k + D.p

def base (D : AsymptoticData) (k : ℕ) : Vec3 :=
  vec3 (α D k) (β D k) (γ D k)

def shifted (D : AsymptoticData) (k : ℕ) : Vec3 :=
  vec3 (α₁ D k) (β₁ D k) (γ₁ D k)

def θ (D : AsymptoticData) (k : ℕ) : ℝ :=
  angle (base D k) (shifted D k)

def δ (D : AsymptoticData) (k : ℕ) : ℝ :=
  max |α D k| (max |β D k| |γ D k|)

def q (D : AsymptoticData) : ℝ :=
  max |D.m| (max |D.n| |D.p|)

def crossNumerator (D : AsymptoticData) (k : ℕ) : ℝ :=
  (α D k * β₁ D k - α₁ D k * β D k) ^ 2 +
    (α D k * γ₁ D k - α₁ D k * γ D k) ^ 2 +
    (β D k * γ₁ D k - β₁ D k * γ D k) ^ 2

def baseSq (D : AsymptoticData) (k : ℕ) : ℝ :=
  α D k ^ 2 + β D k ^ 2 + γ D k ^ 2

def shiftedSq (D : AsymptoticData) (k : ℕ) : ℝ :=
  α₁ D k ^ 2 + β₁ D k ^ 2 + γ₁ D k ^ 2

def upperBound (D : AsymptoticData) (k : ℕ) : ℝ :=
  12 * q D ^ 2 /
    (δ D k ^ 2 - 6 * δ D k * q D - 3 * q D ^ 2)

private theorem ratio_bounds
    (x y z X Y Z : ℝ)
    (hA : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0)
    (hB : Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2) ≠ 0) :
    -1 ≤ (x * X + y * Y + z * Z) /
      (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
        Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2)) ∧
    (x * X + y * Y + z * Z) /
      (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
        Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2)) ≤ 1 := by
  have hA0 : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hB0 : 0 ≤ X ^ 2 + Y ^ 2 + Z ^ 2 := by positivity
  have hsA : 0 < Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hA)
  have hsB : 0 < Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hB)
  have hp : 0 < Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
      Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2) := mul_pos hsA hsB
  have hsA2 := Real.sq_sqrt hA0
  have hsB2 := Real.sq_sqrt hB0
  have hprod :
      (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
        Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2)) ^ 2 =
      (x ^ 2 + y ^ 2 + z ^ 2) * (X ^ 2 + Y ^ 2 + Z ^ 2) := by
    rw [mul_pow, hsA2, hsB2]
  have hcs :
      (x * X + y * Y + z * Z) ^ 2 ≤
        (x ^ 2 + y ^ 2 + z ^ 2) * (X ^ 2 + Y ^ 2 + Z ^ 2) := by
    nlinarith [sq_nonneg (x * Y - X * y),
      sq_nonneg (x * Z - X * z), sq_nonneg (y * Z - Y * z)]
  have hlo :
      -(Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
        Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2)) ≤ x * X + y * Y + z * Z := by
    nlinarith
  have hhi : x * X + y * Y + z * Z ≤
      Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) *
        Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2) := by
    nlinarith
  constructor
  · exact (le_div_iff₀ hp).2 (by simpa using hlo)
  · exact (div_le_iff₀ hp).2 (by simpa using hhi)

private theorem tendsto_atTop_of_le
    (f g : ℕ → ℝ) (hfg : ∀ k, f k ≤ g k)
    (hf : Tendsto f atTop atTop) : Tendsto g atTop atTop := by
  intro s hs
  rcases (Filter.mem_atTop_sets.mp hs) with ⟨b, hb⟩
  have hfb : ∀ᶠ k in atTop, b ≤ f k :=
    hf (Filter.eventually_ge_atTop b)
  change ∀ᶠ k in atTop, g k ∈ s
  exact hfb.mono (fun k hk => hb (g k) (le_trans hk (hfg k)))

private theorem tendsto_abs_mul_atTop
    (a : ℝ) (x : ℕ → ℝ) (ha : a ≠ 0)
    (hx : Tendsto x atTop atTop) :
    Tendsto (fun k => |a * x k|) atTop atTop := by
  intro s hs
  rcases (Filter.mem_atTop_sets.mp hs) with ⟨b, hb⟩
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hxevent : ∀ᶠ k in atTop, max 0 (b / |a|) ≤ x k :=
    hx (Filter.eventually_ge_atTop (max 0 (b / |a|)))
  change ∀ᶠ k in atTop, |a * x k| ∈ s
  refine hxevent.mono ?_
  intro k hk
  apply hb
  have hx0 : 0 ≤ x k := le_trans (le_max_left _ _) hk
  have hquot : b / |a| ≤ x k := le_trans (le_max_right _ _) hk
  calc
    b = |a| * (b / |a|) := by field_simp
    _ ≤ |a| * x k := mul_le_mul_of_nonneg_left hquot ha'.le
    _ = |a * x k| := by rw [abs_mul, abs_of_nonneg hx0]

private theorem tendsto_atTop_nhds_congr
    {f g : ℕ → ℝ} {a : ℝ}
    (hfg : f =ᶠ[atTop] g)
    (hg : Tendsto g atTop (nhds a)) :
    Tendsto f atTop (nhds a) := by
  intro s hs
  have hgs : ∀ᶠ k in atTop, g k ∈ s := hg hs
  change ∀ᶠ k in atTop, f k ∈ s
  filter_upwards [hfg, hgs] with k hEq hk
  simpa [hEq] using hk

private theorem hasDerivAt_scaled_sq (a x : ℝ) :
    HasDerivAt (fun s : ℝ => a * s ^ 2) (2 * a * x) x := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
  convert (hid.mul hid).const_mul a using 1 <;> simp [pow_two] <;> ring

private theorem square_le_square_of_abs_le
    (x B : ℝ) (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  have hm : |x| * |x| ≤ B * B :=
    mul_self_le_mul_self (abs_nonneg x) h
  nlinarith [sq_abs x]

private theorem angle_two_mul (x y z X Y Z : ℝ) :
    angle (vec3 (2 * x) (2 * y) (2 * z))
      (vec3 (2 * X) (2 * Y) (2 * Z)) =
    angle (vec3 x y z) (vec3 X Y Z) := by
  have hs4sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
  have hs4nonneg := Real.sqrt_nonneg (4 : ℝ)
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by nlinarith
  have hsA :
      Real.sqrt ((2 * x) * (2 * x) + (2 * y) * (2 * y) + (2 * z) * (2 * z)) =
        2 * Real.sqrt (x * x + y * y + z * z) := by
    rw [show (2 * x) * (2 * x) + (2 * y) * (2 * y) + (2 * z) * (2 * z) =
      4 * (x * x + y * y + z * z) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]
  have hsB :
      Real.sqrt ((2 * X) * (2 * X) + (2 * Y) * (2 * Y) + (2 * Z) * (2 * Z)) =
        2 * Real.sqrt (X * X + Y * Y + Z * Z) := by
    rw [show (2 * X) * (2 * X) + (2 * Y) * (2 * Y) + (2 * Z) * (2 * Z) =
      4 * (X * X + Y * Y + Z * Z) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]
  unfold angle norm dot
  simp only [vec3, Prod.fst, Prod.snd]
  rw [hsA, hsB]
  congr 1
  ring_nf

theorem gap1 (D : AsymptoticData) :
    Tendsto D.x₀ atTop atTop := by
  exact D.hx

theorem gap2 (D : AsymptoticData) :
    Tendsto D.y₀ atTop atTop := by
  exact D.hy

theorem gap3 (D : AsymptoticData) :
    Tendsto D.z₀ atTop atTop := by
  exact D.hz

theorem gap4 (D : AsymptoticData) :
    ∀ k,
      gradAt (u D) (M₀ D k) =
        vec3 (2 * D.a * D.x₀ k) (2 * D.b * D.y₀ k)
          (2 * D.c * D.z₀ k) := by
  intro k
  ext
  · simp only [gradAt, grad, partialX, M₀, vec3, u]
    have h0 := hasDerivAt_scaled_sq D.a (D.x₀ k)
    have h1 := h0.add_const (D.b * D.y₀ k ^ 2)
    have h2 := h1.add_const (D.c * D.z₀ k ^ 2)
    simpa using h2.deriv
  · simp only [gradAt, grad, partialY, M₀, vec3, u]
    have h0 := hasDerivAt_const (D.y₀ k) (D.a * D.x₀ k ^ 2)
    have h1 := h0.add (hasDerivAt_scaled_sq D.b (D.y₀ k))
    have h2 := h1.add_const (D.c * D.z₀ k ^ 2)
    simpa using h2.deriv
  · simp only [gradAt, grad, partialZ, M₀, vec3, u]
    simpa using (hasDerivAt_scaled_sq D.c (D.z₀ k)).deriv

theorem gap5 (D : AsymptoticData) :
    ∀ k,
      gradAt (v D) (M₀ D k) =
        vec3 (2 * D.a * D.x₀ k + 2 * D.m)
          (2 * D.b * D.y₀ k + 2 * D.n)
          (2 * D.c * D.z₀ k + 2 * D.p) := by
  intro k
  ext
  · simp only [gradAt, grad, partialX, M₀, vec3, v, u]
    have hlin := (hasDerivAt_id (D.x₀ k)).const_mul (2 * D.m)
    have h0 := hasDerivAt_scaled_sq D.a (D.x₀ k)
    have h1 := h0.add_const (D.b * D.y₀ k ^ 2)
    have h2 := h1.add_const (D.c * D.z₀ k ^ 2)
    have h3 := h2.add hlin
    have h4 := h3.add_const (2 * D.n * D.y₀ k)
    have h5 := h4.add_const (2 * D.p * D.z₀ k)
    simpa using h5.deriv
  · simp only [gradAt, grad, partialY, M₀, vec3, v, u]
    have hlin := (hasDerivAt_id (D.y₀ k)).const_mul (2 * D.n)
    have h0 := hasDerivAt_const (D.y₀ k) (D.a * D.x₀ k ^ 2)
    have h1 := h0.add (hasDerivAt_scaled_sq D.b (D.y₀ k))
    have h2 := h1.add_const (D.c * D.z₀ k ^ 2)
    have h3 := h2.add_const (2 * D.m * D.x₀ k)
    have h4 := h3.add hlin
    have h5 := h4.add_const (2 * D.p * D.z₀ k)
    simpa using h5.deriv
  · simp only [gradAt, grad, partialZ, M₀, vec3, v, u]
    have hlin := (hasDerivAt_id (D.z₀ k)).const_mul (2 * D.p)
    have h0 := hasDerivAt_const (D.z₀ k) (D.a * D.x₀ k ^ 2)
    have h1 := h0.add_const (D.b * D.y₀ k ^ 2)
    have h2 := h1.add (hasDerivAt_scaled_sq D.c (D.z₀ k))
    have h3 := h2.add_const (2 * D.m * D.x₀ k)
    have h4 := h3.add_const (2 * D.n * D.y₀ k)
    have h5 := h4.add hlin
    simpa using h5.deriv

theorem gap6 (D : AsymptoticData) (k : ℕ)
    (hbase : norm (base D k) ≠ 0)
    (hshifted : norm (shifted D k) ≠ 0) :
    Real.cos (θ D k) =
      (α D k * α₁ D k + β D k * β₁ D k + γ D k * γ₁ D k) /
        (Real.sqrt (baseSq D k) * Real.sqrt (shiftedSq D k)) := by
  have hb : Real.sqrt (baseSq D k) ≠ 0 := by
    simpa [norm, dot, base, vec3, baseSq, pow_two] using hbase
  have hs : Real.sqrt (shiftedSq D k) ≠ 0 := by
    simpa [norm, dot, shifted, vec3, shiftedSq, pow_two] using hshifted
  have hbounds := ratio_bounds
    (α D k) (β D k) (γ D k)
    (α₁ D k) (β₁ D k) (γ₁ D k) hb hs
  have harg :
      dot (base D k) (shifted D k) /
          (norm (base D k) * norm (shifted D k)) =
        (α D k * α₁ D k + β D k * β₁ D k + γ D k * γ₁ D k) /
          (Real.sqrt (baseSq D k) * Real.sqrt (shiftedSq D k)) := by
    simp [base, shifted, norm, dot, vec3, baseSq, shiftedSq, pow_two]
  unfold θ angle
  rw [harg]
  exact Real.cos_arccos hbounds.1 hbounds.2

theorem gap7 (D : AsymptoticData) (k : ℕ)
    (hbase : norm (base D k) ≠ 0)
    (hshifted : norm (shifted D k) ≠ 0) :
    Real.sin (θ D k) ^ 2 =
      crossNumerator D k / (baseSq D k * shiftedSq D k) := by
  have hb0 : 0 ≤ baseSq D k := by
    simp [baseSq]
    positivity
  have hs0 : 0 ≤ shiftedSq D k := by
    simp [shiftedSq]
    positivity
  have hb : Real.sqrt (baseSq D k) ≠ 0 := by
    simpa [norm, dot, base, vec3, baseSq, pow_two] using hbase
  have hs : Real.sqrt (shiftedSq D k) ≠ 0 := by
    simpa [norm, dot, shifted, vec3, shiftedSq, pow_two] using hshifted
  have hb' : baseSq D k ≠ 0 := by
    intro h
    apply hb
    simp [h]
  have hs' : shiftedSq D k ≠ 0 := by
    intro h
    apply hs
    simp [h]
  have hbsq := Real.sq_sqrt hb0
  have hssq := Real.sq_sqrt hs0
  have htrig := Real.sin_sq_add_cos_sq (θ D k)
  calc
    Real.sin (θ D k) ^ 2 =
        1 - ((α D k * α₁ D k + β D k * β₁ D k + γ D k * γ₁ D k) /
          (Real.sqrt (baseSq D k) * Real.sqrt (shiftedSq D k))) ^ 2 := by
            rw [← gap6 D k hbase hshifted]
            nlinarith
    _ = crossNumerator D k / (baseSq D k * shiftedSq D k) := by
      field_simp [hb, hs, hb', hs']
      rw [hbsq, hssq]
      simp [crossNumerator, baseSq, shiftedSq]
      ring

theorem gap8 (D : AsymptoticData) (k : ℕ)
    (hbase : norm (base D k) ≠ 0)
    (hshifted : norm (shifted D k) ≠ 0) :
    Real.sin (θ D k) ^ 2 =
      ((D.n * α D k - D.m * β D k) ^ 2 +
        (D.p * α D k - D.m * γ D k) ^ 2 +
        (D.p * β D k - D.n * γ D k) ^ 2) /
      (baseSq D k * shiftedSq D k) := by
  rw [gap7 D k hbase hshifted]
  congr 1
  simp [crossNumerator, α₁, β₁, γ₁]
  ring

theorem gap9 (D : AsymptoticData) :
    ∀ k, δ D k ≤ Real.sqrt (baseSq D k) := by
  intro k
  have ha2 : α D k ^ 2 ≤ baseSq D k := by
    simp [baseSq]
    nlinarith [sq_nonneg (β D k), sq_nonneg (γ D k)]
  have hb2 : β D k ^ 2 ≤ baseSq D k := by
    simp [baseSq]
    nlinarith [sq_nonneg (α D k), sq_nonneg (γ D k)]
  have hc2 : γ D k ^ 2 ≤ baseSq D k := by
    simp [baseSq]
    nlinarith [sq_nonneg (α D k), sq_nonneg (β D k)]
  have ha : |α D k| ≤ Real.sqrt (baseSq D k) := by
    simpa [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt ha2
  have hb : |β D k| ≤ Real.sqrt (baseSq D k) := by
    simpa [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hb2
  have hc : |γ D k| ≤ Real.sqrt (baseSq D k) := by
    simpa [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hc2
  exact max_le ha (max_le hb hc)

theorem gap10 (D : AsymptoticData) :
    ∀ k, Real.sqrt (baseSq D k) ≤ Real.sqrt 3 * δ D k := by
  intro k
  let d := δ D k
  have hd : 0 ≤ d := by
    dsimp [d, δ]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have ha : |α D k| ≤ d := by
    dsimp [d, δ]
    exact le_max_left _ _
  have hb : |β D k| ≤ d := by
    dsimp [d, δ]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hc : |γ D k| ≤ d := by
    dsimp [d, δ]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have ha2 : α D k ^ 2 ≤ d ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg (α D k)) ha
  have hb2 : β D k ^ 2 ≤ d ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg (β D k)) hb
  have hc2 : γ D k ^ 2 ≤ d ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg (γ D k)) hc
  have hsum : baseSq D k ≤ 3 * d ^ 2 := by
    simp [baseSq]
    nlinarith
  calc
    Real.sqrt (baseSq D k) ≤ Real.sqrt (3 * d ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * Real.sqrt (d ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = Real.sqrt 3 * d := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hd]
    _ = Real.sqrt 3 * δ D k := by rfl

theorem gap11 (D : AsymptoticData) :
    ∀ k, δ D k ≤ Real.sqrt 3 * δ D k := by
  intro k
  have hd : 0 ≤ δ D k := by
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hs : 1 ≤ Real.sqrt 3 := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  nlinarith

theorem gap12 (D : AsymptoticData) :
    Tendsto (δ D) atTop atTop := by
  by_cases ha : D.a ≠ 0
  · apply tendsto_atTop_of_le
      (fun k => |D.a * D.x₀ k|) (δ D)
    · intro k
      exact le_max_left _ _
    · exact tendsto_abs_mul_atTop D.a D.x₀ ha D.hx
  by_cases hb : D.b ≠ 0
  · apply tendsto_atTop_of_le
      (fun k => |D.b * D.y₀ k|) (δ D)
    · intro k
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact tendsto_abs_mul_atTop D.b D.y₀ hb D.hy
  · have ha0 : D.a = 0 := not_ne_iff.mp ha
    have hb0 : D.b = 0 := not_ne_iff.mp hb
    have hc : D.c ≠ 0 := by
      intro hc0
      apply D.habc
      simp [ha0, hb0, hc0]
    apply tendsto_atTop_of_le
      (fun k => |D.c * D.z₀ k|) (δ D)
    · intro k
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    · exact tendsto_abs_mul_atTop D.c D.z₀ hc D.hz

theorem gap13 (D : AsymptoticData) :
    ∀ k, 0 ≤ Real.sin (θ D k) ^ 2 := by
  intro k
  positivity

theorem gap14 (D : AsymptoticData) (k : ℕ)
    (hlarge : 7 * q D < δ D k) :
    Real.sin (θ D k) ^ 2 ≤ upperBound D k := by
  set_option maxHeartbeats 2000000 in
  let d := δ D k
  let Q := q D
  change 7 * Q < d at hlarge
  have hd : 0 ≤ d := by
    dsimp [d, δ]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hQ : 0 ≤ Q := by
    dsimp [Q, q]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hdpos : 0 < d := by nlinarith
  have ha : |α D k| ≤ d := by
    dsimp [d, δ]
    exact le_max_left _ _
  have hb : |β D k| ≤ d := by
    dsimp [d, δ]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hc : |γ D k| ≤ d := by
    dsimp [d, δ]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hm : |D.m| ≤ Q := by
    dsimp [Q, q]
    exact le_max_left _ _
  have hn : |D.n| ≤ Q := by
    dsimp [Q, q]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hp : |D.p| ≤ Q := by
    dsimp [Q, q]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hbase0 : 0 ≤ baseSq D k := by
    simp [baseSq]
    positivity
  have hdeltaBase : d ^ 2 ≤ baseSq D k := by
    have hnorm := gap9 D k
    have hs : Real.sqrt (baseSq D k) ^ 2 =
        α D k ^ 2 + β D k ^ 2 + γ D k ^ 2 := by
      simpa [baseSq] using Real.sq_sqrt hbase0
    have hs0 := Real.sqrt_nonneg (baseSq D k)
    change d ≤ Real.sqrt (baseSq D k) at hnorm
    simp [baseSq]
    nlinarith
  have ham : |α D k * D.m| ≤ d * Q := by
    rw [abs_mul]
    exact mul_le_mul ha hm (abs_nonneg _) hd
  have hbn : |β D k * D.n| ≤ d * Q := by
    rw [abs_mul]
    exact mul_le_mul hb hn (abs_nonneg _) hd
  have hcp : |γ D k * D.p| ≤ d * Q := by
    rw [abs_mul]
    exact mul_le_mul hc hp (abs_nonneg _) hd
  have hamlow : -d * Q ≤ α D k * D.m := by
    exact le_trans (by nlinarith : -d * Q ≤ -|α D k * D.m|)
      (neg_abs_le (α D k * D.m))
  have hbnlow : -d * Q ≤ β D k * D.n := by
    exact le_trans (by nlinarith : -d * Q ≤ -|β D k * D.n|)
      (neg_abs_le (β D k * D.n))
  have hcplow : -d * Q ≤ γ D k * D.p := by
    exact le_trans (by nlinarith : -d * Q ≤ -|γ D k * D.p|)
      (neg_abs_le (γ D k * D.p))
  have hshiftLower : d ^ 2 - 6 * d * Q ≤ shiftedSq D k := by
    simp [shiftedSq, α₁, β₁, γ₁]
    simp [baseSq] at hdeltaBase
    nlinarith [sq_nonneg D.m, sq_nonneg D.n, sq_nonneg D.p]
  have hL : 0 < d ^ 2 - 6 * d * Q - 3 * Q ^ 2 := by
    have hprod : 0 < (d - 7 * Q) * (d + Q) := by
      exact mul_pos (sub_pos.mpr hlarge) (by nlinarith)
    nlinarith [sq_nonneg Q]
  have hshiftPos : 0 < shiftedSq D k := by
    nlinarith [sq_nonneg Q]
  have hbasePos : 0 < baseSq D k := by nlinarith
  have hbaseNorm : norm (base D k) ≠ 0 := by
    simpa [norm, dot, base, vec3, baseSq, pow_two] using
      ne_of_gt (Real.sqrt_pos.2 hbasePos)
  have hshiftNorm : norm (shifted D k) ≠ 0 := by
    simpa [norm, dot, shifted, vec3, shiftedSq, pow_two] using
      ne_of_gt (Real.sqrt_pos.2 hshiftPos)
  have hna : |D.n * α D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hn ha (abs_nonneg _) hQ
  have hmb : |D.m * β D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hm hb (abs_nonneg _) hQ
  have hpa : |D.p * α D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hp ha (abs_nonneg _) hQ
  have hmc : |D.m * γ D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hm hc (abs_nonneg _) hQ
  have hpb : |D.p * β D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hp hb (abs_nonneg _) hQ
  have hnc : |D.n * γ D k| ≤ Q * d := by
    rw [abs_mul]
    exact mul_le_mul hn hc (abs_nonneg _) hQ
  have h1abs : |D.n * α D k - D.m * β D k| ≤ 2 * Q * d := by
    calc
      |D.n * α D k - D.m * β D k| ≤
          |D.n * α D k| + |D.m * β D k| := abs_sub _ _
      _ ≤ Q * d + Q * d := add_le_add hna hmb
      _ = 2 * Q * d := by ring
  have h2abs : |D.p * α D k - D.m * γ D k| ≤ 2 * Q * d := by
    calc
      |D.p * α D k - D.m * γ D k| ≤
          |D.p * α D k| + |D.m * γ D k| := abs_sub _ _
      _ ≤ Q * d + Q * d := add_le_add hpa hmc
      _ = 2 * Q * d := by ring
  have h3abs : |D.p * β D k - D.n * γ D k| ≤ 2 * Q * d := by
    calc
      |D.p * β D k - D.n * γ D k| ≤
          |D.p * β D k| + |D.n * γ D k| := abs_sub _ _
      _ ≤ Q * d + Q * d := add_le_add hpb hnc
      _ = 2 * Q * d := by ring
  have h1sq : (D.n * α D k - D.m * β D k) ^ 2 ≤ 4 * Q ^ 2 * d ^ 2 := by
    calc
      (D.n * α D k - D.m * β D k) ^ 2 ≤ (2 * Q * d) ^ 2 :=
        square_le_square_of_abs_le _ _ h1abs
      _ = 4 * Q ^ 2 * d ^ 2 := by ring
  have h2sq : (D.p * α D k - D.m * γ D k) ^ 2 ≤ 4 * Q ^ 2 * d ^ 2 := by
    calc
      (D.p * α D k - D.m * γ D k) ^ 2 ≤ (2 * Q * d) ^ 2 :=
        square_le_square_of_abs_le _ _ h2abs
      _ = 4 * Q ^ 2 * d ^ 2 := by ring
  have h3sq : (D.p * β D k - D.n * γ D k) ^ 2 ≤ 4 * Q ^ 2 * d ^ 2 := by
    calc
      (D.p * β D k - D.n * γ D k) ^ 2 ≤ (2 * Q * d) ^ 2 :=
        square_le_square_of_abs_le _ _ h3abs
      _ = 4 * Q ^ 2 * d ^ 2 := by ring
  have hnum :
      (D.n * α D k - D.m * β D k) ^ 2 +
        (D.p * α D k - D.m * γ D k) ^ 2 +
        (D.p * β D k - D.n * γ D k) ^ 2 ≤
      12 * Q ^ 2 * d ^ 2 := by
    linarith
  have hdenLower :
      d ^ 2 * (d ^ 2 - 6 * d * Q - 3 * Q ^ 2) ≤
        baseSq D k * shiftedSq D k := by
    calc
      d ^ 2 * (d ^ 2 - 6 * d * Q - 3 * Q ^ 2) ≤
          d ^ 2 * shiftedSq D k := by
            apply mul_le_mul_of_nonneg_left
            · nlinarith [sq_nonneg Q]
            · exact sq_nonneg d
      _ ≤ baseSq D k * shiftedSq D k :=
        mul_le_mul_of_nonneg_right hdeltaBase hshiftPos.le
  rw [gap8 D k hbaseNorm hshiftNorm]
  unfold upperBound
  change
    ((D.n * α D k - D.m * β D k) ^ 2 +
      (D.p * α D k - D.m * γ D k) ^ 2 +
      (D.p * β D k - D.n * γ D k) ^ 2) /
        (baseSq D k * shiftedSq D k) ≤
      12 * Q ^ 2 / (d ^ 2 - 6 * d * Q - 3 * Q ^ 2)
  apply (div_le_iff₀ (mul_pos hbasePos hshiftPos)).2
  rw [show
      12 * Q ^ 2 / (d ^ 2 - 6 * d * Q - 3 * Q ^ 2) *
          (baseSq D k * shiftedSq D k) =
        (12 * Q ^ 2 * (baseSq D k * shiftedSq D k)) /
          (d ^ 2 - 6 * d * Q - 3 * Q ^ 2) by
      ring]
  apply (le_div_iff₀ hL).2
  calc
    ((D.n * α D k - D.m * β D k) ^ 2 +
        (D.p * α D k - D.m * γ D k) ^ 2 +
        (D.p * β D k - D.n * γ D k) ^ 2) *
        (d ^ 2 - 6 * d * Q - 3 * Q ^ 2)
        ≤ (12 * Q ^ 2 * d ^ 2) *
          (d ^ 2 - 6 * d * Q - 3 * Q ^ 2) :=
            mul_le_mul_of_nonneg_right hnum hL.le
    _ = 12 * Q ^ 2 *
          (d ^ 2 * (d ^ 2 - 6 * d * Q - 3 * Q ^ 2)) := by ring
    _ ≤ 12 * Q ^ 2 * (baseSq D k * shiftedSq D k) :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)

theorem gap15 (D : AsymptoticData) :
    Tendsto (upperBound D) atTop (nhds 0) := by
  let e : ℕ → ℝ := fun k => (δ D k)⁻¹
  have he : Tendsto e atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp (gap12 D)
  have he2 : Tendsto (fun k => e k ^ 2) atTop (nhds 0) := by
    convert he.pow 2 using 1 <;> norm_num
  have h6 : Tendsto (fun k => 6 * q D * e k) atTop (nhds 0) := by
    convert he.const_mul (6 * q D) using 1 <;> norm_num
  have h3 : Tendsto (fun k => 3 * q D ^ 2 * e k ^ 2) atTop (nhds 0) := by
    convert he2.const_mul (3 * q D ^ 2) using 1 <;> norm_num
  have hnum : Tendsto (fun k => 12 * q D ^ 2 * e k ^ 2) atTop (nhds 0) := by
    convert he2.const_mul (12 * q D ^ 2) using 1 <;> norm_num
  have hden : Tendsto
      (fun k => 1 - 6 * q D * e k - 3 * q D ^ 2 * e k ^ 2)
      atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub h6).sub h3 using 1 <;> norm_num
  have hratio : Tendsto
      (fun k => (12 * q D ^ 2 * e k ^ 2) /
        (1 - 6 * q D * e k - 3 * q D ^ 2 * e k ^ 2))
      atTop (nhds 0) := by
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have heq :
      upperBound D =ᶠ[atTop]
        (fun k => (12 * q D ^ 2 * e k ^ 2) /
          (1 - 6 * q D * e k - 3 * q D ^ 2 * e k ^ 2)) := by
    have hδ : ∀ᶠ k in atTop, (1 : ℝ) ≤ δ D k :=
      (gap12 D) (Filter.eventually_ge_atTop (1 : ℝ))
    have hevent : ∀ᶠ k in atTop, δ D k ≠ 0 := by
      filter_upwards [hδ] with k hk
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
    filter_upwards [hevent] with k hk
    dsimp [e]
    unfold upperBound
    field_simp [hk]
  exact tendsto_atTop_nhds_congr heq hratio

theorem gap16 :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) ∧ (0 : ℝ) ≤ 0 := by
  exact ⟨tendsto_const_nhds, le_rfl⟩

theorem gap17 (D : AsymptoticData) :
    Tendsto (fun k => Real.sin (θ D k) ^ 2) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
    (gap15 D)
  · exact Filter.Eventually.of_forall (gap13 D)
  · have hδ : ∀ᶠ k in atTop, 7 * q D + 1 ≤ δ D k :=
      (gap12 D) (Filter.eventually_ge_atTop (7 * q D + 1))
    have hlarge : ∀ᶠ k in atTop, 7 * q D < δ D k := by
      filter_upwards [hδ] with k hk
      linarith
    filter_upwards [hlarge] with k hk
    exact gap14 D k hk

theorem gap18 (D : AsymptoticData) :
    Tendsto (θ D) atTop (nhds 0) := by
  have hsin : Tendsto (fun k => Real.sin (θ D k)) atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp (gap17 D)
    have hsqrt0 : Tendsto
        (fun k => Real.sqrt (Real.sin (θ D k) ^ 2)) atTop (nhds 0) := by
      simpa [Function.comp_def] using hsqrt
    have heq :
        (fun k => Real.sin (θ D k)) =ᶠ[atTop]
          (fun k => Real.sqrt (Real.sin (θ D k) ^ 2)) :=
      Filter.Eventually.of_forall (fun k => by
        change Real.sin (θ D k) = Real.sqrt (Real.sin (θ D k) ^ 2)
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        exact Real.sin_nonneg_of_nonneg_of_le_pi
          (Real.arccos_nonneg _) (Real.arccos_le_pi _))
    exact tendsto_atTop_nhds_congr heq hsqrt0
  have hδ : ∀ᶠ k in atTop, 7 * q D + 1 ≤ δ D k :=
    (gap12 D) (Filter.eventually_ge_atTop (7 * q D + 1))
  have hlarge : ∀ᶠ k in atTop, 7 * q D < δ D k := by
    filter_upwards [hδ] with k hk
    linarith
  have htheta : ∀ᶠ k in atTop, θ D k ≤ Real.pi / 2 := by
    filter_upwards [hlarge] with k hk
    let d := δ D k
    let Q := q D
    change 7 * Q < d at hk
    have hd : 0 ≤ d := by
      dsimp [d, δ]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    have hQ : 0 ≤ Q := by
      dsimp [Q, q]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    have hdpos : 0 < d := by nlinarith
    have ha : |α D k| ≤ d := by
      dsimp [d, δ]
      exact le_max_left _ _
    have hb : |β D k| ≤ d := by
      dsimp [d, δ]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hc : |γ D k| ≤ d := by
      dsimp [d, δ]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hm : |D.m| ≤ Q := by
      dsimp [Q, q]
      exact le_max_left _ _
    have hn : |D.n| ≤ Q := by
      dsimp [Q, q]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hp : |D.p| ≤ Q := by
      dsimp [Q, q]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have ham : |α D k * D.m| ≤ d * Q := by
      rw [abs_mul]
      exact mul_le_mul ha hm (abs_nonneg _) hd
    have hbn : |β D k * D.n| ≤ d * Q := by
      rw [abs_mul]
      exact mul_le_mul hb hn (abs_nonneg _) hd
    have hcp : |γ D k * D.p| ≤ d * Q := by
      rw [abs_mul]
      exact mul_le_mul hc hp (abs_nonneg _) hd
    have hbase0 : 0 ≤ baseSq D k := by
      simp [baseSq]
      positivity
    have hdeltaBase : d ^ 2 ≤ baseSq D k := by
      have hs : Real.sqrt (baseSq D k) ^ 2 =
          α D k ^ 2 + β D k ^ 2 + γ D k ^ 2 := by
        simpa [baseSq] using Real.sq_sqrt hbase0
      have hs0 := Real.sqrt_nonneg (baseSq D k)
      have hnorm := gap9 D k
      change d ≤ Real.sqrt (baseSq D k) at hnorm
      simp [baseSq]
      nlinarith
    have hamlow : -d * Q ≤ α D k * D.m := by
      exact le_trans (by nlinarith : -d * Q ≤ -|α D k * D.m|)
        (neg_abs_le (α D k * D.m))
    have hbnlow : -d * Q ≤ β D k * D.n := by
      exact le_trans (by nlinarith : -d * Q ≤ -|β D k * D.n|)
        (neg_abs_le (β D k * D.n))
    have hcplow : -d * Q ≤ γ D k * D.p := by
      exact le_trans (by nlinarith : -d * Q ≤ -|γ D k * D.p|)
        (neg_abs_le (γ D k * D.p))
    have hdot : 0 ≤
        α D k * α₁ D k + β D k * β₁ D k + γ D k * γ₁ D k := by
      simp [α₁, β₁, γ₁]
      simp [baseSq] at hdeltaBase
      nlinarith
    unfold θ angle
    apply (Real.arccos_le_pi_div_two).2
    exact div_nonneg hdot
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have harcsin := Real.continuous_arcsin.continuousAt.tendsto.comp hsin
  have harcsin0 : Tendsto
      (fun k => Real.arcsin (Real.sin (θ D k))) atTop (nhds 0) := by
    simpa [Function.comp_def] using harcsin
  have heq :
      θ D =ᶠ[atTop] (fun k => Real.arcsin (Real.sin (θ D k))) := by
    filter_upwards [htheta] with k hk
    symm
    apply Real.arcsin_sin
    · have hnonneg : 0 ≤ θ D k := Real.arccos_nonneg _
      nlinarith [Real.pi_pos.le]
    · exact hk
  exact tendsto_atTop_nhds_congr heq harcsin0

theorem gap19 (D : AsymptoticData) :
    Tendsto
      (fun k => angle (gradAt (u D) (M₀ D k)) (gradAt (v D) (M₀ D k)))
      atTop (nhds 0) := by
  have heq :
      (fun k => angle (gradAt (u D) (M₀ D k))
        (gradAt (v D) (M₀ D k))) =ᶠ[atTop] θ D :=
    Filter.Eventually.of_forall (fun k => by
      calc
        angle (gradAt (u D) (M₀ D k)) (gradAt (v D) (M₀ D k)) =
            angle
              (vec3 (2 * D.a * D.x₀ k) (2 * D.b * D.y₀ k)
                (2 * D.c * D.z₀ k))
              (vec3 (2 * D.a * D.x₀ k + 2 * D.m)
                (2 * D.b * D.y₀ k + 2 * D.n)
                (2 * D.c * D.z₀ k + 2 * D.p)) := by
                  rw [gap4 D k, gap5 D k]
        _ = angle (base D k) (shifted D k) := by
          simpa only [α, β, γ, α₁, β₁, γ₁, base, shifted,
            mul_assoc, mul_add] using
            angle_two_mul (α D k) (β D k) (γ D k)
              (α₁ D k) (β₁ D k) (γ₁ D k)
        _ = θ D k := by rfl)
  exact tendsto_atTop_nhds_congr heq (gap18 D)

end

end ProofGap.Exercise3349
