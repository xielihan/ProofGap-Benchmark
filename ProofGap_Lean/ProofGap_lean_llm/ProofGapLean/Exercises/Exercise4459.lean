import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4459

noncomputable section

open scoped BigOperators

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def add (p q : Vec3) : Vec3 :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)

def neg (p : Vec3) : Vec3 :=
  (-p.1, -p.2.1, -p.2.2)

def sub (p q : Vec3) : Vec3 :=
  add p (neg q)

def scale (a : ℝ) (p : Vec3) : Vec3 :=
  (a * p.1, a * p.2.1, a * p.2.2)

def radius (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def regularAt {n : ℕ} (sources : Fin n → Vec3) (p : Vec3) : Prop :=
  ∀ i, p ≠ sources i

def regularDomain {n : ℕ} (sources : Fin n → Vec3) : Set Vec3 :=
  {p | regularAt sources p}

def displacement {n : ℕ} (sources : Fin n → Vec3)
    (p : Vec3) (i : Fin n) : Vec3 :=
  sub p (sources i)

def gravitationalField {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p : Vec3) : Vec3 :=
  ∑ i, scale (-mass i / radius (displacement sources p i) ^ 3)
    (displacement sources p i)

def potential {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p : Vec3) : ℝ :=
  ∑ i, mass i / radius (displacement sources p i)

def fieldOneForm {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p v : Vec3) : ℝ :=
  dot (gravitationalField mass sources p) v

def potentialDifferential {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p v : Vec3) : ℝ :=
  dot (gradient (potential mass sources) p) v

def potentialFamily {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (C : ℝ) (p : Vec3) : ℝ :=
  potential mass sources p + C

private theorem gradient_potential_eq_field {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p : Vec3) (hp : regularAt sources p) :
    gradient (potential mass sources) p = gravitationalField mass sources p := by
  classical
  have derivTerm (m a A B x : ℝ)
      (h : 0 < A + (x - a) ^ 2 + B) :
      HasDerivAt (fun t => m / Real.sqrt (A + (t - a) ^ 2 + B))
        ((-m / Real.sqrt (A + (x - a) ^ 2 + B) ^ 3) * (x - a)) x := by
    have hq : HasDerivAt (fun t => A + (t - a) ^ 2 + B)
        (2 * (x - a)) x := by
      convert (((hasDerivAt_id x).sub_const a).pow 2).add_const (A + B)
        using 1
      · funext t
        dsimp
        ring
      · simp [id] <;> ring_nf
    have hs := (Real.hasDerivAt_sqrt h.ne').comp x hq
    have hi := hs.inv (Real.sqrt_ne_zero'.mpr h)
    have hd := (hasDerivAt_const x m).mul hi
    convert hd using 1 <;>
      simp [Function.comp_def, div_eq_mul_inv] <;>
      field_simp [Real.sqrt_ne_zero'.mpr h] <;>
      ring
  have hpos (i : Fin n) :
      0 < (p.1 - (sources i).1) ^ 2 +
        (p.2.1 - (sources i).2.1) ^ 2 +
        (p.2.2 - (sources i).2.2) ^ 2 := by
    have hn : 0 ≤ (p.1 - (sources i).1) ^ 2 +
        (p.2.1 - (sources i).2.1) ^ 2 +
        (p.2.2 - (sources i).2.2) ^ 2 := by
      positivity
    have hne : (p.1 - (sources i).1) ^ 2 +
        (p.2.1 - (sources i).2.1) ^ 2 +
        (p.2.2 - (sources i).2.2) ^ 2 ≠ 0 := by
      intro hz
      apply hp i
      apply Prod.ext
      · nlinarith [sq_nonneg (p.1 - (sources i).1),
          sq_nonneg (p.2.1 - (sources i).2.1),
          sq_nonneg (p.2.2 - (sources i).2.2)]
      · apply Prod.ext
        · nlinarith [sq_nonneg (p.1 - (sources i).1),
            sq_nonneg (p.2.1 - (sources i).2.1),
            sq_nonneg (p.2.2 - (sources i).2.2)]
        · nlinarith [sq_nonneg (p.1 - (sources i).1),
            sq_nonneg (p.2.1 - (sources i).2.1),
            sq_nonneg (p.2.2 - (sources i).2.2)]
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have hdx (i : Fin n) :
      HasDerivAt
        (fun x => mass i /
          radius (displacement sources (x, p.2.1, p.2.2) i))
        ((-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).1) p.1 := by
    let B := (p.2.1 - (sources i).2.1) ^ 2 +
      (p.2.2 - (sources i).2.2) ^ 2
    have hrad (t : ℝ) :
        radius (displacement sources (t, p.2.1, p.2.2) i) =
          Real.sqrt (0 + (t - (sources i).1) ^ 2 + B) := by
      unfold radius
      apply congrArg Real.sqrt
      simp [dot, displacement, sub, add, neg, B]
      ring
    have h : 0 < 0 + (p.1 - (sources i).1) ^ 2 + B := by
      dsimp [B]
      nlinarith [hpos i]
    simpa only [hrad] using
      derivTerm (mass i) (sources i).1 0 B p.1 h
  have hdy (i : Fin n) :
      HasDerivAt
        (fun y => mass i /
          radius (displacement sources (p.1, y, p.2.2) i))
        ((-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).2.1) p.2.1 := by
    let A := (p.1 - (sources i).1) ^ 2
    let B := (p.2.2 - (sources i).2.2) ^ 2
    have hrad (t : ℝ) :
        radius (displacement sources (p.1, t, p.2.2) i) =
          Real.sqrt (A + (t - (sources i).2.1) ^ 2 + B) := by
      unfold radius
      apply congrArg Real.sqrt
      simp [dot, displacement, sub, add, neg, A, B]
      ring
    have h : 0 < A + (p.2.1 - (sources i).2.1) ^ 2 + B := by
      dsimp [A, B]
      exact hpos i
    simpa only [hrad] using
      derivTerm (mass i) (sources i).2.1 A B p.2.1 h
  have hdz (i : Fin n) :
      HasDerivAt
        (fun z => mass i /
          radius (displacement sources (p.1, p.2.1, z) i))
        ((-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).2.2) p.2.2 := by
    let A := (p.1 - (sources i).1) ^ 2 +
      (p.2.1 - (sources i).2.1) ^ 2
    have hrad (t : ℝ) :
        radius (displacement sources (p.1, p.2.1, t) i) =
          Real.sqrt (A + (t - (sources i).2.2) ^ 2 + 0) := by
      unfold radius
      apply congrArg Real.sqrt
      simp [dot, displacement, sub, add, neg, A]
      ring
    have h : 0 < A + (p.2.2 - (sources i).2.2) ^ 2 + 0 := by
      dsimp [A]
      nlinarith [hpos i]
    simpa only [hrad] using
      derivTerm (mass i) (sources i).2.2 A 0 p.2.2 h
  have hX : HasDerivAt
      (fun x => potential mass sources (x, p.2.1, p.2.2))
      (∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
        (displacement sources p i).1) p.1 := by
    unfold potential
    convert (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) => hdx i) using 1
    funext t
    simp only [Finset.sum_apply]
  have hY : HasDerivAt
      (fun y => potential mass sources (p.1, y, p.2.2))
      (∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
        (displacement sources p i).2.1) p.2.1 := by
    unfold potential
    convert (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) => hdy i) using 1
    funext t
    simp only [Finset.sum_apply]
  have hZ : HasDerivAt
      (fun z => potential mass sources (p.1, p.2.1, z))
      (∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
        (displacement sources p i).2.2) p.2.2 := by
    unfold potential
    convert (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) => hdz i) using 1
    funext t
    simp only [Finset.sum_apply]
  have hsumCoords (s : Finset (Fin n)) :
      s.sum (fun i =>
        scale (-mass i / radius (displacement sources p i) ^ 3)
          (displacement sources p i)) =
      (s.sum (fun i =>
          (-mass i / radius (displacement sources p i) ^ 3) *
            (displacement sources p i).1),
       s.sum (fun i =>
          (-mass i / radius (displacement sources p i) ^ 3) *
            (displacement sources p i).2.1),
       s.sum (fun i =>
          (-mass i / radius (displacement sources p i) ^ 3) *
            (displacement sources p i).2.2)) := by
    induction s using Finset.induction_on with
    | empty =>
        apply Prod.ext
        · simp
        · apply Prod.ext <;> simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, ih]
        apply Prod.ext
        · simp [scale, Finset.sum_insert, hi]
        · apply Prod.ext <;> simp [scale, Finset.sum_insert, hi]
  have hField :
      gravitationalField mass sources p =
      (∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).1,
       ∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).2.1,
       ∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
          (displacement sources p i).2.2) := by
    unfold gravitationalField
    exact hsumCoords Finset.univ
  rw [hField]
  apply Prod.ext
  · simpa only [gradient, partialX] using hX.deriv
  · apply Prod.ext
    · simpa only [gradient, partialY] using hY.deriv
    · simpa only [gradient, partialZ] using hZ.deriv

theorem gap1 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p : Vec3)
    (hp : regularAt sources p) :
    gravitationalField mass sources p =
      ∑ i, scale (-mass i / radius (displacement sources p i) ^ 3)
        (displacement sources p i) := by
  rfl

theorem gap2 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p v : Vec3)
    (hp : regularAt sources p) :
    potentialDifferential mass sources p v =
      fieldOneForm mass sources p v := by
  unfold potentialDifferential fieldOneForm
  rw [gradient_potential_eq_field mass sources p hp]

theorem gap3 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p v : Vec3)
    (hp : regularAt sources p) :
    dot (gradient (potential mass sources) p) v =
      ∑ i, (-mass i / radius (displacement sources p i) ^ 3) *
        dot (displacement sources p i) v := by
  classical
  rw [gradient_potential_eq_field mass sources p hp]
  unfold gravitationalField
  have hdot_add (a b : Vec3) :
      dot (a + b) v = dot a v + dot b v := by
    simp [dot]
    ring
  have hdot_scale (c : ℝ) (a : Vec3) :
      dot (scale c a) v = c * dot a v := by
    simp [dot, scale]
    ring
  have hsum (s : Finset (Fin n)) :
      dot (s.sum fun i =>
        scale (-mass i / radius (displacement sources p i) ^ 3)
          (displacement sources p i)) v =
      s.sum fun i =>
        (-mass i / radius (displacement sources p i) ^ 3) *
          dot (displacement sources p i) v := by
    induction s using Finset.induction_on with
    | empty => simp [dot]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [hdot_add, hdot_scale, ih]
  exact hsum Finset.univ

theorem gap4 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (p : Vec3)
    (hp : regularAt sources p) :
    gradient (potential mass sources) p =
      gravitationalField mass sources p := by
  exact gradient_potential_eq_field mass sources p hp

theorem gap5 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (u : Vec3 → ℝ) (p₀ : Vec3)
    (hp₀ : p₀ ∈ regularDomain sources)
    (hConnected : IsPreconnected (regularDomain sources))
    (hu : DifferentiableOn ℝ u (regularDomain sources))
    (hPotential :
      DifferentiableOn ℝ (potential mass sources) (regularDomain sources))
    (hGradient :
      ∀ p ∈ regularDomain sources,
        gradient u p = gradient (potential mass sources) p) :
    ∃ C : ℝ, ∀ p ∈ regularDomain sources,
      u p = potentialFamily mass sources C p := by
  classical
  have hopen : IsOpen (regularDomain sources) := by
    rw [show regularDomain sources = ⋂ i, ({sources i} : Set Vec3)ᶜ by
      ext p
      simp [regularDomain, regularAt]]
    exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton
  let w : Vec3 → ℝ := fun p => u p - potential mass sources p
  have hw : DifferentiableOn ℝ w (regularDomain sources) := by
    exact hu.sub hPotential
  have hzero : ∀ p ∈ regularDomain sources, fderiv ℝ w p = 0 := by
    intro p hp
    have huAt : DifferentiableAt ℝ u p :=
      hu.differentiableAt (hopen.mem_nhds hp)
    have hvAt : DifferentiableAt ℝ (potential mass sources) p :=
      hPotential.differentiableAt (hopen.mem_nhds hp)
    have hcx :=
      (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) p.2.1 p.1).prodMk
          (hasFDerivAt_const (𝕜 := ℝ) p.2.2 p.1))
    have hcy :=
      (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2.1).prodMk
        ((hasFDerivAt_id (𝕜 := ℝ) p.2.1).prodMk
          (hasFDerivAt_const (𝕜 := ℝ) p.2.2 p.2.1))
    have hcz :=
      (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2.2).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) p.2.1 p.2.2).prodMk
          (hasFDerivAt_id (𝕜 := ℝ) p.2.2))
    have hux : partialX u p = fderiv ℝ u p (1, 0, 0) := by
      simpa [partialX, Function.comp_def, id] using
        (huAt.hasFDerivAt.comp p.1 hcx).hasDerivAt.deriv
    have huy : partialY u p = fderiv ℝ u p (0, 1, 0) := by
      simpa [partialY, Function.comp_def, id] using
        (huAt.hasFDerivAt.comp p.2.1 hcy).hasDerivAt.deriv
    have huz : partialZ u p = fderiv ℝ u p (0, 0, 1) := by
      simpa [partialZ, Function.comp_def, id] using
        (huAt.hasFDerivAt.comp p.2.2 hcz).hasDerivAt.deriv
    have hvx : partialX (potential mass sources) p =
        fderiv ℝ (potential mass sources) p (1, 0, 0) := by
      simpa [partialX, Function.comp_def, id] using
        (hvAt.hasFDerivAt.comp p.1 hcx).hasDerivAt.deriv
    have hvy : partialY (potential mass sources) p =
        fderiv ℝ (potential mass sources) p (0, 1, 0) := by
      simpa [partialY, Function.comp_def, id] using
        (hvAt.hasFDerivAt.comp p.2.1 hcy).hasDerivAt.deriv
    have hvz : partialZ (potential mass sources) p =
        fderiv ℝ (potential mass sources) p (0, 0, 1) := by
      simpa [partialZ, Function.comp_def, id] using
        (hvAt.hasFDerivAt.comp p.2.2 hcz).hasDerivAt.deriv
    have hgx : partialX u p = partialX (potential mass sources) p := by
      simpa [gradient] using
        congrArg (fun q : Vec3 => q.1) (hGradient p hp)
    have hgy : partialY u p = partialY (potential mass sources) p := by
      simpa [gradient] using
        congrArg (fun q : Vec3 => q.2.1) (hGradient p hp)
    have hgz : partialZ u p = partialZ (potential mass sources) p := by
      simpa [gradient] using
        congrArg (fun q : Vec3 => q.2.2) (hGradient p hp)
    have hfd : fderiv ℝ u p = fderiv ℝ (potential mass sources) p := by
      apply ContinuousLinearMap.ext
      intro q
      have hq : q = q.1 • ((1, 0, 0) : Vec3) +
          q.2.1 • ((0, 1, 0) : Vec3) +
          q.2.2 • ((0, 0, 1) : Vec3) := by
        ext <;> simp
      rw [hq]
      simp only [map_add, map_smul]
      rw [← hux, ← huy, ← huz, ← hvx, ← hvy, ← hvz, hgx, hgy, hgz]
    change fderiv ℝ (u - potential mass sources) p = 0
    calc
      fderiv ℝ (u - potential mass sources) p =
          fderiv ℝ u p - fderiv ℝ (potential mass sources) p :=
        fderiv_sub huAt hvAt
      _ = 0 := by rw [hfd, sub_self]
  refine ⟨u p₀ - potential mass sources p₀, ?_⟩
  intro p hp
  dsimp [potentialFamily]
  have hc : w p = w p₀ :=
    hopen.is_const_of_fderiv_eq_zero hConnected hw hzero hp hp₀
  dsimp [w] at hc
  linarith

theorem gap6 {n : ℕ} (mass : Fin n → ℝ)
    (sources : Fin n → Vec3) (u : Vec3 → ℝ) (p₀ : Vec3)
    (hp₀ : p₀ ∈ regularDomain sources)
    (hConnected : IsPreconnected (regularDomain sources))
    (hu : DifferentiableOn ℝ u (regularDomain sources))
    (hPotential :
      DifferentiableOn ℝ (potential mass sources) (regularDomain sources))
    (hGradient :
      ∀ p ∈ regularDomain sources,
        gradient u p = gradient (potential mass sources) p)
    (hnormalized : u p₀ = potential mass sources p₀) :
    ∀ p ∈ regularDomain sources,
      u p = potential mass sources p := by
  obtain ⟨C, hC⟩ :=
    gap5 mass sources u p₀ hp₀ hConnected hu hPotential hGradient
  have hC0 : C = 0 := by
    have h := hC p₀ hp₀
    simp [potentialFamily] at h
    linarith
  intro p hp
  have h := hC p hp
  simpa [potentialFamily, hC0] using h

end

end ProofGap.Exercise4459
