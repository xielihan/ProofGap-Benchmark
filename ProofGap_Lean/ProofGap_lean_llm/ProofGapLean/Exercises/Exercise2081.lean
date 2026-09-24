import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2081
noncomputable section

def Commensurate {m : ℕ} (a : Fin m → ℝ) : Prop :=
  ∃ α : ℝ, α ≠ 0 ∧ ∃ k : Fin m → ℤ, ∀ i, a i = (k i : ℝ) * α
def xOfT (α t : ℝ) := Real.log t / α
def XIntegrand {m : ℕ} (R : (Fin m → ℝ) → ℝ) (a : Fin m → ℝ) (x : ℝ) :=
  R (fun i => Real.exp (a i * x))
def TIntegrand {m : ℕ} (R : (Fin m → ℝ) → ℝ)
    (α : ℝ) (k : Fin m → ℤ) (t : ℝ) :=
  R (fun i => t ^ k i) / (α * t)
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def PullbackFamily (α : ℝ) (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ Set.Ioi (0 : ℝ), G t = F (xOfT α t)}
def ScaledFamily (U : Set ℝ) (c : ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∃ C, ∀ x ∈ U, F x = c * G x + C}

private theorem scaledFamily_eq_family
    (U : Set ℝ) (hU : IsOpen U) (c : ℝ) (hc : c ≠ 0) (f : ℝ → ℝ) :
    ScaledFamily U c f = Family U (fun x => c * f x) := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨G, hG, C, hFG⟩
    intro x hx
    have hd : HasDerivAt (fun y => c * G y + C) (c * f x) x := by
      simpa using ((hG x hx).const_mul c).add_const C
    have heq : F =ᶠ[nhds x] fun y => c * G y + C := by
      exact Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hFG y hy)
    exact heq.hasDerivAt_iff.mpr hd
  · intro hF
    refine ⟨fun x => c⁻¹ * F x, ?_, 0, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul c⁻¹
      convert hd using 1 <;> field_simp [hc] <;> ring
    · intro x hx
      field_simp [hc] <;> ring

theorem gap1 {m : ℕ} (a : Fin m → ℝ) (h : Commensurate a) :
    ∃ α : ℝ, ∃ k : Fin m → ℤ, α ≠ 0 ∧ ∀ i, a i = (k i : ℝ) * α := by
  rcases h with ⟨α, hα, k, hk⟩
  exact ⟨α, k, hα, hk⟩
theorem gap2 (α t : ℝ) : xOfT α t = Real.log t / α := by
  rfl
theorem gap3 (α t : ℝ) (hα : α ≠ 0) (ht : 0 < t) :
    HasDerivAt (xOfT α) (1 / (α * t)) t := by
  unfold xOfT
  convert (Real.hasDerivAt_log ht.ne').div_const α using 1 <;>
    field_simp [hα, ht.ne'] <;> ring
theorem gap4 {m : ℕ} (R : (Fin m → ℝ) → ℝ) (a : Fin m → ℝ)
    (α : ℝ) (k : Fin m → ℤ) (hα : α ≠ 0)
    (ha : ∀ i, a i = (k i : ℝ) * α) :
    PullbackFamily α (Family Set.univ (XIntegrand R a)) =
      ScaledFamily (Set.Ioi 0) (1 / α)
        (fun t => R (fun i => t ^ k i) / t) := by
  have hsubst (t : ℝ) (ht : 0 < t) :
      XIntegrand R a (xOfT α t) = R (fun i => t ^ k i) := by
    unfold XIntegrand
    apply congrArg R
    funext i
    rw [ha i]
    unfold xOfT
    have halg :
        ((k i : ℝ) * α) * (Real.log t / α) =
          (k i : ℝ) * Real.log t := by
      field_simp [hα] <;> ring
    rw [halg]
    calc
      Real.exp ((k i : ℝ) * Real.log t) =
          Real.exp (Real.log t * (k i : ℝ)) := by
        congr 1
        ring
      _ = t ^ (k i : ℝ) := by
        rw [Real.rpow_def_of_pos ht]
      _ = t ^ k i := by
        exact Real.rpow_intCast t (k i)
  have hxexp (x : ℝ) :
      xOfT α (Real.exp (α * x)) = x := by
    unfold xOfT
    rw [Real.log_exp]
    field_simp [hα]
  apply Set.ext
  intro G
  constructor
  · rintro ⟨F, hF, hrel⟩
    refine ⟨fun t => α * F (xOfT α t), ?_, 0, ?_⟩
    · intro t ht
      have ht0 : 0 < t := ht
      have hd :
          HasDerivAt (fun s => α * F (xOfT α s))
            (α * (XIntegrand R a (xOfT α t) * (1 / (α * t)))) t := by
        simpa using
          ((hF (xOfT α t) (Set.mem_univ _)).comp t
            (gap3 α t hα ht0)).const_mul α
      rw [hsubst t ht0] at hd
      convert hd using 1
      field_simp [hα, ht0.ne'] <;> ring
    · intro t ht
      rw [hrel t ht]
      field_simp [hα] <;> ring
  · rintro ⟨H, hH, C, hrel⟩
    refine ⟨fun x => (1 / α) * H (Real.exp (α * x)) + C, ?_, ?_⟩
    · intro x hx
      have ht : 0 < Real.exp (α * x) := Real.exp_pos _
      have hinner :
          HasDerivAt (fun y : ℝ => α * y) α x := by
        simpa using (hasDerivAt_id x).const_mul α
      have hexpder :
          HasDerivAt (fun y : ℝ => Real.exp (α * y))
            (Real.exp (α * x) * α) x :=
        (Real.hasDerivAt_exp (α * x)).comp x hinner
      have hd :
          HasDerivAt
            (fun y : ℝ => (1 / α) * H (Real.exp (α * y)) + C)
            ((1 / α) *
              ((R (fun i => (Real.exp (α * x)) ^ k i) /
                  Real.exp (α * x)) *
                (Real.exp (α * x) * α))) x := by
        simpa using
          (((hH (Real.exp (α * x)) ht).comp x hexpder).const_mul
            (1 / α)).add_const C
      have hs := hsubst (Real.exp (α * x)) ht
      rw [hxexp x] at hs
      convert hd using 1
      rw [hs]
      field_simp [hα, Real.exp_ne_zero (α * x)] <;> ring
    · intro t ht
      have ht0 : 0 < t := ht
      rw [hrel t ht]
      change
        1 / α * H t + C =
          1 / α * H (Real.exp (α * (Real.log t / α))) + C
      have halg : α * (Real.log t / α) = Real.log t := by
        field_simp [hα]
      rw [halg, Real.exp_log ht0]
theorem gap5 {m : ℕ} (R : (Fin m → ℝ) → ℝ) (a : Fin m → ℝ)
    (α : ℝ) (k : Fin m → ℤ) (hα : α ≠ 0)
    (ha : ∀ i, a i = (k i : ℝ) * α) :
    ∃ Rstar : ℝ → ℝ,
      PullbackFamily α (Family Set.univ (XIntegrand R a)) =
        Family (Set.Ioi 0) Rstar := by
  refine ⟨fun t => (1 / α) * (R (fun i => t ^ k i) / t), ?_⟩
  calc
    PullbackFamily α (Family Set.univ (XIntegrand R a)) =
        ScaledFamily (Set.Ioi 0) (1 / α)
          (fun t => R (fun i => t ^ k i) / t) :=
      gap4 R a α k hα ha
    _ = Family (Set.Ioi 0)
          (fun t => (1 / α) * (R (fun i => t ^ k i) / t)) :=
      scaledFamily_eq_family (Set.Ioi 0) isOpen_Ioi (1 / α)
        (div_ne_zero one_ne_zero hα)
        (fun t => R (fun i => t ^ k i) / t)
theorem gap6 {m : ℕ} (R : (Fin m → ℝ) → ℝ) (a : Fin m → ℝ)
    (h : Commensurate a) :
    ∃ α : ℝ, ∃ Rstar : ℝ → ℝ, α ≠ 0 ∧
      PullbackFamily α (Family Set.univ (XIntegrand R a)) =
        Family (Set.Ioi 0) Rstar := by
  rcases gap1 a h with ⟨α, k, hα, ha⟩
  rcases gap5 R a α k hα ha with ⟨Rstar, hRstar⟩
  exact ⟨α, Rstar, hα, hRstar⟩
theorem gap7 {m : ℕ} (R : (Fin m → ℝ) → ℝ) (a : Fin m → ℝ)
    (h : Commensurate a) :
    ∃ α : ℝ, ∃ Rstar : ℝ → ℝ, α ≠ 0 ∧
      PullbackFamily α (Family Set.univ (XIntegrand R a)) =
        Family (Set.Ioi 0) Rstar := by
  exact gap6 R a h
theorem gap8 {m : ℕ} (R : (Fin m → ℝ) → ℝ) :
    ∀ a : Fin m → ℝ, Commensurate a →
      ∃ α : ℝ, ∃ Rstar : ℝ → ℝ, α ≠ 0 ∧
        PullbackFamily α (Family Set.univ (XIntegrand R a)) =
          Family (Set.Ioi 0) Rstar := by
  intro a ha
  exact gap7 R a ha

end
end ProofGap.Exercise2081
