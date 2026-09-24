import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4435_1

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def addVec (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def curlFromPartials (dx dy dz : Vec3) : Vec3 :=
  (dy.2.2 - dz.2.1, dz.1 - dx.2.2, dx.2.1 - dy.1)

def summedCurl (adx ady adz bdx bdy bdz : Vec3) : Vec3 :=
  curlFromPartials (addVec adx bdx) (addVec ady bdy)
    (addVec adz bdz)

theorem gap1 (adx ady adz bdx bdy bdz : Vec3) :
    summedCurl adx ady adz bdx bdy bdz =
      curlFromPartials (addVec adx bdx) (addVec ady bdy)
        (addVec adz bdz) := by
  rfl

theorem gap2 (adx ady adz bdx bdy bdz : Vec3) :
    summedCurl adx ady adz bdx bdy bdz =
      addVec (curlFromPartials adx ady adz)
        (curlFromPartials bdx bdy bdz) := by
  apply Prod.ext
  · dsimp [summedCurl, curlFromPartials, addVec]
    ring
  · apply Prod.ext
    · dsimp [summedCurl, curlFromPartials, addVec]
      ring
    · dsimp [summedCurl, curlFromPartials, addVec]
      ring

theorem gap3 (adx ady adz bdx bdy bdz : Vec3) :
    summedCurl adx ady adz bdx bdy bdz =
      addVec (curlFromPartials adx ady adz)
        (curlFromPartials bdx bdy bdz) := by
  exact gap2 adx ady adz bdx bdy bdz

theorem gap4 (adx ady adz bdx bdy bdz : Vec3) :
    curlFromPartials (addVec adx bdx) (addVec ady bdy)
        (addVec adz bdz) =
      addVec (curlFromPartials adx ady adz)
        (curlFromPartials bdx bdy bdz) := by
  simpa only [summedCurl] using
    (gap2 adx ady adz bdx bdy bdz)

end

end ProofGap.Exercise4435_1
