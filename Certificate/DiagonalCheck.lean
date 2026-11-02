import Std

namespace Certificate
/-- Integer dot product. Shape is checked separately by `checkGramWitness`. -/
def dot (a b : List Int) : Int :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

def entryInterval (a b d scale lo hi product : Int) : Int × Int :=
  let rational := (a - d * product) * scale
  (rational + min (b * lo) (b * hi), rational + max (b * lo) (b * hi))

def checkRow (i : Nat) (as_ bs_ : List Int) (factor : List (List Int))
    (d scale lo hi : Int) : Bool := Id.run do
  let mut radius : Int := 0
  let mut diagonal : Int := 0
  for (a,b,j,row) in as_.zip (bs_.zip ((List.range factor.length).zip factor)) |>.map
      (fun (a,b,j,row) => (a,b,j,row)) do
    let (lower,upper) := entryInterval a b d scale lo hi (dot (factor[i]!) row)
    if i == j then diagonal := lower
    else radius := radius + max lower.natAbs upper.natAbs
  return decide (radius < diagonal)

def symmetric (m : List (List Int)) : Bool :=
  (List.range m.length).all fun i =>
    (List.range m.length).all fun j => decide (m[i]![j]! = m[j]![i]!)

/-- Fully computational witness check, with no floating-point operations. -/
def checkGramWitness (n : Nat) (den facDen scale lo hi : Int)
    (a b factor : List (List Int)) : Bool :=
  decide (0 < den ∧ 0 < facDen ∧ 0 < scale ∧ 0 ≤ lo ∧ lo ≤ hi ∧
    lo*lo ≤ 3*scale*scale ∧ 3*scale*scale ≤ hi*hi ∧ den % (facDen*facDen) = 0) &&
  [a,b,factor].all (fun m => decide (m.length=n) && m.all (fun r => decide (r.length=n))) &&
  symmetric a && symmetric b &&
  ((List.range n).zip (a.zip b)).all (fun (i,as_,bs_) =>
    checkRow i as_ bs_ factor (den / (facDen*facDen)) scale lo hi)
end Certificate
