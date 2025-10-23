
-- Affine Weierstrass curves over a field

open import Algebra.Curve.Params

module Algebra.Curve.Elliptic.Affine ( Curve : WeierstrassCurve ) where

--------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )
open import Data.Fin using ( Fin ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec

open import Meta.Object

open import Algebra.API.Field

open BitLib

--------------------------------------------------------------------------------

open WeierstrassCurve Curve
open FieldAPI baseFieldAPI

private

  A B : Tm F
  A = Lit coeffA
  B = Lit coeffB

  isZero : Tm F -> Tm Bit
  isZero = isEqualℕ 0
  
  _==_ : Tm F -> Tm F -> Tm Bit
  _==_ = isEqual

  infix 40 _==_

Pt : Ty
Pt = Struct (F ∷ F ∷ Bit ∷ [])

private 
  f0 f1 f2 : Fin 3
  f0 = fzero
  f1 = fsuc fzero
  f2 = fsuc (fsuc fzero)

xcoord ycoord : Tm Pt -> Tm F
xcoord = proj f0
ycoord = proj f1

isInf : Tm Pt -> Tm Bit
isInf = proj f2

mkPt : Tm F -> Tm F -> Tm Bit -> Tm Pt
mkPt x y isinf = mkStruct (Cons x (Cons y (Cons isinf Nil)))

withPt : {ty : Ty} -> Tm Pt -> (Tm F -> Tm F -> Tm Bit -> Tm ty)  -> Tm ty
withPt pt f = f (xcoord pt) (ycoord pt) (isInf pt)

inf : Tm Pt
inf = mkPt (fromℕ 0) (fromℕ 0) true

ecIsEqual : Tm Pt -> Tm Pt -> Tm Bit
ecIsEqual pt1 pt2 = runGen do
  inf1 <- gen (isInf pt1)
  inf2 <- gen (isInf pt2)
  return (ifte (not inf1 && not inf2) result
    (ifte (inf1 && inf2) true false))
  where
    result = (xcoord pt1 == xcoord pt2) &&
             (ycoord pt1 == ycoord pt2)

private

  _+_ _-_ _*_ _/_ : Tm F -> Tm F -> Tm F
  _+_ = add
  _-_ = sub
  _*_ = mul
  _/_ = div

  infixl 50 _+_ _-_
  infixl 60 _*_ _/_
  
  dbl : Tm F -> Tm F
  dbl x = x + x
  
-- y^2 =?= x^3 + A*x + B
isOnCurve : Tm Pt -> Tm Bit
isOnCurve pt = isInf pt || check where
  x  = xcoord pt
  y  = ycoord pt
  x2 = sqr x
  y2 = sqr y
  x3 = x2 * x
  Ax = mul A x
  check = isZero (x3 + A * x + B - y2)
  
--------------------------------------------------------------------------------

ecNeg : Tm Pt -> Tm Pt
ecNeg pt = withPt pt \x y inf -> mkPt x (neg y) inf

ecDbl : Tm Pt -> Tm Pt
ecDbl pt1 = ifte (isInf pt1) pt1 result where
  x1 = xcoord pt1
  y1 = ycoord pt1

  numer = (fromℕ 3) * sqr x1 + A
  denom = dbl y1
  t = numer / denom

  xu = sqr t - dbl x1
  yu = neg (y1 + t * (xu - x1))

  result = mkPt xu yu false
 
ecAdd : Tm Pt -> Tm Pt -> Tm Pt
ecAdd pt1 pt2 =
  ifte (isInf pt1) pt2
    (ifte (isInf pt2) pt1
      (ifte (ecIsEqual pt1 pt2) (ecDbl pt1) result))
  where
    x1 = xcoord pt1
    y1 = ycoord pt1
    x2 = xcoord pt2
    y2 = ycoord pt2
    
    s  = (y2 - y1) / (x2 - x1)
    xr = sqr s - (x1 + x2)
    yr = neg (y1 + s * (xr - x1))
    
    result = mkPt xr yr false

ecSub : Tm Pt -> Tm Pt -> Tm Pt
ecSub pt1 pt2 = ecAdd pt1 (ecNeg pt2)

--------------------------------------------------------------------------------

open import Algebra.API.Group

groupAPI : GroupAPI
groupAPI = record
    { G     = Pt
    ; unit  = inf
    ; name  = "Projective Weierstrass elliptic curve"
    -- queries
    ; isUnit  = isInf
    ; isEqual = ecIsEqual
    -- arithmetic
    ; gneg   = ecNeg
    ; gdbl   = ecDbl
    ; gadd   = ecAdd
    ; gsub   = ecSub
    }

withGroupAPI : {A : Set} -> (GroupAPI -> Gen A) -> Gen A
withGroupAPI userAction = userAction groupAPI

--------------------------------------------------------------------------------
