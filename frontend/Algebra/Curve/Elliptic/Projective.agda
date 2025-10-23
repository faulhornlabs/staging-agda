
-- Projective Weierstrass curves over a field

open import Algebra.Curve.Params

module Algebra.Curve.Elliptic.Projective ( Curve : WeierstrassCurve ) where

--------------------------------------------------------------------------------

open import Function using ( _$_ )

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

  -- twoB : Tm F
  -- twoB = Lit (coeffB + coeffB)     -- we cannot compute this without multi-level staging and/or built-in interpretation
  
  isZero : Tm F -> Tm Bit
  isZero x = isEqualℕ 0 x

  _==_ : Tm F -> Tm F -> Tm Bit
  _==_ = isEqual

  infix 40 _==_

Pt : Ty
Pt = Struct (F ∷ F ∷ F ∷ [])

private 
  f0 f1 f2 : Fin 3
  f0 = fzero
  f1 = fsuc fzero
  f2 = fsuc (fsuc fzero)

xcoord ycoord zcoord : Tm Pt -> Tm F
xcoord = proj f0
ycoord = proj f1
zcoord = proj f2

isInf : Tm Pt -> Tm Bit
isInf pt  = isZero (xcoord pt) && isZero (zcoord pt)

mkPt : Tm F -> Tm F -> Tm F -> Tm Pt
mkPt x y z = mkStruct (Cons x (Cons y (Cons z Nil)))

withPt : {ty : Ty} -> Tm Pt -> (Tm F -> Tm F -> Tm F -> Tm ty)  -> Tm ty
withPt pt f = f (xcoord pt) (ycoord pt) (zcoord pt)

withPt2 : {ty : Ty} -> Tm Pt -> Tm Pt -> (Tm F -> Tm F -> Tm F -> Tm F -> Tm F -> Tm F -> Tm ty)  -> Tm ty
withPt2 pt1 pt2 f = f
  (xcoord pt1) (ycoord pt1) (zcoord pt1)
  (xcoord pt2) (ycoord pt2) (zcoord pt2)

inf : Tm Pt
inf = mkPt (fromℕ 0) (fromℕ 1) (fromℕ 0) 

private

  _+_ _-_ _*_ _/_ : Tm F -> Tm F -> Tm F
  _+_ = add
  _-_ = sub
  _*_ = mul
  _/_ = div

  infixl 50 _+_ _-_
  infixl 60 _*_ _/_
  
  dbl : Tm F -> Tm F
  dbl x0 = Let x0 \x -> x + x

  mulBy2 : Tm F -> Tm F
  mulBy2 = dbl

  mulBy3 : Tm F -> Tm F
  mulBy3 x0 = Let x0 \x -> x + x + x

ecIsEqual : Tm Pt -> Tm Pt -> Tm Bit
ecIsEqual pt1 pt2 =
  ifte (isZero z2)
    (ifte (isZero x2)
      (ifte (isZero y2)
        false                    -- actually an invalid point, but we probably don't want to crash
        isEqualY≠0)
      isEqualX≠0)
   isEqualZ≠0

  where

    x1 = xcoord pt1
    y1 = ycoord pt1
    z1 = zcoord pt1

    x2 = xcoord pt2
    y2 = ycoord pt2
    z2 = zcoord pt2

    isEqualX≠0 isEqualY≠0 isEqualZ≠0 : Tm Bit
    isEqualX≠0 = Let (x1 / x2) \s -> (y1 == y2 * s) && (z1 == z2 * s)
    isEqualY≠0 = Let (y1 / y2) \s -> (x1 == x2 * s) && (z1 == z2 * s)
    isEqualZ≠0 = Let (z1 / z2) \s -> (x1 == x2 * s) && (y1 == y2 * s)

ecNormalize : Tm Pt -> Tm Pt
ecNormalize pt = withPt pt \x y z ->
  ifte (isZero z)
    (ifte (isZero x)
      (mkPt (fromℕ 0) (fromℕ 1) (fromℕ 0))                              -- x == 0 && z == 0
      (Let (inv x) \invx -> mkPt (fromℕ 1) (y * invx) (fromℕ 0)))       -- z == 0 but x /= 0 - this isn't supposed to happen?
  (Let (inv z) \invz -> mkPt (x * invz) (y * invz) (fromℕ 1))           -- z /= 0

-- z*y^2 =?= x^3 + A*x*z^2 + B*z^3
isOnCurve : Tm Pt -> Tm Bit
isOnCurve pt = withPt pt \x y z -> runGen do
  x2 <- gen (sqr x)
  y2 <- gen (sqr x)
  z2 <- gen (sqr x)
  return ( isZero (x * x2 + A * x * z2 + B * z * z2 - z * y2) )

--------------------------------------------------------------------------------

import Algebra.Curve.Elliptic.Affine

module Affine = Algebra.Curve.Elliptic.Affine Curve 

Aff : Ty
Aff = Affine.Pt

mkAff : Tm F -> Tm F -> Tm Bit -> Tm Aff
mkAff = Affine.mkPt

withAff : {ty : Ty} -> Tm Aff -> (Tm F -> Tm F -> Tm Bit -> Tm ty) -> Tm ty
withAff = Affine.withPt

fromAff : Tm Aff -> Tm Pt
fromAff pt = withAff pt \x y isinf -> ifte isinf inf (mkPt x y (fromℕ 1))

toAff : Tm Pt -> Tm Aff
toAff pt = runGen do
  norm <- gen (ecNormalize pt)
  return (ifte (isZero (zcoord norm))
    Affine.inf
    (mkAff (xcoord norm) (ycoord norm) false))
    
--------------------------------------------------------------------------------

ecNeg : Tm Pt -> Tm Pt
ecNeg pt = withPt pt \x y z -> mkPt x (neg y) z

-- <https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#doubling-dbl-2007-bl>
ecDbl : Tm Pt -> Tm Pt
ecDbl pt = withPt pt \X1 Y1 Z1 -> runGen do
  XX  <- gen $ sqr X1
  ZZ  <- gen $ sqr Z1
  w   <- gen $ A * ZZ + mulBy3 XX
  s   <- gen $ dbl (Y1 * Z1)
  ss  <- gen $ sqr s
  sss <- gen $ s * ss
  R   <- gen $ Y1 * s
  RR  <- gen $ sqr R
  B   <- gen $ sqr (X1 + R) - XX - RR
  h   <- gen $ sqr w - mulBy2 B
  X3  <- gen $ h * s
  Y3  <- gen $ w * (B - h) - mulBy2 RR
  let Z3 = sss
  return (mkPt X3 Y3 Z3)

-- <https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-add-2015-rcb>
ecAdd : Tm Pt -> Tm Pt -> Tm Pt
ecAdd pt1 pt2 = withPt pt1 \X1 Y1 Z1 -> withPt pt2 \X2 Y2 Z2 -> runGen do
  b3 <- gen (mulBy3 B)     -- normally, we would precalculate this as it is constant. But cannot easily do that in Agda
  t0 <- gen (X1 * X2)
  t1 <- gen (Y1 * Y2)
  t2 <- gen (Z1 * Z2)
  t3 <- gen (X1 + Y1)
  t4 <- gen (X2 + Y2)
  t3 <- gen (t3 * t4)
  t4 <- gen (t0 + t1)
  t3 <- gen (t3 - t4)
  t4 <- gen (X1 + Z1)
  t5 <- gen (X2 + Z2)
  t4 <- gen (t4 * t5)
  t5 <- gen (t0 + t2)
  t4 <- gen (t4 - t5)
  t5 <- gen (Y1 + Z1)
  X3 <- gen (Y2 + Z2)
  t5 <- gen (t5 * X3)
  X3 <- gen (t1 + t2)
  t5 <- gen (t5 - X3)
  Z3 <- gen (A  * t4)
  X3 <- gen (b3 * t2)
  Z3 <- gen (X3 + Z3)
  X3 <- gen (t1 - Z3)
  Z3 <- gen (t1 + Z3)
  Y3 <- gen (X3 * Z3)
  t1 <- gen (t0 + t0)
  t1 <- gen (t1 + t0)
  t2 <- gen (A  * t2)
  t4 <- gen (b3 * t4)
  t1 <- gen (t1 + t2)
  t2 <- gen (t0 - t2)
  t2 <- gen (A  * t2)
  t4 <- gen (t4 + t2)
  t0 <- gen (t1 * t4)
  Y3 <- gen (Y3 + t0)
  t0 <- gen (t5 * t4)
  X3 <- gen (t3 * X3)
  X3 <- gen (X3 - t0)
  t0 <- gen (t3 * t1)
  Z3 <- gen (t5 * Z3)
  Z3 <- gen (Z3 + t0)  
  return (mkPt X3 Y3 Z3)

ecSub : Tm Pt -> Tm Pt -> Tm Pt
ecSub pt1 pt2 = ecAdd pt1 (ecNeg pt2)

--------------------------------------------------------------------------------

-- <https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-madd-1998-cmo>
ecMixedAdd : Tm Aff -> Tm Pt -> Tm Pt
ecMixedAdd aff proj = withPt proj \X1 Y1 Z1 -> withAff aff \X2 Y2 isInf2 ->
  ifte isInf2 proj $  runGen do
    u   <- gen $ Y2 * Z1 - Y1
    uu  <- gen $ sqr u
    v   <- gen $ X2 * Z1 - X1
    vv  <- gen $ sqr v
    vvv <- gen $ v * vv
    R   <- gen $ vv * X1
    A   <- gen $ uu * Z1 - vvv - mulBy2 R
    X3  <- gen $ v * A
    Y3  <- gen $ u * (R - A) - vvv * Y1
    Z3  <- gen $ vvv * Z1
    return (mkPt X3 Y3 Z3)

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
