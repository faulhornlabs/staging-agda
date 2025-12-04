module Algebra.Limbs where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe using ( trustMe )

open import Data.Bool     using ( Bool )
open import Data.Nat      using ( ℕ ; _+_ ; _*_ ; _/_ ; _%_ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Fin      using ( Fin ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec      using ( Vec ; [] ; _∷_ ; _∷ʳ_ ; allFin )
open import Data.List     using ( List ; [] ; _∷_ ; _++_ )
open import Data.Word64   using ( Word64 ; _<_ )
open import Data.String   using ( String )
open import Data.Product

open import Meta.Object

open import Algebra.BigInt using ( BigInt ; BigInt' )
open import Algebra.Misc   using ( twoTo64 )

--------------------------------------------------------------------------------

limbSize : ℕ
limbSize = 64

--------------------------------------------------------------------------------
-- Figure out the required minimum number of limbs

{-# TERMINATING #-}
natToLimbs : ℕ -> Σ[ nlimbs ∈ ℕ ] (Vec Word64 nlimbs)
natToLimbs nzero = (0 , [])
natToLimbs n     = let w₀ = Data.Word64.fromℕ (n % twoTo64)
                       (n₁ , ws) = natToLimbs (n / twoTo64)
                   in  (nsuc n₁ , w₀ ∷ ws)  

natFromLimbs : {nlimbs : ℕ} -> Vec Word64 nlimbs -> ℕ
natFromLimbs [] = 0
natFromLimbs (w ∷ ws) = Data.Word64.toℕ w + twoTo64 * (natFromLimbs ws)

{-
ex0 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
ex1 = natToLimbs ex0
ex2 = natFromLimbs (proj₂ ex1)
-}

--------------------------------------------------------------------------------

natToBigInt'Lit : ℕ -> Σ[ nlimbs ∈ ℕ ] (Literal (BigInt' nlimbs))
natToBigInt'Lit n with natToLimbs n
natToBigInt'Lit _ | (nlimbs , limbs) =
  let big' = Meta.Object.litVec (Data.Vec.map Meta.Object.Literal.U64L limbs)
  in  (nlimbs , big')

natToBigIntLit : ℕ -> Σ[ nlimbs ∈ ℕ ] (Literal (BigInt nlimbs))
natToBigIntLit n with natToBigInt'Lit n
natToBigIntLit _ | (nlimbs , big') = (nlimbs , Meta.Object.Literal.WrapL big')

--------------------------------------------------------------------------------
-- Fit into given number of limbs

limbsFromℕ : {nlimbs : ℕ} -> ℕ -> Vec Word64 nlimbs
limbsFromℕ {nlimbs} = go nlimbs where

  {-# NON_COVERING #-}
  go : (k : ℕ) -> ℕ -> Vec Word64 k
  go nzero     nzero = []
  go (nsuc k₁) n    =
    let w₀ = Data.Word64.fromℕ (n % twoTo64)
        ws = go k₁ (n / twoTo64)
    in  (w₀ ∷ ws)   

bigInt'LitFromℕ : {nlimbs : ℕ} -> ℕ -> Literal (BigInt' nlimbs)
bigInt'LitFromℕ {nlimbs} n with limbsFromℕ {nlimbs} n
bigInt'LitFromℕ _ | limbs = Meta.Object.litVec (Data.Vec.map Meta.Object.Literal.U64L limbs)

bigIntLitFromℕ : {nlimbs : ℕ} -> ℕ -> Literal (BigInt nlimbs)
bigIntLitFromℕ n = Meta.Object.Literal.WrapL (bigInt'LitFromℕ n)

bigIntFromℕ : {nlimbs : ℕ} -> ℕ -> Tm (BigInt nlimbs)
bigIntFromℕ {nlimbs = nlimbs} n = Lit (bigIntLitFromℕ {nlimbs = nlimbs} n)

--------------------------------------------------------------------------------

{-
ex4 : Vec Word64 3
ex4 = limbsFromℕ 22763282186957586750933     -- 1234 * 2^64 + 56789

ex5 : Val (BigInt 3)
ex5 = bigIntFromℕ 22763282186957586750933
-}
