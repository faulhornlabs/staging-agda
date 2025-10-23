
module Algebra.API.Group where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.String

open import Meta.Object

--------------------------------------------------------------------------------

record GroupAPI : Set where
  field
    G     : Ty
    unit  : Tm G
    -- metadata
    name   : String
--    size   : ℕ        -- we don't really know the size of an elliptic curve, a priori
    -- queries
    isUnit   : Tm G -> Tm Bit
    isEqual  : Tm G -> Tm G -> Tm Bit
    -- arithmetic
    gneg   : Tm G -> Tm G
    gdbl   : Tm G -> Tm G
    gadd   : Tm G -> Tm G -> Tm G
    gsub   : Tm G -> Tm G -> Tm G
--    -- scaling
--    Scalar : Ty
--    gscl   : Tm Scalar -> Tm G -> Tm G

--------------------------------------------------------------------------------
