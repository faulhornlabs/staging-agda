
module Seq 
  ( Seq , emptySeq
  , (<|) , (|>) 
  , Semigroup(..) , Monoid(..)
  , seqIndex
  , seqToList
  , seqLength
  )
  where

-------------------------------------------------------------------------------

import Data.Semigroup
import Data.Monoid
import Data.Sequence ( Seq , empty , (<|) , (|>) , (><) , index )
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F

-------------------------------------------------------------------------------

emptySeq :: Seq a
emptySeq = Seq.empty

seqIndex :: Seq a -> Int -> a 
seqIndex = Seq.index

seqLength :: Seq a -> Int
seqLength = Seq.length

seqToList :: Seq a -> [a]
seqToList = F.toList

-------------------------------------------------------------------------------
