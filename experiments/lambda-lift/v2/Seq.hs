
module Seq 
  ( Seq , emptySeq
  , seqFromList ,  seqToList
  , (<|) , (|>) 
  , Semigroup(..) , Monoid(..)
  , seqIndex
  , seqLength
  , seqIsEmpty
  , seqSingleton
  , seqJoin
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

seqIsEmpty :: Seq a -> Bool
seqIsEmpty = Seq.null

seqFromList :: [a] -> Seq a
seqFromList = Seq.fromList

seqToList :: Seq a -> [a]
seqToList = F.toList

seqJoin :: Seq (Seq a) -> Seq a
seqJoin = mconcat . seqToList

seqSingleton :: a -> Seq a
seqSingleton = Seq.singleton

-------------------------------------------------------------------------------
