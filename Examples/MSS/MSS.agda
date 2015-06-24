module Examples.MSS.MSS where

open import Data.List
open import Data.Integer

open import Examples.MSS.IntRNG
import Examples.MSS.Derivation 

module MSSDer = Examples.MSS.Derivation (+ 0)
                  _+_ _↑_ ↑assoc +distr↑
open MSSDer

{-

Try 
    mss (pos 3 :: neg 1 :: pos 1 :: pos 4 :: neg 3 :: [])

-}




