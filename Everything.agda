module Everything where


-- Basic definitions.

import Sets

import Relations
import Relations.Function
import Relations.PowerTrans
import Relations.Product
import Relations.Coreflexive
import Relations.Factor
import Relations.Converse
import Relations.CompChain
import Relations.Minimum
import Relations.WellFound

-- Algebraic reasoning

import AlgebraicReasoning.MonoPreorderReasoning
import AlgebraicReasoning.PolyPreorderReasoning
import AlgebraicReasoning.PolyPreorderReasoning1
import AlgebraicReasoning.PipeReasoning
import AlgebraicReasoning.Equality
import AlgebraicReasoning.ExtensionalEquality
import AlgebraicReasoning.Sets
import AlgebraicReasoning.Relations
import AlgebraicReasoning.Implications

-- Datatypes and their folds

import Data.List.Fold
import Data.List.Unfold
import Data.List.ConvFunThm
import Data.List.GreedyThm
import Data.List.HyloThm
import Data.List.Utilities
import Data.Tree
{- To be updated 
import Data.Tree.Fold
import Data.Tree.Unfold
-}

-- Examples

-- import Examples.MSS.IntRNG   -- not finished yet!
import Examples.MSS.List+
import Examples.MSS.ListProperties
import Examples.MSS.Derivation
-- import Examples.MSS.MSS      -- unfinished because IntRNG is not.

{- To be updated
import Examples.Optimisation.ActivitySelection
import Examples.Sorting.Bags
import Examples.Sorting.Spec
import Examples.Sorting.iSort
import Examples.Sorting.qSort
-}