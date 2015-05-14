module Examples.GC.CoinChange where

open import Sets
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary

open import Relations
open import Relations.Shrink
open import Data.Generic
open import Examples.GC.Relations
open import Examples.GC.List
open import Examples.GC.Nat
open import AlgebraicReasoning.Implications


Coin : ∀ {i} → Set i
Coin = {!!}

val : ∀ {i j} → Coin {i} → Nat {j}
val = {!!}

_≤c_ : ∀ {i j} → Coin {i} ← Coin {j}
_≤c_ = fun val ˘ ○ _≤_ ○ fun val

sumc : Nat ← List Coin
sumc = foldR ListF [ zero , plus ○ bimapR (arg₁ ⊗ arg₂) (fun val) idR ]

{-
  sumc xs = n ≡ xs ⊵ coin-change n
  coin-change ⊑ (sumc ˘) ↾ (_⊴_)
  coin-change ⊑ ⦇[ zero, plus ∘ (val × id) ]⦈ ˘ ↾ (_⊴_)

  coin-change = ⦇([ zero , plus ∘ (val × id) ] ˘ ↾ Q) ˘⦈ ˘
    where Q = (id + _≤c_ × id)
-}

coin-change-der : foldR ListF ((([ zero , (plus ○ bimapR (arg₁ ⊗ arg₂) (fun val) idR) ] ˘) ↾ {!!}) ˘) ˘
                   ⊑ (sumc ˘) ↾ (_⊴_)
coin-change-der = {!!}
