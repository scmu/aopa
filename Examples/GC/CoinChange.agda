module Examples.GC.CoinChange where

open import Level renaming (zero to lzero; _⊔_ to _⊔l_)
open import Sets
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_; _≤_; zero)
open import Function using (const; _∘_)
open import Relation.Binary

open import Relations
open import Relations.Shrink
open import Data.Generic

open import Examples.GC.Relations
open import Examples.GC.List

open import AlgebraicReasoning.Implications

 
data Coin : Set where
  1p : Coin
  2p : Coin
  5p : Coin
  10p : Coin

val : Coin  → ℕ
val 1p = 1
val 2p = 2
val 5p = 5
val 10p = 10

_≤c_ : Coin ← Coin
_≤c_ = fun val ˘ ○ _≤_ ○ fun val

_≥c_ : Coin ← Coin
_≥c_ = _≤c_ ˘

liftc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → ((A × B) → C) → (Fst {i} {j} A × Snd {i} {j} B → C)
liftc f (fst x , snd y) = f (x , y)

liftC : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → (C ← (A × B) ⊣ lzero) → (C ← (Fst {i} {j} A × Snd {i} {j} B))
liftC R z (fst x , snd y) = R z (x , y)

sumc : ℕ ← List Coin
sumc =  ⦇ [ fun (const zero) ,
            fun (liftc plus) ○ bimapR _ (fun val) idR ] ⦈ 
  where plus : ℕ × ℕ → ℕ
        plus (m , n) = m + n

bound : Coin ← List Coin
bound = ⦇ [ fun (const 1p) ,
            liftC ((_≥c_ ○ fun proj₁) ⊓ (_≥c_ ○ fun proj₂)) ] ⦈

sumbound : (ℕ × Coin) ← List Coin
sumbound = ⦇ [ fun (const (0 , 1p)) , liftC ⟨ plus , raise ⟩ ] ⦈
  where plus : ℕ ← (Coin × ℕ × Coin)
        plus m (c , n , b) = (c ≡ b) × (m ≡ val c + n)
        
        raise : Coin ← (Coin × ℕ × Coin)
        raise b' (c , n , b) = (b' ≥c c) × (c ≥c b)
        
{-
  sumc xs = n ≡ xs ⊵ coin-change n
  coin-change ⊑ (sumc ˘) ↾ (_⊴_)
  coin-change ⊑ ⦇[ zero, plus ∘ (val × id) ]⦈ ˘ ↾ (_⊴_)

  coin-change = ⦇([ zero , plus ∘ (val × id) ] ˘ ↾ Q) ˘⦈ ˘
    where Q = (id + _≤c_ × id)
-}

{-
coin-change-der : foldR ListF ((([ zero , (plus ○ bimapR (arg₁ ⊗ arg₂) (fun val) idR) ] ˘) ↾ {!!}) ˘) ˘
                   ⊑ (sumc ˘) ↾ (_⊴_)
coin-change-der = {!!}
-}
