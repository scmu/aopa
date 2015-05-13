module Examples.GC.Nat where

open import Function
open import Data.Sum using (inj₁; inj₂)
open import Data.Product

open import Relations
open import Data.Generic
open import Examples.GC.Relations
open import Examples.GC.List

NatF : PolyF
NatF = one ⊕ arg₂

Nat : ∀ {i} → Set i
Nat = μ NatF One

zero : ∀ {i} → Nat ← One {i}
zero = fun In ○ fun inj₁

suc : ∀ {i} → Nat ← Snd {i} Nat
suc = fun In ○ fun inj₂

_≤_ : Nat ← Nat
_≤_ = foldR NatF [ zero , (zero ○ !) ⊔ suc ]
