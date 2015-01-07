{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.PipeReasoning where

open import Level
open import Data.Product using (_,_)

open import Sets         using (ℙ; _≡_; subst)
open import Relations    using (_←_; _·_; Λ)

{-- a simple example:

test : {A : Set} -> (a : A) -> (idR ○ (idR ○ idR) ○ idR) a a
test a =
  a
  ≫[ idR ]→ a ⟨ ≡-refl ⟩
  →[ idR ○ idR ]→ a ⟨
      a
      ≫[ idR ]→ a ⟨ ≡-refl ⟩
      →[ idR ]→ a ⟨ ≡-refl ⟩
      →∎ ⟩
  →[ idR ]→ a ⟨ ≡-refl ⟩
  →∎

--}

infix  3 _≫[_]→_⟨_⟩   -- _≫₁[_]→_⟨_⟩
infixl 2 _→[_]→_⟨_⟩   _↪_⟨_⟩
infix  1 _→∎

private

  data PipeInfo {i : Level} {B : Set i} (S : ℙ B) (b : B) : Set i where
    pipe : S b → PipeInfo S b

_≫[_]→_⟨_⟩ : {i : Level} {A : Set i} {B : Set} →
  (a : A) (R : B ← A) (b : B) (bRa : R b a) → PipeInfo (Λ R a) b
a ≫[ R ]→ b ⟨ bRa ⟩ = pipe bRa

{-
_≫₁[_]→_⟨_⟩ : {A : Set1} {B : Set} →
  (a : A) (R : B ← A) (b : B) (bRa : R b a) → PipeInfo (Λ R a) b
a ≫₁[ R ]→ b ⟨ bRa ⟩ = pipe bRa -}

_→[_]→_⟨_⟩ : {B C : Set} {S : ℙ B} {b : B} →
  PipeInfo S b → (R : C ← B) (c : C) (cRb : R c b) → PipeInfo (R · S) c
_→[_]→_⟨_⟩ {_} {_} {S} {b} (pipe b∈S) R c cRb = pipe (b , b∈S , cRb)

_↪_⟨_⟩ : {B : Set} {S : ℙ B} {b : B} →
  PipeInfo S b → (b' : B) → b ≡ b' → PipeInfo S b'
_↪_⟨_⟩ {_} {S} {b} (pipe b∈S) b' b≡b' = pipe (subst S b≡b' b∈S)

_→∎ : {B : Set} {S : ℙ B} {b : B} → PipeInfo S b → S b
_→∎ (pipe b∈S) = b∈S
