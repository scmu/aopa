{-# OPTIONS --type-in-type #-}
module Relations where

open import Data.Product  using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum      using (inj₁; inj₂)
open import Data.Function using (_∘_; id)

open import Sets          using (_⊆_; ⊆-refl; ⊆-trans;
                                 ℙ; singleton; _∪_; _∩_;
                                 _≡_; ≡-refl; ≡-subst; ≡-sym; ≡-cong)

_←_   : Set  -> Set  -> Set1
B  ←  A  =  A -> B -> Set

-- union and intersection

_⊔_ : {A B : Set} -> (B ← A) -> (B ← A) -> (B ← A)
(r ⊔ s) a = r a ∪ s a

_⊓_ : {A B : Set} -> (B ← A) -> (B ← A) -> (B ← A)
(r ⊓ s) a = r a ∩ s a

-- Relational Inclusion

infixr 6 _⊑_ _⊒_

_⊑_ : {A B : Set} -> (B ← A) -> (B ← A) -> Set
R ⊑ S = forall a -> R a ⊆ S a

⊑-refl : {A B : Set} {R : B ← A} -> R ⊑ R
⊑-refl _ = ⊆-refl

⊑-trans : {A B : Set} {R S T : B ← A} -> R ⊑ S -> S ⊑ T -> R ⊑ T
⊑-trans R⊑S S⊑T a = ⊆-trans (R⊑S a) (S⊑T a) 

⊑-⊓ : {A B : Set} -> (R S T : B ← A) -> R ⊑ S ⊓ T -> (R ⊑ S) × (R ⊑ T)
⊑-⊓ R S T R⊑S⊓T = ((\a b bRa -> proj₁ (R⊑S⊓T a b bRa)) ,
                   (\a b bRa -> proj₂ (R⊑S⊓T a b bRa)))

-- ⊓-universal :  R ⊑ S ⊓ T  ⇔  R ⊑ S  ×  R ⊑ T

⊓-universal-⇒ : {A B : Set} {R S T : B ← A} -> R ⊑ S ⊓ T -> R ⊑ S × R ⊑ T
⊓-universal-⇒ R⊑S⊓T = (\a b bRa -> proj₁ (R⊑S⊓T a b bRa)) , 
                      (\a b bRa -> proj₂ (R⊑S⊓T a b bRa)) 

⊓-universal-⇐ : {A B : Set} {R S T : B ← A} -> R ⊑ S × R ⊑ T -> R ⊑ S ⊓ T
⊓-universal-⇐ (R⊑S , R⊑T) a b bRa = (R⊑S a b bRa , R⊑T a b bRa)


_⊒_ : {A B : Set} -> (B ← A) -> (B ← A) -> Set
R ⊒ S = S ⊑ R

⊒-refl : {A B : Set} {R : B ← A} -> R ⊒ R
⊒-refl = ⊑-refl

⊒-trans : {A B : Set} {R S T : B ← A} -> R ⊒ S -> S ⊒ T -> R ⊒ T
⊒-trans R⊒S S⊒T = ⊑-trans S⊒T R⊒S

infix 4 _≑_

_≑_ : {A B : Set} -> (B ← A) -> (B ← A) -> Set
R ≑ S = (R ⊑ S × S ⊑ R)

-- converse and composition

_˘ : {A B : Set} -> B ← A -> A ← B
(r ˘) b a = r a b

infixr 8 _·_ 
infixr 9 _○_

_·_ : {A B : Set} -> (B ← A) -> ℙ A -> ℙ B
(R · s)  b = ∃ (\a -> (s a × R a b))

_○_ : {A B C : Set} -> C ← B -> B ← A -> C ← A
(R ○ S) a = R · (S a)

-- Another variation of the standard function composition.
-- Currently it's used only for cases where B is a set.
-- For example, when R is ∈, T/∋, min, etc.
 
○-assocl : {A B C D : Set} ->
       {R : D ← C} {S : C ← B} {T : B ← A} ->
            R ○ (S ○ T) ⊑ (R ○ S) ○ T
○-assocl a d (c , ((b , (bTa , bSc)) , cRd)) = 
             (b , (bTa , (c , (bSc  , cRd))))

○-assocr : {A B C D : Set} ->
      {R : D ← C} {S : C ← B} {T : B ← A} ->
           (R ○ S) ○ T ⊑ R ○ (S ○ T)
○-assocr a d (b , (aTb , (c , (bSc  , cRd)))) =
             (c , ((b , (aTb , bSc)) , cRd))

○-monotonic-r : {A B C : Set} {T : C ← B} {R S : B ← A} ->
   R ⊑ S -> T ○ R ⊑ T ○ S
○-monotonic-r R⊑S a c (b , (bRa , cTb)) = 
                      (b , (R⊑S a b bRa , cTb))  

○-monotonic-l : {A B C : Set} {T : B ← A} {R S : C ← B} ->
    R ⊑ S -> R ○ T ⊑ S ○ T
○-monotonic-l R⊑S a c (b , (bTa , cRb)) =
                      (b , (bTa , R⊑S b c cRb))  

-- Primitive Relations

fun : {A B : Set} -> (A -> B) -> (B ← A)
fun f a = singleton (f a)
-- fun f a b =  f a ≡ b

fun-comp : {A B C : Set} {f : B -> C} {g : A -> B} ->
            fun (f ∘ g)  ⊑  fun f ○ fun g
fun-comp {g = g} a c fga≡c = (g a , ≡-refl , fga≡c)

idR : {A : Set} -> A ← A
idR = fun id

id-idempotent-⊒ : {A : Set} -> idR ○ idR ⊒ idR {A} 
id-idempotent-⊒ a .a ≡-refl = (a , ≡-refl , ≡-refl) 

id-idempotent-⊑ : {A : Set} -> idR ○ idR ⊑ idR {A}
id-idempotent-⊑ a .a (.a , ≡-refl , ≡-refl) = ≡-refl 

id-intro-r : {A B : Set} {R : B ← A} -> R ⊒ R ○ idR
id-intro-r a b (.a , ≡-refl , bRa) = bRa 

id-intro-l : {A B : Set} {R : B ← A} -> R ⊒ idR ○ R
id-intro-l a b (.b , bRa , ≡-refl) = bRa

id-elim-r : {A B : Set} {R : B ← A} -> R ○ idR ⊒ R 
id-elim-r a b bRa = (a , ≡-refl , bRa) 

id-elim-l : {A B : Set} {R : B ← A} -> idR ○ R ⊒ R 
id-elim-l a b bRa = (b , bRa , ≡-refl) 

-- Power Transpose

Λ :  {A : Set}  {B : Set} -> (B ←  A) -> A -> ℙ B
Λ  R = R

∈ : {A : Set} -> A ← ℙ A 
∈  R = R

ℰ : {A B : Set} -> (B ← A) -> ℙ A -> ℙ B
ℰ R = Λ (R ○ ∈)

∋ : {A : Set} -> ℙ A ← A
∋ a s = s a 

-- Products

infixr 2 _⨉_

_⨉_ : {A B C D : Set} -> 
      (B ← A) -> (D ← C) -> ((B × D) ← (A × C)) 
(R ⨉ S) (a , c) (b , d) = (R a b × S c d)

-- coreflexives built from sets

_¿ : {A : Set} -> ℙ A -> (A ← A)
(p ¿) a b = (a ≡ b) × p a

set-corefl⊑idR : {A : Set} -> (s : ℙ A) -> s ¿ ⊑ idR
set-corefl⊑idR s a b (a≡b , bRa) = a≡b
