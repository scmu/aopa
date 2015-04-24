module Examples.GC.TakeWhile where

open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations
open import Relations.Shrink
open import Relations.Galois
open import Relations.Coreflexive
open import Data.Generic
open import AlgebraicReasoning.Relations

-- List

ListF : PolyF
ListF = one ⊕ (arg₁ ⊗ arg₂)

List : ∀ {i} → (A : Set i) → Set i
List A = μ ListF A

[] : ∀ {i} {A : Set i} → List A
[] = In (inj₁ tt)

_∷_ : ∀ {i} {A : Set i} → A → List A → List A
x ∷ xs = In (inj₂ (fst x , snd xs))

nil : ∀ {i j} {A : Set i} → (List A ← One {j})
nil = fun (λ _ → [])

cons : ∀ {i} {A : Set i} → (List A ← ⟦ arg₁ ⊗ arg₂ ⟧ A (List A))
cons ys (fst x , snd xs) = (x ∷ xs) ≡ ys


[_,_] : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
        → (C ← A ⊣ k) → (C ← B ⊣ k) → (C ← A ⊎ B ⊣ k)
[ R , S ] c (inj₁ a) = R c a
[ R , S ] c (inj₂ b) = S c b

join-monotonic : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
                   {R T : C ← A} {S U : C ← B}
                 → R ⊑ T → S ⊑ U → [ R , S ] ⊑ [ T , U ]
join-monotonic R⊑T S⊑U c (inj₁ a) cRa = R⊑T c a cRa
join-monotonic R⊑T S⊑U c (inj₂ b) cSb = S⊑U c b cSb


! : ∀ {i} {A : Set i} → (One {i} ← A)
! = fun (λ _ → tt)

!-fusion : ∀ {i} {A B : Set i} {R : A ← B ⊣ i}
           → ! ○ R ⊑ !
!-fusion tt b (a , bRa , refl) = refl


-- prefix operator

_≼_ : {A : Set} → (List A ← List A)
_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]

_≽_ : {A : Set} → (List A ← List A)
ys ≽ xs = xs ≼ ys


mapR : {A B : Set} → (R : B ← A) → (List B ← List A)
mapR R = foldR ListF [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ]


takeWhile-der : {A : Set} → (p : ℙ A) → foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ⊑ (mapR (p ¿) ○ _≼_) ↾ _≽_
takeWhile-der = {!!}
