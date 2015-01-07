module Data.SortedList 
       {A : Set}
       (_≤_ : A -> A -> Set)
       (≤-refl : ∀ {x} -> x ≤ x)
       (≤-trans : ∀ {x y z} -> x ≤ y -> y ≤ z -> x ≤ z)
     where

open import Data.Unit
open import Data.Product
open import Data.Function using (_∘_)

open import Sets
open import Relations hiding (_,₁_; _×₁_; _⨉₁_)
open import Relations.Minimum

-- 'externally bounded' sorted list.

data SList : A → Set where
   []ˢ    : {z : A} → SList z
   _⋮_∷ˢ_ : {z : A} →
               (x : A) → (z ≤ x) → (xs : SList x) → SList z


-- fold for sorted list. Is this the right definition?

foldˢr : {B : A → Set} {z : A} →
    (∀ {z} → Σ A (λ x → z ≤ x × B x) → B z) → 
       (∀ {z} → B z) → SList z → B z
foldˢr f e []ˢ = e
foldˢr f e (x ⋮ z≤x ∷ˢ xs) = f (x , z≤x , foldˢr f e xs)

uncurry-consˢ : {z : A} →
    Σ A (λ x → z ≤ x × SList x) → SList z
uncurry-consˢ (z , z≤x , xs) = z ⋮ z≤x ∷ˢ xs

-- replacement of "outr."

weaken : ∀ {z} → Σ A (λ x → z ≤ x × SList x) → SList z
weaken (x , z≤x , []ˢ) = []ˢ
weaken (x , z≤x , y ⋮ x≤y ∷ˢ xs) = y ⋮ ≤-trans z≤x x≤y ∷ˢ xs

infixr 4 _,₁_
infixr 2 _×₁_ 

-- Generalising ×₁ to dependent pairs. 

data Σ₁ (A : Set) (B : A → Set1) : Set1 where
  _,₁_ : (x : A) → B x → Σ₁ A B

-- _×₁_ is a special case. Hope we won't break
-- too much code if we put this definition into Relations.agda.

_×₁_ : (A : Set) (B : Set1) → Set1
A ×₁ B = Σ₁ A (λ _ → B)

_⨉₁_ : {A B : Set} {C : Set1} {D : Set} → 
       (B ← A) → (D ←₁ C) → ((B × D) ←₁ (A ×₁ C)) 
(R ⨉₁ S) (a ,₁ c) (b , d) = (R a b × S c d)

-- Functorial lifting for Σ₁. However, this is not very useful.

∑₁ : {A B : Set} {C : A → Set1} {D : B → Set} → 
       (B ← A) → (∀ {a b} → (D b ←₁ C a)) → 
          (Σ B D ←₁ Σ₁ A C) 
∑₁ R S (a ,₁ c) (b , d) = (R a b × S c d)

-- foldˢr₁ is used to define relational fold.

foldˢr₁ : {B : A → Set1} {z : A} →
    (∀ {z} → Σ₁ A (λ x → (z ≤ x ×₁ B x)) → B z) → 
        (∀ {z} → B z) → SList z → B z
foldˢr₁ f e []ˢ = e
foldˢr₁ f e (x ⋮ z≤x ∷ˢ xs) = f (x ,₁ z≤x ,₁ foldˢr₁ f e xs)

_○id×id⨉∈ : {B : A → Set} {z : A} →
              (B z ← Σ A (λ x → z ≤ x × B x)) →
                 (B z ←₁ Σ₁ A (λ x → z ≤ x ×₁ ℙ (B x)))
_○id×id⨉∈ {B} R (x ,₁ z≤x ,₁ Pbx) bz = 
           Σ (B x) (λ bx → Pbx bx × R (x , z≤x , bx) bz) 

foldˢR : {B : A → Set} {z : A} → 
       (∀ {z} → (B z ← Σ A (λ x → z ≤ x × B x))) → 
         (∀ {z} → ℙ (B z)) → 
            (B z ← SList z)
foldˢR {B}{z} R S = ∈ ₁∘ foldˢr₁ (Λ₁ (R ○id×id⨉∈)) S

nilˢ : ∀ {z} → ℙ (SList z)
nilˢ = singleton []ˢ

consˢ : ∀ {z} → (SList z ← Σ A (λ x → z ≤ x × SList x))
consˢ = fun uncurry-consˢ

subseq : ∀ {z} → (SList z ← SList z)
subseq = foldˢR (consˢ ⊔ fun weaken) nilˢ

-- Greedy Theorem and monotonicity.

-- R ○ (id × id × S)

_○id×id⨉_ : {B : A → Set} {z : A} →
              (B z ← Σ A (λ x → z ≤ x × B x)) →
                (∀ {x} → (B x ← B x)) → 
                 (B z ← Σ A (λ x → z ≤ x × B x))
_○id×id⨉_ {B} R S (x , z≤x , bx) bz = 
           Σ (B x) (λ bx' → S bx bx' × R (x , z≤x , bx') bz) 

postulate
  greedy-thm : {B : A → Set} {z : A} → 
      (S : ∀ {z} → (B z ← Σ A (λ x → z ≤ x × B x)))
       (s : ∀ {z} → ℙ (B z)) → 
        (R : ∀ {x} → (B x ← B x)) →
         (∀ {x} → R ○ R ⊑ R {x}) → 
           (S ○id×id⨉ (R ˘) ⊑ R ˘ ○ S {z}) →
             foldˢR {B}{z} (min R ₁∘ Λ S) (min R s) ⊑ min R ₁∘ Λ (foldˢR S s)



{--
How to define this?

∑₁id·id⨉₁∈ : ∀ {z} →
    Σ A (λ x → z ≤ x × B x) ←₁ Σ₁ A (λ x → z ≤ x ×₁ ℙ (B x)) 
∑₁id·id⨉₁∈ {z} (x ,₁ z≤x ,₁ PBx) (x' , z≤x' , Bx') = ...

∑₁id : {A : Set} {C : A → Set1} {D : A → Set} →
        (∀ {a} → (D a ←₁ C a)) → 
          (Σ A D ←₁ Σ₁ A C) 
∑₁id S (a ,₁ c) (a' , d) = ...


--}

{--
(idR ⨉₁ ∈)

_⨉₁_ : {A B : Set} {C : Set1} {D : Set} → 
       (B ← A) → (D ←₁ C) → ((B × D) ←₁ (A ×₁ C)) 
(R ⨉₁ S) (a ,₁ c) (b , d) = (R a b × S c d)
--}

