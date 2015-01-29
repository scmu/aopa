module Data.List.Unfold where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (isInj₁)
open import Data.Product
open import Data.Nat      -- for the example
open import Data.List

open import Relation.Binary.PropositionalEquality 
                      using (inspect; [_])

open import Sets      using (_≡_; refl; subst)
open import Relations using (_←_; _○_; fun; _˘; _⊑_; _⊒_)
open import Relations.WellFound
open import Data.List.Fold

-- A membership relation for the base functor of lists.

ε-listF : {A B : Set} → (B ← (⊤ ⊎ (A × B)))
ε-listF _ (inj₁ _) = ⊥ 
ε-listF b' (inj₂ (a , b)) = b ≡ b'

-- unfoldr terminates of the co-algebra it uses is well-founded,
-- or, inductive, as defined in Chapter 6 of the AoP book.

unfoldr-acc : {A B : Set} → (f : B → ⊤ ⊎ (A × B))
             → (b : B) → Acc (ε-listF ○ fun f) b → List A
unfoldr-acc f b (acc .b h)  with f b
... | inj₁ tt       = []
... | inj₂ (a , b') = a ∷ unfoldr-acc f b' (h b' (inj₂ (a , b') , refl , refl)) 

{- The proof of foldR-unfoldr won't work if I use this definition:

unfoldr-acc : {A B : Set} → (f : B → ⊤ ⊎ (A × B))
             → (b : B) → Acc (ε-listF ○ fun f) b → List A
unfoldr-acc {A}{B} f b (acc .b h) = acc-fold (ε-listF ○ fun f) (body f) b (acc b h)
  where body : (f : B → ⊤ ⊎ (A × B)) →
                 (b : B) → (∀ b' → (ε-listF ○ fun f) b b' → List A) → List A
        body f b rec with f b
        ... | inj₁ tt       = []
        ... | inj₂ (a , b') = a ∷ rec b' (inj₂ (a , b') , ≡-refl , ≡-refl)
-}

unfoldr : {A B : Set} → (f : B → ⊤ ⊎ (A × B)) →
            well-found (ε-listF ○ fun f) → B → List A
unfoldr f wf b = unfoldr-acc f b (wf b)

inj₂˘ : {A B : Set} → (B ← (A ⊎ B))
inj₂˘ = (fun inj₂) ˘

isInj₁ : {B : Set} → ⊤ ⊎ B → Set
isInj₁ x = x ≡ inj₁ tt

_∘'_ : {A B : Set} → (B → Set) → (A → B) → A → Set 
(f ∘' g) x = f (g x)

foldR-unfoldr : {A B : Set} → (f : B → ⊤ ⊎ (A × B)) →
    (b : B) → (accb : Acc (ε-listF ○ fun f) b) →
        foldR ((inj₂˘ ○ fun f)˘) (isInj₁ ∘' f)
            b (unfoldr-acc f b accb)
foldR-unfoldr f b (acc .b h) with f b | inspect f b
foldR-unfoldr f b (acc .b h) | inj₁ tt | [ fb≡v ] = fb≡v
foldR-unfoldr f b (acc .b h) | inj₂ (a , b') | [ fb≡v ] = 
  ((a , b') , (refl , foldR-unfoldr f b' (h b' (inj₂ (a , b') , refl , refl))) ,
                inj₂ (a , b') , fb≡v , refl)

foldR-to-unfoldr : {A B : Set} → (f : B → ⊤ ⊎ (A × B)) →
   (wf : well-found (ε-listF ○ fun f)) →
     (foldR ((inj₂˘ ○ fun f)˘) (isInj₁ ∘' f)) ˘ ⊒
        fun (unfoldr f wf)
foldR-to-unfoldr f wf xs b foldrfb≡xs = 
  subst (λ xs → foldR ((inj₂˘ ○ fun f)˘) (isInj₁ ∘' f) b xs)
        foldrfb≡xs (foldR-unfoldr f b (wf b))

-- Example: down

predF : ℕ → ⊤ ⊎ (ℕ × ℕ)
predF 0 = inj₁ tt
predF (suc n) = inj₂ (n , n)

predF⊑< : (ε-listF ○ fun predF) ⊑ _<′_ 
predF⊑< n 0 (._ , refl , ())
predF⊑< n (suc m) (._ , refl , m≡n) = subst (λ i → suc i ≤′ suc m) m≡n ≤′-refl

down : ℕ → List ℕ
down = unfoldr predF (λ x → acc-⊑ predF⊑< x (ℕ<-wf x))

