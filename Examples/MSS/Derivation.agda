import Sets 
open Sets using (_≡_)
module Examples.MSS.Derivation 
  {Val : Set} 
  (ø : Val) 
  (_+_ : Val → Val → Val)
  (_↑_ : Val → Val → Val) 
  (↑assoc :  ∀ a b c → ((a ↑ b) ↑ c)  ≡ (a ↑ (b ↑ c)))
  (+distr↑ : ∀ a b c → ((a + (b ↑ c)) ≡ ((a + b) ↑ (a + c)))) where

open import Function using (id; _∘_)
open import Data.Product  using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.List     using (List; _∷_; []; foldr)
                   -- hiding (sum; tails; inits; scanr)

open Sets
  using (refl; sym; cong)
open import Relations.Function
open import AlgebraicReasoning.Equality 
  using (≡-begin_; _≡⟨_⟩_; _≡∎)
open import AlgebraicReasoning.ExtensionalEquality 
  using (≐-begin_; _≐⟨_⟩_; _≐∎)

open import Examples.MSS.ListProperties using (foldr-fusion)
open import Examples.MSS.List+ 
  using (List⁺; _∷⁺_; [_]⁺;
         map⁺; foldr⁺; _++⁺_; concat⁺;
         foldr⁺-fusion'; map⁺-compose; map⁺-eq; concat⁺-map⁺)

-- Some more funcions on lists.

til : {A : Set} → A → List⁺ (List A) → List⁺ (List A)
til a [ xs ]⁺     = (a ∷ xs) ∷⁺ [ xs ]⁺
til a (xs ∷⁺ xss) = (a ∷ xs) ∷⁺ xs ∷⁺ xss

tails : {A : Set} → List A → List⁺ (List A)
tails = foldr til [ [] ]⁺

ini : {A : Set} → A → List⁺ (List A) → List⁺ (List A)
ini a xss = [] ∷⁺ map⁺ (_∷_ a) xss

inits : {A : Set} → List A → List⁺ (List A)
inits = foldr ini [ [] ]⁺

-- scan

scanr-der : {A B : Set} → (f : A → B → B) → (e : B) →
      ∃ (λ prog → map⁺ (foldr f e) ∘ tails ≐ prog)
scanr-der f e = 
     (_ , 
      (≐-begin
            map⁺ (foldr f e) ∘ tails
       ≐⟨ foldr-fusion (map⁺ (foldr f e)) (push-map-til f) ⟩ 
           foldr (sc f) ([ e ]⁺)
       ≐∎))
  where sc : {A B : Set} → (A → B → B) → A → List⁺ B → List⁺ B
        sc f a [ b ]⁺    = f a b ∷⁺ [ b ]⁺
        sc f a (b ∷⁺ bs) = f a b ∷⁺ b ∷⁺ bs

        push-map-til : {A B : Set} → (f : A → B → B) → 
          {e : B} → (a : A) → 
            map⁺ (foldr f e) ∘ til a  ≐  sc f a ∘ map⁺ (foldr f e)
        -- Not enough:         push-map-til {A} {B} f {e} a as = refl
        push-map-til f a [ as ]⁺     = refl
        push-map-til f a (as ∷⁺ ass) = refl
        -- expanded version for readability:
        {-
        push-map-til {A} {B} f {e} a [ as ]⁺ =
           ≡-begin
             map⁺ (foldr f e) (til a [ as ]⁺) 
           ≡⟨ refl ⟩ 
             map⁺ (foldr f e) ((a ∷ as) ∷⁺ [ as ]⁺)
           ≡⟨ refl ⟩   
             foldr f e (a ∷ as) ∷⁺ map⁺ (foldr f e) [ as ]⁺
           ≡⟨ refl ⟩ 
             f a (foldr f e as) ∷⁺ map⁺ (foldr f e) [ as ]⁺
           ≡⟨ refl ⟩ 
             sc f a (map⁺ (foldr f e) [ as ]⁺)
           ≡∎
        push-map-til {A} {B} f {e} a (as ∷⁺ ass) =
           ≡-begin
             map⁺ (foldr f e) (til a (as ∷⁺ ass))
           ≡⟨ refl ⟩ 
             map⁺ (foldr f e) ((a ∷ as) ∷⁺ as ∷⁺ ass)
           ≡⟨ refl ⟩ 
             foldr f e (a ∷ as) ∷⁺ foldr f e as ∷⁺ map⁺ (foldr f e) ass
           ≡⟨ refl ⟩ 
             f a (foldr f e as) ∷⁺ foldr f e as ∷⁺ map⁺ (foldr f e) ass
           ≡⟨ refl ⟩ 
             sc f a (foldr f e as ∷⁺ map⁺ (foldr f e) ass)
           ≡⟨ refl ⟩ 
             sc f a (map⁺ (foldr f e) (as ∷⁺ ass)) 
           ≡∎
        -}


scanr : {A B : Set} → (A → B → B) → B → List A → List⁺ B
scanr f e = proj₁ (scanr-der f e)


scanr-pf : {A B : Set} → {f : A → B → B} → {e : B} →
              map⁺ (foldr f e) ∘ tails ≐ scanr f e
scanr-pf {A} {B} {f} {e} = proj₂ (scanr-der f e)

-- Maximum

max : List⁺ Val → Val
max = foldr⁺ _↑_ id

sum : List Val → Val
sum = foldr _+_ ø

max-cat : (vs : List⁺ Val) → (y : List⁺ Val) → max (vs ++⁺ y) ≡ (max vs ↑ max y)
max-cat vs y =
   ≡-begin 
     max (vs ++⁺ y)
   ≡⟨ foldr⁺-fusion' max (λ _ _ → refl) vs ⟩ 
     foldr⁺ _↑_ (λ a → a ↑ max y) vs
   ≡⟨ sym (foldr⁺-fusion' (λ b → b ↑ max y) (λ a b → ↑assoc a b (max y)) vs) ⟩ 
     max vs ↑ max y
   ≡∎

max-concat⁺ : max ∘ concat⁺ ≐ max ∘ map⁺ max
max-concat⁺ =
   ≐-begin
      max ∘ concat⁺
   ≐⟨ foldr⁺-fusion' max (λ vs y → max-cat vs y) ⟩ 
      foldr⁺ (λ vs a → max vs ↑ a) max
   ≐⟨ ≐-sym (foldr⁺-fusion' max (λ _ _ → refl)) ⟩ 
      max ∘ foldr⁺ (λ vs y → max vs ∷⁺ y) ([_]⁺ ∘ max) 
   ≐⟨ ≐-refl ⟩ 
      max ∘ map⁺ max
   ≐∎


max-map+ : (a : Val) → ∀ vs → max (map⁺ (_+_ a) vs) ≡ (a + max vs)
max-map+ a vs =
   ≡-begin 
      max (map⁺ (_+_ a) vs)
   ≡⟨ refl ⟩ 
      max (foldr⁺ (λ b y → (a + b) ∷⁺ y) (λ b → [ a + b ]⁺) vs)
   ≡⟨ foldr⁺-fusion' max (λ _ _ → refl) vs ⟩ 
      foldr⁺ (λ b c → (a + b) ↑ c) (λ b → a + b) vs
   ≡⟨ sym (foldr⁺-fusion' (_+_ a) (λ b c → +distr↑ a b c) vs) ⟩ 
      a + max vs
   ≡∎

sum-∷≡+sum : {a : Val} → map⁺ sum ∘ map⁺ (_∷_ a) ≐ map⁺ (_+_ a) ∘ map⁺ sum
sum-∷≡+sum {a} = 
    ≐-begin
        map⁺ sum ∘ map⁺ (_∷_ a)
    ≐⟨ ≐-sym map⁺-compose ⟩ 
        map⁺ (sum ∘ (_∷_ a))
    ≐⟨ map⁺-eq (λ xs → refl) ⟩ 
        map⁺ ((_+_ a) ∘ sum)
    ≐⟨ map⁺-compose ⟩ 
        map⁺ (_+_ a) ∘ map⁺ sum
    ≐∎

-- Maximum segment sum

segs : {A : Set} → List A → List⁺ (List A)
segs = concat⁺ ∘ map⁺ inits ∘ tails


mss-der : Σ (List Val → Val) (λ prog → max ∘ map⁺ sum ∘ segs ≐ prog)
mss-der = 
   (max ∘ scanr _⊗_ ø , 
    (≐-begin
         max ∘ map⁺ sum ∘ segs
     ≐⟨ ≐-refl ⟩ 
         max ∘ map⁺ sum ∘ concat⁺ ∘ map⁺ inits ∘ tails
     ≐⟨ (λ xs → cong max (sym (concat⁺-map⁺ ((map⁺ inits ∘ tails) xs)))) ⟩ 
         max ∘ concat⁺ ∘ map⁺ (map⁺ sum) ∘ map⁺ inits ∘ tails                
     ≐⟨ (λ xs → max-concat⁺ ((map⁺ (map⁺ sum) ∘ map⁺ inits ∘ tails) xs)) ⟩ 
         max ∘ map⁺ max ∘ map⁺ (map⁺ sum) ∘ map⁺ inits ∘ tails
     ≐⟨ (λ xs → cong (λ xss → max (map⁺ max xss)) (sym (map⁺-compose (tails xs)))) ⟩ 
         max ∘ map⁺ max ∘ map⁺ (map⁺ sum ∘ inits) ∘ tails
     ≐⟨ (λ xs → cong max (sym (map⁺-compose (tails xs)))) ⟩ 
         max ∘ map⁺ (max ∘ map⁺ sum ∘ inits) ∘ tails
     ≐⟨ (λ xs → cong max (map⁺-eq max-sum-prefix (tails xs))) ⟩ 
         max ∘ map⁺ (foldr _⊗_ ø) ∘ tails
     ≐⟨ (λ xs → cong max (scanr-pf xs)) ⟩ 
         max ∘ scanr _⊗_ ø
     ≐∎
    ))
  where _⊕_ : Val → List⁺ Val → List⁺ Val 
        a ⊕ y = ø ∷⁺ map⁺ (_+_ a) y

        _⊗_ : Val → Val → Val
        a ⊗ b = ø ↑ (a + b)

        max-sum-prefix : max ∘ map⁺ sum ∘ inits ≐ foldr _⊗_ ø
        max-sum-prefix =
           ≐-begin
               max ∘ map⁺ sum ∘ inits
           ≐⟨ (λ vs → cong max (foldr-fusion (map⁺ sum) lemma1 vs)) ⟩ 
               max ∘ foldr _⊕_ [ ø ]⁺
           ≐⟨ foldr-fusion max lemma2 ⟩ 
               foldr _⊗_ ø
           ≐∎
         where
           lemma1 : (a : Val) → (xss : List⁺ (List Val)) → 
                           map⁺ sum (ini a xss) ≡ (a ⊕ (map⁺ sum xss))
           lemma1 a xss = 
             ≡-begin
                 map⁺ sum (ini a xss) 
             ≡⟨ refl ⟩ 
                 ø ∷⁺ map⁺ sum (map⁺ (_∷_ a) xss)
             ≡⟨ cong (_∷⁺_ ø) (sum-∷≡+sum xss) ⟩ 
                 ø ∷⁺ map⁺ (_+_ a) (map⁺ sum xss)
             ≡⟨ refl ⟩ 
                 a ⊕ (map⁺ sum xss)
             ≡∎
 
           lemma2 : (a : Val) → (vs : List⁺ Val) →
                                   max (a ⊕ vs) ≡ (a ⊗ max vs)
           lemma2 a vs = 
              ≡-begin
                  max (a ⊕ vs)
              ≡⟨ refl ⟩ 
                  max (ø ∷⁺ map⁺ (_+_ a) vs)
              ≡⟨ refl ⟩ 
                  ø ↑ max (map⁺ (_+_ a) vs)
              ≡⟨ cong (λ b → ø ↑ b) (max-map+ a vs) ⟩ 
                  ø ↑ (a + max vs) 
              ≡⟨ refl ⟩ 
                  a ⊗ max vs
              ≡∎

mss : List Val → Val
mss = proj₁ mss-der
