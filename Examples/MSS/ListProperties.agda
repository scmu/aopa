module Examples.MSS.ListProperties where

open import Sets
  using (_≡_; refl; sym; cong)
open import Data.List 
  using (List; []; _∷_; foldr; _++_; map; concat)
open import Function using (_∘_)
open import Relations.Function using (_≐_; ≐-refl; ≐-sym)
open import AlgebraicReasoning.Equality
  using (≡-begin_; _≡⟨_⟩_; _≡∎)
open import AlgebraicReasoning.ExtensionalEquality
  using (≐-begin_; _≐⟨_⟩_; _≐∎)

foldr-universal : {A B : Set} (h : List A → B) → ∀ f e →
  (h [] ≡ e) → (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) →
    h ≐ foldr f e 
foldr-universal h f e base step [] = base
foldr-universal h f e base step (x ∷ xs) = 
  ≡-begin 
      h (x ∷ xs)
  ≡⟨ step x xs ⟩ 
      f x (h xs)
  ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩ 
      f x (foldr f e xs)
  ≡⟨ refl ⟩ 
      foldr f e (x ∷ xs)
  ≡∎

foldr-fusion : {A B C : Set} (h : B → C) {f : A → B → B} 
   {g : A → C → C} → {e : B} → 
   (∀ a → h ∘ f a ≐ g a ∘ h) →
       h ∘ foldr f e ≐ foldr g (h e)
foldr-fusion h {f} {g} {e} fuse = 
  foldr-universal (h ∘ foldr f e) g (h e) refl (λ x xs → fuse x (foldr f e xs))

foldr-fusion0 : {A B C : Set} → (h : B → C) → {f : A → B → B} → 
   {g : A → C → C} → {z : B} → 
   (push : ∀ a → h ∘ f a ≐ g a ∘ h) →
       h ∘ foldr f z ≐ foldr g (h z)
foldr-fusion0 h {f} {g} {z} _    []       = refl
foldr-fusion0 h {f} {g} {z} push (a ∷ as) =
  ≡-begin 
    h (foldr f z (a ∷ as))
  ≡⟨ refl ⟩ 
    h (f a (foldr f z as))
  ≡⟨ push a (foldr f z as)  ⟩ 
    g a (h (foldr f z as))
  ≡⟨ cong (g a) (foldr-fusion0 h push as) ⟩ 
    g a (foldr g (h z) as)
  ≡⟨ refl ⟩ 
    foldr g (h z) (a ∷ as)
  ≡∎

-- variant with named induction hypothesis 
-- inside = cong
-- byDef  = refl

foldr-fusion1 : {A B C : Set} → (h : B → C) → {f : A → B → B} → 
   {g : A → C → C} → {z : B} → 
   (push : ∀ a → h ∘ f a ≐ g a ∘ h) →
       h ∘ foldr f z ≐ foldr g (h z)
foldr-fusion1 h {f} {g} {z} _    []      = refl
foldr-fusion1 h {f} {g} {z} push (a ∷ as) = 
  let ih = foldr-fusion1 h push as in
  ≡-begin 
    h (foldr f z (a ∷ as))
  ≡⟨ refl ⟩ 
    h (f a (foldr f z as))
  ≡⟨ push a (foldr f z as)  ⟩ 
    g a (h (foldr f z as))
  ≡⟨ cong (g a) ih ⟩ 
    g a (foldr g (h z) as)
  ≡⟨ refl ⟩ 
    foldr g (h z) (a ∷ as)
  ≡∎

idIsFold : {A : Set} → (as : List A) →
              (as ≡ foldr _∷_ [] as)
idIsFold [] = refl
idIsFold (a ∷ as) = 
     ≡-begin
         a ∷ as 
     ≡⟨ cong (_∷_ a) (idIsFold as) ⟩ 
         a ∷ foldr _∷_ [] as
     ≡⟨ refl ⟩ 
         foldr _∷_ [] (a ∷ as)
     ≡∎

++IsFold : {A : Set} → (as : List A) → {y : List A} → 
             as ++ y ≡ (foldr _∷_ y as)
++IsFold as {y} = 
     ≡-begin
          as ++ y
     ≡⟨ cong (λ as → as ++ y) (idIsFold as) ⟩ 
          (foldr _∷_ [] as) ++ y
     ≡⟨ foldr-fusion (λ as → as ++ y) (λ _ _ → refl) as ⟩
          foldr _∷_ ([] ++ y) as
     ≡⟨ refl ⟩ 
          foldr _∷_ y as 
     ≡∎

mapIsFold : {A B : Set} → {f : A → B} →
              map f ≐ foldr (λ a y → f a ∷ y) []
mapIsFold {A} {B} {f} =
     ≐-begin
       map f
     ≐⟨ (λ as → cong (map f) (idIsFold as)) ⟩ 
       map f ∘ foldr _∷_ []
     ≐⟨ foldr-fusion (map f) (λ _ _ → refl) ⟩ 
       foldr (λ a y → f a ∷ y) []
     ≐∎

map-cat : {A B : Set} → {f : A → B} → (as : List A) → {y : List A} →
      map f (as ++ y) ≡ (map f as ++ map f y)
map-cat {A} {B} {f} as {y} = 
     ≡-begin
       map f (as ++ y)
     ≡⟨ cong (map f) (++IsFold as) ⟩
       map f (foldr _∷_ y as)   
     ≡⟨ foldr-fusion (map f) (λ _ _ → refl) as ⟩
       foldr (λ a z → f a ∷ z) (map f y) as
     ≡⟨ sym (foldr-fusion (λ z → z ++ map f y) (λ _ _ → refl) as) ⟩
       foldr (λ a z → f a ∷ z) [] as ++ (map f y)
     ≡⟨ cong (λ z → z ++ map f y) (sym (mapIsFold as)) ⟩
       map f as ++ map f y
     ≡∎

concat-map : {A B : Set} → {f : A → B} → 
          concat ∘ map (map f) ≐ map f ∘ concat
concat-map {_} {_} {f} = 
     ≐-begin
       concat ∘ map (map f)
     ≐⟨ (λ xs → cong concat (mapIsFold xs)) ⟩ 
       concat ∘ foldr (λ as ys → map f as ∷ ys) []
     ≐⟨ foldr-fusion concat (λ _ _ → refl) ⟩ 
       foldr (λ as xs → map f as ++ xs) []
     ≐⟨ (λ xs → sym (foldr-fusion (map f) (λ z w → map-cat z {w}) xs)) ⟩ 
       map f ∘ concat
     ≐∎

map-compose : {A B C : Set} → {g : B → C} → {f : A → B} → 
                 map (g ∘ f)  ≐ map g ∘ map f
map-compose {A} {B} {C} {g} {f} = 
     ≐-begin
       map (g ∘ f)
     ≐⟨ (λ xs → cong (map (g ∘ f)) (idIsFold xs)) ⟩ 
       map (g ∘ f) ∘ foldr _∷_ []
     ≐⟨ foldr-fusion (map (g ∘ f)) (λ _ → ≐-refl) ⟩ 
       foldr (λ a y → g (f a) ∷ y) []
     ≐⟨ (λ xs → ≐-sym (foldr-fusion (map g) (λ _ → ≐-refl)) xs) ⟩ 
       map g ∘ foldr (λ a y → f a ∷ y) []
     ≐⟨ (λ xs → cong (map g) (sym (mapIsFold xs)))  ⟩ 
       map g ∘ map f
     ≐∎

foldr-eq : {A B : Set} → {f g : A → B → B} → {e : B} →
             (∀ a → ∀ b → f a b ≡ g a b) →
               foldr f e ≐ foldr g e
foldr-eq {A} {B} {f} {g} {e} f≡g =
     ≐-begin
       foldr f e
     ≐⟨ (λ xs → cong (foldr f e) (idIsFold xs)) ⟩ 
       foldr f e ∘ foldr _∷_ []
     ≐⟨ foldr-fusion (foldr f e) (λ a as → f≡g a (foldr f e as)) ⟩ 
       foldr g e
     ≐∎

map-eq : {A B : Set} → {f g : A → B} →
            f ≐ g → map f ≐ map g
map-eq {A} {B} {f} {g} f≡g = 
     ≐-begin
       map f
     ≐⟨ mapIsFold ⟩ 
       foldr (λ a y → f a ∷ y) []
     ≐⟨ foldr-eq (λ a y → cong (λ b → b ∷ y) (f≡g a)) ⟩
       foldr (λ a y → g a ∷ y) []
     ≐⟨ ≐-sym mapIsFold ⟩ 
       map g
     ≐∎
