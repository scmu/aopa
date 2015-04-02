module Data.List.Fold where

open import Data.Product using (Σ; _×_; _,_; uncurry)
open import Data.List    using (List; []; _∷_; foldr)

open import Sets 
     using (ℙ; singleton;
            _⊆_; ⊆-refl;
            _⊇_; ⊇-refl;
            _≡_; refl; trans; cong; subst; sym)
open import Relations
     using (_←_; fun; idR; _○_; _⨉_; _⊑_; _⊒_; id-intro-r; id-intro-l;
            id-elim-l; 
            Λ; ∈; ℰ;
            _₁∘_; _·_; _˘; 
            ○-assocl; ○-assocr; ○-monotonic-r; ○-monotonic-l;
            ⊑-refl; ⊒-refl; id-idempotent-⊑; id-idempotent-⊒)
open import Relations.Product
     using (⨉-functor-⊒; ⨉-functor-⊑; ⨉-id-⊑; ⨉-monotonic;
            Λ⨉-absorption-⊆; Λ⨉-absorption-⊇; Λ⨉-monotonic)
open import Relations.PowerTrans
     using (Λ∈-galois-1; Λ∈-galois-2; Λ∈-cancelation;
            Λ-monotonic; ℰ-functor-⊆; ℰ-functor-⊇; ℰ-monotonic')

open import Relations.CompChain

open import AlgebraicReasoning.Sets
     using (⊆-begin_; _⊆⟨_⟩_; _⊆∎;
            ⊇-begin_; _⊇⟨_⟩_; _⊇∎)
open import AlgebraicReasoning.Relations
     using (⊒-begin_; _⊒⟨_⟩_; _⊒∎;
            ⊑-begin_; _⊑⟨_⟩_; _⊑∎)
open import AlgebraicReasoning.Implications

foldr₁ : {A : Set} → {PB : Set1} → ((A × PB) → PB) → PB → List A → PB
foldr₁ f e []      = e
foldr₁ f e (a ∷ x) = f (a , foldr₁ f e x)

foldR : {A B : Set} → (B ← (A × B)) → ℙ B → (B ← List A)
-- foldR R S = foldr₁ (R ○₁ (idR ⨉₁ ∈)) S
foldR R S = ∈ ₁∘ foldr₁ (Λ (R ○ (idR ⨉ ∈))) S

-- Useful shorthands

cons : {A : Set} → List A ← (A × List A)
cons = fun (uncurry _∷_)

nil : {A : Set} → ℙ (List A)
nil = singleton []

cons-injective : {A : Set} → cons ˘ ○ cons ⊑ idR {A = A × List A}
cons-injective (x , xs) (_ , _) (_ , r1 , r2) with r1 | r2
cons-injective (x , xs) (.x , .xs) (._ , _ , _)  | refl | refl = refl

-- universal property of fold

{- The universal property of foldR is:

     S = foldR R e ⇔ (S ○ cons = R ○ (idR ⨉ S)) × (ℰ S nil = e).
  
   It says that foldR is the unique fixed point. By Knaster-Tarski, it is
   also the least prefix-point:
 
     foldR-induction-⊒ : S ⊒ foldR R e ⇐ (S ○ cons ⊒ R ○ (idR ⨉ S)) × (ℰ S nil ⊇ e)
     foldR-computation-cons-⊒ : foldR R e ○ cons ⊒ R ○ (idR ⨉ foldR R e)
     foldR-computation-nil-⊇ : ℰ (foldR R e) nil ⊇ e

   and the greatest postfix-point:

     foldR-induction-⊑ : S ⊑ foldR R e ⇐ (S ○ cons ⊑ R ○ (idR ⨉ S)) × (ℰ S nil ⊆ e)
     foldR-computation-cons-⊑ : foldR R e ○ cons ⊑ R ○ (idR ⨉ foldR R e)        
     foldR-computation-nil-⊆ : ℰ (foldR R e) nil ⊆ e
-}         

foldR-induction-⊒ : {A B : Set} →
    (S : B ← List A) → (R : B ← (A × B)) → (e : ℙ B) → 
       (S ○ cons ⊒ R ○ (idR ⨉ S)) × (ℰ S nil ⊇ e) →
         S ⊒ foldR R e 
foldR-induction-⊒ S R e (S○cons⊒Rid⨉S , ℰSnil⊇e) = 
    (⇐-begin
       foldR R e ⊑ S
     ⇐⟨ ⇐-refl ⟩
        ∈ ₁∘ foldr₁ (Λ (R ○ (idR ⨉ ∈))) e ⊑ S
     ⇐⟨ Λ∈-galois-2 ⟩
      foldr₁ (Λ (R ○ (idR ⨉ ∈))) e ⊑ Λ S
     ⇐∎) foldr⊑ΛS
  where
   foldr⊑ΛS : foldr₁ (Λ (R ○ (idR ⨉ ∈))) e ⊑ Λ S
   foldr⊑ΛS [] =
      ⊆-begin 
          foldr₁ (Λ (R ○ (idR ⨉ ∈))) e []  
      ⊆⟨ ⊆-refl ⟩
          e 
      ⊆⟨ ℰSnil⊇e ⟩
          ℰ S nil
      ⊆⟨  ℰSnil⊆ΛS[]  ⟩
          Λ S []
      ⊆∎    
    where ℰSnil⊆ΛS[] :  ℰ S nil ⊆ Λ S []
          ℰSnil⊆ΛS[] b (.[] , refl , bS[]) = bS[] 
   foldr⊑ΛS (x ∷ xs) = 
     let induction-hypothesis = foldr⊑ΛS xs
     in
        ⊆-begin 
           foldr₁ (Λ (R ○ (idR ⨉ ∈))) e (x ∷ xs)
        ⊆⟨ ⊆-refl ⟩
           Λ (R ○ (idR ⨉ ∈))
             (x , foldr₁ (Λ (R ○ (idR ⨉ ∈))) e xs)
        ⊆⟨ Λ⨉-monotonic R induction-hypothesis x ⟩
           Λ (R ○ (idR ⨉ ∈)) (x , Λ S xs)
        ⊆⟨ Λ⨉-absorption-⊆ R S x xs  ⟩
          Λ (R ○ (idR ⨉ S)) (x , xs)
        ⊆⟨ Λ-monotonic S○cons⊒Rid⨉S (x , xs) ⟩
          Λ (S ○ cons) (x , xs)
        ⊆⟨ ΛScons⊆S∷ ⟩
          Λ S (x ∷ xs)
        ⊆∎    
     where ΛScons⊆S∷ : Λ (S ○ cons) (x , xs) ⊆ Λ S (x ∷ xs)
           ΛScons⊆S∷ b (.(x ∷ xs) , refl , bSx∷xs) = bSx∷xs

foldR-induction-⊑ : {A B : Set} →
    (S : B ← List A) → (R : B ← (A × B)) → (e : ℙ B) → 
       (S ○ cons ⊑ R ○ (idR ⨉ S)) × (ℰ S nil ⊆ e) →
         S ⊑ foldR R e
foldR-induction-⊑ S R e (S○cons⊑Rid⨉S , ℰSnil⊆e) = 
    (⇐-begin
       S ⊑ foldR R e
     ⇐⟨ ⇐-refl ⟩
       S ⊑ ∈ ₁∘ foldr₁ (Λ (R ○ (idR ⨉ ∈))) e
     ⇐⟨ Λ∈-galois-1 ⟩
       Λ S ⊑ foldr₁ (Λ (R ○ (idR ⨉ ∈))) e
     ⇐∎) ΛS⊑foldr
  where 
   ΛS⊑foldr : Λ S ⊑ foldr₁ (Λ (R ○ (idR ⨉ ∈))) e
   ΛS⊑foldr [] = 
      ⊆-begin 
          Λ S []
      ⊆⟨  ΛS[]⊆ℰSnil  ⟩
          ℰ S nil
      ⊆⟨  ℰSnil⊆e  ⟩
          e
      ⊆⟨ ⊆-refl ⟩
          foldr₁ (Λ (R ○ (idR ⨉ ∈))) e []  
      ⊆∎    
     where ΛS[]⊆ℰSnil :  Λ S [] ⊆ ℰ S nil
           ΛS[]⊆ℰSnil b aS[] = ([] , refl , aS[]) 
   ΛS⊑foldr (x ∷ xs) = 
     let induction-hypothesis = ΛS⊑foldr xs
     in
        ⊆-begin 
          Λ S (x ∷ xs)
        ⊆⟨ S∷⊆ΛScons ⟩
          Λ (S ○ cons) (x , xs)
        ⊆⟨ Λ-monotonic S○cons⊑Rid⨉S (x , xs) ⟩
          Λ (R ○ (idR ⨉ S)) (x , xs)
        ⊆⟨  Λ⨉-absorption-⊇ R S x xs   ⟩
          Λ (R ○ (idR ⨉ ∈)) (x , Λ S xs)
        ⊆⟨ Λ⨉-monotonic R induction-hypothesis x ⟩
           Λ (R ○ (idR ⨉ ∈))
             (x , foldr₁ (Λ (R ○ (idR ⨉ ∈))) e xs)
        ⊆⟨ ⊆-refl ⟩
           foldr₁ (Λ (R ○ (idR ⨉ ∈))) e (x ∷ xs)
        ⊆∎  
    where S∷⊆ΛScons : Λ S (x ∷ xs) ⊆ Λ (S ○ cons) (x , xs)
          S∷⊆ΛScons b bSx∷xs = (x ∷ xs , refl , bSx∷xs)

-- Computation rules

foldR-computation-nil-⊇ : {A B : Set} {R : B ← (A × B)} {e : ℙ B} →
    ℰ (foldR R e) nil ⊇ e
foldR-computation-nil-⊇ b b∈e = ([] , refl , b∈e) 

foldR-computation-nil-⊆ : {A B : Set} {R : B ← (A × B)} {e : ℙ B} →
    ℰ (foldR R e) nil ⊆ e
foldR-computation-nil-⊆ b (.[] , refl , b∈e) = b∈e 

foldR-computation-cons-⊒ : {A B : Set} (R : B ← (A × B)) {e : ℙ B} →
    foldR R e ○ cons ⊒ R ○ (idR ⨉ foldR R e)
foldR-computation-cons-⊒ R b' (x , xs) ((_ , b) , (r , bfoldRxs) , b'Rxb) with r
foldR-computation-cons-⊒ R b' (x , xs) ((.x , b) , (_ , bfoldRxs) , b'Rxb) | refl = 
  (x ∷ xs , refl , (x , b) , (refl , bfoldRxs) , b'Rxb)

foldR-computation-cons-⊑ :
  {A B : Set} (R : B ← (A × B)) {e : ℙ B} →
  foldR R e ○ cons ⊑ R ○ (idR ⨉ foldR R e)
foldR-computation-cons-⊑ R b (x , xs) (_ , r1 , p) with r1 
foldR-computation-cons-⊑ R b (x , xs) (._ , _ , ((_ , b') , (r2 , foldR-xs-b') ,  R-x,b'-b)) | refl with r2
foldR-computation-cons-⊑ R b (x , xs) (._ , _ , ((._ , b') , (_ , foldR-xs-b') ,  R-x,b'-b)) | refl | refl  = 
   ((x , b') , (refl , foldR-xs-b') , R-x,b'-b)

-- foldr fusion!

foldR-fusion-⊒ : {A B C : Set} →
  (R : C ← B) → {S : B ← (A × B)} {T : C ← (A × C)} {u : ℙ B} {v : ℙ C} →
      (R ○ S) ⊒ (T ○ (idR ⨉ R)) → 
            ℰ R u ⊇ v → 
             (R ○ foldR S u) ⊒ foldR T v
foldR-fusion-⊒ R {S} {T} {u} {v} RS⊒TFR Ru⊇v = 
   foldR-induction-⊒ (R ○ foldR S u) T v (step-cond , base-cond) 
  where step-cond : (R ○ foldR S u) ○ cons ⊒ T ○ (idR ⨉ (R ○ foldR S u))
        step-cond = 
         ⊒-begin
             (R ○ foldR S u) ○ cons
         ⊒⟨ ○-assocl ⟩
             R ○ foldR S u ○ cons
         ⊒⟨ ○-monotonic-r (foldR-computation-cons-⊒ S)  ⟩
             R ○ S ○ (idR ⨉ foldR S u)
         ⊒⟨ ⇦-mono-l (T ● (idR ⨉ R) ‥) (R ● S ‥) RS⊒TFR  ⟩
             T ○ (idR ⨉ R) ○ (idR ⨉ foldR S u) 
         ⊒⟨ ○-monotonic-r (⨉-functor-⊒ {R = idR}{S = R}{T = idR}{U = foldR S u}) ⟩
             T ○ ((idR ○ idR) ⨉ (R ○ foldR S u))
         ⊒⟨ ○-monotonic-r (⨉-monotonic {T = (R ○ foldR S u)} id-idempotent-⊒ ⊒-refl) ⟩
             T ○ (idR ⨉ (R ○ foldR S u))
         ⊒∎ 
        base-cond : ℰ (R ○ foldR S u) nil ⊇ v
        base-cond = 
         ⊇-begin
            ℰ (R ○ foldR S u) nil
         ⊇⟨  ℰ-functor-⊆ ⟩
            ℰ R (ℰ (foldR S u) nil)
         ⊇⟨ ℰ-monotonic' foldR-computation-nil-⊇  ⟩ 
            ℰ R u
         ⊇⟨ Ru⊇v  ⟩
           v
         ⊇∎ 

foldR-fusion-⊑ : {A B C : Set} →
  (R : C ← B) → {S : B ← (A × B)} {T : C ← (A × C)} {u : ℙ B} {v : ℙ C} →
      (R ○ S) ⊑ (T ○ (idR ⨉ R)) → 
            ℰ R u ⊆ v → 
             (R ○ foldR S u) ⊑ foldR T v
foldR-fusion-⊑ R {S} {T} {u} {v} RS⊑TFR Ru⊆v = 
   foldR-induction-⊑ (R ○ foldR S u) T v (step-cond , base-cond) 
  where step-cond : (R ○ foldR S u) ○ cons ⊑ T ○ (idR ⨉ (R ○ foldR S u))
        step-cond = 
         ⊑-begin
             (R ○ foldR S u) ○ cons
         ⊑⟨ ○-assocr ⟩
             R ○ (foldR S u ○ cons)
         ⊑⟨ ○-monotonic-r (foldR-computation-cons-⊑ S )  ⟩
             R ○ S ○ (idR ⨉ foldR S u)
         ⊑⟨ ⇦-mono-l (R ● S ‥) (T ● (idR ⨉ R) ‥) RS⊑TFR  ⟩
            T ○ (idR ⨉ R) ○ (idR ⨉ foldR S u) 
         ⊑⟨ ○-monotonic-r (⨉-functor-⊑ {R = idR}{S = R}{T = idR}{U = foldR S u}) ⟩
            T ○ ((idR ○ idR) ⨉ (R ○ foldR S u))
         ⊑⟨ ○-monotonic-r (⨉-monotonic {T = (R ○ foldR S u)} id-idempotent-⊑ ⊑-refl) ⟩
            T ○ (idR ⨉ (R ○ foldR S u))
         ⊑∎ 
        base-cond : ℰ (R ○ foldR S u) nil ⊆ v
        base-cond = 
         ⊆-begin
            ℰ (R ○ foldR S u) nil
         ⊆⟨  ℰ-functor-⊇  ⟩
            ℰ R (ℰ (foldR S u) nil)
         ⊆⟨ ℰ-monotonic' foldR-computation-nil-⊆  ⟩ 
            ℰ R u
         ⊆⟨ Ru⊆v  ⟩ 
            v
         ⊆∎ 
 
-- from relational fold to functional fold

foldR-to-foldr : {A B : Set} → (f : A → B → B) → (e : B) →
                   foldR (fun (uncurry f)) (singleton e) ⊒ fun (foldr f e)
foldR-to-foldr f e b []      e≡b        =  e≡b
foldR-to-foldr f e b (a ∷ x) foldr$x≡b  =
  ((a , foldr f e x) , 
      ((refl , (foldR-to-foldr f e
                    (foldr f e x) x (cong (λ g → foldr g e x) refl))) ,
            foldr$x≡b))

-- idR as a relational fold

idR⊑foldR : {A : Set} → idR ⊑ foldR {A} cons nil
idR⊑foldR .[] [] refl = refl
idR⊑foldR .(x ∷ xs) (x ∷ xs) refl = (x , xs) , ((refl , (idR⊑foldR xs xs refl)) , refl)

idR⊒foldR : {A : Set} → idR ⊒ foldR {A} cons nil 
idR⊒foldR = foldR-induction-⊒ idR cons nil (id○cons⊒cons○Pid , ℰidnil⊇nil)
  where id○cons⊒cons○Pid : idR ○ cons ⊒ cons ○ (idR ⨉ idR)
        id○cons⊒cons○Pid = 
          ⊒-begin
             idR ○ cons
          ⊒⟨ id-elim-l ⟩
             cons
          ⊒⟨ id-intro-r  ⟩
             cons ○ idR
          ⊒⟨ ○-monotonic-r ⨉-id-⊑ ⟩
             cons ○ (idR ⨉ idR)
          ⊒∎ 
        ℰidnil⊇nil : ℰ idR nil ⊇ nil
        ℰidnil⊇nil xs []≡xs = (xs , []≡xs , refl)

{-
module Q (A : Set) where
  import Relation.Binary.EqReasoning
  open module ≡-reasoning = Relation.Binary.EqReasoning (≡-setoid (List A))
     renaming (begin_ to ≡-begin_ ; _∎ to _≡∎)

  _⟨_⟩_ : {A B C : Set} {a a' : A} {b b' : B} → 
          (a ≡ a') → (_⊕_ : A → B → C) → (b ≡ b') →
          (a ⊕ b) ≡ (a' ⊕ b')
  p ⟨ _⊕_ ⟩ q = ≡-cong₂ _⊕_ p q

  _⟨∷⟩_ : {A : Set} {a a' : A} {as as' : List A} → 
          (a ≡ a') → (as ≡ as') → (a ∷ as) ≡ (a' ∷ as')
  p ⟨∷⟩ q = p ⟨ _∷_ ⟩ q
  p ⟨∷⟩ q = ≡-cong₂ _∷_ p q -- alternative definition

  -- Just type checking some expressions from the paper
  idR⊒foldRType : Set
  idR⊒foldRType = idR ⊒ foldR {A} cons nil
  idR⊒foldRType = ∀ xs ys → foldR {A} cons nil xs ys  →  xs ≡ ys

  idR≡foldR : idR ⊒ foldR {A} cons nil
  idR≡foldR ys []       []≡ys                                       = []≡ys
  idR≡foldR ys (a ∷ xs) ((a' , y') , (a≡a' , foldRxsys) , a'∷y'≡ys) = 
      ≡-begin
           a ∷ xs
      ≡⟨ a≡a' ⟨∷⟩ idR≡foldR y' xs foldRxsys ⟩
           a' ∷ y'
      ≡⟨ a'∷y'≡ys  ⟩
           ys
      ≡∎

  {- 

  PJ: For readability I use _⟨∷⟩_ = ≡-cong₂ _∷_ as an infix operator
  combining the two proofs. The general operator _⟨_⟩_ is not as
  visually appealing as I would have wished due to extra spaces and
  underscores.

  Hiding the operator argument _∷_ does not work (see below) and we
  have no overloading.

  -}

  {-
  idR≡foldR' : ∀ as → foldR {A} cons nil as ⊆ idR as
  idR≡foldR' []      ys []≡ys                 = []≡ys
  idR≡foldR' (a ∷ xs) ys (exists {a' , x'} q) with q
  ... | ( q1 , a'∷x'≡ys ) = 
    let ih : foldR {A} cons nil xs ⊆ idR xs
          -- ∀ ys → foldR {A} cons nil xs ys → idR xs ys
          -- ∀ ys → foldR {A} cons nil xs ys → xs ≡ ys
        ih = idR≡foldR' xs                              
    in let goal : a ∷ xs ≡ ys
           goal = {! !}
       in goal            
  -}

  listinduction : {A : Set} →
                  (P : ℙ (List A)) → 
                  (base : P []) → 
                  (step : ∀ y → ∀ ys → P ys → P (y ∷ ys)) →
                  (∀ xs → P xs)
  listinduction P base step []        = base 
  listinduction P base step (x ∷ xs') = 
    let ih = listinduction P base step xs' 
    in step x xs' ih  

  P : ℙ (List A)
  P = λ as → foldR {A} cons nil as ⊆ idR as

  PBase : Set
  PBase = P [] 
  PBase = foldR {A} cons nil [] ⊆ idR []
  PBase = ∀ bs → foldR {A} cons nil bs [] → idR [] bs
  PBase = (bs : List A) → (∈ ₁∘ foldr₁ (cons ○₁ (idR ⨉₁ ∈)) nil) bs [] → [] ≡ bs
  PBase = (bs : List A) → ∈ (foldr₁ (cons ○₁ (idR ⨉₁ ∈)) nil []) bs → [] ≡ bs
  PBase = (bs : List A) → foldr₁ (cons ○₁ (idR ⨉₁ ∈)) nil bs [] → [] ≡ bs
  PBase = (bs : List A) → [] ≡ bs → [] ≡ bs

  Pbase : P []
  Pbase = λ bs → λ []≡bs → []≡bs

  -- The definition of foldR could be simplified to not using ∈ ₁∘

  fidR : List A ← List A
  fidR = foldR {A} cons nil

  Pyys : A → List A → Set
  Pyys = λ y ys → P (y ∷ ys)
  Pyys = λ y ys → fidR (y ∷ ys) ⊆ idR (y ∷ ys)
  Pyys = λ y ys → foldR {A} cons nil (y ∷ ys) ⊆ idR (y ∷ ys)
  Pyys = λ y ys → foldr₁ (cons ○₁ (idR ⨉₁ ∈)) nil (y ∷ ys) ⊆ idR (y ∷ ys)
  Pyys = λ y ys → (cons ○₁ (idR ⨉₁ ∈)) (y ,₁ foldr₁ (cons ○₁ (idR ⨉₁ ∈)) nil ys) ⊆ idR (y ∷ ys)
  Pyys = λ y ys → (cons ○₁ (idR ⨉₁ ∈)) (y ,₁ fidR ys) ⊆ idR (y ∷ ys)
  Pyys = λ y ys → (zs : List A) → (cons ○₁ (idR ⨉₁ ∈)) (y ,₁ fidR ys) zs → idR (y ∷ ys) zs
  Pyys = λ y ys → (zs : List A) → (cons · ((idR ⨉₁ ∈) (y ,₁ fidR ys))) zs 
                               → (y ∷ ys) ≡ zs
  Pyys = λ y ys → (zs : List A) → 
            Σ₀ (λ y'∷ys' → (((idR ⨉₁ ∈) (y ,₁ fidR ys)) y'∷ys' × cons y'∷ys' zs))
             → (y ∷ ys) ≡ zs
  Pyys = λ y ys → (zs : List A) → 
            Σ (A × List A) 
               (λ y',ys' → let  y'  = proj₁ y',ys' 
                                ys' = proj₂ y',ys' 
                            in (y ≡ y'  ×  fidR ys ys') × cons (y' , ys') zs)
             → (y ∷ ys) ≡ zs
  Pyys = λ y ys → (zs : List A) → 
            Σ (A × List A) 
               (λ p → let  y'  = proj₁ p 
                           ys' = proj₂ p 
                       in (y ≡ y'  ×  fidR ys ys')  ×  y' ∷ ys' ≡ zs)
             → (y ∷ ys) ≡ zs

  Pstep : (y : A) (ys : List A) → P ys → P (y ∷ ys)
  Pstep y ys ih zs ((y' , ys') , (y≡y' , fidRysys') , y'∷ys'≡zs) = 
    ≡-begin 
       y ∷ ys
    ≡⟨ y≡y' ⟨∷⟩ ih ys' fidRysys' ⟩
       y' ∷ ys'   
    ≡⟨ y'∷ys'≡zs ⟩ 
       zs 
    ≡∎ 

  idR≡foldR' : ∀ as → P as
  idR≡foldR' = listinduction P Pbase Pstep -}

{-
idR≡foldR1 : {A : Set} → idR ⊒ foldR {A} cons nil
idR≡foldR1 {A} = let module q = Q A in q.idR≡foldR


private -- this module is just here to check some intermediate types
  module testPJ (A B : Set) (R : B ← (A × B)) (S : ℙ B) where
    open import Relations using (_←₁_)
    test : (A × B) ←₁ (A ×₁ ℙ B)
    test = idR ⨉₁ ∈

    test2 : (A ×₁ ℙ B) → ℙ (A × B)
    test2 = Λ₁ (idR ⨉₁ ∈)

    testR : A × B → ℙ B
    testR = Λ R

    open import Data.Function using (id₁)
    open import Data.Product  using (proj₁; proj₂)
    open import Logic using (∃₀)

    test3 : List A → ℙ B
    test3 = foldr₁ (R ○₁ (idR ⨉₁ id₁)) S

    test4 : (A ×₁ ℙ B) → ℙ B
    test4 (a ,₁ pb) = (R ○₁ (idR ⨉₁ id₁)) (a ,₁ pb)
    test4 (a ,₁ pb) =  R · ((idR ⨉₁ id₁) (a ,₁ pb)) 
    test4 (a ,₁ pb) =  R · (λ bd → let b = proj₁ bd
                                       d = proj₂ bd
                                   in idR a b × id₁ pb d)

    test4 (a ,₁ pb) =  R · (λ bd → let b = proj₁ bd
                                       d = proj₂ bd
                                   in a ≡ b × pb d)
    
    test5 : (A ×₁ ℙ B) → B → Set
    test5 (a ,₁ pb) b = ∃₀ (λ bd → ((λ bd → let b = proj₁ bd
                                                d = proj₂ bd
                                            in a ≡ b × pb d) bd) × R bd b)
    test5 (a ,₁ pb) b = ∃₀ (λ bd → (let b' = proj₁ bd
                                        d  = proj₂ bd
                                    in a ≡ b'  ×  pb d) 
                                   × R bd b)
    test5 (a ,₁ pb) b = ∃₀ (λ bd → let b' = proj₁ bd
                                       d  = proj₂ bd
                                   in a ≡ b'  ×  pb d  ×  R bd b)
-}

{-
module TooMuchHiding (A : Set) where
  open import Relation.Binary.PropositionalEquality using (≡-setoid)
  import Relation.Binary.EqReasoning
  open module ≡-reasoning = Relation.Binary.EqReasoning (≡-setoid (List A))
     renaming (begin_ to ≡-begin_ ; _∎ to _≡∎)

  _⟨⟩_ : {A B C : Set} {a a' : A} {b b' : B} → 
          {_⊕_ : A → B → C} →  -- this cannot be hidden
          (a ≡ a') → (b ≡ b') →
          (a ⊕ b) ≡ (a' ⊕ b')
  _⟨⟩_ {_⊕_ = _⊕_} p q = ≡-cong₂ _⊕_ p q

  idR≡foldR : idR ⊒ foldR {A} cons nil
  idR≡foldR []      y []≡y                                            = []≡y
  idR≡foldR (a ∷ xs) y (exists {a' , y'} ((a≡a' , foldRxsys) , a'∷y'≡y)) = 
      ≡-begin
           a ∷ xs
      ≡⟨ a≡a' ⟨⟩ idR≡foldR xs y' foldRxsys ⟩
           a' ∷ y'
      ≡⟨ a'∷y'≡y  ⟩
           y
      ≡∎
-}

-- refinement of relational fold

foldR-monotonic : {A B : Set} →
  {R₁ R₂ : B ← (A × B)} {S₁ S₂ : ℙ B} →
    R₁ ⊒ R₂ → S₁ ⊇ S₂ → foldR R₁ S₁ ⊒ foldR R₂ S₂
foldR-monotonic {R₁ = R₁} {R₂} {S₁} {S₂} R₁⊒R₂ S₁⊇S₂ =
    ⊒-begin
       foldR R₁ S₁
    ⊒⟨ id-intro-r ⟩
       foldR R₁ S₁ ○ idR
    ⊒⟨ ○-monotonic-r idR⊒foldR ⟩
       foldR R₁ S₁ ○ foldR cons nil
    ⊒⟨ foldR-fusion-⊒ (foldR R₁ S₁) fuse-step fuse-base ⟩
       foldR R₂ S₂
    ⊒∎
  where fuse-base : Λ (foldR R₁ S₁ ○ ∈) nil ⊇ S₂
        fuse-base b S₂b = ([] , refl , S₁⊇S₂ b S₂b) 

        fuse-step : (foldR R₁ S₁ ○ cons) ⊒ (R₂ ○ (idR ⨉ foldR R₁ S₁))
        fuse-step b (a , x) 
               ((a' , b') , (a≡a' , b'foldR₁x) , bR₂a'b') = 
          (a ∷ x ,  
            (refl ,  
                 ((a' , b') , 
                    (((a≡a' , b'foldR₁x) , 
                      R₁⊒R₂ b (a' , b') bR₂a'b')))))

-- coreflexive folds

corefl-foldR : {A : Set} {C : (A × List A) ← (A × List A)} {s : ℙ (List A)} →
  C ⊑ idR → s ⊆ nil → foldR (cons ○ C) s ⊑ idR
corefl-foldR {_} {C} {s} C⊑idR s⊆nil =
  ⊑-begin
    foldR (cons ○ C) s
  ⊑⟨ foldR-monotonic (○-monotonic-r C⊑idR) s⊆nil ⟩
    foldR (cons ○ idR) nil
  ⊑⟨ foldR-monotonic id-intro-r ⊆-refl ⟩
    foldR cons nil
  ⊑⟨ idR⊒foldR ⟩
    idR
  ⊑∎
