module Data.Tree.Fold where

open import Data.Empty using (⊥)
open import Data.Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Sets
     using (ℙ; _⊆_; _⊇_; ⊆-refl; ⊇-refl; singleton;
            _≡_; ≡-refl; ≡-trans; ≡-cong; ≡-subst; ≡-sym)
open import Relations
open import Relations.PowerTrans
     using (Λ∈-galois-1; Λ∈-galois-2; Λ-monotonic; ℰ-functor-⊆;
            ℰ-functor-⊇; ℰ-monotonic')
open import Relations.Product
     using (Λ₁⨉⨉-monotonic; Λ₁⨉⨉-absorption-⊆; Λ₁⨉⨉-absorption-⊇;
            ⨉3-functor-⊑; ⨉3-functor-⊒; ⨉-monotonic; ⨉3-id-⊑)
open import Relations.CompChain

open import AlgebraicReasoning.Sets
     using (⊆-begin_; _⊆⟨_⟩_; _⊆∎;
            ⊇-begin_; _⊇⟨_⟩_; _⊇∎)
open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎;
            ⊒-begin_; _⊒⟨_⟩_; _⊒∎;
            ⊒₁-begin_; _⊒₁⟨_⟩_; _⊒₁∎ )
open import AlgebraicReasoning.Implications

open import Data.Tree


foldT : {A B : Set} → (B ← (A × B × B)) → ℙ B → (B ← Tree A)
foldT R s = ∈ ₁∘ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) s

-- initial algebras

null : {A : Set} → ℙ (Tree A)
null = singleton Null

fork : {A : Set} → Tree A ← (A × Tree A × Tree A)
fork = fun fr 
  where fr : {A : Set} → (A × Tree A × Tree A) → Tree A
        fr (a , t , u) = Fork a t u

-- universal property

foldT-universal-⊒ : {A B : Set} →
  (S : B ← Tree A) → (R : B ← (A × B × B)) → (e : ℙ B) →
    (S ○ fork ⊒ R ○ (idR ⨉ S ⨉ S)) → (ℰ S null ⊇ e) →
      S ⊒ foldT R e
foldT-universal-⊒ S R e S○fork⊒RidSS ℰSnull⊇e = 
    (⇐-begin
       foldT R e ⊑ S
     ⇐⟨ ⇐-refl ⟩
        ∈ ₁∘ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e ⊑ S
     ⇐⟨ Λ∈-galois-2 ⟩
      foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e ⊑ Λ S
     ⇐∎) foldt⊑ΛS
  where
   foldt⊑ΛS : foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e ⊑ Λ S
   foldt⊑ΛS Null = 
      ⊆-begin 
          foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e Null  
      ⊆⟨ ⊆-refl ⟩
          e 
      ⊆⟨ ℰSnull⊇e ⟩
          ℰ S null
      ⊆⟨  ℰSnull⊆ΛSNull  ⟩
          Λ S Null
      ⊆∎       
     where ℰSnull⊆ΛSNull :  ℰ S null ⊆ Λ S Null
           ℰSnull⊆ΛSNull b (.Null , ≡-refl , bSNull) = bSNull 

   foldt⊑ΛS (Fork a t u) = 
     let induction-hypothesis₁ = foldt⊑ΛS t
         induction-hypothesis₂ = foldt⊑ΛS u
     in
        ⊆-begin 
           foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e (Fork a t u)
        ⊆⟨ ⊆-refl ⟩
           Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))
             (a ,₁ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e t ₁,₁
                   foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e u)
        ⊆⟨ Λ₁⨉⨉-monotonic R induction-hypothesis₁
                             induction-hypothesis₂ a  ⟩
           Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈)) (a ,₁ Λ S t ₁,₁ Λ S u)
        ⊆⟨ Λ₁⨉⨉-absorption-⊆ R S S a t u  ⟩
          Λ (R ○ (idR ⨉ S ⨉ S)) (a , t , u)
        ⊆⟨ Λ-monotonic S○fork⊒RidSS (a , t , u) ⟩
          Λ (S ○ fork) (a , t , u)
        ⊆⟨ ΛSfork⊆SFork  ⟩
          Λ S (Fork a t u)
        ⊆∎ 
    where ΛSfork⊆SFork : Λ (S ○ fork) (a , t , u) ⊆ Λ S (Fork a t u)
          ΛSfork⊆SFork b (._ , ≡-refl , bSFork) = bSFork 

foldT-universal-⊑ : {A B : Set} →
  (S : B ← Tree A) → (R : B ← (A × B × B)) → (e : ℙ B) →
    (S ○ fork ⊑ R ○ (idR ⨉ S ⨉ S)) → (ℰ S null ⊆ e) →
      S ⊑ foldT R e
foldT-universal-⊑ S R e S○fork⊑RidSS ℰSnull⊆e = 
    (⇐-begin
       S ⊑ foldT R e
     ⇐⟨ ⇐-refl ⟩
       S ⊑ ∈ ₁∘ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e
     ⇐⟨ Λ∈-galois-1 ⟩
       Λ S ⊑ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e
     ⇐∎) ΛS⊑foldt
 where 
   ΛS⊑foldt : Λ S ⊑ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e
   ΛS⊑foldt Null = 
      ⊇-begin 
          foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e Null  
      ⊇⟨ ⊇-refl ⟩
          e 
      ⊇⟨ ℰSnull⊆e ⟩
          ℰ S null
      ⊇⟨  ΛSNull⊆ℰSnull  ⟩
          Λ S Null
      ⊇∎       
     where ΛSNull⊆ℰSnull :  Λ S Null ⊆ ℰ S null 
           ΛSNull⊆ℰSnull b bSNull = (Null , ≡-refl , bSNull) 
   ΛS⊑foldt (Fork a t u) = 
     let induction-hypothesis₁ = ΛS⊑foldt t
         induction-hypothesis₂ = ΛS⊑foldt u
     in
        ⊆-begin 
          Λ S (Fork a t u)
        ⊆⟨ SFork⊆ΛSfork ⟩
          Λ (S ○ fork) (a , t , u)
        ⊆⟨ Λ-monotonic S○fork⊑RidSS (a , t , u) ⟩
          Λ (R ○ (idR ⨉ S ⨉ S)) (a , t , u)
        ⊆⟨ Λ₁⨉⨉-absorption-⊇ R S S a t u  ⟩
           Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈)) (a ,₁ Λ S t ₁,₁ Λ S u)
        ⊆⟨ Λ₁⨉⨉-monotonic R induction-hypothesis₁
                             induction-hypothesis₂ a  ⟩
           Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))
             (a ,₁ foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e t ₁,₁
                   foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e u)
        ⊆⟨ ⊆-refl ⟩
           foldt₁ (Λ₁ (R ○₁ (idR ⨉₁ ∈ ₁⨉₁ ∈))) e (Fork a t u)
        ⊆∎ 
    where SFork⊆ΛSfork : Λ S (Fork a t u) ⊆ Λ (S ○ fork) (a , t , u)
          SFork⊆ΛSfork b bSFork = (Fork a t u , ≡-refl , bSFork)

-- computation rules

foldT-computation-null-⊆ : {A B : Set} {R : B ← (A × B × B)} {e : ℙ B} →
    ℰ (foldT R e) null ⊆ e
foldT-computation-null-⊆ b (.Null , ≡-refl , b∈e) = b∈e

foldT-computation-null-⊇ : {A B : Set} {R : B ← (A × B × B)} {e : ℙ B} →
    ℰ (foldT R e) null ⊇ e
foldT-computation-null-⊇ b b∈e = (Null , ≡-refl , b∈e)

foldT-computation-fork-⊑ : {A B : Set} (R : B ← (A × B × B)) {e : ℙ B} →
    foldT R e ○ fork ⊑ R ○ (idR ⨉ foldT R e ⨉ foldT R e)
foldT-computation-fork-⊑ R b (a , t , u)
  (._ , ≡-refl , (.a , b₁ , b₂) , (≡-refl , b₁foldTt , b₂foldTu) , bR<ab₁b₂>) =
   ((a , b₁ , b₂) , (≡-refl , b₁foldTt , b₂foldTu) , bR<ab₁b₂>)  

foldT-computation-fork-⊒ : {A B : Set} (R : B ← (A × B × B)) {e : ℙ B} →
    foldT R e ○ fork ⊒ R ○ (idR ⨉ foldT R e ⨉ foldT R e)
foldT-computation-fork-⊒ R b (a , t , u)
       ((.a , b₁ , b₂) , (≡-refl , b₁foldTt , b₂foldTu) , bR<ab₁b₂>)
   = (Fork a t u ,  
       (≡-refl , ((a , b₁ , b₂), 
          (≡-refl , b₁foldTt , b₂foldTu) ,  bR<ab₁b₂>))) 

-- foldt fusion

foldT-fusion-⊒ : {A B C : Set} →
  (R : C ← B) → {S : B ← (A × B × B)} {T : C ← (A × C × C)} 
    {u : ℙ B} {v : ℙ C} →
        (R ○ S) ⊒ (T ○ (idR ⨉ R ⨉ R)) → 
              ℰ R u ⊇ v → 
               (R ○ foldT S u) ⊒ foldT T v
foldT-fusion-⊒ R {S} {T} {u} {v} RS⊒TFR Ru⊇v =
    foldT-universal-⊒ (R ○ foldT S u) T v step-cond base-cond 
  where step-cond : (R ○ foldT S u) ○ fork ⊒
                      T ○ (idR ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
        step-cond = 
         ⊒-begin
             (R ○ foldT S u) ○ fork
         ⊒⟨ ○-assocl ⟩
             R ○ (foldT S u ○ fork)
         ⊒⟨ ○-monotonic-r (foldT-computation-fork-⊒ S)  ⟩
             R ○ S ○ (idR ⨉ foldT S u ⨉ foldT S u)
         ⊒⟨ ⇦-mono-l (T ● (idR ⨉ R ⨉ R) ‥) (R ● S ‥) RS⊒TFR  ⟩
             T ○ (idR ⨉ R ⨉ R) ○ (idR ⨉ foldT S u ⨉ foldT S u)
         ⊒⟨ ○-monotonic-r ⨉3-functor-⊒ ⟩
             T ○ ((idR ○ idR) ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
         ⊒⟨ ○-monotonic-r (⨉-monotonic id-idempotent-⊒ ⊒-refl) ⟩
             T ○ (idR ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
         ⊒∎ 

        base-cond : ℰ (R ○ foldT S u) null ⊇ v
        base-cond = 
         ⊇-begin
            ℰ (R ○ foldT S u) null
         ⊇⟨  ℰ-functor-⊆  ⟩
            ℰ R (ℰ (foldT S u) null)
         ⊇⟨ ℰ-monotonic' foldT-computation-null-⊇  ⟩ 
            ℰ R u
         ⊇⟨ Ru⊇v  ⟩
           v
         ⊇∎ 

foldT-fusion-⊑ : {A B C : Set} →
  (R : C ← B) → {S : B ← (A × B × B)} {T : C ← (A × C × C)} 
    {u : ℙ B} {v : ℙ C} →
        (R ○ S) ⊑ (T ○ (idR ⨉ R ⨉ R)) → 
              ℰ R u ⊆ v → 
               (R ○ foldT S u) ⊑ foldT T v
foldT-fusion-⊑ R {S} {T} {u} {v} RS⊑TFR Ru⊆v =
   foldT-universal-⊑ (R ○ foldT S u) T v step-cond base-cond 
  where step-cond : (R ○ foldT S u) ○ fork ⊑
                      T ○ (idR ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
        step-cond = 
         ⊑-begin
             (R ○ foldT S u) ○ fork
         ⊑⟨ ○-assocr ⟩
             R ○ (foldT S u ○ fork)
         ⊑⟨ ○-monotonic-r (foldT-computation-fork-⊑ S)  ⟩
             R ○ S ○ (idR ⨉ foldT S u ⨉ foldT S u)
         ⊑⟨ ⇦-mono-l (R ● S ‥) (T ● (idR ⨉ R ⨉ R) ‥) RS⊑TFR  ⟩
             T ○ (idR ⨉ R ⨉ R) ○ (idR ⨉ foldT S u ⨉ foldT S u)
         ⊑⟨ ○-monotonic-r ⨉3-functor-⊑ ⟩
             T ○ ((idR ○ idR) ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
         ⊑⟨ ○-monotonic-r (⨉-monotonic id-idempotent-⊑ ⊑-refl) ⟩
             T ○ (idR ⨉ (R ○ foldT S u) ⨉ (R ○ foldT S u))
         ⊑∎ 
 
        base-cond : ℰ (R ○ foldT S u) null ⊆ v
        base-cond = 
         ⊆-begin
            ℰ (R ○ foldT S u) null
         ⊆⟨  ℰ-functor-⊇  ⟩
            ℰ R (ℰ (foldT S u) null)
         ⊆⟨ ℰ-monotonic' foldT-computation-null-⊆  ⟩ 
            ℰ R u
         ⊆⟨ Ru⊆v  ⟩
           v
         ⊆∎ 

-- from relational fold to functional fold

foldT-to-foldt : {A B : Set} → (f : (A × B × B) → B) → (e : B) →
                   foldT (fun f) (singleton e) ⊒ fun (foldt f e)
foldT-to-foldt f e b Null         e≡b        =  e≡b
foldT-to-foldt f e b (Fork a t u) foldt$x≡b  =
   ((a , foldt f e t , foldt f e u) , 
     ((≡-refl , foldT-to-foldt f e (foldt f e t) t
                  (≡-cong (λ g → foldt g e t) ≡-refl) ,
                foldT-to-foldt f e (foldt f e u) u
                  (≡-cong (λ g → foldt g e u) ≡-refl)) , 
      foldt$x≡b)) 

foldt-to-foldT : {A B : Set} → (f : (A × B × B) → B) → (e : B) →
                   foldT (fun f) (singleton e) ⊑ fun (foldt f e)
foldt-to-foldT f e = 
   foldT-universal-⊒ (fun (foldt f e)) (fun f) (singleton e)
      univ1 univ2
  where univ1 : fun f ○ (idR ⨉ fun (foldt f e) ⨉ fun (foldt f e)) ⊑
                 fun (foldt f e) ○ fork
        univ1 b (a , t , u)
              ((.a , b₁ , b₂) , (≡-refl , foldtt≡b₁ , foldtu≡b₂), fab₁b₂≡b) = 
          (Fork a t u , ≡-refl , 
           ≡-subst (λ b₂ → f (a , foldt f e t , b₂) ≡ b) (≡-sym foldtu≡b₂)
             (≡-subst (λ b₁ → f (a , b₁ , b₂) ≡ b) (≡-sym foldtt≡b₁) fab₁b₂≡b) ) 
        univ2 : singleton e ⊆ ℰ (fun (foldt f e)) null
        univ2 .e ≡-refl = (Null , ≡-refl , ≡-refl) 

-- id is a fold

idR⊑foldT : {A : Set} → idR ⊑ foldT {A} fork null
idR⊑foldT y Null Null≡y = Null≡y
idR⊑foldT Null (Fork _ _ _) ()
idR⊑foldT (Fork b v w) (Fork a t u) atu≡bvw with Fork-injective atu≡bvw
... | (a≡b , t≡v , u≡w) = ((b , v , w) , 
             (a≡b , idR⊑foldT v t t≡v , idR⊑foldT w u u≡w) , ≡-refl)

idR⊒foldT : {A : Set} → idR ⊒ foldT {A} fork null
idR⊒foldT = foldT-universal-⊒ idR fork null id○fork⊒fork○Fid ℰidnull⊇null
  where id○fork⊒fork○Fid : idR ○ fork ⊒ fork ○ (idR ⨉ idR ⨉ idR)
        id○fork⊒fork○Fid = 
          ⊒-begin
             idR ○ fork
          ⊒⟨ id-elim-l ⟩
             fork
          ⊒⟨ id-intro-r  ⟩
             fork ○ idR
          ⊒⟨ ○-monotonic-r ⨉3-id-⊑ ⟩
             fork ○ (idR ⨉ idR ⨉ idR)
          ⊒∎ 
        ℰidnull⊇null : ℰ idR null ⊇ null
        ℰidnull⊇null xs Null≡xs = (xs , Null≡xs , ≡-refl) 


-- refinement of relational fold

foldT-monotonic : {A B : Set} →
  {R₁ R₂ : B ← (A × B × B)} {S₁ S₂ : ℙ B} →
    R₁ ⊒ R₂ → S₁ ⊇ S₂ → foldT R₁ S₁ ⊒ foldT R₂ S₂
foldT-monotonic {A}{B}{R₁}{R₂}{S₁}{S₂} R₁⊒R₂ S₁⊇S₂ =
    ⊒-begin
       foldT R₁ S₁
    ⊒⟨ id-intro-r ⟩
       foldT R₁ S₁ ○ idR
    ⊒⟨ ○-monotonic-r idR⊒foldT ⟩
       foldT R₁ S₁ ○ foldT fork null
    ⊒⟨ foldT-fusion-⊒ (foldT R₁ S₁) fuse-step fuse-base ⟩
       foldT R₂ S₂
    ⊒∎
  where fuse-base : Λ₁ (foldT R₁ S₁ ○₁ ∈) null ⊇ S₂
        fuse-base b S₂b = (Null , ≡-refl , S₁⊇S₂ b S₂b) 

        fuse-step : (foldT R₁ S₁ ○ fork) ⊒ (R₂ ○ (idR ⨉ foldT R₁ S₁ ⨉ foldT R₁ S₁))
        fuse-step b (a , t , u)
            ((a' , b₁ , b₂) , (a≡a' , b₁foldTt , b₂foldTu) , bR₂a'b₁b₂) =
          (Fork a t u , ≡-refl , 
              (a' , b₁ , b₂) , (a≡a' , b₁foldTt , b₂foldTu) ,
                                     R₁⊒R₂ b (a' , b₁ , b₂) bR₂a'b₁b₂)
