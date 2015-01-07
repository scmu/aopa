module Examples.Sorting.qSort where

open import Relation.Nullary using (Dec; yes; no)

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Function
open import Data.Product
open import Data.Sum hiding (isInj₁)
open import Data.Nat using (ℕ ; zero; suc; _≤′_; _<′_ ; ≤′-refl; ≤′-step)
open import Data.List    using (List; []; _∷_; _++_; length)
-- open import Relation.Binary.PropositionalEquality

open import Sets using (ℙ; ∅; _⊆_; _⊇_; singleton; _∪_;
                        _≡_; ≡-refl; ≡-sym; ≡-trans; ≡-subst; ≡-cong)
open import Relations
     using (_←_; _˘; fun; _○_; _·_; idR; _⊔_; 
            _⊑_; _⊒_; ⊑-refl; ∈; _₁∘_; 
            ○-monotonic-r; ○-monotonic-l; ○-assocl; ○-assocr;
            id-intro-r; id-intro-l; id-elim-l; _⨉_; _×₁_; _₁×₁_; _,₁_; _₁,₁_; 
            ℰ)
open import Relations.Product using (⨉-monotonic; ⨉3-id-⊑; ⨉3-functor-⊒)
open import Relations.Function using (fun-simple; fun○-⊒)
open import Relations.Converse
open import Relations.Coreflexive
open import Relations.WellFound
open import Relations.CompChain

open import Data.List.Fold
     using (foldr₁; foldR; nil; foldR-fusion-⊑; foldR-fusion-⊒)


open import Data.Tree
open import Data.Tree.Fold
open import Data.Tree.Unfold

open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎; 
            ⊒-begin_; _⊒⟨_⟩_; _⊒∎)

open import Examples.Sorting.Spec

join : {A : Set} → (A × List A × List A) → List A
join (a , xs , ys) = xs ++ (a ∷ ys)

flatten : {A : Set} → Tree A → List A
flatten = foldt join []

-- Can ε-List and ε-Tree be defined using foldR?
  
ε-List : {A : Set} → (A ← List A) 
-- ε-List = foldR (fun proj₁ ⊔ fun proj₂) ∅
ε-List = ∈ ₁∘ Λε-List
  where Λε-List : {A : Set} → List A → ℙ A
        Λε-List {A} = foldr₁ step ∅
          where step : {A : Set} → (A ×₁ ℙ A) → ℙ A
                step (a ,₁ p) = singleton a ∪ p 
 
ε-Tree : {A : Set} → (A ← Tree A) 
-- ε-Tree = foldT (fun proj₁ ⊔ (fun (proj₁ ∘ proj₂) ⊔ fun (proj₂ ∘ proj₂))) ∅
ε-Tree = ∈ ₁∘ Λε-Tree
  where Λε-Tree : {A : Set} → Tree A → ℙ A
        Λε-Tree = foldt₁ step ∅
          where step : {A : Set} → (A ×₁ ℙ A ₁×₁ ℙ A) → ℙ A
                step (a ,₁ p ₁,₁ q) = singleton a ∪ p ∪ q

okt : ℙ (Val × Tree Val × Tree Val) 
okt (a , t , u) = (∀ a' → ε-Tree a' t → a' ≤ a) ×
                  (∀ a' → ε-Tree a' u → a ≤ a')  

okl : ℙ (Val × List Val × List Val) 
okl (a , t , u) = (∀ a' → ε-List a' t → a' ≤ a) ×
                  (∀ a' → ε-List a' u → a ≤ a')  

ordtree? : Tree Val ← Tree Val
ordtree? = foldT (fork ○ (okt ¿)) null

split : Val → List Val → (List Val × List Val)
split x [] = ([] , [])
split x (y ∷ xs) with split x xs
... | (ys , zs) with y ≤? x
...    | yes _ = (y ∷ ys , zs)
...    | no  _ = (ys , y ∷ zs)

partition : List Val → (⊤ ⊎ (Val × List Val × List Val))
partition [] = inj₁ tt
partition (x ∷ xs) = inj₂ (x , split x xs)

≤′-suc-cong : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
≤′-suc-cong {m} {.m} ≤′-refl = ≤′-refl 
≤′-suc-cong {m} {suc n} (≤′-step m≤′n) = ≤′-step (≤′-suc-cong  m≤′n)

-- Proof of Well-Foundedness

private
  split⊑< : ∀ x xs →
          (length (proj₁ (split x xs)) ≤′ length xs) × (length (proj₂ (split x xs)) ≤′ length xs)
  split⊑< x [] = (≤′-refl , ≤′-refl) 
  split⊑< x (y ∷ xs) with split⊑< x xs 
  ... | ind with split x xs
  ...  |  (ys , zs)  with y ≤? x
  ...    | yes _ = (≤′-suc-cong (proj₁ ind) , ≤′-step (proj₂ ind))
  ...    | no _  = (≤′-step (proj₁ ind) , ≤′-suc-cong (proj₂ ind))

  partition⊑< : fun length ○ (ε-TreeF ○ fun partition) ○ (fun length)˘ ⊑ _<′_
  partition⊑< n m (ys , ([] , #xs≡m , .(inj₁ tt) , ≡-refl , ()) , #ys≡n)
  partition⊑< n m (ys , (x ∷ xs , 1+#xs≡m , ._ , ≡-refl , ysεv) , #ys≡n) with split⊑< x xs
  ... | (#zs≤#xs , #ws≤#xs) with  split x xs
  ...  | (zs , ws)  with ysεv
  ...   | inj₁ zs≡ys = ≡-subst (λ m → suc n ≤′ m) 1+#xs≡m
                         (≤′-suc-cong 
                          (≡-subst (λ n → n ≤′ length xs) #ys≡n
                           (≡-subst (λ ys → length ys ≤′ length xs) zs≡ys #zs≤#xs))) 
  ...   | inj₂ ws≡ys = ≡-subst (λ m → suc n ≤′ m) 1+#xs≡m
                         (≤′-suc-cong 
                          (≡-subst (λ n → n ≤′ length xs) #ys≡n
                           (≡-subst (λ ys → length ys ≤′ length xs) ws≡ys #ws≤#xs)))  

partition-wf : well-found (ε-TreeF ○ fun partition)
partition-wf xs = acc-fRfº xs 
                     (acc-⊑ partition⊑< (length xs) (ℕ<-wf (length xs)))

-- Various properties

--  ordered? ○ fun flatten ⊒ fun flatten ○ ordtree?  

ε-List-join : ∀ {A} → {a b : A}{xs ys : List A} →
             ε-List b (join (a , xs , ys)) →
                a ≡ b ⊎ ε-List b xs ⊎ ε-List b ys
ε-List-join {xs = []} (inj₁ a≡b) = inj₁ a≡b 
ε-List-join {xs = []} (inj₂ b∈ys) = inj₂ (inj₂ b∈ys)
ε-List-join {xs = c ∷ xs} (inj₁ c≡b) = inj₂ (inj₁ (inj₁ c≡b)) 
ε-List-join {_}{a}{b}{xs = c ∷ xs} (inj₂ b∈xs++a∷ys) 
    with (ε-List-join {_}{a}{b}{xs} b∈xs++a∷ys)
... | inj₁ a≡b = inj₁ a≡b 
... | inj₂ (inj₁ b∈xs) = inj₂ (inj₁ (inj₂ b∈xs)) 
... | inj₂ (inj₂ b∈ys) = inj₂ (inj₂ b∈ys) 

∷⇒ε-List : ∀ {A} → (a : A) (xs : List A) → ε-List a (a ∷ xs)
∷⇒ε-List a xs = inj₁ ≡-refl 

∷r⇒ε-List : ∀ {A} → (a b : A) (xs : List A) →  ε-List a xs →  ε-List a (b ∷ xs)
∷r⇒ε-List a b xs a∈xs = inj₂ a∈xs

++l⇒ε-List : ∀ {A} → (a : A) (xs ys : List A) → ε-List a xs → ε-List a (xs ++ ys)
++l⇒ε-List a [] ys ()
++l⇒ε-List a (.a ∷ xs) ys (inj₁ ≡-refl) = ∷⇒ε-List a (xs ++ ys) 
++l⇒ε-List a (x ∷ xs) ys (inj₂ a∈xs) = inj₂ (++l⇒ε-List a xs ys a∈xs) 

++r⇒ε-List : ∀ {A} → (a : A) (xs ys : List A) → ε-List a ys → ε-List a (xs ++ ys)
++r⇒ε-List a [] ys a∈ys = a∈ys
++r⇒ε-List a (x ∷ xs) ys a∈ys = inj₂ (++r⇒ε-List a xs ys a∈ys) 

ε-List⇒ε-Tree : ∀ {A} → (t : Tree A) (a : A) → 
                ε-List a (flatten t) → ε-Tree a t
ε-List⇒ε-Tree Null a ()
ε-List⇒ε-Tree (Fork b t u) a a∈flat 
   with ε-List-join {_}{b}{a}{flatten t}{flatten u} a∈flat
... | inj₁ b≡a = inj₁ b≡a 
... | inj₂ (inj₁ a∈flatt) = inj₂ (inj₁ (ε-List⇒ε-Tree t a a∈flatt)) 
... | inj₂ (inj₂ a∈flatu) = inj₂ (inj₂ (ε-List⇒ε-Tree u a a∈flatu)) 

ε-Tree⇒ε-List : ∀ {A} → (t : Tree A) (a : A) → 
                 ε-Tree a t → ε-List a (flatten t)
ε-Tree⇒ε-List Null a () 
ε-Tree⇒ε-List (Fork .a t u) a (inj₁ ≡-refl) = ++r⇒ε-List a (flatten t) _ (∷⇒ε-List a (flatten u)) 
ε-Tree⇒ε-List (Fork b t u) a (inj₂ (inj₁ a∈t)) = 
    ++l⇒ε-List a (flatten t) (b ∷ flatten u) (ε-Tree⇒ε-List t a a∈t) 
ε-Tree⇒ε-List (Fork b t u) a (inj₂ (inj₂ a∈u)) = 
    ++r⇒ε-List a (flatten t) _ (∷r⇒ε-List a b (flatten u) (ε-Tree⇒ε-List u a a∈u)) 

okl⊑okt : (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten) ⊑ 
                     (idR ⨉ fun flatten ⨉ fun flatten) ○ (okt ¿)
okl⊑okt (a' , xs , ys) (a , t , u) 
          (._ , pf , ≡-refl , b∈xs⇒b≤a' , b∈ys⇒a'≤b) with pf
okl⊑okt (.a , ._ , ._) (a , t , u) 
          (._ , pf , ≡-refl , b∈xs⇒b≤a , b∈ys⇒a≤b) | (≡-refl , ≡-refl , ≡-refl) = 
  ((a , t , u) , (≡-refl , (λ b b∈t → b∈xs⇒b≤a b (ε-Tree⇒ε-List t b b∈t)) , 
                           (λ b b∈u → b∈ys⇒a≤b b (ε-Tree⇒ε-List u b b∈u))) , 
           ≡-refl , ≡-refl , ≡-refl) 
 
okt⊑okl : (idR ⨉ fun flatten ⨉ fun flatten) ○ (okt ¿) ⊑
                      (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
okt⊑okl (.a , ._ , ._) (a , t , u) 
          (._ , (≡-refl , b∈t⇒b≤a , b∈u⇒a≤b) , ≡-refl , ≡-refl , ≡-refl) = 
   ((a , flatten t , flatten u) , (≡-refl , ≡-refl , ≡-refl) , 
      ≡-refl , (λ b b∈ft → b∈t⇒b≤a b (ε-List⇒ε-Tree t b b∈ft)) , 
               (λ b b∈fu → b∈u⇒a≤b b (ε-List⇒ε-Tree u b b∈fu))) 

joinok○flat² : fun join ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten) ⊑
                 fun flatten ○ fork ○ (okt ¿)
joinok○flat² =
   ⊑-begin
      fun join ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ○-monotonic-r okl⊑okt  ⟩
      fun join ○ (idR ⨉ fun flatten ⨉ fun flatten) ○ (okt ¿)
   ⊑⟨ ○-monotonic-r (○-monotonic-l
        (⨉-monotonic ⊑-refl (⨉-monotonic (foldT-to-foldt join []) (foldT-to-foldt join []))))  ⟩
      fun join ○ (idR ⨉ foldT (fun join) nil ⨉ foldT (fun join) nil) ○ (okt ¿)
   ⊑⟨ ⇦-mono-l 
        (fun join ● (idR ⨉ foldT (fun join) nil ⨉ foldT (fun join) nil) ‥) (foldT (fun join) nil ● fork ‥) 
          (foldT-computation-fork-⊒ (fun join))  ⟩
      foldT (fun join) nil ○ fork ○ (okt ¿)
   ⊑⟨ ○-monotonic-l (foldt-to-foldT join []) ⟩
      fun flatten ○ fork ○ (okt ¿)
   ⊑∎ 

flat○okt : fun flatten ○ fork ○ (okt ¿) ⊑
                    (fun join ○ (okl ¿)) ○ (idR ⨉ fun flatten ⨉ fun flatten)
flat○okt = 
   ⊑-begin
     fun flatten ○ fork ○ (okt ¿)
   ⊑⟨ ○-monotonic-l (foldT-to-foldt join []) ⟩
     foldT (fun join) nil ○ fork ○ (okt ¿)
   ⊑⟨ ⇦-mono-l (foldT (fun join) nil ● fork ‥) 
        (fun join ● (idR ⨉ foldT (fun join) nil ⨉ foldT (fun join) nil)‥)
          (foldT-computation-fork-⊑ (fun join))   ⟩
     fun join ○ (idR ⨉ foldT (fun join) nil ⨉ foldT (fun join) nil) ○ (okt ¿)
   ⊑⟨ ○-monotonic-r (○-monotonic-l
        (⨉-monotonic ⊑-refl (⨉-monotonic (foldt-to-foldT join []) (foldt-to-foldT join []))))  ⟩
     fun join ○ (idR ⨉ fun flatten ⨉ fun flatten) ○ (okt ¿)
   ⊑⟨ ○-monotonic-r okt⊑okl  ⟩
     fun join ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ○-assocl  ⟩
     (fun join ○ (okl ¿)) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑∎ 


ε-lbound : ∀ a xs → (∀ b → ε-List b xs → a ≤ b) → lbound (a , xs)
ε-lbound a [] _ = tt 
ε-lbound a (x ∷ xs) b≡x⊎b∈xs⇒a≤b = 
  (b≡x⊎b∈xs⇒a≤b x (inj₁ ≡-refl) , ε-lbound a xs (λ b b∈xs → b≡x⊎b∈xs⇒a≤b b (inj₂ b∈xs)))

lbound² : ∀ {a} → ∀ xs ys → lbound (a , xs) → lbound (a , ys) → lbound (a , xs ++ ys)
lbound² [] ys a≤xs a≤ys = a≤ys 
lbound² (x ∷ xs) ys (a≤x , a≤xs) a≤ys = (a≤x , lbound² xs ys a≤xs a≤ys)

join○ordered² : (fun join ○ (okl ¿)) ○ (idR ⨉ ordered? ⨉ ordered?) ⊑
                    ordered? ○ fun join
join○ordered² .(a ∷ ys') (a , [] , ys) 
     ((.a , .[] , ys') , (≡-refl , ≡-refl , ys'≡ordered?ys) , 
       (.a , .[] , .ys') , (≡-refl , _ , b∈ys⇒a≤b), ≡-refl) = 
  (a ∷ ys , ≡-refl , (a , ys') , (≡-refl , ys'≡ordered?ys) , 
   (a , ys') , (≡-refl , ε-lbound a ys' b∈ys⇒a≤b) , ≡-refl) 
join○ordered² .(x ∷ xs' ++ a ∷ ys') (a , x ∷ xs , ys) 
     ((.a , .(x ∷ xs') , ys') , 
      (≡-refl , ((.x , xs') , (≡-refl , xs'≡ordered?xs) ,
                 (.x , .xs') , (≡-refl , x≤xs') , ≡-refl) , ys'≡ordered?ys) , 
      .(a , x ∷ xs' , ys') , (≡-refl , b≡x⊎b∈xs'⇒b≤a , b∈ys'⇒a≤b) , ≡-refl) 
   with join○ordered² (xs' ++ a ∷ ys') (a , xs , ys) 
           ((a , xs' , ys') , (≡-refl , xs'≡ordered?xs , ys'≡ordered?ys) , 
             (a , xs' , ys') , (≡-refl , 
               (λ b b∈xs' → b≡x⊎b∈xs'⇒b≤a b (inj₂ b∈xs')) , b∈ys'⇒a≤b) , ≡-refl)
... | (._ , ≡-refl , xs'ays'≡ordered?xsays) = 
       ((x ∷ xs ++ a ∷ ys) , ≡-refl , (x , xs' ++ a ∷ ys') , 
        (≡-refl , xs'ays'≡ordered?xsays) , (x , xs' ++ a ∷ ys') , 
          (≡-refl , lbound² xs' (a ∷ ys') x≤xs'
             let x≤a = b≡x⊎b∈xs'⇒b≤a x (inj₁ ≡-refl)
             in (x≤a , ε-lbound x ys' (λ b b∈ys' → ≤-trans x≤a (b∈ys'⇒a≤b b b∈ys')))) , ≡-refl)

ℰflattnull⊆nil : ℰ (fun flatten) null ⊆ nil {Val}
ℰflattnull⊆nil .[] (.Null , ≡-refl , ≡-refl)  = ≡-refl 

nil⊆ℰord?nil : nil ⊆ ℰ ordered? nil
nil⊆ℰord?nil .[] ≡-refl = ([] , ≡-refl , ≡-refl ) 

ordflatten : ordered? ○ fun flatten ⊒ fun flatten ○ ordtree?  
ordflatten = 
   ⊑-begin
     fun flatten ○ ordtree? 
   ⊑⟨ ⊑-refl ⟩
     fun flatten ○ foldT (fork ○ (okt ¿)) null
   ⊑⟨ foldT-fusion-⊑ (fun flatten) flat○okt ℰflattnull⊆nil  ⟩
     foldT (fun join ○ (okl ¿)) nil
   ⊑⟨ foldT-fusion-⊒ ordered? join○ordered² nil⊆ℰord?nil ⟩
     ordered? ○ foldT (fun join) nil
   ⊑⟨ ○-monotonic-r (foldt-to-foldT join [])  ⟩
     ordered? ○ fun flatten
   ⊑∎ 

-- ordtree? ˘ ⊑ ordtree?

ordtree?⊑id : ordtree? ⊑ idR
ordtree?⊑id = foldT-universal-⊒ idR (fork ○ (okt ¿)) null 
                 fork○okt⊑fork null⊆ℰidnull  
  where fork○okt⊑fork : (fork ○ (okt ¿)) ○ (idR ⨉ idR ⨉ idR) ⊑ idR ○ fork
        fork○okt⊑fork = 
           ⊑-begin
             (fork ○ (okt ¿)) ○ (idR ⨉ idR ⨉ idR)
           ⊑⟨ ○-monotonic-r ⨉3-id-⊑  ⟩
             (fork ○ (okt ¿)) ○ idR
           ⊑⟨ id-intro-r  ⟩
             fork ○ (okt ¿)
           ⊑⟨ ○-monotonic-r (set-corefl⊑idR okt) ⟩
             fork ○ idR
           ⊑⟨ id-intro-r ⟩
             fork
           ⊑⟨ id-elim-l ⟩
             idR ○ fork
           ⊑∎ 

        null⊆ℰidnull : null ⊆ ℰ (idR {Tree Val}) null
        null⊆ℰidnull .Null ≡-refl = (Null , ≡-refl , ≡-refl) 

ordtree-˘-idem : ordtree? ˘ ⊑ ordtree?
ordtree-˘-idem = C˘⊑C ordtree?⊑id


-- Is it fair to take this as an axiom?

postulate ε-List-bCons-⇒ : ∀ a xs bg → bagify xs ≡ bCons a bg → ε-List a xs

ε-List-bCons-⇐ : ∀ a xs → ε-List a xs → Σ Bag (λ bg → bagify xs ≡ bCons a bg)
ε-List-bCons-⇐ a [] ()
ε-List-bCons-⇐ a (.a ∷ xs) (inj₁ ≡-refl) = (bagify xs , ≡-refl)  
ε-List-bCons-⇐ a (x ∷ xs) (inj₂ a∈xs) with ε-List-bCons-⇐ a xs a∈xs
... | (bg , bagify·xs≡a∷ʳbg) = (bCons x bg ,
                               ≡-trans (≡-cong (bCons x) bagify·xs≡a∷ʳbg)
                                  (|≈|-≡-cong (λ x → x) (prop-bCons-commute x a bg))) 

ε-List-permute : ∀ a xs ys → 
                ε-List a xs → permute ys xs → ε-List a ys
ε-List-permute a xs ys a∈xs (bg , bagify·xs≡bg , bagify·ys≡bg) 
    with ε-List-bCons-⇐ a xs a∈xs
... | (bg' , bagify·xs≡a∷ʳbg') =
   ε-List-bCons-⇒ a ys bg' (≡-trans bagify·ys≡bg (≡-trans (≡-sym bagify·xs≡bg)  bagify·xs≡a∷ʳbg')) 

okl○permute² : (okl ¿) ○ (idR ⨉ permute ⨉ permute) ⊑ (idR ⨉ permute ⨉ permute) ○ (okl ¿)
okl○permute² (.a , xs' , ys') (a , xs , ys)
    ((.a , .xs' , .ys') , 
          (≡-refl , xs'·bagify·xs , ys'·bagify·ys) , 
          ≡-refl , b∈xs'⇒b≤a , b∈ys'⇒a≤b) = 
  ((a , xs , ys) , 
       (≡-refl , (λ b b∈xs → b∈xs'⇒b≤a b (ε-List-permute b xs xs' b∈xs xs'·bagify·xs)) , 
                 (λ b b∈ys → b∈ys'⇒a≤b b (ε-List-permute b ys ys' b∈ys ys'·bagify·ys))) , 
       ≡-refl , xs'·bagify·xs , ys'·bagify·ys)

-- I thought they will be needed for proving bag-++.

ε-remove : ∀ {A} → {a : A} (xs : List A) → ε-List a xs → List A
ε-remove [] ()
ε-remove (a ∷ xs) (inj₁ ≡-refl) = xs 
ε-remove (x ∷ xs) (inj₂ a∈xs) = x ∷ ε-remove xs a∈xs

postulate remove-bg : ∀ {a} xs bg → (pf : bagify xs ≡ bCons a bg) → 
              bagify (ε-remove xs (ε-List-bCons-⇒ a xs bg pf)) ≡ bg

-- Why can't I prove this property? It seems that we need an operation to extract
-- an element out of a bag, with which we can define the join of two bags.

postulate bag-++ : ∀ xs xs' ys ys' → 
               bagify xs ≡ bagify xs' → bagify ys ≡ bagify ys' → bagify (xs ++ ys) ≡ bagify (xs' ++ ys')

{-
bag2-++ : ∀ xs xs' ys ys' → 
               bagify xs ≡ bagify xs' → 
               bagify ys ≡ bagify ys' → 
               bagify (xs ++ ys) ≡ bagify (xs' ++ ys')
bag2-++ [] [] ys ys' _ py = py 
bag2-++ [] (x ∷ xs) ys ys' px _ = {! !} -- both impossible
bag2-++ (x ∷ xs) [] ys ys' px _ = {! !} -- both impossible
bag2-++ (x ∷ xs) (x' ∷ xs') ys ys' px py = 
  let ih = bag2-++ xs xs' ys ys' {! !} py 
  in {!|≈|-≡-cong (bCons x) !}
-}

{-
  bagify ((x ∷ xs) ++ ys) ≡ bagify ((x' ∷ xs') ++ ys')
=
  bagify (x ∷ (xs ++ ys)) ≡ bagify (x' ∷ (xs' ++ ys'))
=
  bCons x (bagify (xs ++ ys)) ≡ bCons x' (bagify (xs' ++ ys'))

-}

∷⇒permute : ∀ a xs xs' → permute xs' xs → permute (a ∷ xs') (a ∷ xs)
∷⇒permute a xs xs' (bx , bagify·xs≡bx , bagify·xs'≡bx) = 
  (bCons a bx , ≡-cong (bCons a) bagify·xs≡bx , ≡-cong (bCons a) bagify·xs'≡bx) 

++⇒permute : ∀ xs xs' ys ys' → 
               permute xs' xs → permute ys' ys → permute (xs' ++ ys') (xs ++ ys)
++⇒permute xs xs' ys ys' 
   (._ , ≡-refl , bag·xs'≡bag·xs) (._ , ≡-refl , bag·ys'≡bag·ys) = 
  (bagify (xs ++ ys) , ≡-refl , bag-++ xs' xs ys' ys bag·xs'≡bag·xs bag·ys'≡bag·ys) 

join○permute² : fun join ○ (idR ⨉ permute ⨉ permute) ⊑ permute ○ fun join
join○permute² ._ (a , xs , ys)
    ((.a , xs' , ys'), (≡-refl , xs'·permute·xs , ys'·permute·ys), ≡-refl) = 
  ((xs ++ a ∷ ys) , ≡-refl , ++⇒permute xs xs' _ _ xs'·permute·xs (∷⇒permute a ys ys' ys'·permute·ys) ) 

fuse1 : (permute ○ fun join ○ (okl ¿)) ○ (idR ⨉ (permute ○ fun flatten) ⨉ (permute ○ fun flatten))
            ⊑ (permute ○ fun flatten) ○ (fork ○ (okt ¿))
fuse1 = 
   ⊑-begin
       (permute ○ fun join ○ (okl ¿)) ○ (idR ⨉ (permute ○ fun flatten) ⨉ (permute ○ fun flatten))
   ⊑⟨ ○-monotonic-r (⨉-monotonic id-elim-l ⊑-refl) ⟩
       (permute ○ fun join ○ (okl ¿)) ○ ((idR ○ idR) ⨉ (permute ○ fun flatten) ⨉ (permute ○ fun flatten))
   ⊑⟨ ○-monotonic-r ⨉3-functor-⊒ ⟩
       (permute ○ fun join ○ (okl ¿)) ○ (idR ⨉ permute ⨉ permute) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ○-assocr  ⟩
       permute ○ (fun join ○ (okl ¿)) ○ (idR ⨉ permute ⨉ permute) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ○-monotonic-r ○-assocr  ⟩
       permute ○ fun join ○ (okl ¿) ○ (idR ⨉ permute ⨉ permute) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ⇦-mono (permute ● fun join ‥) (okl ¿ ● (idR ⨉ permute ⨉ permute) ‥) 
          ((idR ⨉ permute ⨉ permute) ● okl ¿ ‥) okl○permute²  ⟩
       permute ○ fun join ○ (idR ⨉ permute ⨉ permute) ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ⇦-mono (permute ‥) (fun join ● (idR ⨉ permute ⨉ permute) ‥)
          (permute ● fun join ‥) join○permute²  ⟩
       permute ○ permute ○ fun join ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ⇦-mono-l (permute ● permute ‥) (permute ‥) permute-idem  ⟩
       permute ○ fun join ○ (okl ¿) ○ (idR ⨉ fun flatten ⨉ fun flatten)
   ⊑⟨ ○-monotonic-r joinok○flat²  ⟩
       permute ○ fun flatten ○ fork ○ (okt ¿)
   ⊑⟨ ○-assocl  ⟩
       (permute ○ fun flatten) ○ fork ○ (okt ¿)
   ⊑∎ 

fuse2 : nil ⊆ ℰ (permute ○ fun flatten) null
fuse2 .[] ≡-refl = (Null , ≡-refl , [] , ≡-refl , bNil , 
                      |≈|-≡-cong (λ x → x) |≈|-refl ,  |≈|-≡-cong (λ x → x) |≈|-refl) 

postulate m≰n⇒n≤m : ∀ m n → ((m ≤ n) → ⊥) → n ≤ m

split-okl : ∀ x xs → okl (x , split x xs)
split-okl x [] = ((λ _ bot → ⊥-elim bot) , λ _ bot → ⊥-elim bot)  
split-okl x (y ∷ xs) with split-okl x xs
... | ind with split x xs
...   | (ys , zs) with y ≤? x
split-okl x (y ∷ xs) | (b∈ys⇒b≤x , b∈zs⇒x≤b) | (ys , zs) | yes y≤x = 
   ((λ b → [_,_] (λ y≡b → ≡-subst (λ y → y ≤ x) y≡b y≤x) (b∈ys⇒b≤x b)) , b∈zs⇒x≤b) 
split-okl x (y ∷ xs) | (b∈ys⇒b≤x , b∈zs⇒x≤b) | (ys , zs) | no  y≰x = 
   (b∈ys⇒b≤x , λ b → [_,_] (λ y≡b → ≡-subst (λ y → x ≤ y) y≡b (m≰n⇒n≤m y x y≰x)) (b∈zs⇒x≤b b))

bCons-commute-++ : ∀ a xs ys → 
             bagify (xs ++ a ∷ ys) ≡ bagify (a ∷ xs ++ ys)
bCons-commute-++ a [] ys = ≡-refl 
bCons-commute-++ a (x ∷ xs) ys with bCons-commute-++ a xs ys
... | bag·xs++a∷ys≡bag·a∷xs++ys = 
       ≡-trans (≡-cong (bCons x) bag·xs++a∷ys≡bag·a∷xs++ys)
           (|≈|-≡-cong (λ x → x) (prop-bCons-commute x a _)) 

split-permute : ∀ x xs → permute xs (uncurry {_}{_}{λ _ → List Val} _++_ (split x xs))
split-permute x [] = (bNil , ≡-refl , ≡-refl) 
split-permute x (y ∷ xs) with split-permute x xs
split-permute x (y ∷ xs) | ind                           with split x xs
split-permute x (y ∷ xs) | ._ , ≡-refl , bg·xs≡bg·ys++zs | (ys , zs) with y ≤? x
... | yes _ = (bCons y (bagify (ys ++ zs)) , ≡-refl , ≡-cong (bCons y) bg·xs≡bg·ys++zs)  
... | no _ = (bCons y (bagify (ys ++ zs)) , bCons-commute-++ y ys zs , 
                    ≡-cong (bCons y) bg·xs≡bg·ys++zs) 

split-join-permute : ∀ x xs → permute (x ∷ xs) (join (x , split x xs))
split-join-permute x xs with split-permute x xs
... | (._ , bag·ys++zs≡bag·xs , ≡-refl) with split x xs
...   | (ys , zs) = (bagify (ys ++ x ∷ zs) , ≡-refl , 
            ≡-sym (≡-trans (bCons-commute-++ x ys zs) (≡-cong (bCons x) bag·ys++zs≡bag·xs))) 

part1 : (fun partition)˘ ○ fun inj₂ ⊑ permute ○ fun join ○ (okl ¿) 
part1 zs (a , xs , ys) (inj₁ tt , () , _) 
part1 [] (a , xs , ys) (._ , ≡-refl , ())
part1 (_ ∷ zs) (a , _) (._ , ≡-refl , pf) with pf 
part1 (.a ∷ zs) (a , ._) (._  , ≡-refl , pf) | ≡-refl = 
  (join (a , split a zs) , 
     ((a , split a zs) , (≡-refl , split-okl a zs) , ≡-refl) , 
       split-join-permute a zs) 

part2 : (λ b → isInj₁ (partition b)) ⊆ nil
part2 [] _ = ≡-refl 
part2 (x ∷ xs) ()

qsort-der : ∃ (λ f → ordered? ○ permute ⊒ fun f )
qsort-der = (_ ,  
   (⊒-begin
        ordered? ○ permute
    ⊒⟨ ○-monotonic-r id-intro-l ⟩
        ordered? ○ idR ○ permute
    ⊒⟨ ⇦-mono (ordered? ‥) (fun flatten ● (fun flatten)˘ ‥) (idR ‥) fun-simple ⟩
        ordered? ○ fun flatten ○ (fun flatten)˘ ○ permute
    ⊒⟨ ⇦-mono-l (fun flatten ● ordtree? ‥) (ordered? ● fun flatten  ‥) ordflatten  ⟩
        fun flatten ○ ordtree? ○ (fun flatten)˘ ○ permute
    ⊒⟨ ○-monotonic-r refine-converses ⟩
        fun flatten ○ ((permute ○ fun flatten) ○ ordtree?)˘          
    ⊒⟨ ○-monotonic-r (˘-monotonic-⇐ (foldT-fusion-⊒ (permute ○ fun flatten) fuse1 fuse2))  ⟩
        fun flatten ○ (foldT (permute ○ fun join ○ (okl ¿)) nil)˘
    ⊒⟨ ○-monotonic-r (˘-monotonic-⇐ (foldT-monotonic part1 part2))  ⟩
        fun flatten ○ (foldT ((fun partition)˘ ○ fun inj₂) (λ b → isInj₁ (partition b)))˘
    ⊒⟨ ○-monotonic-r (foldT-to-unfoldt partition partition-wf) ⟩
        fun flatten ○ fun (unfoldt partition partition-wf)
    ⊒⟨ fun○-⊒ ⟩
        fun (flatten ∘ unfoldt partition partition-wf)
    ⊒∎ ))
  where 
        refine-converses : ordtree? ○ (fun flatten)˘ ○ permute ⊒
                              ((permute ○ fun flatten) ○ ordtree?)˘ 
        refine-converses = 
           ⊒-begin 
               ordtree? ○ (fun flatten)˘ ○ permute
           ⊒⟨ ○-monotonic-l ordtree-˘-idem ⟩
               ordtree? ˘ ○ (fun flatten)˘ ○ permute
           ⊒⟨ ⇦-mono-r (ordtree? ˘ ● (fun flatten)˘  ‥) permute-˘-idem  ⟩
               ordtree? ˘ ○ (fun flatten)˘ ○ permute ˘
           ⊒⟨ ˘-○-distr3-⊑  ⟩
               (permute ○ fun flatten ○ ordtree?)˘ 
           ⊒⟨ ˘-monotonic-⇐ ○-assocr  ⟩
               ((permute ○ fun flatten) ○ ordtree?)˘
           ⊒∎
