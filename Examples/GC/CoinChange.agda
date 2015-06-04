module Examples.GC.CoinChange where

open import Level renaming (zero to lzero; _⊔_ to _⊔l_; suc to lsuc)
open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃)
open import Data.Nat using (ℕ; _+_; _≤_; _≥_; zero; suc; s≤s; z≤n)
open import Function using (const; _∘_)
open import Relation.Binary

open import Relations
open import Relations.Shrink
open import Relations.Function
open import Relations.Coreflexive
open import Relations.Converse
open import Relations.WellFound
open import Data.Generic
open import Data.Generic.Greedy
open import Data.Generic.Membership

open import Examples.GC.Relations
open import Examples.GC.List

open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

data Coin : Set where
  1p : Coin
  2p : Coin
  5p : Coin
  10p : Coin

val : Coin  → ℕ
val 1p = 1
val 2p = 2
val 5p = 5
val 10p = 10

_≤c_ : Coin ← Coin
_≤c_ = fun val ˘ ○ _≤_ ○ fun val

_≥c_ : Coin ← Coin
_≥c_ = _≤c_ ˘

liftc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → ((A × B) → C) → (Fst {i} {j} A × Snd {i} {j} B → C)
liftc f (fst x , snd y) = f (x , y)

liftC : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → (C ← (A × B) ⊣ lzero) → (C ← (Fst {i} {j} A × Snd {i} {j} B))
liftC R z (fst x , snd y) = R z (x , y)

sumc : ℕ ← List Coin
sumc =  ⦇ [ fun (const zero) ,
            fun (liftc plus) ○ bimapR _ (fun val) idR ] ⦈ 
  where plus : ℕ × ℕ → ℕ
        plus (m , n) = m + n

bound : Coin ← List Coin
bound = ⦇ [ fun (const 1p) ,
            liftC ((_≥c_ ○ fun proj₁) ⊓ (_≥c_ ○ fun proj₂)) ] ⦈

ordered? : List Coin ← List Coin
ordered? = ⦇ [ nil , liftC scons ] ⦈
  where scons : List Coin ← Coin × List Coin ⊣ lzero
        scons (In (inj₁ tt)) (c , cs) = ⊥
        scons (In (inj₂ ds)) (c , cs) = (In (inj₂ ds) ≡ c ∷ cs) × mapR ((Λ _≤c_ c) ¿) cs cs

ordered?-corefl : ordered? ⊑ idR
ordered?-corefl .(In (inj₁ tt)) (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , .(inj₁ tt) , refl , refl)) = refl
ordered?-corefl ds (In (inj₁ tt)) (.(inj₂ cs) , () , inj₂ (cs , refl , _))
ordered?-corefl ds (In (inj₂ (fst c , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , _))
ordered?-corefl ds (In (inj₂ (fst c , snd cs))) (.(inj₂ (fst c , snd cs')) , (refl , ord) , inj₂ ((fst .c , snd cs') , refl , scons)) with ordered?-corefl cs' cs ord
ordered?-corefl (In (inj₁ tt)) (In (inj₂ (fst c , snd cs))) (.(inj₂ (fst c , snd cs)) , (refl , ord) , inj₂ ((fst .c , snd .cs) , refl , ())) | refl
ordered?-corefl (In (inj₂ .(fst c , snd cs))) (In (inj₂ (fst c , snd cs))) (.(inj₂ (fst c , snd cs)) , (refl , ord) , inj₂ ((fst .c , snd .cs) , refl , refl , all)) | refl = refl

S : (ℕ × Coin) ← ⟦ ListF ⟧ Coin (ℕ × Coin)
S = [ ⟨ fun (const 0) , Π ⟩ , liftC ⟨ plus , raise ⟩ ]
  where plus : ℕ ← (Coin × ℕ × Coin)
        plus m (c , n , b) = (c ≡ b) × (m ≡ val c + n)
        
        raise : Coin ← (Coin × ℕ × Coin)
        raise b' (c , n , b) = (b' ≥c c) × (c ≥c b)

sumbound : (ℕ × Coin) ← List Coin
sumbound = ⦇ S ⦈

Q : ⟦ ListF ⟧ Coin (ℕ × Coin) ← ⟦ ListF ⟧ Coin (ℕ × Coin)
Q (inj₁ tt) (inj₁ tt) = ⊤
Q (inj₁ tt) (inj₂ y) = ⊥
Q (inj₂ x) (inj₁ tt) = ⊥
Q (inj₂ (fst c , snd x)) (inj₂ (fst d , snd y)) = c ≥c d

-- some properties of ≤

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : ∀ {n m} → n ≤ m → n ≤ suc m
≤-step {zero} x = z≤n
≤-step {suc n} {zero} ()
≤-step {suc n} {suc m} (s≤s n≤m) = s≤s (≤-step n≤m)

≤-steps : ∀ {m} → (k : ℕ) → m ≤ k + m
≤-steps zero = ≤-refl
≤-steps (suc k) = ≤-step (≤-steps k)

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n _ = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤c-refl : ∀ {c} → c ≤c c
≤c-refl = (_ , (_ , refl , ≤-refl) , refl)

≤c-trans : ∀ {c d e} → c ≤c d → d ≤c e → c ≤c e
≤c-trans {c}{d}{e} (._ , (._ , refl , c≤d) , refl) (._ , (._ , refl , d≤e) , refl) = (val c , (val e , refl , ≤-trans c≤d d≤e) , refl)

1≱2 : 1 ≥ 2 → ⊥
1≱2 (s≤s ())


-- ordering between coins

1p≥1p : 1p ≥c 1p
1p≥1p = (1 , (1 , refl , s≤s z≤n) , refl)

2p≥1p : 2p ≥c 1p
2p≥1p = (1 , (2 , refl , s≤s z≤n) , refl)

2p≥2p : 2p ≥c 2p
2p≥2p = (2 , (2 , refl , ≤-refl) , refl)

5p≥1p : 5p ≥c 1p
5p≥1p = (1 , (5 , refl , s≤s z≤n) , refl)

5p≥2p : 5p ≥c 2p
5p≥2p = (2 , (5 , refl , s≤s (s≤s z≤n)) , refl)

5p≥5p : 5p ≥c 5p
5p≥5p = (5 , (5 , refl , ≤-refl) , refl)

10p≥1p : 10p ≥c 1p
10p≥1p = (1 , (10 , refl , s≤s z≤n) , refl)

10p≥2p : 10p ≥c 2p
10p≥2p = (2 , (10 , refl , s≤s (s≤s z≤n)) , refl)

10p≥5p : 10p ≥c 5p
10p≥5p = (5 , (10 , refl , s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) , refl)

10p≥10p : 10p ≥c 10p
10p≥10p = (10 , (10 , refl , ≤-refl) , refl)

-- 1p and 10p are the lowerbound and upperbound of all coins
1p-lb : ∀ {c} → 1p ≤c c
1p-lb {1p} = 1p≥1p
1p-lb {2p} = 2p≥1p
1p-lb {5p} = 5p≥1p
1p-lb {10p} = 10p≥1p

10p-ub : ∀ {c} → c ≤c 10p
10p-ub {1p} = 10p≥1p
10p-ub {2p} = 10p≥2p
10p-ub {5p} = 10p≥5p
10p-ub {10p} = 10p≥10p



1p≱2p : (1p ≥c 2p) → ⊥
1p≱2p (.2 , (.1 , refl , s≤s ()) , refl)

1p≱5p : (1p ≥c 5p) → ⊥
1p≱5p (.5 , (.1 , refl , s≤s ()) , refl)

2p≱5p : (2p ≥c 5p) → ⊥
2p≱5p (.5 , (.2 , refl , s≤s (s≤s ())) , refl)

1p≱10p : (1p ≥c 10p) → ⊥
1p≱10p (.10 , (.1 , refl , s≤s ()) , refl)

2p≱10p : (2p ≥c 10p) → ⊥
2p≱10p (.10 , (.2 , refl , s≤s (s≤s ())) , refl)

5p≱10p : (5p ≥c 10p) → ⊥
5p≱10p (.10 , (.5 , refl , s≤s (s≤s (s≤s (s≤s (s≤s ()))))) , refl)



extract : ∀ {c c' n cs} → sumbound (val c + n , c') (c ∷ cs) → sumbound (n , c) cs
extract (.(inj₁ tt) , () , inj₁ (tt , refl , _))
extract (.(inj₂ (fst 1p , snd (m , 1p))) , (refl , sb) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , refl) , raise)) = sb

out-of-bound : ∀ {c d n cs} → (d ≥c c → ⊥) → sumbound (n , d) (c ∷ cs) → ⊥
out-of-bound c≰d (.(inj₁ tt) , () , inj₁ (tt , refl , _))
out-of-bound c≰d (.(inj₂ (fst c , snd (proj₁ , c))) , (refl , proj₃) , inj₂ ((fst c , snd (proj₁ , .c)) , refl , (refl , proj₅) , c≤d , proj₄)) = c≰d c≤d

out-of-sum : ∀ {c d n cs} → (n ≥ val c → ⊥) → sumbound (n , d) (c ∷ cs) → ⊥
out-of-sum n≱c (.(inj₁ tt) , () , inj₁ (tt , refl , _))
out-of-sum n≱c (.(inj₂ (fst 1p , snd (m , 1p))) , (refl , sb) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , refl) , raise)) = n≱c (s≤s Data.Nat.z≤n)
out-of-sum n≱c (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s Data.Nat.z≤n))
out-of-sum n≱c (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s (s≤s (s≤s (s≤s Data.Nat.z≤n)))))
out-of-sum n≱c (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s Data.Nat.z≤n))))))))))

lemma-1p : ∀ {n} → (m : ℕ) → (cs : List Coin) → m ≤ n → sumbound (n , 1p) cs → ∃ (λ ds → ds ⊴ cs × sumbound (m , 1p) ds)
lemma-1p zero cs m≤n sb = ([] , ⊴-nil , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)))
lemma-1p (suc m) (In (inj₁ tt)) () (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
lemma-1p (suc m) (In (inj₁ tt)) m≤n (.(inj₂ (fst x , snd x₁)) , () , inj₂ ((fst x , snd x₁) , refl , proj₆))
lemma-1p (suc m) (In (inj₂ (fst 1p , snd cs))) m≤n (.(inj₁ tt) , () , inj₁ (tt , refl , _))
lemma-1p (suc m) (In (inj₂ (fst 1p , snd cs))) (s≤s m≤n) (._ , (refl , sb) , inj₂ ((fst .1p , snd (n , .1p)) , refl , (refl , refl) , raise)) with lemma-1p m cs m≤n sb
... | (ds , leq , sb') = (1p ∷ ds , ⊴-cons leq , inj₂ (fst 1p , snd (m , 1p)) , (refl , sb') , inj₂ (_ , refl , ((refl , refl) , raise)))
lemma-1p (suc m) (In (inj₂ (fst 2p , snd cs))) m≤n sb with out-of-bound 1p≱2p sb
... | ()
lemma-1p (suc m) (In (inj₂ (fst 5p , snd cs))) m≤n sb with out-of-bound 1p≱5p sb
... | ()
lemma-1p (suc m) (In (inj₂ (fst 10p , snd cs))) m≤n sb with out-of-bound 1p≱10p sb
... | ()

lemma-nil : ∀ {n c} → 1 ≤ n → sumbound (n , c) [] → ⊥
lemma-nil () (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
lemma-nil n≥1 (.(inj₂ proj₃) , () , inj₂ (proj₃ , refl , proj₅))

relax' : ∀ {n c d} → d ≥c c → (cs : List Coin) → sumbound (n , c) cs → sumbound (n , d) cs
relax' c≤d (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) = (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
relax' c≤d (In (inj₁ tt)) (.(inj₂ (fst x , proj₄)) , () , inj₂ ((fst x , proj₄) , refl , proj₆)) 
relax' c≤d (In (inj₂ (fst c' , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , _))
relax' {c = c} {d} c≤d (In (inj₂ (fst c' , snd cs))) (.(inj₂ (fst c' , snd (m , c'))) , (refl , sb) , inj₂ ((fst .c' , snd (m , .c')) , refl , (refl , refl) , c'≤c , c'≤c'))
   = (inj₂ (fst c' , snd (m , c')) , (refl , sb) , inj₂ (_ , refl , (refl , refl) , (≤c-trans {c'}{c}{d} c'≤c c≤d , c'≤c')))

relax : ∀ {m c d cs} → d ≥c c → ∃ (λ ds → ds ⊴ cs × sumbound (m , c) ds) → ∃ (λ ds → ds ⊴ cs × sumbound (m , d) ds)
relax c≤d (ds , leq , sb) = (ds , leq , (relax' c≤d _ sb))

tighten : ∀ {n c d} → (cs : List Coin) → sumbound (n , d) (c ∷ cs) → sumbound (n , c) (c ∷ cs)
tighten cs (.(inj₁ tt) , () , inj₁ (tt , refl , _))
tighten cs (.(inj₂ (fst c , snd (m , c))) , (refl , sb) , inj₂ ((fst c , snd (m , .c)) , refl , (refl , refl) , c≤d , c≤c))
   = (inj₂ (fst c , snd (m , c)) , (refl , sb) , inj₂ (_ , refl , (refl , refl) , c≤c , c≤c))

add-1p : ∀ {m c} → (cs : List Coin) → sumbound (m , 2p) cs → ∃ (λ ds → ds ⊴ (c ∷ cs) × sumbound (suc m , 2p) ds)
add-1p (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) = relax {c = 1p} 2p≥1p (1p ∷ [] , ⊴-cons ⊴-refl' , inj₂ (fst 1p , snd (0 , 1p)) , (refl , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))) , inj₂ (_ , refl , (refl , refl) , (1p≥1p , 1p≥1p)))
add-1p (In (inj₁ tt)) (.(inj₂ proj₃) , () , inj₂ (proj₃ , refl , proj₅)) 
add-1p (In (inj₂ (fst c , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , proj₄))
add-1p (In (inj₂ (fst 1p , snd cs))) sb = relax {c = 1p} 2p≥1p (1p ∷ (1p ∷ cs) , ⊴-cons ⊴-refl' , inj₂ (fst 1p , snd (_ , 1p)) , (refl , tighten cs sb) , inj₂ ((fst 1p , snd (_ , 1p)) , refl , (refl , refl) , 1p≥1p , 1p≥1p))
add-1p (In (inj₂ (fst 2p , snd cs))) (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst .2p , snd (m , .2p)) , refl , (refl , refl) , 2p≥c , c≥c)) with add-1p {c = 2p} cs sb
... | (ds , leq , dsb) = (2p ∷ ds , ⊴-cons leq , inj₂ (fst 2p , snd (_ , 2p)) , (refl , dsb) , inj₂ (_ , refl , (refl , refl) , (2p≥2p , 2p≥2p)))
add-1p (In (inj₂ (fst 5p , snd cs))) (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst .5p , snd (m , .5p)) , refl , (refl , refl) , 2p≥c , c≥c)) with 2p≱5p 2p≥c
... | ()
add-1p (In (inj₂ (fst 10p , snd cs))) (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst .10p , snd (m , .10p)) , refl , (refl , refl) , 2p≥c , c≥c)) with 2p≱10p 2p≥c
... | ()


greedy-lemma : (c d : Coin) → (n m : ℕ) → (cs : List Coin) → c ≤c d → val c + n ≡ val d + m → sumbound (n , c) cs → ∃(λ ds → ds ⊴ cs × sumbound (m , d) ds)
greedy-lemma 1p 1p n .n cs c≤d refl sb = lemma-1p n cs ≤-refl sb
greedy-lemma 1p 2p ._ m cs c≤d refl sb = relax 2p≥1p (lemma-1p m cs (≤-steps 1) sb)
greedy-lemma 1p 5p ._ m cs c≤d refl sb = relax 5p≥1p (lemma-1p m cs (≤-steps 4) sb)
greedy-lemma 1p 10p ._ m cs c≤d refl sb = relax 10p≥1p (lemma-1p m cs (≤-steps 9) sb)
greedy-lemma 2p 1p n m cs c≤d eq sb with 1p≱2p c≤d
greedy-lemma 2p 1p n m cs c≤d eq sb | ()
greedy-lemma 2p 2p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)
greedy-lemma 2p 5p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 2p 5p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 5p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 3) (tighten cs sb))
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' with lemma-nil (s≤s z≤n) sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl sb | sb' with extract sb'
...| sb'' = (cs , ⊴-step (⊴-step ⊴-refl') , (relax' 5p≥1p cs sb''))
greedy-lemma 2p 5p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with out-of-sum 1≱2 sb'
greedy-lemma 2p 5p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ (suc m) (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with add-1p {c = 2p} cs (extract sb')
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 5p≥2p ds dsb)
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱5p sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱10p sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with out-of-bound 2p≱5p sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb with out-of-bound 2p≱10p sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 2p 10p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 10p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 8) (tighten cs sb))
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' with lemma-nil (s≤s z≤n) sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl sb | sb' with lemma-1p m (1p ∷ cs) (≤-steps 6) (tighten cs sb')
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with extract sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' with lemma-nil (s≤s z≤n) sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs))))))))) c≤d refl sb | sb' | sb'' with lemma-1p m (1p ∷ cs) (≤-steps 4) (tighten cs sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with extract sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt))))))))))) c≤d refl sb | sb' | sb'' | sb''' with lemma-nil (s≤s z≤n) sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with lemma-1p m (1p ∷ cs) (≤-steps 2) (tighten cs sb''')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step (⊴-step leq)) , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb'''
    = (cs , ⊴-step (⊴-step (⊴-step (⊴-step ⊴-refl'))) , relax' 10p≥2p cs (extract sb'''))
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with out-of-bound 2p≱5p sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with out-of-bound 2p≱10p sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱5p sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱10p sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱5p sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱10p sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with out-of-bound 2p≱5p sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb with out-of-bound 2p≱10p sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb | ()
greedy-lemma 5p 1p n m cs c≤d eq sb with 1p≱5p c≤d
greedy-lemma 5p 1p n m cs c≤d eq sb | ()
greedy-lemma 5p 2p n m cs c≤d eq sb with 2p≱5p c≤d
greedy-lemma 5p 2p n m cs c≤d eq sb | ()
greedy-lemma 5p 5p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)
greedy-lemma 5p 10p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 5p 10p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 10p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 5) (tighten cs sb))
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl _ | sb with lemma-nil (s≤s Data.Nat.z≤n) sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl _ | sb with lemma-1p m (1p ∷ cs) (≤-steps 3) (tighten cs sb)
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 10p≥1p ds dsb)
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with extract sb'
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' with lemma-nil (s≤s z≤n) sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs))))))))) c≤d refl sb | sb' | sb'' with lemma-1p m (1p ∷ cs) (≤-steps 1) (tighten cs sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥1p ds dsb)
greedy-lemma 5p 10p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-sum 1≱2 sb''
greedy-lemma 5p 10p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ (suc m) (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with add-1p {c = 2p} cs (extract sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥2p ds dsb)
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱5p sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱10p sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl _ | sb with out-of-bound 2p≱5p sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl _ | sb with out-of-bound 2p≱10p sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with extract sb
... | sb' = (cs , ⊴-step ⊴-refl' , (relax' 10p≥5p cs sb'))
greedy-lemma 5p 10p n m (In (inj₂ (fst 10p , snd cs))) c≤d eq sb with out-of-bound 5p≱10p sb
greedy-lemma 5p 10p n m (In (inj₂ (fst 10p , snd cs))) c≤d eq sb | ()
greedy-lemma 10p 1p n m cs c≤d eq sb with 1p≱10p c≤d
greedy-lemma 10p 1p n m cs c≤d eq sb | ()
greedy-lemma 10p 2p n m cs c≤d eq sb with 2p≱10p c≤d
greedy-lemma 10p 2p n m cs c≤d eq sb | ()
greedy-lemma 10p 5p n m cs c≤d eq sb with 5p≱10p c≤d
greedy-lemma 10p 5p n m cs c≤d eq sb | ()
greedy-lemma 10p 10p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)


{-
  sumc xs = n ≡ xs ⊵ coin-change n
  coin-change ⊑ (sumc ˘) ↾ (_⊴_)
  coin-change ⊑ ⦇[ zero, plus ∘ (val × id) ]⦈ ˘ ↾ (_⊴_)

  coin-change = ⦇([ zero , plus ∘ (val × id) ] ˘ ↾ Q) ˘⦈ ˘
    where Q = (id + _≤c_ × id)
-}



sumbound⇒all : ∀ {n d} → (cs : List Coin) → sumbound (n , d) cs →  mapR ((Λ _≤c_ d) ¿) cs cs
sumbound⇒all (In (inj₁ tt)) sb = (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , []-nil))
sumbound⇒all (In (inj₂ (fst c , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , _))
sumbound⇒all {d = d} (In (inj₂ (fst c , snd cs))) (.(inj₂ (fst c , snd (m , c))) , (refl , sb) , inj₂ ((fst .c , snd (m , .c)) , refl , (refl , eq) , d≥c , c≥c))
  = (inj₂ (fst c , snd cs) , (refl , (sumbound⇒all cs (relax' {d = d} d≥c cs sb))) , inj₂ (_ , refl , _ , ((refl , d≥c) , refl) , ∷-cons))

tighten-by-all : ∀ {n d e} → (cs : List Coin) → sumbound (n , d) cs → mapR ((Λ _≤c_ e) ¿) cs cs → sumbound (n , e) cs
tighten-by-all (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) all = (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
tighten-by-all (In (inj₁ tt)) (.(inj₂ m) , () , inj₂ (m , refl , _)) all
tighten-by-all (In (inj₂ (fst c , snd cs))) sb (.(inj₁ tt) , () , inj₁ (tt , refl , _))
tighten-by-all {e = e} (In (inj₂ (fst c , snd cs))) sb (.(inj₂ (fst c , snd cs)) , (refl , all) , inj₂ ((fst .c , snd .cs) , refl , .(fst c , snd cs) , ((refl , c≤e) , refl) , .(inj₂ (fst c , snd cs)) , refl , refl)) = relax' c≤e (c ∷ cs) (tighten cs sb)

sumbound-universal₁-⊑ : fun proj₁ ○ sumbound ⊑ sumc ○ ordered?
sumbound-universal₁-⊑ .0 (In (inj₁ tt)) ((.0 , d) , (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) , refl) = ([] , (inj₁ tt , Data.Unit.tt , inj₁ (tt , (refl , []-nil))) , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl)))
sumbound-universal₁-⊑ n (In (inj₁ tt)) ((.n , d) , (.(inj₂ proj₂) , () , inj₂ (proj₂ , refl , proj₄)) , refl)
sumbound-universal₁-⊑ n (In (inj₂ (fst c , snd cs))) ((.n , d) , (.(inj₁ tt) , () , inj₁ (tt , refl , _)) , refl)
sumbound-universal₁-⊑ n (In (inj₂ (fst c , snd cs))) ((.n , d) , (.(inj₂ (fst c , snd (m , c))) , (refl , sb) , inj₂ ((fst .c , snd (m , .c)) , refl , (refl , eq) , d≥c , c≥c)) , refl) with sumbound-universal₁-⊑ m cs ((m , c) , sb , refl)
... | (cs' , ord-cs , sum-cs) with ordered?-corefl cs' cs ord-cs
sumbound-universal₁-⊑ n (In (inj₂ (fst c , snd cs))) ((.n , d) , (.(inj₂ (fst c , snd (m , c))) , (refl , sb) , inj₂ ((fst .c , snd (m , .c)) , refl , (refl , eq) , d≥c , c≥c)) , refl) | (.cs , ord-cs , sum-cs) | refl = (c ∷ cs , (inj₂ (fst c , snd cs) , (refl , ord-cs) , inj₂ (_ , refl , refl , (sumbound⇒all cs sb))) , (inj₂ (fst c , snd m) , (refl , sum-cs) , inj₂ (_ , refl , (fst (val c) , snd m) , (refl , refl) , sym eq)))

sumbound-universal₁-⊒ : fun proj₁ ○ sumbound ⊒ sumc ○ ordered?
sumbound-universal₁-⊒ .0 (In (inj₁ tt)) (.(In (inj₁ tt)) , (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , .(inj₁ tt) , refl , refl)) , .(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl)) = ((0 , 10p) , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) , refl)
sumbound-universal₁-⊒ n (In (inj₁ tt)) (.(In (inj₁ tt)) , (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , .(inj₁ tt) , refl , refl)) , .(inj₂ proj₃) , () , inj₂ (proj₃ , refl , proj₅))
sumbound-universal₁-⊒ n (In (inj₁ tt)) (cs , (.(inj₂ proj₄) , () , inj₂ (proj₄ , refl , proj₆)) , sum)
sumbound-universal₁-⊒ n (In (inj₂ (fst c , snd cs))) (cs' , (.(inj₁ tt) , () , inj₁ (tt , refl , _)) , sum)
sumbound-universal₁-⊒ n (In (inj₂ (fst c , snd cs))) (In (inj₁ tt) , (.(inj₂ (fst c , snd cs')) , (refl , proj₃) , inj₂ ((fst .c , snd cs') , refl , ())) , sum)
sumbound-universal₁-⊒ n (In (inj₂ (fst c , snd cs))) (In (inj₂ .(fst c , snd cs')) , (.(inj₂ (fst c , snd cs')) , (refl , ord) , inj₂ ((fst .c , snd cs') , refl , refl , all)) , .(inj₁ tt) , () , inj₁ (tt , refl , proj₅))
sumbound-universal₁-⊒ n (In (inj₂ (fst c , snd cs))) (In (inj₂ .(fst c , snd cs')) , (.(inj₂ (fst c , snd cs')) , (refl , ord) , inj₂ ((fst .c , snd cs') , refl , refl , all)) , .(inj₂ (fst c , snd m)) , (refl , sum) , inj₂ ((fst .c , snd m) , refl , (fst .(val c) , snd .m) , (refl , refl) , eq)) with ordered?-corefl cs' cs ord
sumbound-universal₁-⊒ n (In (inj₂ (fst c , snd cs))) (In (inj₂ .(fst c , snd cs)) , (._ , (refl , ord) , inj₂ ((fst .c , snd .cs) , refl , refl , all)) ,.(inj₂ (fst c , snd m)) , (refl , sum) , inj₂ ((fst .c , snd m) , refl , (fst .(val c) , snd .m) , (refl , refl) , eq)) | refl with sumbound-universal₁-⊒ m cs (cs , ord , sum)
... | ((.m , d) , sb , refl) = ((n , c) , (inj₂ (fst c , snd (m , c)) , (refl , tighten-by-all cs sb all) , inj₂ (_ , refl , (refl , sym eq) , ≤c-refl {c} , ≤c-refl {c})) , refl)


coin-change-der : ∃(λ f → fun f ⊑ (sumc ○ ordered?) ˘ ↾ _⊴_)
coin-change-der = _ , 
                (⊒-begin
     (sumc ○ ordered?) ˘ ↾ _⊴_
   ⊒⟨ proj₂ (↾-subst ((sumc ○ ordered?) ˘) ((fun proj₁ ○ sumbound) ˘) _⊴_ (˘-monotonic-⇐ sumbound-universal₁-⊒ , ˘-monotonic-⇐ sumbound-universal₁-⊑)) ⟩
     (fun proj₁ ○ sumbound) ˘ ↾ _⊴_
   ⊒⟨ proj₂ (↾-subst ((fun proj₁ ○ sumbound) ˘) (sumbound ˘ ○ fun proj₁ ˘) _⊴_ ((˘-○-distr-⊑ _ _) , (˘-○-distr-⊒ _ _))) ⟩
     (sumbound ˘ ○ fun proj₁ ˘) ↾ _⊴_
   ⊒⟨ proj₂ (↾-subst _ _ _⊴_ (proj₁˘⊑ten , (○-monotonic-r ten⊑proj₁˘))) ⟩
     (sumbound ˘ ○ fun ten) ↾ _⊴_
   ⊒⟨ ↾-fun-absorption (sumbound ˘) ten _⊴_ ⟩
     (sumbound ˘ ↾ _⊴_) ○ fun ten
   ⊒⟨ ○-monotonic-l (proj₂ (↾-subst (sumbound ˘) (idR ○ sumbound ˘) _⊴_ (id-elim-l , id-intro-l))) ⟩
     ((idR ○ sumbound ˘) ↾ _⊴_) ○ fun ten
   ⊒⟨ ○-monotonic-l (proj₂ (↾-subst (idR ○ sumbound ˘) (⦇ fun In ⦈ ○ sumbound ˘) _⊴_
       (○-monotonic-l (idR-foldR-⊑ ListF) , ○-monotonic-l (idR-foldR-⊒ ListF)))) ⟩
     ((⦇ fun In ⦈ ○ (sumbound ˘)) ↾ _⊴_) ○ fun ten
   ⊒⟨ ○-monotonic-l (greedy-ana-cxt ⊴-isPreorder fun-simple mono-cond greedy-cond) ⟩
     (⦇ fun In ⦈ ○ ⦇ (S ˘ ↾ Q) ˘ ⦈ ˘) ○ fun ten
   ⊒⟨ ○-monotonic-l (○-monotonic-r (˘-monotonic-⇐ (foldR-monotonic ListF (fun pick-max ˘) ((S ˘ ↾ Q) ˘) (˘-monotonic-⇐ pick-max⊑S˘↾Q)))) ⟩
     (⦇ fun In ⦈ ○ ⦇ (fun pick-max) ˘ ⦈ ˘) ○ fun ten
   ⊒⟨ ○-monotonic-l (proj₂ (hylo-refine In pick-max wf)) ⟩
     fun (hylo In pick-max wf) ○ fun ten
   ⊒⟨ fun○-⊒ ⟩
     fun (hylo In pick-max wf ∘ ten)
   ⊒∎)
 where
   ten : ℕ → ℕ × Coin
   ten n = (n , 10p)
   
   ten⊑proj₁˘ : fun ten ⊑ fun proj₁ ˘
   ten⊑proj₁˘ .(n , 10p) n refl = refl

   proj₁˘⊑ten : sumbound ˘ ○ fun proj₁ ˘ ⊑ sumbound ˘ ○ fun ten
   proj₁˘⊑ten cs n ((.n , c) , refl , sb) = ((n , 10p) , refl , relax' (10p-ub {c}) cs sb)


   pick-max : (ℕ × Coin) → ⟦ ListF ⟧ Coin (ℕ × Coin)
   pick-max (zero , c) = inj₁ tt
   pick-max (suc n , 1p) = inj₂ (fst 1p , snd (n , 1p))
   pick-max (1 , 2p) = inj₂ (fst 1p , snd (0 , 1p))
   pick-max (suc (suc n) , 2p) = inj₂ (fst 2p , snd (n , 2p))
   pick-max (1 , 5p) = inj₂ (fst 1p , snd (0 , 1p))
   pick-max (2 , 5p) = inj₂ (fst 2p , snd (0 , 2p))
   pick-max (3 , 5p) = inj₂ (fst 2p , snd (1 , 2p))
   pick-max (4 , 5p) = inj₂ (fst 2p , snd (2 , 2p))
   pick-max (suc (suc (suc (suc (suc n)))) , 5p) = inj₂ (fst 5p , snd (n , 5p))
   pick-max (1 , 10p) = inj₂ (fst 1p , snd (0 , 1p))
   pick-max (2 , 10p) = inj₂ (fst 2p , snd (0 , 2p))
   pick-max (3 , 10p) = inj₂ (fst 2p , snd (1 , 2p))
   pick-max (4 , 10p) = inj₂ (fst 2p , snd (2 , 2p))
   pick-max (5 , 10p) = inj₂ (fst 5p , snd (0 , 5p))
   pick-max (6 , 10p) = inj₂ (fst 5p , snd (1 , 5p))
   pick-max (7 , 10p) = inj₂ (fst 5p , snd (2 , 5p))
   pick-max (8 , 10p) = inj₂ (fst 5p , snd (3 , 5p))
   pick-max (9 , 10p) = inj₂ (fst 5p , snd (4 , 5p))
   pick-max (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) , 10p) = inj₂ (fst 10p , snd (n , 10p))
   
   pick-max⊑S˘ : (fun pick-max) ⊑ S ˘
   pick-max⊑S˘ .(inj₁ tt) (zero , c) refl = inj₁ (tt , refl , refl , Data.Unit.tt)
   pick-max⊑S˘ .(inj₂ (fst 1p , snd (n , 1p))) (suc n , 1p) refl = inj₂ (_ , refl , (refl , refl) , (1p≥1p , 1p≥1p))
   pick-max⊑S˘ .(inj₂ (fst 1p , snd (0 , 1p))) (1 , 2p) refl = inj₂ (_ , refl , (refl , refl) , (2p≥1p , 1p≥1p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (n , 2p))) (suc (suc n) , 2p) refl = inj₂ (_ , refl , (refl , refl) , (2p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 1p , snd (0 , 1p))) (1 , 5p) refl = inj₂ (_ , refl , (refl , refl) , (5p≥1p , 1p≥1p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (0 , 2p))) (2 , 5p) refl = inj₂ (_ , refl , (refl , refl) , (5p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (1 , 2p))) (3 , 5p) refl = inj₂ (_ , refl , (refl , refl) , (5p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (2 , 2p))) (4 , 5p) refl = inj₂ (_ , refl , (refl , refl) , (5p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (n , 5p))) (suc (suc (suc (suc (suc n)))) , 5p) refl = inj₂ (_ , refl , (refl , refl) , (5p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 1p , snd (0 , 1p))) (1 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥1p , 1p≥1p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (0 , 2p))) (2 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (1 , 2p))) (3 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 2p , snd (2 , 2p))) (4 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥2p , 2p≥2p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (0 , 5p))) (5 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (1 , 5p))) (6 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (2 , 5p))) (7 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (3 , 5p))) (8 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 5p , snd (4 , 5p))) (9 , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥5p , 5p≥5p))
   pick-max⊑S˘ .(inj₂ (fst 10p , snd (n , 10p))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) , 10p) refl = inj₂ (_ , refl , (refl , refl) , (10p≥10p , 10p≥10p))
   
   pick-maxS⊑Q : (fun pick-max) ○ S ⊑ Q
   pick-maxS⊑Q .(inj₁ tt) .(inj₁ tt) ((.0 , c) , inj₁ (tt , refl , refl , Data.Unit.tt) , refl) = Data.Unit.tt
   pick-maxS⊑Q .(inj₁ tt) x ((zero , c) , inj₂ ((fst 1p , snd (m , .1p)) , eq , (refl , ()) , raise) , refl)
   pick-maxS⊑Q .(inj₁ tt) x ((zero , c) , inj₂ ((fst 2p , snd (m , .2p)) , eq , (refl , ()) , raise) , refl)
   pick-maxS⊑Q .(inj₁ tt) x ((zero , c) , inj₂ ((fst 5p , snd (m , .5p)) , eq , (refl , ()) , raise) , refl)
   pick-maxS⊑Q .(inj₁ tt) x ((zero , c) , inj₂ ((fst 10p , snd (m , .10p)) , eq , (refl , ()) , raise) , refl)
   pick-maxS⊑Q ._ ._ ((suc n , 1p) , inj₂ ((fst d , snd (m , .d)) , refl , (refl , eq) , 1p≥d , d≥d) , refl) = 1p≥d
   pick-maxS⊑Q ._ ._ ((1 , 2p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 2p≥d , d≥d) , refl) = 1p≥1p
   pick-maxS⊑Q ._ ._ ((1 , 2p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , ()) , 2p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 2p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 2p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 2p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 2p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((suc (suc n) , 2p) , inj₂ ((fst d , snd (m , .d)) , refl , (refl , eq) , 2p≥d , d≥d) , refl) = 2p≥d
   pick-maxS⊑Q ._ ._ ((suc zero , 5p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 1p≥1p
   pick-maxS⊑Q ._ ._ ((1 , 5p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 5p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 5p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((2 , 5p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((2 , 5p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((2 , 5p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((2 , 5p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((3 , 5p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((3 , 5p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((3 , 5p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((3 , 5p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((4 , 5p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((4 , 5p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((4 , 5p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((4 , 5p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 5p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((suc (suc (suc (suc (suc n)))) , 5p) , inj₂ ((fst d , snd (m , .d)) , refl , (refl , eq) , 5p≥d , d≥d) , refl) = 5p≥d
   pick-maxS⊑Q ._ ._ ((1 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 1p≥1p
   pick-maxS⊑Q ._ ._ ((1 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((1 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((2 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((2 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((2 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((2 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((3 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((3 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((3 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((3 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((4 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥1p
   pick-maxS⊑Q ._ ._ ((4 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 2p≥2p
   pick-maxS⊑Q ._ ._ ((4 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((4 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((5 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥1p
   pick-maxS⊑Q ._ ._ ((5 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥2p
   pick-maxS⊑Q ._ ._ ((5 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥5p
   pick-maxS⊑Q ._ ._ ((5 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((6 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥1p
   pick-maxS⊑Q ._ ._ ((6 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥2p
   pick-maxS⊑Q ._ ._ ((6 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥5p
   pick-maxS⊑Q ._ ._ ((6 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((7 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥1p
   pick-maxS⊑Q ._ ._ ((7 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥2p
   pick-maxS⊑Q ._ ._ ((7 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥5p
   pick-maxS⊑Q ._ ._ ((7 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((8 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥1p
   pick-maxS⊑Q ._ ._ ((8 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥2p
   pick-maxS⊑Q ._ ._ ((8 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥5p
   pick-maxS⊑Q ._ ._ ((8 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((9 , 10p) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥1p
   pick-maxS⊑Q ._ ._ ((9 , 10p) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥2p
   pick-maxS⊑Q ._ ._ ((9 , 10p) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 5p≥5p
   pick-maxS⊑Q ._ ._ ((9 , 10p) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , ()) , 10p≥d , d≥d) , refl)
   pick-maxS⊑Q ._ ._ ((suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) , 10p) , inj₂ ((fst d , snd (m , .d)) , refl , (refl , eq) , 10p≥d , d≥d) , refl) = 10p≥d
   
   pick-max⊑S˘↾Q : fun pick-max ⊑ S ˘ ↾ Q
   pick-max⊑S˘↾Q = ↾-universal-⇐ (pick-max⊑S˘ , pick-maxS⊑Q) 
   
   wf : well-found (ε ListF ○ fun pick-max)
   wf x = acc x (access x)
     where
       access : (x : ℕ × Coin) → (y : ℕ × Coin) → (ε ListF ○ fun pick-max) y x → Acc (ε ListF ○ fun pick-max) y
       access (zero , c) y (.(inj₁ tt) , refl , ())
       access (suc n , 1p) y (.(inj₂ (fst 1p , snd (n , 1p))) , refl , inj₁ ())
       access (suc n , 1p) .(n , 1p) (.(inj₂ (fst 1p , snd (n , 1p))) , refl , inj₂ refl) = acc (n , 1p) (access (n , 1p))
       access (1 , 2p) y (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₁ ())
       access (1 , 2p) .(0 , 1p) (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₂ refl) = acc (0 , 1p) (access (0 , 1p))
       access (suc (suc n) , 2p) y (.(inj₂ (fst 2p , snd (n , 2p))) , refl , inj₁ ())
       access (suc (suc n) , 2p) .(n , 2p) (.(inj₂ (fst 2p , snd (n , 2p))) , refl , inj₂ refl) = acc (n , 2p) (access (n , 2p))
       access (1 , 5p) y (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₁ ())
       access (1 , 5p) .(0 , 1p) (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₂ refl) = acc (0 , 1p) (access (0 , 1p))
       access (2 , 5p) y (.(inj₂ (fst 2p , snd (0 , 2p))) , refl , inj₁ ())
       access (2 , 5p) .(0 , 2p) (.(inj₂ (fst 2p , snd (0 , 2p))) , refl , inj₂ refl) = acc (0 , 2p) (access (0 , 2p))
       access (3 , 5p) y (.(inj₂ (fst 2p , snd (1 , 2p))) , refl , inj₁ ())
       access (3 , 5p) .(1 , 2p) (.(inj₂ (fst 2p , snd (1 , 2p))) , refl , inj₂ refl) = acc (1 , 2p) (access (1 , 2p))
       access (4 , 5p) y (.(inj₂ (fst 2p , snd (2 , 2p))) , refl , inj₁ ())
       access (4 , 5p) .(2 , 2p) (.(inj₂ (fst 2p , snd (2 , 2p))) , refl , inj₂ refl) = acc (2 , 2p) (access (2 , 2p))
       access (suc (suc (suc (suc (suc n)))) , 5p) y (.(inj₂ (fst 5p , snd (n , 5p))) , refl , inj₁ ())
       access (suc (suc (suc (suc (suc n)))) , 5p) .(n , 5p) (.(inj₂ (fst 5p , snd (n , 5p))) , refl , inj₂ refl) = acc (n , 5p) (access (n , 5p))
       access (1 , 10p) y (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₁ ())
       access (1 , 10p) .(0 , 1p) (.(inj₂ (fst 1p , snd (0 , 1p))) , refl , inj₂ refl) = acc (0 , 1p) (access (0 , 1p))
       access (2 , 10p) y (.(inj₂ (fst 2p , snd (0 , 2p))) , refl , inj₁ ())
       access (2 , 10p) .(0 , 2p) (.(inj₂ (fst 2p , snd (0 , 2p))) , refl , inj₂ refl) = acc (0 , 2p) (access (0 , 2p))
       access (3 , 10p) y (.(inj₂ (fst 2p , snd (1 , 2p))) , refl , inj₁ ())
       access (3 , 10p) .(1 , 2p) (.(inj₂ (fst 2p , snd (1 , 2p))) , refl , inj₂ refl) = acc (1 , 2p) (access (1 , 2p))
       access (4 , 10p) y (.(inj₂ (fst 2p , snd (2 , 2p))) , refl , inj₁ ())
       access (4 , 10p) .(2 , 2p) (.(inj₂ (fst 2p , snd (2 , 2p))) , refl , inj₂ refl) = acc (2 , 2p) (access (2 , 2p))
       access (5 , 10p) y (.(inj₂ (fst 5p , snd (0 , 5p))) , refl , inj₁ ())
       access (5 , 10p) .(0 , 5p) (.(inj₂ (fst 5p , snd (0 , 5p))) , refl , inj₂ refl) = acc (0 , 5p) (access (0 , 5p))
       access (6 , 10p) y (.(inj₂ (fst 5p , snd (1 , 5p))) , refl , inj₁ ())
       access (6 , 10p) .(1 , 5p) (.(inj₂ (fst 5p , snd (1 , 5p))) , refl , inj₂ refl) = acc (1 , 5p) (access (1 , 5p))
       access (7 , 10p) y (.(inj₂ (fst 5p , snd (2 , 5p))) , refl , inj₁ ())
       access (7 , 10p) .(2 , 5p) (.(inj₂ (fst 5p , snd (2 , 5p))) , refl , inj₂ refl) = acc (2 , 5p) (access (2 , 5p))
       access (8 , 10p) y (.(inj₂ (fst 5p , snd (3 , 5p))) , refl , inj₁ ())
       access (8 , 10p) .(3 , 5p) (.(inj₂ (fst 5p , snd (3 , 5p))) , refl , inj₂ refl) = acc (3 , 5p) (access (3 , 5p))
       access (9 , 10p) y (.(inj₂ (fst 5p , snd (4 , 5p))) , refl , inj₁ ())
       access (9 , 10p) .(4 , 5p) (.(inj₂ (fst 5p , snd (4 , 5p))) , refl , inj₂ refl) = acc (4 , 5p) (access (4 , 5p))
       access (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) , 10p) y (.(inj₂ (fst 10p , snd (n , 10p))) , refl , inj₁ ())
       access (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) , 10p) .(n , 10p) (.(inj₂ (fst 10p , snd (n , 10p))) , refl , inj₂ refl) = acc (n , 10p) (access (n , 10p))



   mono-cond : fun In ○ fmapR ListF _⊴_ ⊑ _⊴_ ○ fun In
   mono-cond (In (inj₁ tt)) (inj₁ tt) (.(inj₁ tt) , Data.Unit.tt , refl) = ([] , refl , ⊴-refl')
   mono-cond (In (inj₂ ys)) (inj₁ tt) (.(inj₂ ys) , () , refl)
   mono-cond (In (inj₁ tt)) (inj₂ xs) (.(inj₁ tt) , () , refl)
   mono-cond (In (inj₂ (fst x , snd xs))) (inj₂ (fst .x , snd ys)) (.(inj₂ (fst x , snd xs)) , (refl , xs⊴ys) , refl)
     = (x ∷ ys , refl , ⊴-cons xs⊴ys)

   greedy-cond : fun In ○ fmapR ListF (⦇ fun In ⦈ ○ ⦇ S ⦈ ˘) ○ (Q ⊓ (S ˘ ○ S)) ˘ ⊑ (_⊴_) ˘ ○ fun In ○ fmapR ListF (⦇ fun In ⦈ ○ ⦇ S ⦈ ˘)
   greedy-cond (In (inj₁ tt)) (inj₁ tt) (.(inj₁ tt) , (inj₁ tt , (Data.Unit.tt , (s , p) , _ , _) , sb) , refl) = ([] , (inj₁ tt , sb , refl) , ⊴-refl')
   greedy-cond (In (inj₁ tt)) (inj₁ tt) (.(inj₁ tt) , (inj₂ n , (() , (s , p) , _ , _) , sb) , refl)
   greedy-cond (In (inj₁ tt)) (inj₂ m) (.(inj₁ tt) , (inj₁ tt , (() , (s , p) , _ , _) , sb) , refl)
   greedy-cond (In (inj₁ tt)) (inj₂ m) (.(inj₁ tt) , (inj₂ n , (c≤d , (s , p) , _ , _) , ()) , refl)
   greedy-cond (In (inj₂ cs)) (inj₁ tt) (.(inj₂ cs) , (inj₁ tt , (Data.Unit.tt , (s , p) , _ , _) , ()) , refl)
   greedy-cond (In (inj₂ cs)) (inj₁ tt) (.(inj₂ cs) , (inj₂ n , (() , (s , p) , _ , _) , sb) , refl)
   greedy-cond (In (inj₂ cs)) (inj₂ m) (.(inj₂ cs) , (inj₁ tt , (() , (s , p) , _ , _) , sb) , refl)
   greedy-cond (In (inj₂ (fst c , snd cs))) (inj₂ (fst d , snd (m , d'))) (._ , (inj₂ n , (c≤d , (s , p) , inj₁ (tt , () , raise₁) , _) , sb) , refl)
   greedy-cond (In (inj₂ (fst c , snd cs))) (inj₂ (fst d , snd (m , d'))) (._ , (inj₂ (fst c' , snd (n , .c')) , (c≤d , (s , p) , inj₂ (._ , refl , (refl , proj₄) , proj₅) , inj₁ (tt , () , proj₃)) , sb) , refl)
   greedy-cond (In (inj₂ (fst c , snd cs))) (inj₂ (fst d , snd (m , .d))) (._ , (inj₂ (fst .c , snd (n , .c)) , (c≤d , (s , p) , inj₂ (._ , refl , (refl , s≡c+n) , raise₁) , inj₂ ((fst .d , .(snd (m , d))) , refl , (refl , s≡d+m) , raise₂)) , refl , cs' , sb , fIn) , refl) with idR-foldR-⊒ ListF cs cs' fIn
   greedy-cond (In (inj₂ (fst c , snd cs))) (inj₂ (fst d , snd (m , .d))) (._ , (inj₂ (fst .c , snd (n , .c)) , (c≤d , (s , p) , inj₂ (._ , refl , (refl , s≡c+n) , raise₁) , inj₂ ((fst .d , .(snd (m , d))) , refl , (refl , s≡d+m) , raise₂)) , refl , .cs , sb , fIn) , refl) | refl with greedy-lemma c d n m cs c≤d (trans (sym s≡c+n) s≡d+m) sb
   ... | (ds , ds⊴cs , dsb) = (d ∷ ds , (_ , (refl , (ds , dsb , idR-foldR-⊑ ListF ds ds refl)) , refl) , ⊴-cons ds⊴cs)

