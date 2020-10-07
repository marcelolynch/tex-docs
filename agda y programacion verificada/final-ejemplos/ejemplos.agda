import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_ ; s≤s; z≤n ; ≤-pred)
open import Data.Product

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

const : ℕ → ℕ → ℕ
const n _ = n

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a



-- Dems
+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

<-pred : ∀ { n m : ℕ } → (suc n) < (suc m) → n < m
<-pred = ≤-pred 


<⇒≤ : ∀ {n m : ℕ} → n < m → n ≤ m
<⇒≤ {0} {m} p = z≤n
<⇒≤ {suc n} {0} ()
<⇒≤ {suc n} {suc m} p = s≤s (<⇒≤ {n} {m} (<-pred p)) 


≤-trans : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans {0} {b} {c} p q = z≤n
≤-trans {(suc n)} {0} {_} ()
≤-trans {_} {(suc n)} {0} _ ()
≤-trans {(suc m)} {(suc n)} {(suc t)} p q = s≤s (≤-trans {m} {n} {t} (≤-pred p) (≤-pred q))

data 𝔹 : Set where
    tt : 𝔹
    ff : 𝔹


eq : ℕ → ℕ → 𝔹
eq 0 0 = tt
eq 0 (suc n) = ff
eq (suc n) 0 = ff
eq (suc m) (suc n) = eq n m

lt : ℕ → ℕ → 𝔹
lt _ 0 = ff
lt 0 (suc n) = tt
lt (suc n) (suc m) = lt n m

le : ℕ → ℕ → 𝔹
le 0 m = tt
le (suc n) 0 = ff
le (suc n) (suc m) = le n m

𝔹-contra : (ff ≡ tt) → ∀ {P : Set} → P 
𝔹-contra ()

sum : (ℕ → ℕ) → (i : ℕ) → (j : ℕ) → ℕ
sum f n m with (eq n m)
sum f n m | tt  = f n
sum f n m | ff with inspect (lt n m)
sum f n m | ff | ff with≡ _ = 0 
sum f n (suc m) | ff | tt with≡ p = sum f n m + f (suc m) 
sum f n 0 | ff | tt with≡ n<0 = 𝔹-contra n<0

suc-inj : ∀ (a b : ℕ) → suc a ≡ suc b → a ≡ b
suc-inj _ _ refl = refl

+l-elim : ∀ (a b c : ℕ) → a + b ≡ a + c → b ≡ c
+l-elim 0 _ _ p = p
+l-elim (suc n) b c p = +l-elim n b c (suc-inj (n + b) (n + c) p) 

le-suc : ∀ {n m : ℕ} → (le n m ≡ tt) → (le (suc n) (suc m) ≡ tt)
le-suc {0} {0} p = refl
le-suc {suc n} {0} ()
le-suc {m} {n} p = p

le-rsuc : ∀ {n m : ℕ} → (le n m ≡ tt) → (le n (suc m) ≡ tt)
le-rsuc {0} {0} p = refl
le-rsuc {suc n} {0} ()
le-rsuc {0} {_} p = refl
le-rsuc {suc n} {suc m} p = le-rsuc {n} {m} p

lt-suc : ∀ {n m : ℕ} → (lt n m ≡ tt) → (lt (suc n) (suc m) ≡ tt)
lt-suc {0} {0} ()
lt-suc {suc n} {0} ()
lt-suc {m} {n} p = p

lt-rsuc : ∀ {n m : ℕ} → (lt n m ≡ tt) → (lt n (suc m) ≡ tt)
lt-rsuc {0} {0} p = refl
lt-rsuc {suc n} {0} ()
lt-rsuc {0} {_} p = refl
lt-rsuc {suc n} {suc m} p = lt-rsuc {n} {m} p

eq-sym : ∀ (m n : ℕ) → (eq n m) ≡ (eq m n)
eq-sym 0 0 = refl 
eq-sym 0 (suc n) = refl
eq-sym (suc n) 0 = refl
eq-sym (suc n) (suc m) = eq-sym m n

eq-suc : ∀ (m n : ℕ) → eq n m ≡ eq (suc n) (suc m)
eq-suc 0 0 = refl 
eq-suc 0 (suc n) = refl
eq-suc (suc n) 0 = refl
eq-suc (suc n) (suc m) = eq-suc m n

sum-last-term : ∀ ( f : ℕ → ℕ ) (n m : ℕ) → le n m ≡ tt → sum f n (suc m) ≡ sum f n m + f (suc m)
sum-last-term f n m p = {!!}



<-is-lt : ∀ {n m : ℕ} → n < m → lt n m ≡ tt
<-is-lt {0} {0} ()
<-is-lt {_} {0} ()
<-is-lt {0} {suc m} p = refl
<-is-lt {suc n} {suc m} p = <-is-lt (<-pred p)


sum-assoc-from-0 : ∀ (f : ℕ → ℕ) (j k : ℕ)
                 → (le j k ≡ tt)
                 → (sum f 0 j) + sum f (suc j) k ≡ sum f 0 k
sum-assoc-from-0 f 0 k p = {!!} 
sum-assoc-from-0 = {!!}


1-le-suc : ∀ (n : ℕ) → le 1 (suc n) ≡ tt
1-le-suc 0 = refl
1-le-suc (suc n) = refl

sum-safe : (ℕ → ℕ) → (i : ℕ) → (j : ℕ) → (le i j ≡ tt) → ℕ
sum-safe f 0 0 p = f 0
sum-safe f (suc n) 0 ()
sum-safe f 0 (suc m) p = (sum-safe f 0 m refl) + f (suc m)
sum-safe f (suc n) (suc m) p = {!f (suc m) + !}



~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl


