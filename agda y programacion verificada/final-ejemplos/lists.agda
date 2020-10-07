import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Agda.Builtin.List
open import isomorphism using (_≃_; _⇔_ ; extensionality ; ∀-extensionality)


pattern [_] z = z ∷ []

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys          = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_


-- Con rewrite
++-r-identity : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-r-identity [] = refl
++-r-identity (x ∷ xs) rewrite (++-r-identity xs) = refl


-- Usando razonamientos
++-r-identity' : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-r-identity' [] = refl
++-r-identity' (x ∷ xs) =
                     begin
                         (x ∷ xs) ++ []
                     ≡⟨⟩ 
                        x ∷ (xs ++ [])
                     ≡⟨ cong (x ∷_) (++-r-identity xs) ⟩
                       x ∷ xs
                     ∎

++-l-identity : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-l-identity xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎


-- Asociatividad de append
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
   [] ++ (ys ++ zs)
  ∎
   
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨⟩                                                       -- Definición de ++ 
    (x ∷ (xs ++ ys)) ++ zs
  ≡⟨⟩                                                       -- Definición de ++
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩     -- Hipótesis inductiva
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩                                                       -- Definición de ++ 
    (x ∷ xs) ++ (ys ++ zs)
  ∎

-- Reverse lento: O(N²)
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

-- Reverse rápido (helper)
fastrev : ∀ {A : Set} → List A → List A → List A
fastrev [] ys  =  ys
fastrev (x ∷ xs) ys  =  fastrev xs (x ∷ ys)

-- Reverse  rápido: O(N)
rev : ∀ {A : Set} → List A → List A
rev xs = fastrev xs []


-- Demostremos este lema
fastrev-lem : ∀ {A : Set} (xs ys : List A)
                    → fastrev xs ys ≡ reverse xs ++ ys

-- Caso base
fastrev-lem [] ys =
  begin
    fastrev [] ys         
  ≡⟨⟩                                                                    -- Definicion de fastrev
    ys
  ≡⟨⟩                                                                    -- Definición de reverse
    reverse [] ++ ys
  ∎

-- Paso inductivo
fastrev-lem (x ∷ xs) ys =
        begin
           fastrev (x ∷ xs) ys
        ≡⟨⟩                                                               -- Definicion de fastrev
           fastrev xs (x ∷ ys)
        ≡⟨ fastrev-lem xs (x ∷ ys) ⟩                           -- Hipótesis inductiva
           reverse xs ++ (x ∷ ys)
        ≡⟨⟩                                                               -- Definicion de ++ (1)
          reverse xs ++ (x ∷ ([] ++ ys))
        ≡⟨⟩                                                               -- Definición de ++ (2)
          reverse xs ++ ((x ∷ []) ++ ys)
        ≡⟨⟩                                                               -- Notación: x ∷ [] ≡ [ x ]
          reverse xs ++ ([ x ] ++ ys)
        ≡⟨ sym (++-assoc (reverse xs) ([ x ]) ys)  ⟩   -- Asociatividad de ++
          (reverse xs ++ [ x ]) ++ ys
        ≡⟨⟩                                                               -- Definición de reverse
          reverse (x ∷ xs) ++ ys
        ∎



-- Demostración: reverse y rev hacen lo mismo para cualquier argumento 
reverses-equal-app : ∀ {A : Set} (xs : List A) → rev xs ≡ reverse xs
reverses-equal-app xs =
  begin
    rev xs
  ≡⟨⟩
    fastrev xs []
  ≡⟨ fastrev-lem xs [] ⟩                      -- Aplico el lema
    reverse xs ++ []
  ≡⟨ ++-r-identity (reverse xs) ⟩       -- xs + [] ≡ xs
    reverse xs
  ∎



-- Con extensionalidad puedo probar la igualdad de las funciones
reverses-equal : ∀ {A : Set} → rev {A} ≡ reverse {A}
reverses-equal = extensionality reverses-equal-app


reverse-++ : ∀ {A : Set} (xs ys : List A)
                     → reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
reverse-++ [] ys = begin
                                 reverse ([] ++ ys)
                              ≡⟨⟩ reverse ys
                              ≡⟨ sym (++-r-identity (reverse ys))  ⟩
                                     reverse ys ++ []
                              ≡⟨⟩ (reverse ys) ++ (reverse [])
                              ∎
reverse-++ (x ∷ xs) ys =
                           begin
                              reverse ((x ∷ xs) ++ ys)
                           ≡⟨⟩
                              reverse (x ∷ (xs ++ ys))
                           ≡⟨⟩
                              reverse (xs ++ ys) ++ [ x ]
                           ≡⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
                             (reverse ys ++ reverse xs) ++ [ x ]
                           ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
                             reverse ys ++ (reverse xs ++ [ x ])
                           ≡⟨⟩
                             reverse ys ++ reverse (x ∷ xs)
                          ∎
                             


reverse-idempotent : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-idempotent [] = begin
                                     reverse (reverse [])
                                   ≡⟨⟩
                                     reverse []
                                   ≡⟨⟩
                                     []
                                   ∎
                                   
reverse-idempotent (x ∷ xs) =
                             begin
                                reverse (reverse (x ∷ xs))
                             ≡⟨⟩
                                reverse (reverse xs ++ [ x ])
                              ≡⟨ reverse-++ (reverse xs) [ x ] ⟩
                                 reverse [ x ] ++ reverse (reverse xs)
                              ≡⟨⟩
                                [ x ] ++ (reverse (reverse xs))
                              ≡⟨ cong ([ x ] ++_) (reverse-idempotent xs)  ⟩
                                [ x ] ++ xs
                              ≡⟨⟩
                                 (x ∷ xs)
                              ∎



rev-idempotent : ∀ {A : Set} (xs : List A) → rev (rev xs) ≡ xs
rev-idempotent {A} xs =
               begin
                  rev (rev xs)
               ≡⟨ reverses-equal-app (rev xs)  ⟩
                  reverse (rev xs)
               ≡⟨ cong reverse (reverses-equal-app xs) ⟩ 
                  reverse (reverse xs)
               ≡⟨ reverse-idempotent xs ⟩
                 xs
               ∎   




data 𝔹 : Set where
   tt : 𝔹
   ff : 𝔹

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && _ = ff

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl

~~&& : ∀ (b1 b2 : 𝔹) → (~ ~ b1) && b2 ≡ b1 && b2
~~&& b1 b2 rewrite (~~-elim b1)= refl
