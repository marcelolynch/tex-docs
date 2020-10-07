import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans)

module EqReasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

 -- Cosmético
  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y


-- Me deja encadenar cosas definicionalmente iguales
  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y


-- El argumento del medio es 'justificación' (mediante transitividad)
-- para decir que el de la izquierda y la derecha son iguales
  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z


-- Cosmético
  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl




  -- La igualdad es simétrica
  sym : ∀ {A : Set}{x y : A}
            → x ≡ y → y ≡ x
  sym refl = refl


  -- La igualdad es una congruencia
  cong : ∀ {A B : Set} (f : A → B) {x y}
             → x ≡ y → f x ≡ f y
  cong f refl = refl


