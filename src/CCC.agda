module CCC where

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

_⟶_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
_⟶_ A B = A → B

record _↔_ {α} {β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  field
    from : A ⟶ B
    to : B ⟶ A

record Category (_⇒_ : Set → Set → Set) : Set₁ where
  field
    id : ∀ {a : Set} → a ⇒ a
    _∘_ : ∀ {a b c : Set} → b ⇒ c → a ⇒ b → a ⇒ c
  infixr 9 _∘_

instance
  ⟶-Category : Category _⟶_
  ⟶-Category = record { id = λ x → x ; _∘_ = λ f g x → f (g x) }


record Cartesian (_⇒_ : Set → Set → Set) : Set₁ where
  field
    ⦃ ⇒-Category ⦄ : Category _⇒_
  open Category ⇒-Category
  field
    _▵_ :  ∀ {a c d : Set} → a ⇒ c → a ⇒ d → a ⇒ (c × d)
    exl : ∀ {a b : Set} → (a × b) ⇒ a
    exr : ∀ {a b : Set} → (a × b) ⇒ b
  infixr 3 _▵_
  field
    cart-univ : ∀ {a c d} (h : a ⇒ (c × d)) f g → (h ≡ (f ▵ g)) ↔ ((exl ∘ h ≡ f) × (exr ∘ h ≡ g))

instance
  ⟶-Cartesian : Cartesian _⟶_
  ⟶-Cartesian = record { _▵_ = λ f g x → f x , g x ; exl = λ { (a , b) → a } ; exr = λ { (a , b) → b } ;
                        cart-univ = λ h f g → record { from = λ lhs → {!!} , {!!} ; to = {!!} } }

