------------------------------------------------------------------------
-- Non-dependent lenses
------------------------------------------------------------------------

module Lens.Non-dependent where

open import Data.Product
open import Function as F hiding (id) renaming (_∘_ to _⊚_)
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

------------------------------------------------------------------------
-- Lenses

record Lens {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    -- Getter.
    get : A → B

    -- Setter.
    set : A → B → A

    -- Lens laws.
    get-set : ∀ a b → get (set a b) ≡ b
    set-get : ∀ a → set a (get a) ≡ a
    set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂

------------------------------------------------------------------------
-- Lens combinators

-- Identity lens.

id : ∀ {a} {A : Set a} → Lens A A
id = record
  { get     = F.id
  ; set     = flip const
  ; get-set = λ _ _   → P.refl
  ; set-get = λ _     → P.refl
  ; set-set = λ _ _ _ → P.refl
  }

-- Composition of lenses.

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      Lens B C → Lens A B → Lens A C
l₁ ∘ l₂ = record
  { get     = get l₁ ⊚ get l₂
  ; set     = λ a c → let b = set l₁ (get l₂ a) c in
                      set l₂ a b
  ; get-set = λ a c → let b = set l₁ (get l₂ a) c in

                begin
                get l₁ (get l₂ (set l₂ a b))  ≡⟨ P.cong (get l₁) $ get-set l₂ a b ⟩
                get l₁ b                      ≡⟨ P.refl ⟩
                get l₁ (set l₁ (get l₂ a) c)  ≡⟨ get-set l₁ (get l₂ a) c ⟩
                c                             ∎
  ; set-get = λ a →
                begin
                set l₂ a (set l₁ (get l₂ a) (get l₁ (get l₂ a)))  ≡⟨ P.cong (set l₂ a) $ set-get l₁ (get l₂ a) ⟩
                set l₂ a (get l₂ a)                               ≡⟨ set-get l₂ a ⟩
                a                                                 ∎
  ; set-set = λ a c₁ c₂ →
                let b₁ = set l₁ (get l₂ a) c₁
                    b₂ = set l₁ (get l₂ a) c₂

                    lemma = begin
                      set l₁ (get l₂ (set l₂ a b₁)) c₂  ≡⟨ P.cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
                      set l₁ b₁                     c₂  ≡⟨ P.refl ⟩
                      set l₁ (set l₁ (get l₂ a) c₁) c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩
                      set l₁ (get l₂ a)             c₂  ≡⟨ P.refl ⟩
                      b₂                                ∎

                in begin
                set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ P.cong (set l₂ (set l₂ a b₁)) lemma ⟩
                set l₂ (set l₂ a b₁) b₂                                  ≡⟨ set-set l₂ a b₁ b₂ ⟩
                set l₂ a             b₂                                  ∎
  }
  where
  open Lens
  open P.≡-Reasoning
