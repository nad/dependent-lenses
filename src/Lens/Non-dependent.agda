------------------------------------------------------------------------
-- Representation-independent results for non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bij using (module _↔_)
open import Equivalence equality-with-J using (_≃_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b c c₁ c₂ c₃    : Level
    A B               : Set a
    Lens₁ Lens₂ Lens₃ : Set a → Set b → Set c

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type, assuming that lenses with contractible domains have
-- contractible codomains.

no-first-projection-lens :
  (Lens : Set (a ⊔ b) → Set a → Set c) →
  @0 (∀ {A B} → Lens A B → Contractible A → Contractible B) →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens {b = b} _ contractible-to-contractible =
  ↑ _ Bool ,
  (λ b → ↑ _ (lower b ≡ true)) ,
  λ l →                                           $⟨ singleton-contractible _ ⟩
     Contractible (Singleton true)                ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (∃ λ b → ↑ _ (lower b ≡ true))  ↝⟨ (λ hyp → [ contractible-to-contractible l hyp ]) ⟩
     Erased (Contractible (↑ _ Bool))             ↝⟨ Erased-cong (H-level.respects-surjection (_↔_.surjection Bij.↑↔) 0) ⟩
     Erased (Contractible Bool)                   ↝⟨ Erased-cong (mono₁ 0) ⟩
     Erased (Is-proposition Bool)                 ↝⟨ inverse-ext? ¬-Erased↔¬ _ ¬-Bool-propositional ⟩□
     ⊥                                            □
  where
  surj : Singleton true ↠ ∃ λ b → ↑ _ (lower b ≡ true)
  surj = record
    { logical-equivalence = record
      { to   = λ { (b , b≡true) → lift b , lift b≡true }
      ; from = λ { (lift b , lift b≡true) → b , b≡true }
      }
    ; right-inverse-of = refl
    }

------------------------------------------------------------------------
-- Statements of preservation results, and some related lemmas

-- Lens-like things with getters and setters.

record Has-getter-and-setter
         (Lens : Set a → Set b → Set c) :
         Set (lsuc (a ⊔ b ⊔ c)) where
  field
    -- Getter.
    get : {A : Set a} {B : Set b} → Lens A B → A → B

    -- Setter.
    set : {A : Set a} {B : Set b} → Lens A B → A → B → A

-- A statement of what it means for two lenses to have the same getter
-- and setter.

Same-getter-and-setter :
  {Lens₁ : Set a → Set b → Set c₁}
  {Lens₂ : Set a → Set b → Set c₂}
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  {A : Set a} {B : Set b} →
  Lens₁ A B → Lens₂ A B → Set (a ⊔ b)
Same-getter-and-setter ⦃ L₁ = L₁ ⦄ ⦃ L₂ = L₂ ⦄ l₁ l₂ =
  get L₁ l₁ ≡ get L₂ l₂ ×
  set L₁ l₁ ≡ set L₂ l₂
  where
  open Has-getter-and-setter

-- A statement of what it means for a function to preserve getters and
-- setters for all inputs.

Preserves-getters-and-setters-→ :
  {Lens₁ : Set a → Set b → Set c₁}
  {Lens₂ : Set a → Set b → Set c₂}
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  (A : Set a) (B : Set b) →
  (Lens₁ A B → Lens₂ A B) →
  Set (a ⊔ b ⊔ c₁)
Preserves-getters-and-setters-→ {Lens₁ = Lens₁} A B f =
  (l : Lens₁ A B) → Same-getter-and-setter (f l) l

-- A statement of what it means for a logical equivalence to preserve
-- getters and setters.

Preserves-getters-and-setters-⇔ :
  {Lens₁ : Set a → Set b → Set c₁}
  {Lens₂ : Set a → Set b → Set c₂}
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  (A : Set a) (B : Set b) →
  (Lens₁ A B ⇔ Lens₂ A B) →
  Set (a ⊔ b ⊔ c₁ ⊔ c₂)
Preserves-getters-and-setters-⇔ A B eq =
  Preserves-getters-and-setters-→ A B (_⇔_.to eq) ×
  Preserves-getters-and-setters-→ A B (_⇔_.from eq)

-- Composition preserves Preserves-getters-and-setters-→.

Preserves-getters-and-setters-→-∘ :
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  ⦃ L₃ : Has-getter-and-setter Lens₃ ⦄
  {f : Lens₂ A B → Lens₃ A B}
  {g : Lens₁ A B → Lens₂ A B} →
  Preserves-getters-and-setters-→ A B f →
  Preserves-getters-and-setters-→ A B g →
  Preserves-getters-and-setters-→ A B (f ∘ g)
Preserves-getters-and-setters-→-∘ p-f p-g _ =
    trans (proj₁ (p-f _)) (proj₁ (p-g _))
  , trans (proj₂ (p-f _)) (proj₂ (p-g _))

-- Composition preserves Preserves-getters-and-setters-⇔.

Preserves-getters-and-setters-⇔-∘ :
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  ⦃ L₃ : Has-getter-and-setter Lens₃ ⦄
  {f : Lens₂ A B ⇔ Lens₃ A B}
  {g : Lens₁ A B ⇔ Lens₂ A B} →
  Preserves-getters-and-setters-⇔ A B f →
  Preserves-getters-and-setters-⇔ A B g →
  Preserves-getters-and-setters-⇔ A B (f F.∘ g)
Preserves-getters-and-setters-⇔-∘ p-f p-g =
    Preserves-getters-and-setters-→-∘ (proj₁ p-f) (proj₁ p-g)
  , Preserves-getters-and-setters-→-∘ (proj₂ p-g) (proj₂ p-f)

-- The function inverse preserves Preserves-getters-and-setters-⇔.

Preserves-getters-and-setters-⇔-inverse :
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  {f : Lens₁ A B ⇔ Lens₂ A B} →
  Preserves-getters-and-setters-⇔ A B f →
  Preserves-getters-and-setters-⇔ A B (inverse f)
Preserves-getters-and-setters-⇔-inverse = swap

-- If the forward direction of a split surjection preserves getters
-- and setters, then both directions do.

Preserves-getters-and-setters-→-↠-⇔ :
  ⦃ L₁ : Has-getter-and-setter Lens₁ ⦄
  ⦃ L₂ : Has-getter-and-setter Lens₂ ⦄
  (f : Lens₁ A B ↠ Lens₂ A B) →
  Preserves-getters-and-setters-→ A B (_↠_.to f) →
  Preserves-getters-and-setters-⇔ A B (_↠_.logical-equivalence f)
Preserves-getters-and-setters-→-↠-⇔ ⦃ L₁ = L₁ ⦄ ⦃ L₂ = L₂ ⦄ f p =
    p
  , λ l →
        (get L₁ (_↠_.from f l)             ≡⟨ sym $ proj₁ $ p (_↠_.from f l) ⟩
         get L₂ (_↠_.to f (_↠_.from f l))  ≡⟨ cong (get L₂) $ _↠_.right-inverse-of f _ ⟩∎
         get L₂ l                          ∎)
      , (set L₁ (_↠_.from f l)             ≡⟨ sym $ proj₂ $ p (_↠_.from f l) ⟩
         set L₂ (_↠_.to f (_↠_.from f l))  ≡⟨ cong (set L₂) $ _↠_.right-inverse-of f _ ⟩∎
         set L₂ l                          ∎)
  where
  open Has-getter-and-setter
