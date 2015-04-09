------------------------------------------------------------------------
-- Comparisons of different kinds of lenses, focusing on the
-- definition of composable record setters and getters
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module uses both dependent and non-dependent lenses, in order
-- to illustrate a problem with the non-dependent ones. It also uses
-- two kinds of dependent lenses, in order to illustrate a minor
-- problem with one of them.

module README.Record-getters-and-setters where

open import Equality.Propositional
open import Prelude hiding (_∘_)

open import Bijection equality-with-J
  using (_↔_; decidable-equality-respects)
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (_∘_)

import Lens.Dependent
import Lens.Non-dependent

------------------------------------------------------------------------
-- Dependent lenses with "remainder types" visible in the type

module Dependent₃ where

  open Lens.Dependent

  -- Nested records.

  record R₁ (A : Set) : Set where
    field
      f     : A → A
      x     : A
      lemma : ∀ y → f y ≡ y

  record R₂ : Set₁ where
    field
      A  : Set
      r₁ : R₁ A

  -- Lenses for each of the three fields of R₁.

  -- The x field is easiest, because it is independent of the others.
  --
  -- (Note that the from function is inferred automatically.)

  x : {A : Set} →
      Lens₃ (R₁ A) (∃ λ (f : A → A) → ∀ y → f y ≡ y) (λ _ → A)
  x = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ r → (R₁.f r , R₁.lemma r) , R₁.x r
        ; from = _
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  -- The lemma field depends on the f field, so whenever the f field
  -- is set the lemma field needs to be updated as well.

  f : {A : Set} →
      Lens₃ (R₁ A) A (λ _ → ∃ λ (f : A → A) → ∀ y → f y ≡ y)
  f = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ r → R₁.x r , (R₁.f r , R₁.lemma r)
        ; from = _
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  -- The lemma field can be updated independently.

  lemma : {A : Set} →
          Lens₃ (R₁ A) (A × (A → A)) (λ r → ∀ y → proj₂ r y ≡ y)
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ r → (R₁.x r , R₁.f r) , R₁.lemma r
        ; from = _
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  -- Note that the type of the last lens may not be quite
  -- satisfactory: the type of the lens does not guarantee that the
  -- lemma applies to the input's f field. The following lemma may
  -- provide some form of consolation:

  consolation : {A : Set} (r : R₁ A) → ∀ y → R₁.f r y ≡ y
  consolation = Lens₃.get lemma

  -- Let us now construct lenses for the same fields, but accessed
  -- through an R₂ record.

  -- First we define lenses for the fields of R₂ (note that the A lens
  -- does not seem to be very useful):

  A : Lens₃ R₂ ⊤ (λ _ → R₂)
  A = id₃

  r₁ : Lens₃ R₂ Set R₁
  r₁ = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ r → R₂.A r , R₂.r₁ r
        ; from = _
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  -- The lenses for the three R₁ fields can now be defined by
  -- composition:

  x₂ : Lens₃ R₂ _ (λ r → proj₁ r)
  x₂ = x ₃∘₃ r₁

  f₂ : Lens₃ R₂ _ (λ r → ∃ λ (f : proj₁ r → proj₁ r) → ∀ y → f y ≡ y)
  f₂ = f ₃∘₃ r₁

  lemma₂ : Lens₃ R₂ _ (λ r → ∀ y → proj₂ (proj₂ r) y ≡ y)
  lemma₂ = lemma ₃∘₃ r₁

  consolation₂ : (r : R₂) → ∀ y → proj₁ (Lens₃.get f₂ r) y ≡ y
  consolation₂ = Lens₃.get lemma₂

------------------------------------------------------------------------
-- Dependent lenses without "remainder types" visible in the type

module Dependent where

  open Lens.Dependent
  open Dependent₃ using (R₁; module R₁; R₂; module R₂)

  -- Lenses for each of the three fields of R₁.

  x : {A : Set} → Lens _ (R₁ A) (λ _ → A)
  x = Lens₃-to-Lens Dependent₃.x

  f : {A : Set} → Lens _ (R₁ A) (λ _ → ∃ λ (f : A → A) → ∀ y → f y ≡ y)
  f = Lens₃-to-Lens Dependent₃.f

  lemma : {A : Set} → Lens _ (R₁ A) (λ r → ∀ y → R₁.f r y ≡ y)
  lemma = Lens₃-to-Lens Dependent₃.lemma

  -- Note that the type of lemma is now more satisfactory: the type of
  -- the lens /does/ guarantee that the lemma applies to the input's f
  -- field.

  -- A lens for the r₁ field of R₂.

  r₁ : Lens _ R₂ (λ r → R₁ (R₂.A r))
  r₁ = Lens₃-to-Lens Dependent₃.r₁

  -- Lenses for the fields of R₁, accessed through an R₂ record. Note
  -- the use of /forward/ composition.

  x₂ : Lens _ R₂ (λ r → R₂.A r)
  x₂ = r₁ ∘ x

  f₂ : Lens _ R₂ (λ r → ∃ λ (f : R₂.A r → R₂.A r) → ∀ y → f y ≡ y)
  f₂ = r₁ ∘ f

  lemma₂ : Lens _ R₂ (λ r → ∀ y → proj₁ (Lens.get f₂ r) y ≡ y)
  lemma₂ = r₁ ∘ lemma

------------------------------------------------------------------------
-- Non-dependent lenses

module Non-dependent where

  open Lens.Non-dependent

  -- Labels.

  data Label : Set where
    ″f″ ″x″ ″lemma″ ″A″ ″r₁″ : Label

  -- Labels come with decidable equality.

  Label↔Fin : Label ↔ Fin 5
  Label↔Fin = record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    }
    where

    to : Label → Fin 5
    to ″f″     = fzero
    to ″x″     = fsuc fzero
    to ″lemma″ = fsuc (fsuc fzero)
    to ″A″     = fsuc (fsuc (fsuc fzero))
    to ″r₁″    = fsuc (fsuc (fsuc (fsuc fzero)))

    from : Fin 5 → Label
    from fzero                                 = ″f″
    from (fsuc fzero)                          = ″x″
    from (fsuc (fsuc fzero))                   = ″lemma″
    from (fsuc (fsuc (fsuc fzero)))            = ″A″
    from (fsuc (fsuc (fsuc (fsuc fzero))))     = ″r₁″
    from (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

    to∘from : ∀ i → to (from i) ≡ i
    to∘from fzero                                 = refl
    to∘from (fsuc fzero)                          = refl
    to∘from (fsuc (fsuc fzero))                   = refl
    to∘from (fsuc (fsuc (fsuc fzero)))            = refl
    to∘from (fsuc (fsuc (fsuc (fsuc fzero))))     = refl
    to∘from (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

    from∘to : ∀ ℓ → from (to ℓ) ≡ ℓ
    from∘to ″f″     = refl
    from∘to ″x″     = refl
    from∘to ″lemma″ = refl
    from∘to ″A″     = refl
    from∘to ″r₁″    = refl

  _≟_ : Decidable-equality Label
  _≟_ = decidable-equality-respects (inverse Label↔Fin) Fin._≟_

  -- Records.

  open import Record Label _≟_

  -- Nested records (defined using the record language from Record, so
  -- that we can use manifest fields).

  R₁ : Set → Signature _
  R₁ A = ∅ , ″f″     ∶ (λ _ → A → A)
           , ″x″     ∶ (λ _ → A)
           , ″lemma″ ∶ (λ r → ∀ y → (r · ″f″) y ≡ y)

  R₂ : Signature _
  R₂ = ∅ , ″A″  ∶ (λ _ → Set)
         , ″r₁″ ∶ (λ r → ↑ _ (Record (R₁ (r · ″A″))))

  -- Lenses for each of the three fields of R₁.

  -- The x field is easiest, because it is independent of the others.
  -- Note that the get field is inferred.

  x : {A : Set} → Lens (Record (R₁ A)) A
  x = record
    { set     = λ r x → rec (rec (rec (_
                  , r · ″f″)
                  , x)
                  , r · ″lemma″)
    ; get-set = λ _ _   → refl
    ; set-get = λ _     → refl
    ; set-set = λ _ _ _ → refl
    }

  -- The lemma field depends on the f field, so whenever the f field
  -- is set the lemma field needs to be updated as well.

  f : {A : Set} →
      Lens (Record (R₁ A))
           (Record (∅ , ″f″     ∶ (λ _ → A → A)
                      , ″lemma″ ∶ (λ r → ∀ x → (r · ″f″) x ≡ x)))
  f = record
    { set     = λ r f-lemma → rec (rec (rec (_
                  , f-lemma · ″f″)
                  , r · ″x″)
                  , f-lemma · ″lemma″)
    ; get-set = λ _ _   → refl
    ; set-get = λ _     → refl
    ; set-set = λ _ _ _ → refl
    }

  -- The lemma field can be updated independently. Note the use of a
  -- manifest field in the type of the lens to capture the dependency
  -- between the two lens parameters.

  lemma : {A : Set} {f : A → A} →
          Lens (Record (R₁ A With ″f″ ≔ (λ _ → f)))
               (∀ x → f x ≡ x)
  lemma = record
    { set     = λ r lemma → rec (rec (_
                  , r · ″x″)
                  , lemma)
    ; get-set = λ _ _   → refl
    ; set-get = λ _     → refl
    ; set-set = λ _ _ _ → refl
    }

  -- The use of a manifest field is problematic, because the domain of
  -- the lens is no longer Record (R₁ A). It is easy to convert
  -- records into the required form, but this conversion is not a
  -- non-dependent lens (due to the dependency).

  convert : {A : Set} (r : Record (R₁ A)) →
            Record (R₁ A With ″f″ ≔ (λ _ → r · ″f″))
  convert (rec (rec (rec (_ , f) , x) , lemma)) =
    rec (rec (_ , x) , lemma)

  -- Let us now try to construct lenses for the same fields, but now
  -- accessed through an R₂ record.

  -- First we define a lens for the r₁ field.

  r₁ : {A : Set} →
       Lens (Record (R₂ With ″A″ ≔ λ _ → A)) (Record (R₁ A))
  r₁ = record
    { set     = λ _ r → rec (_ , lift r)
    ; get-set = λ _ _   → refl
    ; set-get = λ _     → refl
    ; set-set = λ _ _ _ → refl
    }

  -- It is now easy to construct lenses for the embedded x and f
  -- fields using composition of lenses.

  x₂ : {A : Set} → Lens (Record (R₂ With ″A″ ≔ λ _ → A)) A
  x₂ = x ∘ r₁

  f₂ : {A : Set} →
       Lens (Record (R₂ With ″A″ ≔ λ _ → A))
            (Record (∅ , ″f″     ∶ (λ _ → A → A)
                       , ″lemma″ ∶ (λ r → ∀ x → (r · ″f″) x ≡ x)))
  f₂ = f ∘ r₁

  {-

  -- However, it is less obvious how to construct the corresponding
  -- lens for the embedded lemma field. To start with, what should its
  -- type be? The type used below is an obvious choice.

  lemma₂ : {A : Set} {r : Record (R₁ A)} →
           Lens (Record (R₂ With ″A″  ≔ (λ _ → A)
                            With ″r₁″ ≔ (λ _ → lift r)))
                (∀ x → (r · ″f″) x ≡ x)

  -- Now, in order to define this lens using composition with lemma,
  -- we need a lens with the following type:

  r₁₂ : {A : Set} {r : Record (R₁ A)} →
        Lens (Record (R₂ With ″A″  ≔ (λ _ → A)
                         With ″r₁″ ≔ (λ _ → lift r)))
             (Record (R₁ A With ″f″  ≔ (λ _ → r · ″f″)))

  lemma₂ = lemma ∘ r₁₂

  -- However, we cannot define r₁₂. Its set field is uniquely
  -- determined (up to extensional equality)—it must return a unique
  -- value—and the get-set law requires us to prove that an arbitrary
  -- value of type
  --
  --   Record (R₁ A With ″f″ ≔ (λ _ → r · ″f″))
  --
  -- is equal to the result of applying get to this unique value.

  r₁₂ = record
    { get     = λ s → convert (lower (s · ″r₁″))
    ; get-set = λ _ _   → ?
    ; set-get = λ _     → refl
    ; set-set = λ _ _ _ → refl
    }

  -- Conclusions: The use of manifest fields limits the usefulness of
  -- these lenses, because they do not compose as well as they do for
  -- non-dependent records. Dependent lenses seem to be more useful.

  -}
