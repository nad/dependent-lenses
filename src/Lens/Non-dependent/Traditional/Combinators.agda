------------------------------------------------------------------------
-- Identity and composition for traditional non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical #-}

import Equality.Path as P

module Lens.Non-dependent.Traditional.Combinators
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

import Bi-invertibility
open import Bijection equality-with-J as Bijection using (_↔_)
open import Category equality-with-J as C using (Category; Precategory)
open import Circle eq as Circle using (𝕊¹)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Erased.Cubical eq as E using (Erased; [_])
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥)
import Integer equality-with-J as Int
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J as Surjection using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent.Traditional eq

private
  variable
    a b h o : Level
    A B C D : Type a
    l₁ l₂   : Lens A B

------------------------------------------------------------------------
-- Lens combinators

-- If two types are isomorphic, then there is a lens between them.

↔→lens : A ↔ B → Lens A B
↔→lens A↔B = record
  { get     = to
  ; set     = const from
  ; get-set = const right-inverse-of
  ; set-get = left-inverse-of
  ; set-set = λ _ _ _ → refl _
  }
  where
  open _↔_ A↔B

-- If two types are equivalent, then there is a lens between them.

≃→lens : A ≃ B → Lens A B
≃→lens = ↔→lens ⊚ _≃_.bijection

-- Identity lens.

id : Lens A A
id = ↔→lens F.id

-- Composition of lenses.

infixr 9 _∘_

_∘_ : Lens B C → Lens A B → Lens A C
l₁ ∘ l₂ = record
  { get     = λ a → get l₁ (get l₂ a)
  ; set     = λ a c → set l₂ a (set l₁ (get l₂ a) c)
  ; get-set = λ a c →
      get l₁ (get l₂ (set l₂ a (set l₁ (get l₂ a) c)))  ≡⟨ cong (get l₁) $ get-set l₂ _ _ ⟩
      get l₁                   (set l₁ (get l₂ a) c)    ≡⟨ get-set l₁ _ _ ⟩∎
                                                  c     ∎
  ; set-get = λ a →
      set l₂ a (set l₁ (get l₂ a) (get l₁ (get l₂ a)))  ≡⟨ cong (set l₂ _) $ set-get l₁ _ ⟩
      set l₂ a         (get l₂ a)                       ≡⟨ set-get l₂ _ ⟩∎
             a                                          ∎
  ; set-set = λ a c₁ c₂ →
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁ (get l₂ (set l₂ a (set l₁ (get l₂ a) c₁))) c₂)  ≡⟨ set-set l₂ _ _ _ ⟩
      set l₂         a                         (set l₁ (get l₂ (set l₂ a (set l₁ (get l₂ a) c₁))) c₂)  ≡⟨ cong (λ b → set l₂ _ (set l₁ b _)) $
                                                                                                          get-set l₂ _ _ ⟩
      set l₂         a                         (set l₁                   (set l₁ (get l₂ a) c₁)   c₂)  ≡⟨ cong (set l₂ _) $ set-set l₁ _ _ _ ⟩∎
      set l₂         a                         (set l₁                           (get l₂ a)       c₂)  ∎
  }
  where
  open Lens

-- Note that composition can be defined in several different ways.
-- Here are two alternative implementations.

infixr 9 _∘′_ _∘″_

_∘′_ : Lens B C → Lens A B → Lens A C
l₁ ∘′ l₂ = record (l₁ ∘ l₂)
  { set-set = λ a c₁ c₂ →
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁ (get l₂ (set l₂ a (set l₁ (get l₂ a) c₁))) c₂)  ≡⟨ cong
                                                                                                            (λ b → set l₂ (set l₂ _ (set l₁ _ _))
                                                                                                                     (set l₁ b _)) $
                                                                                                          get-set l₂ _ _ ⟩
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁                   (set l₁ (get l₂ a) c₁)   c₂)  ≡⟨ set-set l₂ _ _ _ ⟩
      set l₂         a                         (set l₁                   (set l₁ (get l₂ a) c₁)   c₂)  ≡⟨ cong (set l₂ _) $ set-set l₁ _ _ _ ⟩∎
      set l₂         a                         (set l₁                           (get l₂ a)       c₂)  ∎
  }
  where
  open Lens

_∘″_ : Lens B C → Lens A B → Lens A C
l₁ ∘″ l₂ = record (l₁ ∘ l₂)
  { set-set = λ a c₁ c₂ →
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁ (get l₂ (set l₂ a (set l₁ (get l₂ a) c₁))) c₂)  ≡⟨ cong
                                                                                                            (λ b → set l₂ (set l₂ _ (set l₁ _ _))
                                                                                                                     (set l₁ b _)) $
                                                                                                          get-set l₂ _ _ ⟩
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁                   (set l₁ (get l₂ a) c₁)   c₂)  ≡⟨ cong (set l₂ _) $ set-set l₁ _ _ _ ⟩
      set l₂ (set l₂ a (set l₁ (get l₂ a) c₁)) (set l₁                           (get l₂ a)       c₂)  ≡⟨ set-set l₂ _ _ _ ⟩∎
      set l₂         a                         (set l₁                           (get l₂ a)       c₂)  ∎
  }
  where
  open Lens

-- These two implementations are pointwise equal to the other one.
-- However, I don't know if there is some other definition that is
-- distinct from these two (if we require that the definitions are
-- polymorphic, that get and set are implemented in the same way as
-- for _∘_, and that the three composition laws below hold).

∘≡∘′ : l₁ ∘ l₂ ≡ l₁ ∘′ l₂
∘≡∘′ {l₁ = l₁} {l₂ = l₂} = equal-laws→≡
  (λ _ _ → refl _)
  (λ _ → refl _)
  (λ a c₁ c₂ →
     let b₁ = set l₁ (get l₂ a) c₁
         b₂ = set l₁ b₁ c₂
         a′ = set l₂ a b₁
         b′ = set l₁ (get l₂ a′) c₂
     in
     set-set (l₁ ∘ l₂) a c₁ c₂                                          ≡⟨⟩

     trans (set-set l₂ a b₁ b′)
       (trans (cong (λ b → set l₂ a (set l₁ b c₂)) (get-set l₂ a b₁))
          (cong (set l₂ a) (set-set l₁ (get l₂ a) c₁ c₂)))              ≡⟨ sym $ trans-assoc _ _ _ ⟩

     trans (trans (set-set l₂ a b₁ b′)
              (cong (λ b → set l₂ a (set l₁ b c₂)) (get-set l₂ a b₁)))
       (cong (set l₂ a) (set-set l₁ (get l₂ a) c₁ c₂))                  ≡⟨ cong (flip trans _) $
                                                                           elim₁
                                                                             (λ eq →
                                                                                trans (set-set l₂ _ b₁ _)
                                                                                  (cong (λ b → set l₂ _ (set l₁ b _)) eq) ≡
                                                                                trans (cong (λ b → set l₂ _ (set l₁ b _)) eq)
                                                                                  (set-set l₂ _ _ _))
                                                                             (
         trans (set-set l₂ a b₁ b₂)
           (cong (λ b → set l₂ a (set l₁ b c₂)) (refl _))                     ≡⟨ trans (cong (trans _) $ cong-refl _) $
                                                                                 trans-reflʳ _ ⟩

         set-set l₂ a b₁ b₂                                                   ≡⟨ sym $
                                                                                 trans (cong (flip trans _) $ cong-refl _) $
                                                                                 trans-reflˡ _ ⟩∎
         trans (cong (λ b → set l₂ a′ (set l₁ b c₂)) (refl _))
           (set-set l₂ a b₁ b₂)                                               ∎)
                                                                             (get-set l₂ a b₁) ⟩
     trans (trans (cong (λ b → set l₂ a′ (set l₁ b c₂))
                     (get-set l₂ a b₁))
              (set-set l₂ a b₁ b₂))
       (cong (set l₂ a) (set-set l₁ (get l₂ a) c₁ c₂))                  ≡⟨ trans-assoc _ _ _ ⟩

     trans (cong (λ b → set l₂ a′ (set l₁ b c₂)) (get-set l₂ a b₁))
       (trans (set-set l₂ a b₁ b₂)
          (cong (set l₂ a) (set-set l₁ (get l₂ a) c₁ c₂)))              ≡⟨⟩

     set-set (l₁ ∘′ l₂) a c₁ c₂                                         ∎)
  where
  open Lens

∘≡∘″ : l₁ ∘ l₂ ≡ l₁ ∘″ l₂
∘≡∘″ {l₁ = l₁} {l₂ = l₂} = equal-laws→≡
  (λ _ _ → refl _)
  (λ _ → refl _)
  (λ a c₁ c₂ →
     let b₁ = set l₁ (get l₂ a) c₁
         b₂ = set l₁ (get l₂ a) c₂
         a′ = set l₂ a b₁
         b′ = set l₁ (get l₂ a′) c₂

         eq : b′ ≡ b₂
         eq = trans (cong (λ b → set l₁ b c₂) (get-set l₂ a b₁))
                (set-set l₁ (get l₂ a) c₁ c₂)
     in
     set-set (l₁ ∘ l₂) a c₁ c₂                                         ≡⟨⟩

     trans (set-set l₂ a b₁ b′)
       (trans (cong (λ b → set l₂ a (set l₁ b c₂)) (get-set l₂ a b₁))
          (cong (set l₂ a) (set-set l₁ (get l₂ a) c₁ c₂)))             ≡⟨ cong (trans (set-set l₂ a b₁ b′)) $
                                                                          trans (cong (flip trans _) $ sym $ cong-∘ _ _ _) $
                                                                          sym $ cong-trans _ _ _ ⟩

     trans (set-set l₂ a b₁ b′) (cong (set l₂ a) eq)                   ≡⟨ elim¹
                                                                            (λ {b₂} eq → trans (set-set l₂ a b₁ b′) (cong (set l₂ a) eq) ≡
                                                                                         trans (cong (set l₂ a′) eq) (set-set l₂ a b₁ b₂))
                                                                            (
         trans (set-set l₂ a b₁ b′) (cong (set l₂ a) (refl _))               ≡⟨ cong (trans _) $ cong-refl _ ⟩
         trans (set-set l₂ a b₁ b′) (refl _)                                 ≡⟨ trans-reflʳ _ ⟩
         set-set l₂ a b₁ b′                                                  ≡⟨ sym $ trans-reflˡ _ ⟩
         trans (refl _) (set-set l₂ a b₁ b′)                                 ≡⟨ cong (flip trans _) $ sym $ cong-refl _ ⟩∎
         trans (cong (set l₂ a′) (refl _)) (set-set l₂ a b₁ b′)              ∎)
                                                                            eq ⟩

     trans (cong (set l₂ a′) eq) (set-set l₂ a b₁ b₂)                  ≡⟨ trans (cong (flip trans _) $
                                                                                 trans (cong-trans _ _ _) $
                                                                                 cong (flip trans _) $ cong-∘ _ _ _) $
                                                                          trans-assoc _ _ _ ⟩
     trans (cong (λ b → set l₂ a′ (set l₁ b c₂)) (get-set l₂ a b₁))
       (trans (cong (set l₂ a′) (set-set l₁ (get l₂ a) c₁ c₂))
          (set-set l₂ a b₁ b₂))                                        ≡⟨⟩

     set-set (l₁ ∘″ l₂) a c₁ c₂                                        ∎)
  where
  open Lens

-- id is a left identity of _∘_.

left-identity : (l : Lens A B) → id ∘ l ≡ l
left-identity l = equal-laws→≡
  (λ a b →
     trans (cong P.id (get-set a b)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
     cong P.id (get-set a b)                   ≡⟨ sym $ cong-id _ ⟩∎
     get-set a b                               ∎)
  (λ a →
     trans (cong (set a) (refl _)) (set-get a)  ≡⟨ cong (flip trans _) $ cong-refl _ ⟩
     trans (refl _) (set-get a)                 ≡⟨ trans-reflˡ _ ⟩∎
     set-get a                                  ∎)
  (λ a b₁ b₂ →
     trans (set-set a b₁ b₂)
       (trans (cong (λ _ → set a b₂) (get-set a b₁))
          (cong (set a) (refl _)))                      ≡⟨ cong₂ (λ p q → trans _ (trans p q))
                                                             (cong-const _)
                                                             (cong-refl _) ⟩

     trans (set-set a b₁ b₂) (trans (refl _) (refl _))  ≡⟨ trans (cong (trans _) trans-refl-refl) $
                                                           trans-reflʳ _ ⟩∎
     set-set a b₁ b₂                                    ∎)
  where
  open Lens l

-- id is a right identity of _∘_.

right-identity : (l : Lens A B) → l ∘ id ≡ l
right-identity l = equal-laws→≡
  (λ a b →
     trans (cong get (refl _)) (get-set a b)  ≡⟨ cong (flip trans _) $ cong-refl _ ⟩
     trans (refl _) (get-set a b)             ≡⟨ trans-reflˡ _ ⟩∎
     get-set a b                              ∎)
  (λ a →
     trans (cong P.id (set-get a)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
     cong P.id (set-get a)                   ≡⟨ sym $ cong-id _ ⟩∎
     set-get a                               ∎)
  (λ a b₁ b₂ →
     trans (refl _)
       (trans (cong (λ b → set b b₂) (refl _))
          (cong P.id (set-set a b₁ b₂)))        ≡⟨ trans-reflˡ _ ⟩

     trans (cong (λ b → set b b₂) (refl _))
       (cong P.id (set-set a b₁ b₂))            ≡⟨ cong₂ trans (cong-refl _) (sym $ cong-id _) ⟩

     trans (refl _) (set-set a b₁ b₂)           ≡⟨ trans-reflˡ _ ⟩∎

     set-set a b₁ b₂                            ∎)
  where
  open Lens l

-- _∘_ is associative.

associativity :
  (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
  l₁ ∘ (l₂ ∘ l₃) ≡ (l₁ ∘ l₂) ∘ l₃
associativity l₁ l₂ l₃ = equal-laws→≡ lemma₁ lemma₂ lemma₃
  where
  open Lens

  lemma₁ = λ a d →
    let
      f  = get l₁
      g  = get l₂
      b  = get l₃ a
      c  = g b
      c′ = set l₁ c d
      x  = get-set l₃ a (set l₂ b c′)
      y  = get-set l₂ b c′
      z  = get-set l₁ c d
    in
    trans (cong f $ trans (cong g x) y) z           ≡⟨ cong (λ x → trans x z) (cong-trans f _ y) ⟩
    trans (trans (cong f $ cong g x) (cong f y)) z  ≡⟨ trans-assoc _ _ z ⟩
    trans (cong f $ cong g x) (trans (cong f y) z)  ≡⟨ cong (λ x → trans x (trans (cong f y) z)) (cong-∘ f g x) ⟩∎
    trans (cong (f ⊚ g) x) (trans (cong f y) z)     ∎

  lemma₂ = λ a →
    let
      b = get l₃ a
      f = set l₃ a
      g = set l₂ b
      x = set-get l₁ (get l₂ b)
      y = set-get l₂ b
      z = set-get l₃ a
    in
    trans (cong (f ⊚ g) x) (trans (cong f y) z)     ≡⟨ sym $ trans-assoc _ _ z ⟩
    trans (trans (cong (f ⊚ g) x) (cong f y)) z     ≡⟨ cong (λ x → trans (trans x (cong f y)) z) (sym $ cong-∘ f g x) ⟩
    trans (trans (cong f (cong g x)) (cong f y)) z  ≡⟨ cong (λ x → trans x z) (sym $ cong-trans f _ y) ⟩∎
    trans (cong f $ trans (cong g x) y) z           ∎

  lemma₃ = λ a d₁ d₂ →
    let
      f   = set l₃ a
      g   = set l₂ (get l₃ a)
      h   = λ x → set l₁ x d₂
      i   = get l₂

      c₁  = set l₁ (get (l₂ ∘ l₃) a) d₁
      c₂  = h (i (get l₃ a))
      c₂′ = h (i (get l₃ (set (l₂ ∘ l₃) a c₁)))
      c₂″ = h (i (set l₂ (get l₃ a) c₁))

      b₁  = g c₁
      b₁′ = get l₃ (f b₁)

      x   = set-set l₃ a b₁ (set l₂ b₁′ c₂′)
      y   = get-set l₃ a b₁
      z   = set-set l₂ (get l₃ a) c₁
      u   = get-set l₂ (get l₃ a) c₁
      v   = set-set l₁ (get (l₂ ∘ l₃) a) d₁ d₂

      c₂′≡c₂″ =
        c₂′  ≡⟨ cong (h ⊚ i) y ⟩∎
        c₂″  ∎

      lemma₁₀ =
        trans (sym (cong (h ⊚ i) y)) (cong h (cong i y))  ≡⟨ cong (trans _) (cong-∘ h i y) ⟩
        trans (sym (cong (h ⊚ i) y)) (cong (h ⊚ i) y)     ≡⟨ trans-symˡ (cong (h ⊚ i) y) ⟩∎
        refl _                                            ∎

      lemma₉ =
        trans (cong (λ x → set l₂ x c₂′) y) (cong (set l₂ b₁) c₂′≡c₂″)  ≡⟨ cong (trans (cong (λ x → set l₂ x c₂′) y))
                                                                                (cong-∘ (set l₂ b₁) (h ⊚ i) y) ⟩
        trans (cong (λ x → set l₂ x  (h (i b₁′))) y)
              (cong (λ x → set l₂ b₁ (h (i x  ))) y)                    ≡⟨ trans-cong-cong (λ x y → set l₂ x (h (i y))) y ⟩∎

        cong (λ x → set l₂ x (h (i x))) y                               ∎

      lemma₈ =
        sym (cong (set l₂ b₁) (sym c₂′≡c₂″))  ≡⟨ sym $ cong-sym (set l₂ b₁) (sym c₂′≡c₂″) ⟩
        cong (set l₂ b₁) (sym (sym c₂′≡c₂″))  ≡⟨ cong (cong (set l₂ b₁)) (sym-sym c₂′≡c₂″) ⟩∎
        cong (set l₂ b₁) c₂′≡c₂″              ∎

      lemma₇ =
        trans (cong g (sym c₂′≡c₂″)) (cong g (cong h (cong i y)))  ≡⟨ sym $ cong-trans g _ (cong h (cong i y)) ⟩
        cong g (trans (sym c₂′≡c₂″) (cong h (cong i y)))           ≡⟨ cong (cong g) lemma₁₀ ⟩
        cong g (refl _)                                            ≡⟨ cong-refl _ ⟩∎
        refl _                                                     ∎

      lemma₆ =
        trans (cong (λ x → set l₂ x c₂′) y)
              (trans (cong (set l₂ b₁) c₂′≡c₂″)
                     (trans (z c₂″) (cong g (sym c₂′≡c₂″))))       ≡⟨ sym $ trans-assoc _ _ (trans _ (cong g (sym c₂′≡c₂″))) ⟩

        trans (trans (cong (λ x → set l₂ x c₂′) y)
                     (cong (set l₂ b₁) c₂′≡c₂″))
              (trans (z c₂″) (cong g (sym c₂′≡c₂″)))               ≡⟨ cong (λ e → trans e (trans (z c₂″) (cong g (sym c₂′≡c₂″)))) lemma₉ ⟩

        trans (cong (λ x → set l₂ x (h (i x))) y)
              (trans (z c₂″) (cong g (sym c₂′≡c₂″)))               ≡⟨ sym $ trans-assoc _ _ (cong g (sym c₂′≡c₂″)) ⟩∎

        trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
              (cong g (sym c₂′≡c₂″))                               ∎

      lemma₅ =
        z c₂′                                                  ≡⟨ sym $ dcong z (sym c₂′≡c₂″) ⟩

        subst (λ x → set l₂ b₁ x ≡ g x) (sym c₂′≡c₂″) (z c₂″)  ≡⟨ subst-in-terms-of-trans-and-cong {f = set l₂ b₁} {g = g} {x≡y = sym c₂′≡c₂″} ⟩

        trans (sym (cong (set l₂ b₁) (sym c₂′≡c₂″)))
              (trans (z c₂″) (cong g (sym c₂′≡c₂″)))           ≡⟨ cong (λ e → trans e (trans (z c₂″) (cong g (sym c₂′≡c₂″)))) lemma₈ ⟩∎

        trans (cong (set l₂ b₁) c₂′≡c₂″)
              (trans (z c₂″) (cong g (sym c₂′≡c₂″)))           ∎

      lemma₄ =
        trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
              (cong g (cong h (cong i y)))                            ≡⟨ cong (λ e → trans (trans (cong (λ x → set l₂ x c₂′) y) e)
                                                                                                  (cong g (cong h (cong i y))))
                                                                              lemma₅ ⟩
        trans (trans (cong (λ x → set l₂ x c₂′) y)
                     (trans (cong (set l₂ b₁) c₂′≡c₂″)
                            (trans (z c₂″) (cong g (sym c₂′≡c₂″)))))
              (cong g (cong h (cong i y)))                            ≡⟨ cong (λ e → trans e (cong g (cong h (cong i y)))) lemma₆ ⟩

        trans (trans (trans (cong (λ x → set l₂ x (h (i x))) y)
                            (z c₂″))
                     (cong g (sym c₂′≡c₂″)))
              (cong g (cong h (cong i y)))                            ≡⟨ trans-assoc _ _ (cong g (cong h (cong i y))) ⟩

        trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
              (trans (cong g (sym c₂′≡c₂″))
                     (cong g (cong h (cong i y))))                    ≡⟨ cong (trans (trans _ (z c₂″))) lemma₇ ⟩

        trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
              (refl _)                                                ≡⟨ trans-reflʳ _ ⟩∎

        trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″)             ∎

      lemma₃ =
        cong g (trans (cong h (trans (cong i y) u)) v)           ≡⟨ cong (λ e → cong g (trans e v)) (cong-trans h _ u) ⟩

        cong g (trans (trans (cong h (cong i y)) (cong h u)) v)  ≡⟨ cong (cong g) (trans-assoc _ _ v) ⟩

        cong g (trans (cong h (cong i y)) (trans (cong h u) v))  ≡⟨ cong-trans g _ (trans _ v) ⟩∎

        trans (cong g (cong h (cong i y)))
              (cong g (trans (cong h u) v))                      ∎

      lemma₂ =
        trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
              (cong g (trans (cong h (trans (cong i y) u)) v))      ≡⟨ cong (trans (trans _ (z c₂′))) lemma₃ ⟩

        trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
              (trans (cong g (cong h (cong i y)))
                     (cong g (trans (cong h u) v)))                 ≡⟨ sym $ trans-assoc _ _ (cong g (trans _ v)) ⟩

        trans (trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                     (cong g (cong h (cong i y))))
              (cong g (trans (cong h u) v))                         ≡⟨ cong (λ e → trans e (cong g (trans (cong h u) v))) lemma₄ ⟩

        trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
              (cong g (trans (cong h u) v))                         ≡⟨ trans-assoc _ _ (cong g (trans _ v)) ⟩∎

        trans (cong (λ x → set l₂ x (h (i x))) y)
              (trans (z c₂″) (cong g (trans (cong h u) v)))         ∎

      lemma₁ =
        trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
              (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))    ≡⟨ cong (λ e → trans
                                                                                         (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))) e)
                                                                                (sym $ cong-∘ f g (trans _ v)) ⟩
        trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
              (cong f (cong g (trans (cong h (trans (cong i y) u))
                                     v)))                               ≡⟨ sym $ cong-trans f (trans _ (z c₂′)) (cong g (trans _ v)) ⟩

        cong f (trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                      (cong g (trans (cong h (trans (cong i y) u))
                                     v)))                               ≡⟨ cong (cong f) lemma₂ ⟩

        cong f (trans (cong (λ x → set l₂ x (h (i x))) y)
                      (trans (z c₂″) (cong g (trans (cong h u) v))))    ≡⟨ cong-trans _ _ _ ⟩

        trans (cong f (cong (λ x → set l₂ x (h (i x))) y))
          (cong f (trans (z c₂″) (cong g (trans (cong h u) v))))        ≡⟨ cong₂ (λ p q → trans p (cong f (trans (z c₂″) q)))
                                                                             (cong-∘ _ _ _)
                                                                             (trans (cong-trans _ _ _) $
                                                                              cong (flip trans _) $
                                                                              cong-∘ _ _ _) ⟩∎
        trans (cong (λ x → f (set l₂ x (h (i x)))) y)
          (cong f (trans (z c₂″) (trans (cong (g ⊚ h) u) (cong g v))))  ∎

    in
    trans (trans x (trans (cong (λ x → f (set l₂ x c₂′)) y)
                      (cong f (z c₂′))))
      (trans (cong (f ⊚ g ⊚ h) (trans (cong i y) u))
         (cong (f ⊚ g) v))                                          ≡⟨ cong₂ (λ p q → trans (trans x p) q)
                                                                         (trans (cong (flip trans _) $ sym $ cong-∘ _ _ _) $
                                                                          sym $ cong-trans _ _ _)
                                                                         (trans (cong (flip trans _) $ sym $ cong-∘ _ _ _) $
                                                                          sym $ cong-trans _ _ _) ⟩
    trans (trans x (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                  (z c₂′))))
          (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))    ≡⟨ trans-assoc _ _ _ ⟩

    trans x (trans (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                  (z c₂′)))
                   (cong (f ⊚ g)
                         (trans (cong h (trans (cong i y) u)) v)))  ≡⟨ cong (trans x) lemma₁ ⟩∎

    trans x (trans (cong (λ x → f (set l₂ x (h (i x)))) y)
               (cong f (trans (z c₂″) (trans (cong (g ⊚ h) u)
                                         (cong g v)))))             ∎

-- Every lens of type Lens A A that satisfies a certain right
-- identity law is equal to the identity lens.

id-unique :
  (id′ : Lens A A) →
  ((l : Lens A A) → l ∘ id′ ≡ l) →
  id′ ≡ id
id-unique id′ right-identity =
  id′       ≡⟨ sym $ left-identity _ ⟩
  id ∘ id′  ≡⟨ right-identity _ ⟩∎
  id        ∎

-- An equality characterisation lemma that can be used when one of
-- the lenses is the identity.

equality-characterisation-id :
  {l : Lens A A} → let open Lens l in

  l ≡ id
    ↔
  ∃ λ (g : ∀ a → get a ≡ a) →
  ∃ λ (s : ∀ a b → set a b ≡ b) →
    (∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
    (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
    (∀ a b₁ b₂ →
       trans (set-set a b₁ b₂) (s a b₂) ≡
       cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
equality-characterisation-id {l = l} =
  l ≡ id                                                              ↝⟨ equality-characterisation₄ ⟩

  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a b → set a b ≡ b) →
     (∀ a b →
        trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
        refl _) ×
     (∀ a →
        trans (sym (trans (s a (get a)) (cong P.id (g a))))
          (set-get a) ≡
        refl _) ×
     (∀ a b₁ b₂ →
        trans (set-set a b₁ b₂) (s a b₂) ≡
        trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
          (refl _)))                                                  ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∃-cong λ _ →
                                                                          (∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (λ eq → trans (sym (trans _ eq)) (set-get _) ≡ _) $ sym $
                                                                           cong-id (g _))
                                                                           ×-cong
                                                                          ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (_ ≡_) $ trans-reflʳ _) ⟩
  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a b → set a b ≡ b) →
     (∀ a b →
        trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
        refl _) ×
     (∀ a →
        trans (sym (trans (s a (get a)) (g a))) (set-get a) ≡
        refl _) ×
     (∀ a b₁ b₂ →
        trans (set-set a b₁ b₂) (s a b₂) ≡
        cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                          (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                           ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                            ×-cong
                                                                          (∀-cong ext λ _ →
                                                                           ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                           ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                            ×-cong
                                                                          F.id) ⟩□
  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a b → set a b ≡ b) →
     (∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
     (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
     (∀ a b₁ b₂ →
        trans (set-set a b₁ b₂) (s a b₂) ≡
        cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        □
  where
  open Lens l

-- A lemma that can be used to show that a lens with a constant
-- setter (such as the ones produced by getter-equivalence→lens
-- below) is equal to the identity lens.

constant-setter→≡id :
  {l′ : ∃ λ (get : A → A) →
        ∃ λ (set : A → A) →
          (A → ∀ a → get (set a) ≡ a) ×
          (∀ a → set (get a) ≡ a) ×
          (A → A → ∀ a → set a ≡ set a)} →

  let l   = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
      set = proj₁ (proj₂ l′)
      open Lens l hiding (set)
  in

  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a → set a ≡ a) →
     (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
     (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
     (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _)) →
  l ≡ id
constant-setter→≡id {A = A} {l′ = l′} =
  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a → set a ≡ a) →
     (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
     (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
     (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _))                          ↝⟨ (Σ-map P.id $ Σ-map P.id λ {s} → Σ-map P.id $ Σ-map P.id λ hyp a a₁ a₂ →

      trans (set-set a a₁ a₂) (s a₂)                                        ≡⟨ cong (λ eq → trans eq (s a₂)) $ hyp _ _ _ ⟩
      trans (refl _) (s a₂)                                                 ≡⟨ trans-reflˡ (s _) ⟩∎
      s a₂                                                                  ∎) ⟩

  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a → set a ≡ a) →
     (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
     (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
     (∀ a a₁ a₂ → trans (set-set a a₁ a₂) (s a₂) ≡ s a₂))             ↔⟨ (∃-cong λ _ → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                          ∀-cong ext λ a → ∀-cong ext λ a₁ → ∀-cong ext λ a₂ →
                                                                          ≡⇒↝ equivalence $ cong (trans _ (s _) ≡_) (
      s a₂                                                                  ≡⟨ sym $ cong-ext ext ⟩
      cong (λ set → set a₂) (⟨ext⟩ s)                                       ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ s) ⟩
      cong (λ set → set (set a a₁) a₂) (cong const (⟨ext⟩ s))               ≡⟨ cong (cong (λ set → set (set a a₁) a₂)) $ sym $
                                                                               ext-const ext ⟩∎
      cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s)                ∎)) ⟩

  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : ∀ a → set a ≡ a) →
     (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
     (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
     (∀ a a₁ a₂ →
        trans (set-set a a₁ a₂) (s a₂) ≡
        cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s)))      ↝⟨ Σ-map P.id (Σ-map const P.id) ⟩

  (∃ λ (g : ∀ a → get a ≡ a) →
   ∃ λ (s : A → ∀ a → set a ≡ a) →
     (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₁ a₂)) (g a₂)) ×
     (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
     (∀ a a₁ a₂ →
        trans (set-set a a₁ a₂) (s a a₂) ≡
        cong (λ set → set (set a a₁) a₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        ↔⟨ inverse equality-characterisation-id ⟩□

  l″ ≡ id                                                             □
  where
  l″  = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
  set = proj₁ (proj₂ l′)

  open Lens l″ hiding (set)

-- An identity function for lenses for which the forward direction
-- is an equivalence.
--
-- Note that the setter of the resulting lens is definitionally
-- equal to a constant function returning the right-to-left
-- direction of the equivalence.
--
-- Note also that two proofs, set-get and set-set, have been
-- "obfuscated". They could have been shorter, but then it might not
-- have been possible to prove getter-equivalence→lens≡.

getter-equivalence→lens :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) →
  Lens A B
getter-equivalence→lens l is-equiv = record
  { get     = to
  ; set     = const from
  ; get-set = const right-inverse-of
  ; set-get = λ a →
              from (to a)                ≡⟨ cong from (sym (get-set a (to a))) ⟩
              from (get (set a (to a)))  ≡⟨⟩
              from (to (set a (get a)))  ≡⟨ cong (from ⊚ to) (set-get a) ⟩
              from (to a)                ≡⟨ left-inverse-of _ ⟩∎
              a                          ∎
  ; set-set = λ a b₁ b₂ →
              let s = from≡set l is-equiv in
              from b₂            ≡⟨ cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)) ⟩
              set (set a b₁) b₂  ≡⟨ set-set a b₁ b₂ ⟩
              set a b₂           ≡⟨ sym (s a b₂) ⟩∎
              from b₂            ∎
  }
  where
  A≃B = Eq.⟨ _ , is-equiv ⟩

  open _≃_ A≃B
  open Lens l

-- The function getter-equivalence→lens returns its input.

getter-equivalence→lens≡ :
  ∀ (l : Lens A B) is-equiv →
  getter-equivalence→lens l is-equiv ≡ l
getter-equivalence→lens≡ l is-equiv =
  _↔_.from equality-characterisation₄
    ( g
    , s
    , lemma₁
    , lemma₂
    , lemma₃
    )
  where
  open Lens

  A≃B = Eq.⟨ get l , is-equiv ⟩

  open _≃_ A≃B

  l′ = getter-equivalence→lens l is-equiv

  g = λ _ → refl _

  s = from≡set l is-equiv

  lemma₁ = λ a b →
    let lem =
          cong (get l) (s a b)                               ≡⟨⟩

          cong (get l)
            (trans (cong from (sym (get-set l a b)))
               (left-inverse-of _))                          ≡⟨ cong-trans _ _ (left-inverse-of _) ⟩

          trans (cong (get l)
                   (cong from (sym (get-set l a b))))
            (cong (get l) (left-inverse-of _))               ≡⟨ cong₂ trans
                                                                  (cong-∘ _ _ (sym (get-set l a b)))
                                                                  (left-right-lemma _) ⟩∎
          trans (cong (get l ⊚ from) (sym (get-set l a b)))
            (right-inverse-of _)                             ∎
    in
    trans (sym (trans (cong (get l) (s a b))
                  (g (set l a b))))
      (get-set l′ a b)                                        ≡⟨⟩

    trans (sym (trans (cong (get l) (s a b)) (refl _)))
      (right-inverse-of _)                                    ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) $
                                                                 trans-reflʳ _ ⟩
    trans (sym (cong (get l) (s a b)))
      (right-inverse-of _)                                    ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) lem ⟩

    trans (sym (trans (cong (get l ⊚ from)
                         (sym (get-set l a b)))
                  (right-inverse-of _)))
      (right-inverse-of _)                                    ≡⟨ elim¹
                                                                   (λ eq → trans (sym (trans (cong (get l ⊚ from) (sym eq))
                                                                                         (right-inverse-of _)))
                                                                             (right-inverse-of _) ≡ eq) (
      trans (sym (trans (cong (get l ⊚ from) (sym (refl _)))
                    (right-inverse-of _)))
        (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym (trans (cong (get l ⊚ from) eq) _)) _)
                                                                        sym-refl ⟩
      trans (sym (trans (cong (get l ⊚ from) (refl _))
                    (right-inverse-of _)))
        (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym (trans eq _)) _) $
                                                                        cong-refl _ ⟩
      trans (sym (trans (refl _) (right-inverse-of _)))
        (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) $
                                                                        trans-reflˡ (right-inverse-of _) ⟩
      trans (sym (right-inverse-of _))
        (right-inverse-of _)                                         ≡⟨ trans-symˡ (right-inverse-of _) ⟩∎

      refl _                                                         ∎)
                                                                   _ ⟩∎
    get-set l a b                                             ∎

  lemma₂ = λ a →
    trans (sym (trans (s a (get l a)) (cong (set l a) (g a))))
       (set-get l′ a)                                                  ≡⟨⟩

    trans (sym (trans (s a (get l a)) (cong (set l a) (refl _))))
       (set-get l′ a)                                                  ≡⟨ cong (λ eq → trans (sym (trans (s a (get l a)) eq)) (set-get l′ a)) $
                                                                          cong-refl _ ⟩

    trans (sym (trans (s a (get l a)) (refl _))) (set-get l′ a)        ≡⟨ cong (λ eq → trans (sym eq) (set-get l′ a)) $
                                                                          trans-reflʳ _ ⟩

    trans (sym (s a (get l a))) (set-get l′ a)                         ≡⟨⟩

    trans (sym (trans (cong from (sym (get-set l a (get l a))))
                  (left-inverse-of _)))
      (trans (cong from (sym (get-set l a (get l a))))
         (trans (cong (from ⊚ get l) (set-get l a))
            (left-inverse-of _)))                                      ≡⟨ cong (λ eq → trans (sym (trans
                                                                                                     (cong from (sym (get-set l a (get l a))))
                                                                                                     (left-inverse-of _)))
                                                                                         (trans (cong from (sym (get-set l a (get l a)))) eq)) $
                                                                          elim¹
                                                                            (λ eq → trans (cong (from ⊚ get l) eq) (left-inverse-of _) ≡
                                                                                    trans (left-inverse-of _) eq)
                                                                            (
        trans (cong (from ⊚ get l) (refl _))
          (left-inverse-of (set l a (get l a)))                              ≡⟨ cong (flip trans _) $ cong-refl _ ⟩

        trans (refl _) (left-inverse-of (set l a (get l a)))                 ≡⟨ trans-reflˡ _ ⟩

        left-inverse-of (set l a (get l a))                                  ≡⟨ sym $ trans-reflʳ _ ⟩∎

        trans (left-inverse-of (set l a (get l a))) (refl _)                 ∎)
                                                                            (set-get l a) ⟩
    trans (sym (trans (cong from
                         (sym (get-set l a (get l a))))
                  (left-inverse-of _)))
      (trans (cong from (sym (get-set l a (get l a))))
         (trans (left-inverse-of _) (set-get l a)))                    ≡⟨ cong (trans _) $ sym $
                                                                          trans-assoc _ _ (set-get l a) ⟩
    trans (sym (trans (cong from
                         (sym (get-set l a (get l a))))
                  (left-inverse-of _)))
      (trans (trans (cong from (sym (get-set l a (get l a))))
               (left-inverse-of _))
         (set-get l a))                                                ≡⟨ trans-sym-[trans] _ _ ⟩∎

    set-get l a                                                        ∎

  lemma₃ = λ a b₁ b₂ →
    trans (set-set l′ a b₁ b₂) (s a b₂)                           ≡⟨⟩

    trans (trans (cong (λ set → set (set a b₁) b₂)
                    (⟨ext⟩ (⟨ext⟩ ⊚ s)))
             (trans (set-set l a b₁ b₂)
                (sym (s a b₂))))
      (s a b₂)                                                    ≡⟨ cong (λ eq → trans eq (s a b₂)) $ sym $
                                                                     trans-assoc _ _ (sym (s a b₂)) ⟩
    trans (trans (trans (cong (λ set → set (set a b₁) b₂)
                           (⟨ext⟩ (⟨ext⟩ ⊚ s)))
                    (set-set l a b₁ b₂))
             (sym (s a b₂)))
      (s a b₂)                                                    ≡⟨ trans-[trans-sym]- _ (s a b₂) ⟩∎

    trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
      (set-set l a b₁ b₂)                                         ∎

------------------------------------------------------------------------
-- Some existence results

-- The lenses bad a and id {A = ↑ a 𝕊¹} have equal setters, and their
-- getters are equivalences, but they are not equal (assuming
-- univalence).

equal-setters-and-equivalences-as-getters-but-not-equal :
  Univalence lzero →
  let l₁ = bad a
      l₂ = id {A = ↑ a 𝕊¹}
  in
  Is-equivalence (Lens.get l₁) ×
  Is-equivalence (Lens.get l₂) ×
  Lens.set l₁ ≡ Lens.set l₂ ×
  l₁ ≢ l₂
equal-setters-and-equivalences-as-getters-but-not-equal {a = ℓa} univ =
  let is-equiv , not-coherent , _ =
        getter-equivalence-but-not-coherent univ
  in
    is-equiv
  , _≃_.is-equivalence F.id
  , refl _
  , (bad ℓa ≡ id                                        ↝⟨ (λ eq → subst (λ l → ∀ a → cong (get l) (set-get l a) ≡
                                                                                      get-set l a (get l a))
                                                                         (sym eq)
                                                                         (λ _ → cong-refl _)) ⟩
     (∀ a → cong (get (bad ℓa)) (set-get (bad ℓa) a) ≡
            get-set (bad ℓa) a (get (bad ℓa) a))        ↝⟨ not-coherent ⟩□
     ⊥                                                  □)
  where
  open Lens

-- There is in general no split surjection from equivalences to lenses
-- with getters that are equivalences, if the right-to-left direction
-- of the split surjection is required to return the lens's getter
-- plus some proof (assuming univalence).

¬-≃-↠-Σ-Lens-Is-equivalence-get :
  Univalence lzero →
  ¬ ∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠
             (∃ λ (l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) →
                Is-equivalence (Lens.get l))) →
      ∀ p → _≃_.to (_↠_.from f p) ≡ Lens.get (proj₁ p)
¬-≃-↠-Σ-Lens-Is-equivalence-get {a = a} univ =
  let is-equiv₁ , is-equiv₂ , _ , bad≢id =
        equal-setters-and-equivalences-as-getters-but-not-equal univ
  in
  λ (f , hyp) →                                $⟨ refl _ ⟩

    Lens.get (bad a) ≡ Lens.get id             ↝⟨ (λ eq → trans (hyp _) (trans eq (sym (hyp _)))) ⟩

    _≃_.to (_↠_.from f (bad a , is-equiv₁)) ≡
    _≃_.to (_↠_.from f (id , is-equiv₂))       ↝⟨ Eq.lift-equality ext ⟩

    _↠_.from f (bad a , is-equiv₁) ≡
    _↠_.from f (id , is-equiv₂)                ↝⟨ _↠_.to (Surjection.↠-≡ f) ⟩

    (bad a , is-equiv₁) ≡ (id , is-equiv₂)     ↝⟨ cong proj₁ ⟩

    bad a ≡ id                                 ↝⟨ bad≢id ⟩□

    ⊥                                          □

-- There is in general no equivalence from equivalences to lenses with
-- getters that are equivalences, if the right-to-left direction of
-- the equivalence is required to return the lens's getter plus some
-- proof (assuming univalence).

¬-≃-≃-Σ-Lens-Is-equivalence-get :
  Univalence lzero →
  ¬ ∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ≃
             (∃ λ (l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) → Is-equivalence (Lens.get l))) →
      ∀ p → _≃_.to (_≃_.from f p) ≡ Lens.get (proj₁ p)
¬-≃-≃-Σ-Lens-Is-equivalence-get {a = a} univ =
  (∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ≃
            (∃ λ (l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) →
               Is-equivalence (Lens.get l))) →
     ∀ p → _≃_.to (_≃_.from f p) ≡ Lens.get (proj₁ p))  ↝⟨ Σ-map _≃_.surjection P.id ⟩

  (∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠
            (∃ λ (l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) →
               Is-equivalence (Lens.get l))) →
     ∀ p → _≃_.to (_↠_.from f p) ≡ Lens.get (proj₁ p))  ↝⟨ ¬-≃-↠-Σ-Lens-Is-equivalence-get univ ⟩□

  ⊥                                                     □

-- The lemma ≃Σ∥set⁻¹∥× does not hold in general if the requirement
-- that A is a set is dropped (assuming univalence).
--
-- I proved this together with Paolo Capriotti.

≄Σ∥set⁻¹∥× :
  Univalence lzero →
  ¬ ({A B : Type a} (l : Lens A B) →
     A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ f ∥) × B))
≄Σ∥set⁻¹∥× {a = a} univ =
  ({A B : Type a} (l : Lens A B) →
   A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ f ∥) × B))                      ↝⟨ (λ hyp → hyp) ⟩

  ((l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) →
   ↑ a 𝕊¹ ≃ ((∃ λ (f : ↑ a 𝕊¹ → ↑ a 𝕊¹) → ∥ Lens.set l ⁻¹ f ∥) × ↑ a 𝕊¹))  ↝⟨ _$ id ⟩

  ↑ a 𝕊¹ ≃ ((∃ λ (f : ↑ a 𝕊¹ → ↑ a 𝕊¹) → ∥ const P.id ⁻¹ f ∥) × ↑ a 𝕊¹)    ↝⟨ lemma ⟩

  𝕊¹ ≃ (𝕊¹ × 𝕊¹)                                                           ↝⟨ 𝕊¹≄𝕊¹×𝕊¹ ⟩□

  ⊥                                                                        □
  where
  open Circle
  open Int

  lemma = λ hyp →
    𝕊¹                                                            ↔⟨ inverse Bijection.↑↔ ⟩

    ↑ a 𝕊¹                                                        ↝⟨ hyp ⟩

    (∃ λ (f : ↑ a 𝕊¹ → ↑ a 𝕊¹) → ∥ const P.id ⁻¹ f ∥) × ↑ a 𝕊¹    ↔⟨⟩

    (∃ λ (f : ↑ a 𝕊¹ → ↑ a 𝕊¹) → ∥ ↑ a 𝕊¹ × P.id ≡ f ∥) × ↑ a 𝕊¹  ↝⟨ (×-cong₁ λ _ → ∃-cong λ _ → T.∥∥-cong-⇔ $
                                                                      record { to = proj₂; from = λ eq → lift base , eq }) ⟩

    (∃ λ (f : ↑ a 𝕊¹ → ↑ a 𝕊¹) → ∥ P.id ≡ f ∥) × ↑ a 𝕊¹           ↝⟨ (Σ-cong (→-cong ext Bijection.↑↔ Bijection.↑↔) λ _ → T.∥∥-cong $
                                                                      inverse $ Eq.≃-≡ (Eq.↔⇒≃ $ →-cong ext Bijection.↑↔ Bijection.↑↔))
                                                                       ×-cong
                                                                     Eq.↔⇒≃ Bijection.↑↔ ⟩

    (∃ λ (f : 𝕊¹ → 𝕊¹) → ∥ P.id ≡ f ∥) × 𝕊¹                       ↝⟨ (×-cong₁ λ _ →
                                                                      Σ-cong (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) λ f →
                                                                      T.∥∥-cong (
      P.id ≡ f                                                          ↝⟨ inverse $ Eq.≃-≡ $ 𝕊¹→𝕊¹≃𝕊¹×ℤ univ ⟩
      _≃_.to (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) P.id ≡ _≃_.to (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) f        ↝⟨ ≡⇒≃ $ cong (_≡ _≃_.to (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) f) $ 𝕊¹→𝕊¹≃𝕊¹×ℤ-id univ ⟩
      (base , + 1) ≡ _≃_.to (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) f                         ↔⟨ ≡-comm ⟩□
      _≃_.to (𝕊¹→𝕊¹≃𝕊¹×ℤ univ) f ≡ (base , + 1)                         □)) ⟩

    (∃ λ (p : 𝕊¹ × ℤ) → ∥ p ≡ (base , + 1) ∥) × 𝕊¹                ↔⟨ (×-cong₁ λ _ → ∃-cong λ _ → inverse $
                                                                      T.∥∥-cong ≡×≡↔≡ F.∘ T.∥∥×∥∥↔∥×∥) ⟩

    (∃ λ ((x , i) : 𝕊¹ × ℤ) → ∥ x ≡ base ∥ × ∥ i ≡ + 1 ∥) × 𝕊¹    ↔⟨ (×-cong₁ λ _ →
                                                                      Σ-assoc F.∘
                                                                      (∃-cong λ _ → ∃-comm) F.∘
                                                                      inverse Σ-assoc) ⟩

    ((∃ λ x → ∥ x ≡ base ∥) × (∃ λ i → ∥ i ≡ + 1 ∥)) × 𝕊¹         ↔⟨ (×-cong₁ λ _ →
                                                                      (drop-⊤-right λ _ →
                                                                       T.inhabited⇒∥∥↔⊤ $ all-points-on-the-circle-are-merely-equal _)
                                                                        ×-cong
                                                                      ∃-cong λ _ → T.∥∥↔ ℤ-set) ⟩

    (𝕊¹ × (∃ λ i → i ≡ + 1)) × 𝕊¹                                 ↔⟨ (×-cong₁ λ _ → drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                      singleton-contractible _) ⟩□
    𝕊¹ × 𝕊¹                                                       □

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private

  module B {a} =
    Bi-invertibility
      equality-with-J (Type a) Lens id _∘_
  module BM {a} =
    B.More {a = a} left-identity right-identity associativity

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≅_ to _≅_; Has-quasi-inverse to Has-quasi-inverse)

-- An equality characterisation lemma for A ≅ B that applies when A is
-- a set.

equality-characterisation-for-sets-≅ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≅ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≅
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂            ↔⟨ BM.equality-characterisation-≅-domain (lens-preserves-h-level-of-domain 1 A-set) _ _ ⟩
  l₁₁ ≡ l₁₂          ↝⟨ equality-characterisation-for-sets A-set ⟩□
  set l₁₁ ≡ set l₁₂  □
  where
  open Lens

-- There is a split surjection from A ≅ B to A ≃ B.

≅↠≃ : (A ≅ B) ↠ (A ≃ B)
≅↠≃ {A = A} {B = B} = record
  { logical-equivalence = record
    { to   = λ (l₁ , l₂ , eq₁ , eq₂) → Eq.↔⇒≃ (record
               { surjection = record
                 { logical-equivalence = record
                   { to   = get l₁
                   ; from = get l₂
                   }
                 ; right-inverse-of = ext⁻¹ $
                     getters-equal-if-setters-equal (l₁ ∘ l₂) id
                       (cong set eq₁)
               }
               ; left-inverse-of = ext⁻¹ $
                   getters-equal-if-setters-equal (l₂ ∘ l₁) id
                     (cong set eq₂)
               })
    ; from = λ A≃B → ≃→lens A≃B
                   , ≃→lens (inverse A≃B)
                   , lemma A≃B
                   , (≃→lens (inverse A≃B) ∘ ≃→lens A≃B  ≡⟨ cong (λ A≃B′ → ≃→lens (inverse A≃B) ∘ ≃→lens A≃B′) $
                                                            sym $ Eq.inverse-involutive ext A≃B ⟩
                      ≃→lens (inverse A≃B) ∘
                      ≃→lens (inverse $ inverse A≃B)     ≡⟨ lemma (inverse A≃B) ⟩∎

                      id                                 ∎)
    }
  ; right-inverse-of = λ _ → Eq.lift-equality ext (refl _)
  }
  where
  open Lens

  lemma :
    (C≃D : C ≃ D) → ≃→lens C≃D ∘ ≃→lens (inverse C≃D) ≡ id
  lemma C≃D = _↔_.from equality-characterisation₂
    ( ⟨ext⟩ (_≃_.right-inverse-of C≃D)
    , (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
    , lemma₁
    , lemma₂
    , lemma₃
    )
    where
    lemma₁ = λ d₁ d₂ →
      let lemma =
            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)      ≡⟨ cong (cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))) $
                                                                     ext-const ext ⟩

            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
              (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)     ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₂)))
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D)                  ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (_≃_.to C≃D ⊚ _≃_.from C≃D)
              (cong (λ set → set d₂)
                 (⟨ext⟩ $ _≃_.right-inverse-of C≃D))              ≡⟨ cong (cong (_≃_.to C≃D ⊚ _≃_.from C≃D)) $ cong-ext ext ⟩

            cong (_≃_.to C≃D ⊚ _≃_.from C≃D)
              (_≃_.right-inverse-of C≃D _)                        ≡⟨ sym $ cong-∘ _ _ (_≃_.right-inverse-of C≃D _) ⟩

            cong (_≃_.to C≃D)
              (cong (_≃_.from C≃D) (_≃_.right-inverse-of C≃D _))  ≡⟨ cong (cong (_≃_.to C≃D)) $ _≃_.right-left-lemma C≃D _ ⟩∎

            cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _)         ∎
      in

      trans (sym
        (trans (cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D))
           (cong (λ get → get d₂)
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D))))
      (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
         (_≃_.right-inverse-of C≃D _))                                ≡⟨ cong₂ (λ p q → trans (sym (trans p q))
                                                                                          (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
                                                                                             (_≃_.right-inverse-of C≃D _)))
                                                                           lemma
                                                                           (cong-ext ext) ⟩
      trans (sym
        (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
           (_≃_.right-inverse-of C≃D _)))
      (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
         (_≃_.right-inverse-of C≃D _))                                ≡⟨ trans-symˡ (trans _ (_≃_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                          ∎

    lemma₂ = λ d →
      let lemma =
            cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)    ≡⟨ cong (cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))) $
                                                                   ext-const ext ⟩

            cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
              (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)   ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → set (_≃_.to C≃D (_≃_.from C≃D d)))
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D)                ≡⟨ cong-ext ext ⟩∎

            _≃_.right-inverse-of C≃D _                          ∎
      in
      trans (sym
        (trans (cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D))
           (cong (λ get → get d)
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D))))
        (trans
           (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
           (_≃_.left-inverse-of (inverse C≃D) _))                   ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                         (cong₂ trans lemma (cong-ext ext))
                                                                         (cong₂ trans
                                                                            (_≃_.left-right-lemma C≃D _)
                                                                            (Eq.left-inverse-of∘inverse C≃D)) ⟩
      trans (sym (trans (_≃_.right-inverse-of C≃D _)
                    (_≃_.right-inverse-of C≃D _)))
        (trans (_≃_.right-inverse-of C≃D _)
           (_≃_.right-inverse-of C≃D _))                            ≡⟨ trans-symˡ (trans _ (_≃_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                        ∎

    lemma₃ = λ d d₁ d₂ →
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
         (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
         (trans (refl _)
            (trans
               (cong (λ _ → _≃_.to C≃D (_≃_.from C≃D d₂))
                  (_≃_.right-inverse-of (inverse C≃D)
                     (_≃_.from C≃D d₁)))
               (cong (_≃_.to C≃D) (refl _))))              ≡⟨ cong (subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
                                                                       (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)) $
                                                              trans (trans-reflˡ _) $
                                                              trans (cong (flip trans _) $ cong-const _) $
                                                              trans (trans-reflˡ _) $
                                                              cong-refl _ ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
         (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
         (refl _)                                          ≡⟨ cong (flip (subst (λ set → set (set d d₁) d₂ ≡ set d d₂)) _) $
                                                              ext-const ext ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
        (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (refl _)                                           ≡⟨ sym $ subst-∘ _ _ _ ⟩

      subst (λ set → set d₂ ≡ set d₂)
        (⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (refl _)                                           ≡⟨ subst-ext ext ⟩

      subst (λ set → set ≡ set)
        (_≃_.right-inverse-of C≃D d₂)
        (refl _)                                           ≡⟨ ≡⇒↝ _ (sym [subst≡]≡[trans≡trans]) (

          trans (refl _) (_≃_.right-inverse-of C≃D d₂)          ≡⟨ trans-reflˡ _ ⟩
          _≃_.right-inverse-of C≃D d₂                           ≡⟨ sym $ trans-reflʳ _ ⟩
          trans (_≃_.right-inverse-of C≃D d₂) (refl _)          ∎) ⟩

      refl _                                               ∎

-- The right-to-left direction of ≅↠≃ maps identity to an isomorphism
-- for which the first projection is the identity.

≅↠≃-id≡id : proj₁ (_↠_.from ≅↠≃ F.id) ≡ id {A = A}
≅↠≃-id≡id = equal-laws→≡
  (λ _ _ → refl _)
  (λ a →
     _≃_.left-inverse-of F.id a               ≡⟨ sym $ _≃_.right-left-lemma F.id _ ⟩
     cong P.id (_≃_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                       ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                   ∎)
  (λ _ _ _ → refl _)

-- If A is a set, then there is an equivalence between A ≃ B and A ≅ B.

≃≃≅ :
  Is-set A →
  (A ≃ B) ≃ (A ≅ B)
≃≃≅ {A = A} {B = B} A-set = Eq.↔⇒≃ $ inverse (record
  { surjection      = ≅↠≃
  ; left-inverse-of = λ (l₁ , l₂ , eq₁ , eq₂) →
      _↔_.from (equality-characterisation-for-sets-≅ A-set) $
      ⟨ext⟩ λ a → ⟨ext⟩ λ b →
        get l₂ b                                            ≡⟨ sym $ ext⁻¹ (ext⁻¹ (cong set eq₂) _) _ ⟩

        set l₁ (set l₁ a b)
          (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))         ≡⟨ set-set l₁ _ _ _ ⟩

        set l₁ a (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))  ≡⟨ cong (λ b′ → set l₁ a (set l₂ b′ (get l₂ b))) $ get-set l₁ _ _ ⟩

        set l₁ a (set l₂ b (get l₂ b))                      ≡⟨ cong (set l₁ a) $ set-get l₂ _ ⟩∎

        set l₁ a b                                          ∎
  })
  where
  open Lens

-- The equivalence maps identity to an isomorphism for which the first
-- projection is the identity.

≃≃≅-id≡id :
  (A-set : Is-set A) →
  proj₁ (_≃_.to (≃≃≅ A-set) F.id) ≡ id
≃≃≅-id≡id _ = ≅↠≃-id≡id

-- The type Has-quasi-inverse id is not necessarily a proposition
-- (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-type-of-refl-propositional.)

Has-quasi-inverse-id-not-proposition :
  Univalence lzero →
  ∃ λ (A : Type a) →
    ¬ Is-proposition (Has-quasi-inverse (id {A = A}))
Has-quasi-inverse-id-not-proposition _ =
    X
  , (Is-proposition (Has-quasi-inverse id)         ↝⟨ flip propositional⇒inhabited⇒contractible q ⟩
     Contractible (Has-quasi-inverse id)           ↝⟨ H-level-cong _ 0 lemma₁ ⟩
     Contractible (∃ λ (g : (x : X) → x ≡ x) → _)  ↝⟨ flip proj₁-closure 0
                                                        (λ g → (λ _ x → sym (g x)) , lemma₂ g , lemma₃ g , lemma₄ g) ⟩
     Contractible ((x : X) → x ≡ x)                ↝⟨ mono₁ 0 ⟩
     Is-proposition ((x : X) → x ≡ x)              ↝⟨ ¬-prop ⟩□
     ⊥                                             □)
  where
  X      = Erased (proj₁ Circle.¬-type-of-refl-propositional)
  ¬-prop =
    E.Stable-¬
      [ Is-proposition ((x : X) → x ≡ x)       ↝⟨ H-level-cong _ 1 (Π-cong ext (E.erased E.Erased↔) λ _ → E.≡≃erased≡erased) ⟩
        Is-proposition ((x : ↑ _ 𝕊¹) → x ≡ x)  ↝⟨ proj₂ Circle.¬-type-of-refl-propositional ⟩□
        ⊥                                      □
      ]

  q = id , left-identity _ , right-identity _

  lemma₁ =
    Has-quasi-inverse id                                             ↝⟨ BM.Has-quasi-inverse≃id≡id-domain q ⟩

    id ≡ id                                                          ↔⟨ equality-characterisation₄ ⟩□

    (∃ λ (g : ∀ x → x ≡ x) →
     ∃ λ (s : X → ∀ x → x ≡ x) →
       (∀ x y →
          trans (sym (trans (cong P.id (s x y)) (g y))) (refl _) ≡
          refl _) ×
       (∀ x →
          trans (sym (trans (s x x) (cong P.id (g x)))) (refl _) ≡
          refl _) ×
       (∀ x y z →
         trans (refl _) (s x z) ≡
         trans (cong (λ set → set (set x y) z) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
           (refl _)))                                                □

  lemma₂ : (g : ∀ x → x ≡ x) (x y : X) → _
  lemma₂ g x y =
    trans (sym (trans (cong P.id (sym (g y))) (g y))) (refl _)  ≡⟨ trans-reflʳ _ ⟩
    sym (trans (cong P.id (sym (g y))) (g y))                   ≡⟨ cong (λ eq → sym (trans eq (g y))) $ sym $ cong-id _ ⟩
    sym (trans (sym (g y)) (g y))                               ≡⟨ cong sym $ trans-symˡ (g y) ⟩
    sym (refl _)                                                ≡⟨ sym-refl ⟩∎
    refl _                                                      ∎

  lemma₃ : (g : ∀ x → x ≡ x) (x : X) → _
  lemma₃ g x =
    trans (sym (trans (sym (g x)) (cong P.id (g x)))) (refl _)  ≡⟨ trans-reflʳ _ ⟩
    sym (trans (sym (g x)) (cong P.id (g x)))                   ≡⟨ cong (λ eq → sym (trans (sym (g x)) eq)) $ sym $ cong-id (g x) ⟩
    sym (trans (sym (g x)) (g x))                               ≡⟨ cong sym $ trans-symˡ (g x) ⟩
    sym (refl _)                                                ≡⟨ sym-refl ⟩∎
    refl _                                                      ∎

  lemma₄ : (g : ∀ x → x ≡ x) (x y z : X) → _
  lemma₄ g x y z =
    trans (refl _) (sym (g z))                                            ≡⟨ trans-reflˡ (sym (g z)) ⟩
    sym (g z)                                                             ≡⟨ sym $ cong-ext ext ⟩
    cong (_$ z) (⟨ext⟩ (sym ⊚ g))                                         ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ (sym ⊚ g)) ⟩
    cong (λ set → set (set x y) z) (cong const (⟨ext⟩ (sym ⊚ g)))         ≡⟨ cong (cong (λ set → set (set x y) z)) $ sym $ ext-const ext ⟩
    cong (λ set → set (set x y) z) (⟨ext⟩ λ _ → ⟨ext⟩ (sym ⊚ g))          ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans (cong (λ set → set (set x y) z) (⟨ext⟩ λ _ → ⟨ext⟩ (sym ⊚ g)))
      (refl _)                                                            ∎

-- There is not necessarily a split surjection from
-- Is-equivalence (Lens.get l) to Has-quasi-inverse l, if l is a lens
-- between types in the same universe (assuming univalence).

¬Is-equivalence↠Has-quasi-inverse :
  Univalence lzero →
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalence (Lens.get l) ↠ Has-quasi-inverse l)
¬Is-equivalence↠Has-quasi-inverse univ surj =
                                         $⟨ mono₁ 0 ⊤-contractible ⟩
  Is-proposition ⊤                       ↝⟨ H-level.respects-surjection lemma 1 ⟩
  Is-proposition (Has-quasi-inverse id)  ↝⟨ proj₂ $ Has-quasi-inverse-id-not-proposition univ ⟩□
  ⊥                                      □
  where
  lemma =
    ⊤                     ↔⟨ inverse $ _⇔_.to contractible⇔↔⊤ $
                             propositional⇒inhabited⇒contractible
                               (Is-equivalence-propositional ext)
                               (_≃_.is-equivalence Eq.id) ⟩
    Is-equivalence P.id   ↝⟨ surj id ⟩□
    Has-quasi-inverse id  □

------------------------------------------------------------------------
-- Isomorphisms expressed using bi-invertibility for lenses

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≊_ to _≊_;
            Has-left-inverse to Has-left-inverse;
            Has-right-inverse to Has-right-inverse;
            Is-bi-invertible to Is-bi-invertible)

open BM public
  using ()
  renaming (Is-bi-invertible-propositional to
            Is-bi-invertible-propositional)

-- An equality characterisation lemma for A ≊ B that applies when A is
-- a set.

equality-characterisation-for-sets-≊ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≊ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≊
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂            ↔⟨ BM.equality-characterisation-≊ _ _ ⟩
  l₁₁ ≡ l₁₂          ↝⟨ equality-characterisation-for-sets A-set ⟩□
  set l₁₁ ≡ set l₁₂  □
  where
  open Lens

-- There is a split surjection from A ≊ B to A ≃ B.

≊↠≃ : (A ≊ B) ↠ (A ≃ B)
≊↠≃ = record
  { logical-equivalence = record
    { to   = _↠_.to ≅↠≃ ⊚ _↠_.from BM.≅↠≊
    ; from = _↠_.to BM.≅↠≊ ⊚ _↠_.from ≅↠≃
    }
  ; right-inverse-of = λ _ → Eq.lift-equality ext (refl _)
  }

-- The right-to-left direction maps identity to an isomorphism for
-- which the first projection is the identity.

≊↠≃-id≡id :
  proj₁ (_↠_.from ≊↠≃ F.id) ≡ id {A = A}
≊↠≃-id≡id = equal-laws→≡
  (λ _ _ → refl _)
  (λ a →
     _≃_.left-inverse-of F.id a               ≡⟨ sym $ _≃_.right-left-lemma F.id _ ⟩
     cong P.id (_≃_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                       ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                   ∎)
  (λ _ _ _ → refl _)

-- If A is a set, then there is an equivalence between A ≊ B and
-- A ≃ B.

≃≃≊ : Is-set A → (A ≃ B) ≃ (A ≊ B)
≃≃≊ {A = A} {B = B} A-set =
  A ≃ B  ↝⟨ ≃≃≅ A-set ⟩
  A ≅ B  ↝⟨ inverse $ BM.≊≃≅-domain (lens-preserves-h-level-of-domain 1 A-set) ⟩□
  A ≊ B  □

-- The equivalence ≃≃≊ maps identity to an isomorphism for which the
-- first projection is the identity.

≃≃≊-id≡id :
  (A-set : Is-set A) →
  proj₁ (_≃_.to (≃≃≊ A-set) F.id) ≡ id
≃≃≊-id≡id _ = ≊↠≃-id≡id

-- The right-to-left direction of ≃≃≊ maps bi-invertible lenses to
-- their getter functions.

to-from-≃≃≊≡get :
  (A-set : Is-set A) (A≊B@(l , _) : A ≊ B) →
  _≃_.to (_≃_.from (≃≃≊ A-set) A≊B) ≡ Lens.get l
to-from-≃≃≊≡get _ _ = refl _

-- The getter function of a bi-invertible lens is an equivalence.

Is-bi-invertible→Is-equivalence-get :
  (l : Lens A B) →
  Is-bi-invertible l → Is-equivalence (Lens.get l)
Is-bi-invertible→Is-equivalence-get l is-bi-inv =
  _≃_.is-equivalence (_↠_.to ≊↠≃ (l , is-bi-inv))

-- If the getter function is an equivalence, then the lens is
-- bi-invertible.

Is-equivalence-get→Is-bi-invertible :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) → Is-bi-invertible l
Is-equivalence-get→Is-bi-invertible {A = A} {B = B} l′ is-equiv =
                       $⟨ l⁻¹ , l∘l⁻¹≡id , l⁻¹∘l≡id ⟩
  Has-quasi-inverse l  ↝⟨ B.Has-quasi-inverse→Is-bi-invertible l ⟩
  Is-bi-invertible l   ↝⟨ subst Is-bi-invertible (getter-equivalence→lens≡ l′ is-equiv) ⟩□
  Is-bi-invertible l′  □
  where
  open Lens

  -- A lens that is equal to l′.

  l : Lens A B
  l = getter-equivalence→lens l′ is-equiv

  A≃B = Eq.⟨ get l , is-equiv ⟩

  open _≃_ A≃B

  -- An inverse of l.
  --
  -- Note that the set-get and set-set proofs have been "obfuscated".
  -- They could have been shorter, but then it might not have been
  -- possible to prove l∘l⁻¹≡id and l⁻¹∘l≡id.

  l⁻¹ : Lens B A
  l⁻¹ = record
    { get     = from
    ; set     = λ _ → get l
    ; get-set = λ _ a →
                  from (get l a)  ≡⟨ left-inverse-of a ⟩∎
                  a               ∎
    ; set-get = λ b →
                  get l (from b)                 ≡⟨ sym $ cong (get l) $ set-get l (from b) ⟩
                  get l (from (get l (from b)))  ≡⟨ right-inverse-of (get l (from b)) ⟩
                  get l (from b)                 ≡⟨ right-inverse-of b ⟩∎
                  b                              ∎
    ; set-set = λ b a₁ a₂ →
                  get l a₂                 ≡⟨ sym $ right-inverse-of _ ⟩
                  get l (from (get l a₂))  ≡⟨ sym $ cong (get l) (set-set l (from b) (get l a₁) (get l a₂)) ⟩
                  get l (from (get l a₂))  ≡⟨ right-inverse-of _ ⟩∎
                  get l a₂                 ∎
    }

  opaque

    -- The lens l⁻¹ is a right inverse of l.

    l∘l⁻¹≡id : l ∘ l⁻¹ ≡ id
    l∘l⁻¹≡id = constant-setter→≡id
      ( right-inverse-of
      , right-inverse-of
      , (λ b₁ b₂ →
           get-set (l ∘ l⁻¹) b₁ b₂                                 ≡⟨⟩

           trans (cong (get l) (get-set l⁻¹ b₁ (from b₂)))
             (get-set l (from b₁) b₂)                              ≡⟨⟩

           trans (cong (get l) (left-inverse-of (from b₂)))
             (right-inverse-of b₂)                                 ≡⟨ cong (λ eq → trans (cong (get l) eq) (right-inverse-of b₂)) $ sym $
                                                                      right-left-lemma _ ⟩
           trans (cong (get l) (cong from (right-inverse-of b₂)))
             (right-inverse-of b₂)                                 ≡⟨ cong (λ eq → trans eq (right-inverse-of b₂)) $
                                                                      cong-∘ _ _ (right-inverse-of b₂) ⟩
           trans (cong (get l ⊚ from) (right-inverse-of b₂))
             (right-inverse-of b₂)                                 ≡⟨⟩

           trans (cong (get (l ∘ l⁻¹)) (right-inverse-of b₂))
             (right-inverse-of b₂)                                 ∎)
      , (λ b →
           set-get (l ∘ l⁻¹) b                                 ≡⟨⟩

           trans (cong (get l) (set-get l (from b)))
             (set-get l⁻¹ b)                                   ≡⟨⟩

           trans (cong (get l) (set-get l (from b)))
             (trans (sym (cong (get l) (set-get l (from b))))
                (trans (right-inverse-of (get l (from b)))
                   (right-inverse-of b)))                      ≡⟨ trans--[trans-sym] _ _ ⟩

           trans (right-inverse-of (get l (from b)))
             (right-inverse-of b)                              ≡⟨⟩

           trans (right-inverse-of (get (l ∘ l⁻¹) b))
             (right-inverse-of b)                              ∎)
      , (λ b b₁ b₂ →
           set-set (l ∘ l⁻¹) b b₁ b₂                                      ≡⟨⟩

           trans (set-set l⁻¹ b (from b₁) (from b₂))
             (trans (cong (λ _ → get l (from b₂))
                       (get-set l⁻¹ b (from b₁)))
                (cong (get l) (set-set l (from b) b₁ b₂)))                ≡⟨ cong (trans _) $
                                                                             trans (cong (flip trans _) $ cong-const _) $
                                                                             trans-reflˡ _ ⟩
           trans (set-set l⁻¹ b (from b₁) (from b₂))
             (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨⟩

           trans (trans (sym (right-inverse-of _))
                    (trans (sym (cong (get l)
                                   (set-set l (from b) (get l (from b₁))
                                      (get l (from b₂)))))
                       (right-inverse-of _)))
             (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ cong (λ b′ → trans (trans (sym (right-inverse-of _))
                                                                                                   (trans (sym (cong (get l)
                                                                                                                  (set-set l (from b) b′
                                                                                                                     (get l (from b₂)))))
                                                                                                      (right-inverse-of _)))
                                                                                            (cong (get l) (set-set l (from b) b₁ b₂))) $
                                                                             right-inverse-of _ ⟩
           trans (trans (sym (right-inverse-of _))
                    (trans (sym (cong (get l)
                                   (set-set l (from b) b₁
                                      (get l (from b₂)))))
                       (right-inverse-of _)))
             (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ cong (λ f → trans (trans (sym (f _))
                                                                                                  (trans (sym (cong (get l)
                                                                                                                 (set-set l (from b) b₁
                                                                                                                    (get l (from b₂)))))
                                                                                                     (f _)))
                                                                                           (cong (get l) (set-set l (from b) b₁ b₂))) $ sym $
                                                                             _≃_.left-inverse-of (Eq.extensionality-isomorphism ext)
                                                                               right-inverse-of ⟩
           trans (trans (sym (ext⁻¹ (⟨ext⟩ right-inverse-of) _))
                    (trans (sym (cong (get l)
                                   (set-set l (from b) b₁
                                      (get l (from b₂)))))
                       (ext⁻¹ (⟨ext⟩ right-inverse-of) _)))
             (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ elim₁
                                                                               (λ {f} (p : f ≡ P.id) →
                                                                                  (q : ∀ b → f b ≡ f b) →
                                                                                  trans (trans (sym (ext⁻¹ p (f b₂)))
                                                                                           (trans (sym (q (f b₂))) (ext⁻¹ p (f b₂))))
                                                                                    (q b₂) ≡
                                                                                  refl _)
                                                                               (λ q →
               trans (trans (sym (ext⁻¹ (refl P.id) _))
                        (trans (sym (q _)) (ext⁻¹ (refl P.id) _)))
                 (q _)                                                            ≡⟨ cong (λ eq → trans (trans (sym eq) (trans (sym (q _)) eq))
                                                                                                    (q _)) $
                                                                                     ext⁻¹-refl _ ⟩
               trans (trans (sym (refl _))
                        (trans (sym (q _)) (refl _)))
                 (q _)                                                            ≡⟨ cong₂ (λ p r → trans (trans p r) (q _))
                                                                                       sym-refl
                                                                                       (trans-reflʳ _) ⟩

               trans (trans (refl _) (sym (q _))) (q _)                           ≡⟨ cong (λ eq → trans eq (q _)) $ trans-reflˡ (sym (q _)) ⟩

               trans (sym (q _)) (q _)                                            ≡⟨ trans-symˡ (q _) ⟩∎

               refl _                                                             ∎)
                                                                               (⟨ext⟩ right-inverse-of)
                                                                               (cong (get l) ⊚ set-set l (from b) b₁) ⟩
           refl _                                                         ∎)
      )

    -- The lens l⁻¹ is a left inverse of l.

    l⁻¹∘l≡id : l⁻¹ ∘ l ≡ id
    l⁻¹∘l≡id = constant-setter→≡id
      ( left-inverse-of
      , left-inverse-of
      , (λ a₁ a₂ →
           get-set (l⁻¹ ∘ l) a₁ a₂                                ≡⟨⟩

           trans (cong from (get-set l a₁ (to a₂)))
             (get-set l⁻¹ (get l a₁) a₂)                          ≡⟨⟩

           trans (cong from (right-inverse-of (to a₂)))
             (left-inverse-of a₂)                                 ≡⟨ cong (λ eq → trans (cong from eq) (left-inverse-of _)) $ sym $
                                                                     left-right-lemma _ ⟩
           trans (cong from (cong (get l) (left-inverse-of a₂)))
             (left-inverse-of a₂)                                 ≡⟨ cong (λ eq → trans eq (left-inverse-of _)) $
                                                                     cong-∘ _ _ (left-inverse-of _) ⟩
           trans (cong (from ⊚ get l) (left-inverse-of a₂))
             (left-inverse-of a₂)                                 ≡⟨⟩

           trans (cong (get (l⁻¹ ∘ l)) (left-inverse-of a₂))
             (left-inverse-of a₂)                                 ∎)
      , (λ a →
           let lemma₁ =
                 cong from
                   (trans (sym (cong (get l)
                                  (set-get l (from (get l a)))))
                      (trans (right-inverse-of _)
                         (right-inverse-of _)))                        ≡⟨ cong-trans _ _ (trans _ (right-inverse-of _)) ⟩

                 trans (cong from (sym (cong (get l) $
                                        set-get l (from (get l a)))))
                   (cong from (trans (right-inverse-of _)
                                 (right-inverse-of _)))                ≡⟨ cong (λ eq → trans (cong from eq)
                                                                                         (cong from (trans (right-inverse-of _)
                                                                                                       (right-inverse-of _)))) $ sym $
                                                                          cong-sym _ (set-get l (from (get l a))) ⟩
                 trans (cong from (cong (get l) $
                                   sym (set-get l (from (get l a)))))
                   (cong from (trans (right-inverse-of _)
                                 (right-inverse-of _)))                ≡⟨ cong₂ trans
                                                                            (cong-∘ _ _ (sym (set-get l (from (get l a)))))
                                                                            (cong-trans _ _ (right-inverse-of _)) ⟩
                 trans (cong (from ⊚ get l)
                          (sym (set-get l (from (get l a)))))
                   (trans (cong from (right-inverse-of _))
                      (cong from (right-inverse-of _)))                ≡⟨ cong₂ (λ p q → trans (cong (from ⊚ get l)
                                                                                                  (sym (set-get l (from (get l a)))))
                                                                                           (trans p q))
                                                                            (right-left-lemma _)
                                                                            (right-left-lemma _) ⟩∎
                 trans (cong (from ⊚ get l)
                          (sym (set-get l (from (get l a)))))
                   (trans (left-inverse-of _)
                      (left-inverse-of _))                             ∎

               f = from ⊚ get l

               lemma₂ : ∀ _ → _
               lemma₂ = λ a →
                 trans (left-inverse-of (f a))
                   (left-inverse-of a)                        ≡⟨ cong (λ g → trans (g (f a)) (g a)) $ sym $
                                                                 _≃_.left-inverse-of (Eq.extensionality-isomorphism ext)
                                                                   left-inverse-of ⟩∎
                 trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))
                   (ext⁻¹ (⟨ext⟩ left-inverse-of) a)          ∎

               lemma₃ =
                 trans (ext⁻¹ (refl P.id) a) (ext⁻¹ (refl P.id) a)  ≡⟨ cong₂ trans (ext⁻¹-refl _) (ext⁻¹-refl _) ⟩
                 trans (refl _) (refl _)                            ≡⟨ trans-refl-refl ⟩∎
                 refl _                                             ∎
           in
           trans (cong from (set-get l⁻¹ (get l a)))
             (set-get l a)                                            ≡⟨⟩

           trans (cong from
                    (trans (sym (cong (get l)
                                   (set-get l (from (get l a)))))
                       (trans (right-inverse-of _)
                          (right-inverse-of _))))
             (set-get l a)                                            ≡⟨ cong (λ eq → trans eq (set-get l a)) lemma₁ ⟩

           trans (trans (cong f (sym (set-get l (f a))))
                    (trans (left-inverse-of (f (f a)))
                       (left-inverse-of (f a))))
             (set-get l a)                                            ≡⟨ cong (λ eq → trans (trans (cong f (sym (set-get l (f a)))) eq)
                                                                                        (set-get l a)) $
                                                                         lemma₂ _ ⟩
           trans (trans (cong f (sym (set-get l (f a))))
                    (trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f (f a)))
                       (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))))
             (set-get l a)                                            ≡⟨ elim₁
                                                                           (λ {f} (p : f ≡ P.id) →
                                                                              (q : ∀ a → f a ≡ a) →
                                                                              trans (trans (cong f (sym (q (f a))))
                                                                                       (trans (ext⁻¹ p (f (f a))) (ext⁻¹ p (f a))))
                                                                                (q a) ≡
                                                                              trans (ext⁻¹ p (f a)) (ext⁻¹ p a))
                                                                           (λ q →
               trans (trans (cong P.id (sym (q a)))
                        (trans (ext⁻¹ (refl P.id) a)
                           (ext⁻¹ (refl P.id) a)))
                 (q a)                                                        ≡⟨ cong₂ (λ p r → trans (trans p r) (q a))
                                                                                   (sym $ cong-id _)
                                                                                   lemma₃ ⟩

               trans (trans (sym (q a)) (refl _)) (q a)                       ≡⟨ cong (flip trans _) $ trans-reflʳ _ ⟩

               trans (sym (q a)) (q a)                                        ≡⟨ trans-symˡ (q a) ⟩

               refl _                                                         ≡⟨ sym lemma₃ ⟩∎

               trans (ext⁻¹ (refl P.id) a) (ext⁻¹ (refl P.id) a)              ∎)
                                                                           (⟨ext⟩ left-inverse-of)
                                                                           (set-get l) ⟩
           trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))
             (ext⁻¹ (⟨ext⟩ left-inverse-of) a)                        ≡⟨ sym $ lemma₂ _ ⟩

           trans (left-inverse-of (f a))
             (left-inverse-of a)                                      ≡⟨⟩

           trans (left-inverse-of (get (l⁻¹ ∘ l) a))
             (left-inverse-of a)                                      ∎)
      , (λ a a₁ a₂ →
           let q = set-set l a (get l a₁) (get l a₂)

               lemma =
                 cong from
                   (trans (sym (right-inverse-of _))
                      (trans (sym (cong (get l) q))
                         (right-inverse-of _)))                    ≡⟨ cong-trans _ _ (trans (sym (cong (get l) q)) (right-inverse-of _)) ⟩

                 trans (cong from (sym (right-inverse-of _)))
                   (cong from (trans (sym (cong (get l) q))
                                 (right-inverse-of _)))            ≡⟨ cong₂ trans
                                                                        (cong-sym _ (right-inverse-of _))
                                                                        (cong-trans _ _ (right-inverse-of _)) ⟩
                 trans (sym (cong from (right-inverse-of _)))
                   (trans (cong from (sym (cong (get l) q)))
                      (cong from (right-inverse-of _)))            ≡⟨ cong₂ (λ p r → trans (sym p) (trans (cong from (sym (cong (get l) q))) r))
                                                                        (right-left-lemma _)
                                                                        (right-left-lemma _) ⟩
                 trans (sym (left-inverse-of _))
                   (trans (cong from (sym (cong (get l) q)))
                      (left-inverse-of _))                         ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                     (trans eq (left-inverse-of _))) $
                                                                      cong-sym _ (cong (get l) q) ⟩
                 trans (sym (left-inverse-of _))
                   (trans (sym (cong from (cong (get l) q)))
                      (left-inverse-of _))                         ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                     (trans (sym eq) (left-inverse-of _))) $
                                                                      cong-∘ _ _ q ⟩
                 trans (sym (left-inverse-of _))
                   (trans (sym (cong (from ⊚ get l) q))
                      (left-inverse-of _))                         ≡⟨ cong (λ g → trans (sym (g _))
                                                                                    (trans (sym (cong (from ⊚ get l) q)) (g _))) $ sym $
                                                                      _≃_.left-inverse-of (Eq.extensionality-isomorphism ext)
                                                                        left-inverse-of ⟩∎
                 trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) _))
                   (trans (sym (cong (from ⊚ get l) q))
                      (ext⁻¹ (⟨ext⟩ left-inverse-of) _))           ∎

               f = from ⊚ get l
           in
           set-set (l⁻¹ ∘ l) a a₁ a₂                                     ≡⟨⟩

           trans (set-set l a (get l a₁) (get l a₂))
             (trans (cong (λ _ → from (get l a₂))
                       (right-inverse-of (get l a₁)))
                (cong from (set-set l⁻¹ (get l a) a₁ a₂)))               ≡⟨ cong (trans _) $
                                                                            trans (cong (flip trans _) $ cong-const _) $
                                                                            trans-reflˡ _ ⟩
           trans (set-set l a (get l a₁) (get l a₂))
             (cong from (set-set l⁻¹ (get l a) a₁ a₂))                   ≡⟨⟩

           trans (set-set l a (get l a₁) (get l a₂))
             (cong from
                (trans (sym (right-inverse-of _))
                   (trans (sym (cong (get l)
                                  (set-set l (from (get l a))
                                     (get l a₁) (get l a₂))))
                      (right-inverse-of _))))                            ≡⟨ cong (λ a′ → trans q
                                                                                           (cong from
                                                                                              (trans (sym (right-inverse-of _))
                                                                                                 (trans (sym (cong (get l)
                                                                                                                (set-set l a′ (get l a₁) (get l a₂))))
                                                                                                    (right-inverse-of _))))) $
                                                                            left-inverse-of _ ⟩
           trans q
             (cong from
                (trans (sym (right-inverse-of _))
                   (trans (sym (cong (get l) q))
                      (right-inverse-of _))))                            ≡⟨ cong (trans q) lemma ⟩

           trans q
             (trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂)))
                (trans (sym (cong f q))
                   (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂))))              ≡⟨ elim₁
                                                                              (λ {f} (p : f ≡ P.id) →
                                                                                 (q : f a₂ ≡ f a₂) →
                                                                                 trans q
                                                                                   (trans (sym (ext⁻¹ p (f a₂)))
                                                                                      (trans (sym (cong f q))
                                                                                         (ext⁻¹ p (f a₂)))) ≡
                                                                                 refl _)
                                                                            (λ q →
               trans q
                 (trans (sym (ext⁻¹ (refl P.id) a₂))
                    (trans (sym (cong P.id q))
                       (ext⁻¹ (refl P.id) a₂)))                                ≡⟨ cong (λ eq → trans q (trans (sym eq)
                                                                                                          (trans (sym (cong P.id q)) eq))) $
                                                                                  ext⁻¹-refl _ ⟩
               trans q (trans (sym (refl _))
                          (trans (sym (cong P.id q)) (refl _)))                ≡⟨ cong₂ (λ p r → trans q (trans p r))
                                                                                    sym-refl
                                                                                    (trans-reflʳ _) ⟩

               trans q (trans (refl _) (sym (cong P.id q)))                    ≡⟨ cong (trans q) $ trans-reflˡ (sym (cong P.id q)) ⟩

               trans q (sym (cong P.id q))                                     ≡⟨ cong (λ eq → trans q (sym eq)) $ sym $ cong-id q ⟩

               trans q (sym q)                                                 ≡⟨ trans-symʳ q ⟩∎

               refl _                                                          ∎)
                                                                            (⟨ext⟩ left-inverse-of)
                                                                            q ⟩

           refl _                                                        ∎)
      )

-- There is an equivalence between "l is bi-invertible" and "the
-- getter of l is an equivalence".

Is-bi-invertible≃Is-equivalence-get :
  (l : Lens A B) →
  Is-bi-invertible l ≃ Is-equivalence (Lens.get l)
Is-bi-invertible≃Is-equivalence-get l = Eq.⇔→≃
  (BM.Is-bi-invertible-propositional l)
  (Is-equivalence-propositional ext)
  (Is-bi-invertible→Is-equivalence-get l)
  (Is-equivalence-get→Is-bi-invertible l)

-- There is in general no split surjection from equivalences to
-- bi-invertible lenses, if the right-to-left direction of the split
-- surjection is required to map bi-invertible lenses to their getter
-- functions (assuming univalence).

¬≃↠≊ :
  Univalence lzero →
  ¬ ∃ λ (≃↠≊ : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠ (↑ a 𝕊¹ ≊ ↑ a 𝕊¹)) →
      (x@(l , _) : ↑ a 𝕊¹ ≊ ↑ a 𝕊¹) →
      _≃_.to (_↠_.from ≃↠≊ x) ≡ Lens.get l
¬≃↠≊ {a = a} univ =
  (∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠ (↑ a 𝕊¹ ≊ ↑ a 𝕊¹)) →
     ∀ p → _≃_.to (_↠_.from f p) ≡ Lens.get (proj₁ p))  ↝⟨ Σ-map
                                                             ((∃-cong λ l → _≃_.surjection $ Is-bi-invertible≃Is-equivalence-get l) F.∘_)
                                                             (λ hyp _ → hyp _) ⟩
  (∃ λ (f : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠
            (∃ λ (l : Lens (↑ a 𝕊¹) (↑ a 𝕊¹)) →
               Is-equivalence (Lens.get l))) →
     ∀ p → _≃_.to (_↠_.from f p) ≡ Lens.get (proj₁ p))  ↝⟨ ¬-≃-↠-Σ-Lens-Is-equivalence-get univ ⟩□

  ⊥                                                     □

-- There is in general no equivalence between equivalences and
-- bi-invertible lenses, if the right-to-left direction of the
-- equivalence is required to map bi-invertible lenses to their getter
-- functions (assuming univalence).

¬≃≃≊ :
  Univalence lzero →
  ¬ ∃ λ (≃≃≊ : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ≃ (↑ a 𝕊¹ ≊ ↑ a 𝕊¹)) →
      (x@(l , _) : ↑ a 𝕊¹ ≊ ↑ a 𝕊¹) →
      _≃_.to (_≃_.from ≃≃≊ x) ≡ Lens.get l
¬≃≃≊ {a = a} univ =
  (∃ λ (≃≃≊ : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ≃ (↑ a 𝕊¹ ≊ ↑ a 𝕊¹)) →
     (x@(l , _) : ↑ a 𝕊¹ ≊ ↑ a 𝕊¹) →
     _≃_.to (_≃_.from ≃≃≊ x) ≡ Lens.get l)              ↝⟨ Σ-map _≃_.surjection P.id ⟩

  (∃ λ (≃↠≊ : (↑ a 𝕊¹ ≃ ↑ a 𝕊¹) ↠ (↑ a 𝕊¹ ≊ ↑ a 𝕊¹)) →
     (x@(l , _) : ↑ a 𝕊¹ ≊ ↑ a 𝕊¹) →
     _≃_.to (_↠_.from ≃↠≊ x) ≡ Lens.get l)              ↝⟨ ¬≃↠≊ univ ⟩□

  ⊥                                                     □

------------------------------------------------------------------------
-- A category

-- Lenses between sets with the same universe level form a
-- precategory.

precategory : Precategory (lsuc a) a
precategory {a = a} = record
  { precategory =
      Set a
    , (λ (A , A-set) (B , _) →
           Lens A B
         , lens-preserves-h-level-of-domain 1 A-set)
    , id
    , _∘_
    , left-identity _
    , right-identity _
    , (λ {_ _ _ _ l₁ l₂ l₃} → associativity l₃ l₂ l₁)
  }

-- Lenses between sets with the same universe level form a
-- category (assuming univalence).

category :
  Univalence a →
  Category (lsuc a) a
category {a = a} univ =
  C.precategory-with-Set-to-category
    ext
    (λ _ _ → univ)
    (proj₂ Pre.precategory)
    (λ (_ , A-set) _ → ≃≃≅ A-set)
    (λ (_ , A-set) → ≃≃≅-id≡id A-set)
  where
  module Pre = C.Precategory precategory

-- The following four results (up to and including ¬-univalent) are
-- based on a suggestion by Paolo Capriotti, in response to a question
-- from an anonymous reviewer.

-- A "naive" notion of category.
--
-- Note that the hom-sets are not required to be sets.

Naive-category : (o h : Level) → Type (lsuc (o ⊔ h))
Naive-category o h =
  ∃ λ (Obj : Type o) →
  ∃ λ (Hom : Obj → Obj → Type h) →
  ∃ λ (id : {A : Obj} → Hom A A) →
  ∃ λ (_∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C) →
    ({A B : Obj} (h : Hom A B) → id ∘ h ≡ h) ×
    ({A B : Obj} (h : Hom A B) → h ∘ id ≡ h) ×
    ({A B C D : Obj} (h₁ : Hom C D) (h₂ : Hom B C) (h₃ : Hom A B) →
     (h₁ ∘ (h₂ ∘ h₃)) ≡ ((h₁ ∘ h₂) ∘ h₃))

-- A notion of univalence for naive categories.

Univalent : Naive-category o h → Type (o ⊔ h)
Univalent (Obj , Hom , id , _∘_ , id-∘ , ∘-id , assoc) =
  Bi-invertibility.More.Univalence-≊
    equality-with-J Obj Hom id _∘_ id-∘ ∘-id assoc

-- Types in a fixed universe and traditional lenses between them form
-- a naive category.

naive-category : ∀ a → Naive-category (lsuc a) a
naive-category a =
    Type a
  , Lens
  , id
  , _∘_
  , left-identity
  , right-identity
  , associativity

-- However, this category is not univalent (assuming univalence).

¬-univalent :
  Univalence lzero →
  Univalence a →
  ¬ Univalent (naive-category a)
¬-univalent {a = a} univ₀ univ u = ¬≃≃≊ univ₀ (equiv , lemma₂)
  where
  equiv : {A B : Type a} → (A ≃ B) ≃ (A ≊ B)
  equiv {A = A} {B = B} =
    (A ≃ B)  ↝⟨ inverse $ ≡≃≃ univ ⟩
    (A ≡ B)  ↝⟨ Eq.⟨ _ , u ⟩ ⟩□
    (A ≊ B)  □

  lemma₁ :
    (eq : ↑ a 𝕊¹ ≃ ↑ a 𝕊¹) →
    _≃_.to eq ≡ Lens.get (proj₁ (_≃_.to equiv eq))
  lemma₁ =
    ≃-elim₁
      univ
      (λ eq → _≃_.to eq ≡ Lens.get (proj₁ (_≃_.to equiv eq)))
      (P.id                                        ≡⟨ cong (Lens.get ⊚ proj₁) $ sym $ elim-refl _ _ ⟩
       Lens.get (proj₁ (BM.≡→≊ (refl _)))          ≡⟨ cong (Lens.get ⊚ proj₁ ⊚ BM.≡→≊) $ sym $ ≃⇒≡-id univ ⟩
       Lens.get (proj₁ (BM.≡→≊ (≃⇒≡ univ Eq.id)))  ≡⟨⟩
       Lens.get (proj₁ (_≃_.to equiv Eq.id))       ∎)

  lemma₂ :
    (x@(l , _) : ↑ a 𝕊¹ ≊ ↑ a 𝕊¹) →
    _≃_.to (_≃_.from equiv x) ≡ Lens.get l
  lemma₂ x@(l , _) =
    _≃_.to (_≃_.from equiv x)                           ≡⟨ lemma₁ (_≃_.from equiv x) ⟩
    Lens.get (proj₁ (_≃_.to equiv (_≃_.from equiv x)))  ≡⟨ cong (Lens.get ⊚ proj₁) $ _≃_.right-inverse-of equiv _ ⟩
    Lens.get (proj₁ x)                                  ≡⟨⟩
    Lens.get l                                          ∎

-- There is in general no pointwise equivalence between equivalences
-- and bi-invertible lenses (assuming univalence).

¬Π≃≃≊ :
  Univalence lzero →
  Univalence a →
  ¬ ({A B : Type a} → (A ≃ B) ≃ (A ≊ B))
¬Π≃≃≊ {a = a} univ₀ univ =
  ({A B : Type a} → (A ≃ B) ≃ (A ≊ B))  ↝⟨ F._∘ ≡≃≃ univ ⟩
  ({A B : Type a} → (A ≡ B) ≃ (A ≊ B))  ↝⟨ BM.≡≃≊→Univalence-≊ ⟩
  Univalent (naive-category a)          ↝⟨ ¬-univalent univ₀ univ ⟩□
  ⊥                                     □

-- There is in general no pointwise equivalence between equivalences
-- (between types in the same universe) and lenses with getters that
-- are equivalences (assuming univalence).

¬Π≃-≃-Σ-Lens-Is-equivalence-get :
  Univalence lzero →
  Univalence a →
  ¬ ({A B : Type a} →
     (A ≃ B) ≃ ∃ λ (l : Lens A B) → Is-equivalence (Lens.get l))
¬Π≃-≃-Σ-Lens-Is-equivalence-get {a = a} univ₀ univ =
  ({A B : Type a} →
   (A ≃ B) ≃ ∃ λ (l : Lens A B) → Is-equivalence (Lens.get l))  ↝⟨ inverse (∃-cong Is-bi-invertible≃Is-equivalence-get) F.∘_ ⟩

  ({A B : Type a} → (A ≃ B) ≃ (A ≊ B))                          ↝⟨ ¬Π≃≃≊ univ₀ univ ⟩□

  ⊥                                                             □
