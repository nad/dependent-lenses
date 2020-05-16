------------------------------------------------------------------------
-- Traditional non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Traditional where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent

private
  variable
    a b c p         : Level
    A B C D         : Set a
    u v x₁ x₂ y₁ y₂ : A

------------------------------------------------------------------------
-- Traditional lenses

-- Lenses.

record Lens (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    -- Getter and setter.
    get : A → B
    set : A → B → A

    -- Lens laws.
    get-set : ∀ a b → get (set a b) ≡ b
    set-get : ∀ a → set a (get a) ≡ a
    set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

private
  variable
    l₁ l₂ : Lens A B

-- The record type above is isomorphic to a nested Σ-type.

Lens-as-Σ :
  Lens A B ↔
  ∃ λ (get : A → B) →
  ∃ λ (set : A → B → A) →
  (∀ a b → get (set a b) ≡ b) ×
  (∀ a → set a (get a) ≡ a) ×
  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)
Lens-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ l → get l , set l , get-set l , set-get l , set-set l
      ; from = λ { (get , set , get-set , set-get , set-set) →
                   record
                     { get     = get
                     ; set     = set
                     ; get-set = get-set
                     ; set-get = set-get
                     ; set-set = set-set
                     }
                 }
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }
  where
  open Lens

-- Equality characterisation.

abstract

  equality-characterisation :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                 (subst (λ set → get l₁ (set a b) ≡ b) s
                    (get-set l₁ a b))
                 ≡
               get-set l₂ a b)
        ×
      (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
               (subst (λ set → set a (get l₁ a) ≡ a) s
                  (set-get l₁ a))
               ≡
             set-get l₂ a)
        ×
      (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                     (set-set l₁ a b₁ b₂)
                     ≡
                   set-set l₂ a b₁ b₂)

  equality-characterisation {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                          ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Lens-as-Σ)) ⟩

    l₁′ ≡ l₂′                                                        ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Σ-assoc)) ⟩

    ((get l₁ , set l₁) , proj₂ (proj₂ l₁′))
      ≡
    ((get l₂ , set l₂) , proj₂ (proj₂ l₂′))                          ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           gs (proj₂ (proj₂ l₁′))
       ≡
     proj₂ (proj₂ l₂′))                                              ↝⟨ Σ-cong (inverse ≡×≡↔≡) (λ gs → ≡⇒↝ _ $
                                                                        cong (λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
                                                                                subst (λ { (get , set) →
                                                                                           (∀ a b → get (set a b) ≡ b) ×
                                                                                           (∀ a → set a (get a) ≡ a) ×
                                                                                           (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
                                                                                      gs (proj₂ (proj₂ l₁′))
                                                                                  ≡
                                                                                proj₂ (proj₂ l₂′))
                                                                             (sym $ _↔_.right-inverse-of ≡×≡↔≡ gs)) ⟩
    (∃ λ (gs : get l₁ ≡ get l₂ × set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ gs) (proj₂ (proj₂ l₁′))
       ≡
     proj₂ (proj₂ l₂′))                                              ↝⟨ inverse Σ-assoc ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ l₁′))
       ≡
     proj₂ (proj₂ l₂′))                                              ↝⟨ (∃-cong λ g → ∃-cong λ s → ≡⇒↝ _ $
                                                                         cong (λ x → x ≡ proj₂ (proj₂ l₂′))
                                                                              (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     ( subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
             (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
     , subst (λ { (get , set) →
                  (∀ a → set a (get a) ≡ a) ×
                  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁′)))
     )
       ≡
     proj₂ (proj₂ l₂′))                                              ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
       ≡
     get-set l₂
       ×
     subst (λ { (get , set) →
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁′)))
       ≡
     proj₂ (proj₂ (proj₂ l₂′)))                                      ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ≡⇒↝ _ $
                                                                         cong (λ x → x ≡ proj₂ (proj₂ (proj₂ l₂′)))
                                                                              (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
       ≡
     get-set l₂
       ×
     ( subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
             (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁)
     , subst (λ { (get , set) →
                  ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
             (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁)
     )
       ≡
     proj₂ (proj₂ (proj₂ l₂′)))                                      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
       ≡
     get-set l₂
       ×
     subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
           (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁)
       ≡
     set-get l₂
       ×
     subst (λ { (get , set) →
                ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
           (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁)
       ≡
       set-set l₂)                                                   ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         lemma₁ (λ { (get , set) a → ∀ b → get (set a b) ≡ b })
                                                                                (_↔_.to ≡×≡↔≡ (g , s))
                                                                           ×-cong
                                                                         lemma₁ (λ { (get , set) a → set a (get a) ≡ a })
                                                                                (_↔_.to ≡×≡↔≡ (g , s))
                                                                           ×-cong
                                                                         lemma₁ (λ { (get , set) a → ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                (_↔_.to ≡×≡↔≡ (g , s))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a → subst (λ { (get , set) → ∀ b → get (set a b) ≡ b })
                  (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a)
              ≡
            get-set l₂ a)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a)
              ≡
            set-get l₂ a)
       ×
     (∀ a → subst (λ { (get , set) →
                       ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a)
              ≡
            set-set l₂ a))                                           ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         (∀-cong ext λ a →
                                                                            lemma₁ (λ { (get , set) b → get (set a b) ≡ b })
                                                                                   (_↔_.to ≡×≡↔≡ (g , s)))
                                                                           ×-cong
                                                                         F.id
                                                                           ×-cong
                                                                         (∀-cong ext λ a →
                                                                            lemma₁ (λ { (get , set) b₁ → ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                   (_↔_.to ≡×≡↔≡ (g , s)))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                    (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b)
                ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a)
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ → subst (λ { (get , set) →
                          ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁)
                 ≡
               set-set l₂ a b₁))                                     ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                         ∀-cong ext λ a → ∀-cong ext λ b₁ →
                                                                           lemma₁ (λ { (get , set) b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                    (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b)
                ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a)
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ { (get , set) →
                             set (set a b₁) b₂ ≡ set a b₂ })
                        (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁ b₂)
                    ≡
                  set-set l₂ a b₁ b₂))                               ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         (∀-cong ext λ a → ∀-cong ext λ b →
                                                                          lemma₂ (λ { (get , set) → get (set a b) ≡ b }) g s)
                                                                           ×-cong
                                                                         (∀-cong ext λ a →
                                                                          lemma₂ (λ { (get , set) → set a (get a) ≡ a }) g s)
                                                                           ×-cong
                                                                         (∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                          lemma₂ (λ { (get , set) → set (set a b₁) b₂ ≡ set a b₂ }) g s)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                (subst (λ set → get l₁ (set a b) ≡ b) s
                   (get-set l₁ a b))
                ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a))
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ →
        subst (λ get → set l₂ (set l₂ a b₁) b₂ ≡ set l₂ a b₂) g
          (subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
             (set-set l₁ a b₁ b₂))
          ≡
        set-set l₂ a b₁ b₂))                                         ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                         ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                         ≡⇒↝ _ $ cong (λ x → x ≡ _) $ subst-const g) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                (subst (λ set → get l₁ (set a b) ≡ b) s
                   (get-set l₁ a b))
                ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a))
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                    (set-set l₁ a b₁ b₂)
                    ≡
                  set-set l₂ a b₁ b₂))                               □
    where
    open Lens

    l₁′ = _↔_.to Lens-as-Σ l₁
    l₂′ = _↔_.to Lens-as-Σ l₂

    abstract

      lemma₁ :
        ∀ (C : A → B → Set c) (eq : u ≡ v) {f g} →
        (subst (λ x → ∀ y → C x y) eq f ≡ g)
          ↔
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)
      lemma₁ C eq {f} {g} =
        subst (λ x → ∀ y → C x y) eq f ≡ g              ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (∀ y → subst (λ x → ∀ y → C x y) eq f y ≡ g y)  ↝⟨ (∀-cong ext λ y → ≡⇒↝ _ $
                                                            cong (λ x → x ≡ _) (sym $ push-subst-application eq _)) ⟩□
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)      □

    lemma₂ :
      ∀ (P : A × B → Set p) (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : y₁ ≡ y₂) {p p′} →
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡ p′)
        ↔
      (subst (λ x → P (x , y₂)) x₁≡x₂ (subst (λ y → P (x₁ , y)) y₁≡y₂ p)
         ≡
       p′)
    lemma₂ P refl refl = F.id

-- Combinators.

module Lens-combinators where

  -- Identity lens.

  id : Lens A A
  id = record
    { get     = λ a      → a
    ; set     = λ _ a    → a
    ; get-set = λ _ _    → refl
    ; set-get = λ _      → refl
    ; set-set = λ _ _ _  → refl
    }

  -- Composition of lenses.
  --
  -- Note that composition can be defined in several different ways. I
  -- don't know if these definitions are equal (if we require that the
  -- three composition laws below must hold).

  infixr 9 _∘_

  _∘_ : Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = record
    { get     = λ a → get l₁ (get l₂ a)
    ; set     = λ a c →
                let b = set l₁ (get l₂ a) c in
                set l₂ a b
    ; get-set = λ a c →
        let b = set l₁ (get l₂ a) c in
        get l₁ (get l₂ (set l₂ a b))  ≡⟨ cong (get l₁) $ get-set l₂ a b ⟩
        get l₁ b                      ≡⟨⟩
        get l₁ (set l₁ (get l₂ a) c)  ≡⟨ get-set l₁ (get l₂ a) c ⟩∎
        c                             ∎
    ; set-get = λ a →
        set l₂ a (set l₁ (get l₂ a) (get l₁ (get l₂ a)))  ≡⟨ cong (set l₂ a) $ set-get l₁ (get l₂ a) ⟩
        set l₂ a (get l₂ a)                               ≡⟨ set-get l₂ a ⟩∎
        a                                                 ∎
    ; set-set = λ a c₁ c₂ →
        let b₁ = set l₁ (get l₂ a) c₁
            b₂ = set l₁ (get l₂ a) c₂

            lemma =
              set l₁ (get l₂ (set l₂ a b₁))  c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
              set l₁ b₁                      c₂  ≡⟨⟩
              set l₁ (set l₁ (get l₂ a) c₁)  c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩∎
              set l₁ (get l₂ a)              c₂  ∎

        in
        set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ set-set l₂ a b₁ _ ⟩
        set l₂ a             (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ a) lemma ⟩∎
        set l₂ a             b₂                                  ∎
    }
    where
    open Lens

  -- id is a left identity of _∘_.

  left-identity : (l : Lens A B) → id ∘ l ≡ l
  left-identity l =
    _↔_.from equality-characterisation
             (refl , refl , lemma₁ , lemma₂ , lemma₃)
    where
    open Lens l

    lemma₁ = λ a b →
      cong P.id (get-set a b)  ≡⟨ sym $ cong-id _ ⟩∎
      get-set a b              ∎

    lemma₂ = λ a →
      trans refl (set-get a)  ≡⟨ trans-reflˡ _ ⟩∎
      set-get a               ∎

    lemma₃ = λ a b₁ b₂ →
      trans (set-set a b₁ b₂)
            (cong (set a) (cong (const b₂) (get-set a b₁)))  ≡⟨ cong (trans _ ⊚ cong (set a)) (cong-const (get-set a b₁)) ⟩∎

      set-set a b₁ b₂                                        ∎

  -- id is a right identity of _∘_.

  right-identity : (l : Lens A B) → l ∘ id ≡ l
  right-identity l =
    _↔_.from equality-characterisation
             (refl , refl , lemma₁ , lemma₂ , lemma₃)
    where
    open Lens l

    lemma₁ = λ a b →
      trans refl (get-set a b)  ≡⟨ trans-reflˡ _ ⟩∎
      get-set a b               ∎

    lemma₂ = λ a →
      cong P.id (set-get a)  ≡⟨ sym $ cong-id _ ⟩∎
      set-get a              ∎

    lemma₃ = λ a b₁ b₂ →
      trans refl (cong P.id (trans refl (set-set a b₁ b₂)))  ≡⟨ trans-reflˡ _ ⟩
      cong P.id (trans refl (set-set a b₁ b₂))               ≡⟨ sym $ cong-id _ ⟩
      trans refl (set-set a b₁ b₂)                           ≡⟨ trans-reflˡ _ ⟩∎
      set-set a b₁ b₂                                        ∎

  -- _∘_ is associative.

  associativity :
    (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
    l₁ ∘ (l₂ ∘ l₃) ≡ (l₁ ∘ l₂) ∘ l₃
  associativity l₁ l₂ l₃ =
    _↔_.from equality-characterisation
             (refl , refl , lemma₁ , lemma₂ , lemma₃)
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

        b₁  = set l₂ (get l₃ a) c₁
        b₁′ = get l₃ (set l₃ a b₁)

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
          refl                                              ∎

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
          cong g (trans (sym c₂′≡c₂″) (cong h (cong i y)))           ≡⟨ cong (cong g) lemma₁₀ ⟩∎
          refl                                                       ∎

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
                       (cong g (cong h (cong i y))))                    ≡⟨ cong (trans (trans _ (z c₂″))) lemma₇ ⟩∎

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
                (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))  ≡⟨ cong (λ e → trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
                                                                                             e)
                                                                                (sym $ cong-∘ f g (trans _ v)) ⟩
          trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
                (cong f (cong g (trans (cong h (trans (cong i y) u))
                                       v)))                             ≡⟨ sym $ cong-trans f (trans _ (z c₂′)) (cong g (trans _ v)) ⟩

          cong f (trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                        (cong g (trans (cong h (trans (cong i y) u))
                                       v)))                             ≡⟨ cong (cong f) lemma₂ ⟩∎

          cong f (trans (cong (λ x → set l₂ x (h (i x))) y)
                        (trans (z c₂″) (cong g (trans (cong h u) v))))  ∎
      in
      trans (trans x (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                    (z c₂′))))
            (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))    ≡⟨ trans-assoc _ _ (cong (f ⊚ g) (trans _ v)) ⟩

      trans x (trans (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                    (z c₂′)))
                     (cong (f ⊚ g)
                           (trans (cong h (trans (cong i y) u)) v)))  ≡⟨ cong (trans x) lemma₁ ⟩∎

      trans x (cong f (trans (cong (λ x → set l₂ x (h (i x))) y)
                             (trans (z c₂″)
                                    (cong g (trans (cong h u) v)))))  ∎

------------------------------------------------------------------------
-- Some lens isomorphisms

-- If B is a proposition, then Lens a b is isomorphic to
-- (A → B) × ((a : A) → a ≡ a).

lens-to-proposition↔ :
  Is-proposition B →
  Lens A B ↔ (A → B) × ((a : A) → a ≡ a)
lens-to-proposition↔ {B = B} {A = A} B-prop =
  Lens A B                                                          ↝⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))                    ↝⟨ (∃-cong λ get → ∃-cong λ set → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                          ≡⇒↝ _ (
       (set (set a b₁)                         b₂ ≡ set a b₂)               ≡⟨ cong (λ b → set (set a b) b₂ ≡ _) (B-prop _ _) ⟩
       (set (set a (get a))                    b₂ ≡ set a b₂)               ≡⟨ cong (λ b → set (set a (get a)) b ≡ _) (B-prop _ _) ⟩
       (set (set a (get a)) (get (set a (get a))) ≡ set a b₂)               ≡⟨ cong (λ b → _ ≡ set a b) (B-prop _ _) ⟩∎
       (set (set a (get a)) (get (set a (get a))) ≡ set a (get a))          ∎)) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a → B → B →
        set (set a (get a)) (get (set a (get a))) ≡
        set a (get a)))                                             ↝⟨ (∃-cong λ get →
                                                                        Σ-cong (A→B→A↔A→A get) λ set →
                                                                          drop-⊤-left-× λ _ →
                                                                            _⇔_.to contractible⇔↔⊤ $
                                                                              Π-closure ext 0 λ _ →
                                                                              Π-closure ext 0 λ _ →
                                                                              +⇒≡ B-prop) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → B → f (f a) ≡ f a))                                 ↝⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a →
                                                                          drop-⊤-left-Π ext (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → f (f a) ≡ f a))                                     ↝⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a →
                                                                          drop-⊤-left-Π ext (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → f (f a) ≡ f a))                                         ↝⟨ (∃-cong λ _ → ∃-cong λ f →
                                                                        Σ-cong (Eq.extensionality-isomorphism ext) λ f≡id →
                                                                        ∀-cong ext λ a →
                                                                        ≡⇒↝ _ (cong₂ _≡_ (trans (f≡id (f a)) (f≡id a)) (f≡id a ))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     f ≡ P.id ×
     (∀ a → a ≡ a))                                                 ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (A → B) ×
  (∃ λ (f : A → A) → f ≡ P.id) ×
  (∀ a → a ≡ a)                                                     ↝⟨ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                                          _⇔_.to contractible⇔↔⊤ $
                                                                            singleton-contractible _) ⟩□
  (A → B) × (∀ a → a ≡ a)                                           □

  where
  A→B→A↔A→A : (A → B) → (A → B → A) ↔ (A → A)
  A→B→A↔A→A get =
    (A → B → A)  ↝⟨ ∀-cong ext (λ a →
                      drop-⊤-left-Π ext $
                        _⇔_.to contractible⇔↔⊤ $
                          propositional⇒inhabited⇒contractible B-prop (get a)) ⟩□
    (A → A)      □

  B↔⊤ : B → B ↔ ⊤
  B↔⊤ b =
    _⇔_.to contractible⇔↔⊤ $
      propositional⇒inhabited⇒contractible B-prop b

-- Lens A ⊤ is isomorphic to (a : A) → a ≡ a.

lens-to-⊤↔ : Lens A ⊤ ↔ ((a : A) → a ≡ a)
lens-to-⊤↔ {A = A} =
  Lens A ⊤                     ↝⟨ lens-to-proposition↔ (mono₁ 0 ⊤-contractible) ⟩
  (A → ⊤) × ((a : A) → a ≡ a)  ↝⟨ drop-⊤-left-× (λ _ → →-right-zero) ⟩□
  ((a : A) → a ≡ a)            □

-- Lens A ⊥ is isomorphic to ¬ A.

lens-to-⊥↔ : Lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔ {A = A} =
  Lens A ⊥                     ↝⟨ lens-to-proposition↔ ⊥-propositional ⟩
  (A → ⊥) × ((a : A) → a ≡ a)  ↝⟨ →-cong ext F.id (Bij.⊥↔uninhabited ⊥-elim)
                                    ×-cong
                                  F.id ⟩
  ¬ A × ((a : A) → a ≡ a)      ↝⟨ drop-⊤-right lemma ⟩□
  ¬ A                          □
  where
  lemma : ¬ A → ((a : A) → a ≡ a) ↔ ⊤
  lemma ¬a = record
    { surjection = record
      { logical-equivalence = record
        { to   = _
        ; from = λ _ _ → refl
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ eq → ⟨ext⟩ λ a →
        ⊥-elim (¬a a)
    }

-- Lens ⊥ B is isomorphic to the unit type.

lens-from-⊥↔⊤ : Lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ =
  _⇔_.to contractible⇔↔⊤ $
    record
      { get = ⊥-elim
      ; set = ⊥-elim
      ; get-set = λ a → ⊥-elim a
      ; set-get = λ a → ⊥-elim a
      ; set-set = λ a → ⊥-elim a
      } ,
    λ l → _↔_.from equality-characterisation
            ( ⟨ext⟩ (λ a → ⊥-elim a)
            , ⟨ext⟩ (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            )

------------------------------------------------------------------------
-- Some lens results related to h-levels

-- If the domain of a lens is inhabited and has h-level n,
-- then the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} n l a =
  H-level n A  ↝⟨ H-level.respects-surjection surj n ⟩
  H-level n B  □
  where
  open Lens l

  surj : A ↠ B
  surj = record
    { logical-equivalence = record
      { to   = get
      ; from = set a
      }
    ; right-inverse-of = λ b →
        get (set a b)  ≡⟨ get-set a b ⟩∎
        b              ∎
    }

-- Lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited _ l (proj₁ c) c

-- If A and B have h-level n (where, in the case of B, one can assume
-- that A is inhabited), then Lens a b also has h-level n.

lens-preserves-h-level :
  ∀ n → H-level n A → (A → H-level n B) →
  H-level n (Lens A B)
lens-preserves-h-level n hA hB =
  H-level.respects-surjection (_↔_.surjection (inverse Lens-as-Σ)) n $
  Σ-closure n (Π-closure ext n λ a →
               hB a) λ _ →
  Σ-closure n (Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               hA) λ _ →
  ×-closure n (Π-closure ext n λ a →
               Π-closure ext n λ _ →
               +⇒≡ $ mono₁ n (hB a)) $
  ×-closure n (Π-closure ext n λ _ →
               +⇒≡ $ mono₁ n hA)
              (Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               +⇒≡ $ mono₁ n hA)

-- If A has positive h-level n, then Lens A B also has h-level n.

lens-preserves-h-level-of-domain :
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain n hA =
  [inhabited⇒+]⇒+ n λ l →
    lens-preserves-h-level (1 + n) hA λ a →
      h-level-respects-lens-from-inhabited _ l a hA

-- There is a type A such that Lens A ⊤ is not propositional (assuming
-- univalence).

¬-lens-to-⊤-propositional :
  Univalence (# 0) →
  ∃ λ (A : Set₁) → ¬ Is-proposition (Lens A ⊤)
¬-lens-to-⊤-propositional univ =
  A′ , (
  Is-proposition (Lens A′ ⊤)         ↝⟨ H-level.respects-surjection (_↔_.surjection lens-to-⊤↔) 1 ⟩
  Is-proposition ((a : A′) → a ≡ a)  ↝⟨ proj₂ $ ¬-type-of-refl-propositional ext univ ⟩□
  ⊥₀                                 □)
  where
  A′ = _

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens =
  Lens.Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible
