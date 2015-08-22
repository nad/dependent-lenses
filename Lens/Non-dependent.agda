------------------------------------------------------------------------
-- Non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lens.Non-dependent where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_; module _≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation equality-with-J
open import Preimage equality-with-J
open import Surjection equality-with-J using (_↠_; module _↠_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Traditional lenses

-- Lenses.

Traditional-lens : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Traditional-lens A B =
  ∃ λ (get : A → B) →
  ∃ λ (set : A → B → A) →
  (∀ a b → get (set a b) ≡ b) ×
  (∀ a → set a (get a) ≡ a) ×
  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)

-- Projections.

module Traditional-lens {a b} {A : Set a} {B : Set b}
                        (l : Traditional-lens A B) where

  -- Getter.

  get : A → B
  get = proj₁ l

  -- Setter.

  set : A → B → A
  set = proj₁ (proj₂ l)

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set = proj₁ (proj₂ (proj₂ l))

  set-get : ∀ a → set a (get a) ≡ a
  set-get = proj₁ (proj₂ (proj₂ (proj₂ l)))

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set = proj₂ (proj₂ (proj₂ (proj₂ l)))

-- Equality characterisation.

abstract

  equality-characterisation :
    ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Traditional-lens A B} →
    let open Traditional-lens in
    Extensionality (a ⊔ b) (a ⊔ b) →

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

  equality-characterisation {ℓa} {ℓb} {A} {B} {l₁} {l₂} ext =
    l₁ ≡ l₂                                                          ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Σ-assoc)) ⟩

    ((get l₁ , set l₁) , proj₂ (proj₂ l₁))
      ≡
    ((get l₂ , set l₂) , proj₂ (proj₂ l₂))                           ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           gs (proj₂ (proj₂ l₁))
       ≡
     proj₂ (proj₂ l₂))                                               ↝⟨ Σ-cong (inverse ≡×≡↔≡) (λ gs → ≡⇒↝ _ $
                                                                        cong (λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
                                                                                subst (λ { (get , set) →
                                                                                           (∀ a b → get (set a b) ≡ b) ×
                                                                                           (∀ a → set a (get a) ≡ a) ×
                                                                                           (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
                                                                                      gs (proj₂ (proj₂ l₁))
                                                                                  ≡
                                                                                proj₂ (proj₂ l₂))
                                                                             (sym $ _↔_.right-inverse-of ≡×≡↔≡ gs)) ⟩
    (∃ λ (gs : get l₁ ≡ get l₂ × set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ gs) (proj₂ (proj₂ l₁))
       ≡
     proj₂ (proj₂ l₂))                                               ↝⟨ inverse Σ-assoc ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ l₁))
       ≡
     proj₂ (proj₂ l₂))                                               ↝⟨ (∃-cong λ g → ∃-cong λ s → ≡⇒↝ _ $
                                                                         cong (λ x → x ≡ proj₂ (proj₂ l₂))
                                                                              (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     ( subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
             (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
     , subst (λ { (get , set) →
                  (∀ a → set a (get a) ≡ a) ×
                  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁)))
     )
       ≡
     proj₂ (proj₂ l₂))                                               ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

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
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁)))
       ≡
     proj₂ (proj₂ (proj₂ l₂)))                                       ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ≡⇒↝ _ $
                                                                         cong (λ x → x ≡ proj₂ (proj₂ (proj₂ l₂)))
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
     proj₂ (proj₂ (proj₂ l₂)))                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

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
       set-set l₂)                                                   ↔⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         lemma₁ (lower-extensionality ℓb ℓa ext)
                                                                                (λ { (get , set) a → ∀ b → get (set a b) ≡ b })
                                                                                (_↔_.to ≡×≡↔≡ (g , s))
                                                                           ×-cong
                                                                         lemma₁ (lower-extensionality ℓb ℓb ext)
                                                                                (λ { (get , set) a → set a (get a) ≡ a })
                                                                                (_↔_.to ≡×≡↔≡ (g , s))
                                                                           ×-cong
                                                                         lemma₁ (lower-extensionality ℓb lzero ext)
                                                                                (λ { (get , set) a → ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
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
            set-set l₂ a))                                           ↔⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         (Eq.∀-preserves (lower-extensionality ℓb ℓa ext) λ a →
                                                                            lemma₁ (lower-extensionality ℓa ℓa ext)
                                                                                   (λ { (get , set) b → get (set a b) ≡ b })
                                                                                   (_↔_.to ≡×≡↔≡ (g , s)))
                                                                           ×-cong
                                                                         F.id
                                                                           ×-cong
                                                                         (Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                                            lemma₁ (lower-extensionality ℓa lzero ext)
                                                                                   (λ { (get , set) b₁ → ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
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
               set-set l₂ a b₁))                                     ↔⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                         Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                                         Eq.∀-preserves (lower-extensionality ℓa lzero ext) λ b₁ →
                                                                           lemma₁ (lower-extensionality ℓa ℓb ext)
                                                                                  (λ { (get , set) b₂ → set (set a b₁) b₂ ≡ set a b₂ })
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
                  set-set l₂ a b₁ b₂))                               ↔⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         (Eq.∀-preserves (lower-extensionality ℓb ℓa ext) λ a →
                                                                          Eq.∀-preserves (lower-extensionality ℓa ℓa ext) λ b →
                                                                          lemma₂ (λ { (get , set) → get (set a b) ≡ b }) g s)
                                                                           ×-cong
                                                                         (Eq.∀-preserves (lower-extensionality ℓb ℓb ext) λ a →
                                                                          lemma₂ (λ { (get , set) → set a (get a) ≡ a }) g s)
                                                                           ×-cong
                                                                         (Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                                          Eq.∀-preserves (lower-extensionality ℓa lzero ext) λ b₁ →
                                                                          Eq.∀-preserves (lower-extensionality ℓa ℓb    ext) λ b₂ →
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
        set-set l₂ a b₁ b₂))                                         ↔⟨ (∃-cong λ g → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                         Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ _ →
                                                                         Eq.∀-preserves (lower-extensionality ℓa lzero ext) λ _ →
                                                                         Eq.∀-preserves (lower-extensionality ℓa ℓb    ext) λ _ →
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
    open Traditional-lens

    abstract

      lemma₁ :
        ∀ {a b c} {A : Set a} {B : Set b} {u v} →
        Extensionality b c →
        ∀ (C : A → B → Set c) (eq : u ≡ v) {f g} →
        (subst (λ x → ∀ y → C x y) eq f ≡ g)
          ≃
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)
      lemma₁ ext C eq {f} {g} =
        subst (λ x → ∀ y → C x y) eq f ≡ g              ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (∀ y → subst (λ x → ∀ y → C x y) eq f y ≡ g y)  ↝⟨ (Eq.∀-preserves ext λ y → ≡⇒↝ _ $
                                                            cong (λ x → x ≡ _) (sym $ push-subst-application eq _)) ⟩□
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)      □

    lemma₂ :
      ∀ {a b p} {A : Set a} {B : Set b} {x₁ x₂ : A} {y₁ y₂ : B}
      (P : A × B → Set p) (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : y₁ ≡ y₂) {p p′} →
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡ p′)
        ≃
      (subst (λ x → P (x , y₂)) x₁≡x₂ (subst (λ y → P (x₁ , y)) y₁≡y₂ p)
         ≡
       p′)
    lemma₂ P refl refl = F.id

-- Combinators.

module Traditional-lens-combinators where

  -- Identity lens.

  id : ∀ {a} {A : Set a} → Traditional-lens A A
  id =
    P.id ,
    flip const ,
    (λ _ _   → refl) ,
    (λ _     → refl) ,
    (λ _ _ _ → refl)

  -- Composition of lenses.

  infixr 9 _∘_

  _∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        Traditional-lens B C → Traditional-lens A B →
        Traditional-lens A C
  l₁ ∘ l₂ =
    get l₁ ⊚ get l₂ ,
    (λ a c → let b = set l₁ (get l₂ a) c in
             set l₂ a b) ,
    (λ a c → let b = set l₁ (get l₂ a) c in

       get l₁ (get l₂ (set l₂ a b))  ≡⟨ cong (get l₁) $ get-set l₂ a b ⟩
       get l₁ b                      ≡⟨⟩
       get l₁ (set l₁ (get l₂ a) c)  ≡⟨ get-set l₁ (get l₂ a) c ⟩∎
       c                             ∎) ,
    (λ a →
       set l₂ a (set l₁ (get l₂ a) (get l₁ (get l₂ a)))  ≡⟨ cong (set l₂ a) $ set-get l₁ (get l₂ a) ⟩
       set l₂ a (get l₂ a)                               ≡⟨ set-get l₂ a ⟩∎
       a                                                 ∎) ,
    (λ a c₁ c₂ →
       let b₁ = set l₁ (get l₂ a) c₁
           b₂ = set l₁ (get l₂ a) c₂

           lemma =
             set l₁ (get l₂ (set l₂ a b₁)) c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
             set l₁ b₁                     c₂  ≡⟨⟩
             set l₁ (set l₁ (get l₂ a) c₁) c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩∎
             set l₁ (get l₂ a)             c₂  ∎

       in
       set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ (set l₂ a b₁)) lemma ⟩
       set l₂ (set l₂ a b₁) b₂                                  ≡⟨ set-set l₂ a b₁ b₂ ⟩∎
       set l₂ a             b₂                                  ∎)
    where
    open Traditional-lens

------------------------------------------------------------------------
-- Alternative formulations of lenses

-- Paolo Capriotti has described higher lenses
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/). In the
-- following definition I have used the Church-encoded propositional
-- truncation instead of the one from the HoTT book. The
-- Church-encoded truncation is perhaps less usable than the other
-- one, but when both definitions are available they are isomorphic
-- (see H-level.Truncation.Real-propositional-truncation.isomorphic).

Higher-lens : ∀ {a b} → Set a → Set b → Set (lsuc (lsuc (a ⊔ b)))
Higher-lens {a} {b} A B =
  ∃ λ (g : A → B) →
  ∃ λ (H : Pow lzero (∥ B ∥ 1 (a ⊔ b))) →
    ↑ _ ⊚ (g ⁻¹_) ≡ H ⊚ ∣_∣

-- The following more traditional (?) alternative definition uses a
-- bijection:
--
--   ∃ R. A ↔ (R × B).
--
-- However, this definition is not in general isomorphic to the ones
-- above, not even if A, B and R are sets (consider the case in which
-- A and B are empty). The following variant of the definition solves
-- this problem.
--
-- (I had previously considered some other variants, when Andrea
-- Vezzosi suggested that I should look at higher lenses, and that I
-- could perhaps use R → ∥ B ∥. This worked out nicely.)

Iso-lens : ∀ {a b} → Set a → Set b → Set (lsuc (lsuc (a ⊔ b)))
Iso-lens {a} {b} A B =
  ∃ λ (R : Set (lsuc (a ⊔ b))) →
    (A ≃ (R × B)) ×
    (R → ∥ B ∥ 1 (a ⊔ b))

------------------------------------------------------------------------
-- Simple definitions related to Iso-lenses

-- Some derived definitions.

module Iso-lens {a b} {A : Set a} {B : Set b} (l : Iso-lens A B) where

  -- Remainder type.

  R : Set (lsuc (a ⊔ b))
  R = proj₁ l

  -- Equivalence.

  equiv : A ≃ (R × B)
  equiv = proj₁ (proj₂ l)

  -- The proof of (mere) inhabitance.

  inhabited : R → ∥ B ∥ 1 (a ⊔ b)
  inhabited = proj₂ (proj₂ l)

  -- Remainder.

  remainder : A → R
  remainder a = proj₁ (_≃_.to equiv a)

  -- Getter.

  get : A → B
  get a = proj₂ (_≃_.to equiv a)

  -- Setter.

  set : A → B → A
  set a b = _≃_.from equiv (remainder a , b)

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    proj₂ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₂ (_≃_.right-inverse-of equiv _) ⟩∎
    proj₂ (remainder a , b)                                  ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    _≃_.from equiv (_≃_.to equiv a)  ≡⟨ _≃_.left-inverse-of equiv _ ⟩∎
    a                                ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    let r = remainder a in

    _≃_.from equiv (remainder (_≃_.from equiv (r , b₁)) , b₂)             ≡⟨⟩
    _≃_.from equiv (proj₁ (_≃_.to equiv (_≃_.from equiv (r , b₁))) , b₂)  ≡⟨ cong (λ x → _≃_.from equiv (proj₁ x , b₂))
                                                                                  (_≃_.right-inverse-of equiv _) ⟩∎
    _≃_.from equiv (r , b₂)                                               ∎

  -- Traditional lens.

  traditional-lens : Traditional-lens A B
  traditional-lens = get , set , get-set , set-get , set-set

-- Isomorphisms can be converted into lenses (assuming
-- extensionality).

isomorphism-to-lens :
  ∀ {a b} {A : Set a} {B : Set b} {R : Set (lsuc (a ⊔ b))} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  A ↔ R × B → Iso-lens A B
isomorphism-to-lens {A = A} {B} {R} ext iso =

  (R × ∥ B ∥ 1 _) ,

  (A                    ↔⟨ iso ⟩
   R × B                ↔⟨ F.id ×-cong inverse (∥∥×↔ ext) ⟩
   R × ∥ B ∥ 1 _ × B    ↔⟨ ×-assoc ⟩□
   (R × ∥ B ∥ 1 _) × B  □) ,

  proj₂

-- A variant of isomorphism-to-lens.

isomorphism-to-lens′ :
  ∀ {a b} {A : Set a} {B : Set b} {R : Set (a ⊔ b)} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  A ↔ R × B → Iso-lens A B
isomorphism-to-lens′ {A = A} {B} {R} ext iso =
  isomorphism-to-lens ext
    (A          ↝⟨ iso ⟩
     R × B      ↝⟨ inverse Bij.↑↔ ×-cong F.id ⟩□
     ↑ _ R × B  □)

------------------------------------------------------------------------
-- Equality characterisations for Iso-lenses

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- extensionality).

equality-characterisation₀ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B} {l₁} {l₂} ext =
  l₁ ≡ l₂                                                        ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B) × (R → ∥ B ∥ 1 _)) p (proj₂ l₁) ≡
     proj₂ l₂)                                                   ↝⟨ (∃-cong λ _ → inverse $
                                                                       ignore-propositional-component
                                                                         (Π-closure ext 1 λ _ →
                                                                          truncation-has-correct-h-level 1
                                                                            (lower-extensionality lzero _ ext))) ⟩
  (∃ λ (p : R l₁ ≡ R l₂) →
     proj₁ (subst (λ R → A ≃ (R × B) × (R → ∥ B ∥ 1 _))
                  p
                  (proj₂ l₁)) ≡
     equiv l₂)                                                   ↝⟨ (∃-cong λ p → ≡⇒↝ _ $
                                                                       cong (λ x → proj₁ x ≡ _) (push-subst-, {y≡z = p} _ _)) ⟩□
  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)          □
  where
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- extensionality and univalence).

equality-characterisation₁ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂
equality-characterisation₁ {A = A} {B} {l₁} {l₂} ext univ =
  l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₀ ext ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)              ↝⟨ inverse $ Σ-cong (inverse $ ≡≃≃ univ) (λ _ → F.id) ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     subst (λ R → A ≃ (R × B)) (≃⇒≡ univ eq) (equiv l₁) ≡ equiv l₂)  ↝⟨ (∃-cong λ _ → inverse $ ≡⇒↝ _ $ cong (λ p → p ≡ _) $
                                                                           transport-theorem
                                                                             (λ R → A ≃ (R × B)) resp
                                                                             (λ _ → Eq.lift-equality ext refl)
                                                                             univ _ _) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) → resp eq (equiv l₁) ≡ equiv l₂)           □
  where
  open Iso-lens

  resp : ∀ {X Y} → X ≃ Y → A ≃ (X × B) → A ≃ (Y × B)
  resp {X} {Y} X≃Y A≃X×B =
    A      ↝⟨ A≃X×B ⟩
    X × B  ↝⟨ X≃Y ×-cong F.id ⟩□
    Y × B  □

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- extensionality and univalence).

equality-characterisation₂ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
          _≃_.to (equiv l₂) x
equality-characterisation₂ {l₁ = l₁} {l₂} ext univ =
  l₁ ≡ l₂                                             ↝⟨ equality-characterisation₁ ext univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)        ↝⟨ (∃-cong λ _ → inverse $ ≃-to-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                       □
  where
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain triples (assuming
-- extensionality and univalence).

equality-characterisation₃ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₃ {l₁ = l₁} {l₂} ext univ =
  l₁ ≡ l₂                                                 ↝⟨ equality-characterisation₂ ext univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                           ↔⟨ (∃-cong λ _ →
                                                              Eq.∀-preserves (lower-extensionality _ lzero ext) λ _ →
                                                                Eq.↔⇒≃ $ inverse ≡×≡↔≡) ⟩
  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x
             ×
           get l₁ x ≡ get l₂ x)                           ↝⟨ (∃-cong λ _ → ΠΣ-comm) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
       ×
     (∀ x → get l₁ x ≡ get l₂ x))                         □
  where
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- extensionality and univalence).

equality-characterisation₄ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃_.from (equiv l₂) p
equality-characterisation₄ {l₁ = l₁} {l₂} ext univ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ ext univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)                      ↝⟨ (∃-cong λ _ → inverse $ ≃-from-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃_.from (equiv l₂) p)                                   □
  where
  open Iso-lens

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Iso-lens preserves bijections (assuming
-- extensionality).

Iso-lens′-cong :
  ∀ {r t}
    {a₁ b₁} {A₁ : Set a₁} {B₁ : Set b₁}
    {a₂ b₂} {A₂ : Set a₂} {B₂ : Set b₂} →
  Extensionality (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ r ⊔ lsuc t)
                 (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ r ⊔ lsuc t) →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  (∃ λ (R : Set r) → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥ 1 t)) ↔
  (∃ λ (R : Set r) → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥ 1 t))
Iso-lens′-cong {r} {t} {a₁} {b₁} {A₁} {B₁} {a₂} {b₂} {A₂} {B₂}
               ext A₁↔A₂ B₁↔B₂ =
  ∃-cong λ _ →
  Eq.≃-preserves-bijections (lower-extensionality (lsuc t) (lsuc t) ext)
                            A₁↔A₂ (F.id ×-cong B₁↔B₂)
    ×-cong
  →-cong (lower-extensionality (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ lsuc t)
                               (a₁ ⊔ a₂ ⊔ r) ext)
         F.id
         (∥∥-cong (lower-extensionality (a₁ ⊔ a₂ ⊔ r)
                                        (a₁ ⊔ a₂ ⊔ r ⊔ lsuc t) ext)
                  B₁↔B₂)

-- Iso-lens preserves level-preserving bijections (assuming
-- extensionality).

Iso-lens-cong :
  ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  Iso-lens A₁ B₁ ↔ Iso-lens A₂ B₂
Iso-lens-cong = Iso-lens′-cong

-- If B is a proposition, then Iso-lens A B is isomorphic to A → B
-- (assuming extensionality and univalence).

lens-to-proposition↔get :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Is-proposition B →
  Iso-lens A B ↔ (A → B)
lens-to-proposition↔get {a} {A = A} {B} ext univ B-prop =
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥ 1 _))  ↔⟨ (∃-cong λ _ →
                                               ∃-cong λ _ →
                                               Eq.∀-preserves ext λ _ →
                                                 Eq.↔⇒≃ $ ∥∥↔ a (lower-extensionality lzero _ ext) B-prop) ⟩
  (∃ λ R → A ≃ (R × B) × (R → B))          ↝⟨ (∃-cong λ _ →
                                               ×-cong₁ λ R→B →
                                               Eq.≃-preserves-bijections ext F.id $
                                                 drop-⊤-right λ r →
                                                   inverse $ _⇔_.to contractible⇔⊤↔ $
                                                     propositional⇒inhabited⇒contractible B-prop (R→B r)) ⟩
  (∃ λ R → A ≃ R × (R → B))                ↔⟨ (∃-cong λ _ →
                                               ∃-cong λ A≃R →
                                               →-cong (lower-extensionality lzero _ ext) {k = equivalence}
                                                 (inverse A≃R) F.id) ⟩
  (∃ λ R → A ≃ R × (A → B))                ↝⟨ Σ-assoc ⟩
  (∃ λ R → A ≃ R) × (A → B)                ↝⟨ (drop-⊤-left-× λ _ → other-singleton-with-≃-↔-⊤ ext univ) ⟩□
  (A → B)                                  □

-- If B is contractible, then Iso-lens A B is isomorphic to ⊤
-- (assuming extensionality and univalence).

lens-to-contractible↔⊤ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Contractible B →
  Iso-lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} ext univ cB =
  Iso-lens A B  ↝⟨ lens-to-proposition↔get ext univ (mono₁ 0 cB) ⟩
  (A → B)       ↝⟨ →-cong (lower-extensionality _ _ ext) F.id $
                     inverse $ _⇔_.to contractible⇔⊤↔ cB ⟩
  (A → ⊤)       ↝⟨ →-right-zero ⟩□
  ⊤             □

-- Iso-lens A ⊥ is isomorphic to ¬ A (assuming extensionality and
-- univalence).

lens-to-⊥↔¬ :
  ∀ {a b} {A : Set a} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Iso-lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔¬ {a} {A = A} ext univ =
  Iso-lens A ⊥  ↝⟨ lens-to-proposition↔get ext univ ⊥-propositional ⟩
  (A → ⊥)       ↝⟨ →-cong (lower-extensionality _ _ ext) F.id (⊥↔uninhabited ⊥-elim) ⟩□
  ¬ A           □

-- If A is contractible, then Iso-lens A B is isomorphic to
-- Contractible B (assuming extensionality and univalence).

lens-from-contractible↔codomain-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Contractible A →
  Iso-lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible {A = A} {B} ext univ cA =
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥ 1 _))                        ↝⟨ inverse $
                                                                    ∃-cong (λ _ →
                                                                      Eq.≃-preserves-bijections ext (_⇔_.to contractible⇔⊤↔ cA) F.id
                                                                        ×-cong
                                                                      F.id) ⟩
  (∃ λ R → ⊤ ≃ (R × B) × (R → ∥ B ∥ 1 _))                        ↝⟨ ∃-cong (λ _ → inverse (contractible↔⊤≃ ext) ×-cong F.id) ⟩
  (∃ λ R → Contractible (R × B) × (R → ∥ B ∥ 1 _))               ↔⟨ ∃-cong (λ _ → Contractible-commutes-with-× ext ×-cong F.id) ⟩
  (∃ λ R → (Contractible R × Contractible B) × (R → ∥ B ∥ 1 _))  ↝⟨ ∃-cong (λ _ → inverse ×-assoc) ⟩
  (∃ λ R → Contractible R × Contractible B × (R → ∥ B ∥ 1 _))    ↝⟨ inverse $
                                                                    ∃-cong (λ _ → ∃-cong λ cR →
                                                                      F.id
                                                                        ×-cong
                                                                      →-cong ext (_⇔_.to contractible⇔⊤↔ cR) F.id) ⟩
  (∃ λ R → Contractible R × Contractible B × (⊤ → ∥ B ∥ 1 _))    ↝⟨ ∃-cong (λ _ → F.id ×-cong F.id ×-cong Π-left-identity) ⟩
  (∃ λ R → Contractible R × Contractible B × ∥ B ∥ 1 _)          ↝⟨ ∃-cong (λ _ → ×-comm) ⟩
  (∃ λ R → (Contractible B × ∥ B ∥ 1 _) × Contractible R)        ↝⟨ ∃-comm ⟩
  (Contractible B × ∥ B ∥ 1 _) × (∃ λ R → Contractible R)        ↝⟨ drop-⊤-right (λ _ → ∃Contractible↔⊤ ext univ) ⟩
  Contractible B × ∥ B ∥ 1 _                                     ↝⟨ drop-⊤-right (λ cB →
                                                                      inhabited⇒∥∥↔⊤ (lower-extensionality lzero _ ext) ∣ proj₁ cB ∣) ⟩□
  Contractible B                                                 □

-- Iso-lens ⊥ B is isomorphic to the unit type (assuming
-- extensionality and univalence).

lens-from-⊥↔⊤ :
  ∀ {a b} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Iso-lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ {B = B} ext univ =
  inverse $ _⇔_.to contractible⇔⊤↔ $
    isomorphism-to-lens (lower-extensionality lzero _ ext)
      (⊥      ↝⟨ inverse ×-left-zero ⟩□
       ⊥ × B  □) ,
    λ l → _↔_.from (equality-characterisation₂ ext univ)
            ( (⊥ × ∥ B ∥ 1 _  ↔⟨ ×-left-zero ⟩
               ⊥₀             ↔⟨ lemma l ⟩□
               R l            □)
            , λ x → ⊥-elim x
            )
  where
  open Iso-lens

  lemma : (l : Iso-lens ⊥ B) → ⊥₀ ↔ R l
  lemma l = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⊥-elim
        ; from = whatever
        }
      ; right-inverse-of = whatever
      }
    ; left-inverse-of = λ x → ⊥-elim x
    }
    where
    whatever : ∀ {ℓ} {Whatever : R l → Set ℓ} → (r : R l) → Whatever r
    whatever r = ⊥-elim $
      rec ⊥-propositional
          (λ b → ⊥-elim (_≃_.from (equiv l) (r , b)))
          (inhabited l r)

-- If B is a proposition, then Traditional-lens A B is isomorphic to
-- (A → B) × ((a : A) → a ≡ a) (assuming extensionality).

traditional-lens-to-proposition↔ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-proposition B →
  Traditional-lens A B ↔ (A → B) × ((a : A) → a ≡ a)
traditional-lens-to-proposition↔ {ℓa} {ℓb} {A} {B} ext B-prop =
  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))     ↔⟨ (∃-cong λ get → ∃-cong λ set → ∃-cong λ _ → ∃-cong λ _ →
                                                         Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                         Eq.∀-preserves (lower-extensionality ℓa lzero ext) λ b₁ →
                                                         Eq.∀-preserves (lower-extensionality ℓa ℓb    ext) λ b₂ →
                                                           ≡⇒↝ _ (
       (set (set a b₁)                         b₂ ≡ set a b₂)       ≡⟨ cong (λ b → set (set a b) b₂ ≡ _)
                                                                            (_⇔_.to propositional⇔irrelevant B-prop _ _) ⟩
       (set (set a (get a))                    b₂ ≡ set a b₂)       ≡⟨ cong (λ b → set (set a (get a)) b ≡ _)
                                                                            (_⇔_.to propositional⇔irrelevant B-prop _ _) ⟩
       (set (set a (get a)) (get (set a (get a))) ≡ set a b₂)       ≡⟨ cong (λ b → _ ≡ set a b)
                                                                            (_⇔_.to propositional⇔irrelevant B-prop _ _) ⟩∎
       (set (set a (get a)) (get (set a (get a))) ≡ set a (get a))  ∎)) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a → B → B →
        set (set a (get a)) (get (set a (get a))) ≡
        set a (get a)))                              ↝⟨ (∃-cong λ get →
                                                         Σ-cong (A→B→A≃A→A get) λ set →
                                                           drop-⊤-left-× λ _ →
                                                             inverse $ _⇔_.to contractible⇔⊤↔ $
                                                               Π-closure (lower-extensionality ℓb ℓa ext) 0 λ _ →
                                                               Π-closure (lower-extensionality ℓa ℓa ext) 0 λ _ →
                                                               B-prop _ _) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → B → f (f a) ≡ f a))                  ↔⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                         Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                           Eq.↔⇒≃ $ drop-⊤-left-Π (lower-extensionality ℓa lzero ext) (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → f (f a) ≡ f a))                      ↔⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                         Eq.∀-preserves (lower-extensionality ℓb lzero ext) λ a →
                                                           Eq.↔⇒≃ $ drop-⊤-left-Π (lower-extensionality ℓa ℓb ext) (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → f (f a) ≡ f a))                          ↔⟨ (∃-cong λ _ → ∃-cong λ f →
                                                         Σ-cong (Eq.extensionality-isomorphism
                                                                   (lower-extensionality ℓb ℓb ext)) λ f≡id →
                                                         Eq.∀-preserves (lower-extensionality ℓb ℓb ext) λ a →
                                                         ≡⇒↝ _ (cong₂ _≡_ (trans (f≡id (f a)) (f≡id a)) (f≡id a ))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     f ≡ P.id ×
     (∀ a → a ≡ a))                                  ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (A → B) ×
  (∃ λ (f : A → A) → f ≡ P.id) ×
  (∀ a → a ≡ a)                                      ↝⟨ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                           inverse $ _⇔_.to contractible⇔⊤↔ $
                                                             singleton-contractible _) ⟩□
  (A → B) × (∀ a → a ≡ a)                            □

  where
  A→B→A≃A→A : (A → B) → (A → B → A) ≃ (A → A)
  A→B→A≃A→A get =
    (A → B → A)  ↝⟨ Eq.∀-preserves (lower-extensionality ℓb lzero ext) (λ a →
                      Eq.↔⇒≃ $
                      drop-⊤-left-Π (lower-extensionality ℓa ℓb ext) $
                        inverse $ _⇔_.to contractible⇔⊤↔ $
                          propositional⇒inhabited⇒contractible B-prop (get a)) ⟩□
    (A → A)      □

  B↔⊤ : B → B ↔ ⊤
  B↔⊤ b =
    inverse $ _⇔_.to contractible⇔⊤↔ $
      propositional⇒inhabited⇒contractible B-prop b

-- Traditional-lens A ⊤ is isomorphic to (a : A) → a ≡ a (assuming
-- extensionality).

traditional-lens-to-⊤↔ :
  ∀ {a} {A : Set a} →
  Extensionality a a →
  Traditional-lens A ⊤ ↔ ((a : A) → a ≡ a)
traditional-lens-to-⊤↔ {A = A} ext =
  Traditional-lens A ⊤         ↝⟨ traditional-lens-to-proposition↔ ext (mono₁ 0 ⊤-contractible) ⟩
  (A → ⊤) × ((a : A) → a ≡ a)  ↝⟨ drop-⊤-left-× (λ _ → →-right-zero) ⟩□
  ((a : A) → a ≡ a)            □

-- Traditional-lens A ⊥ is isomorphic to ¬ A (assuming
-- extensionality).

traditional-lens-to-⊥↔ :
  ∀ {a b} {A : Set a} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Traditional-lens A (⊥ {ℓ = b}) ↔ ¬ A
traditional-lens-to-⊥↔ {a} {b} {A} ext =
  Traditional-lens A ⊥         ↝⟨ traditional-lens-to-proposition↔ ext ⊥-propositional ⟩
  (A → ⊥) × ((a : A) → a ≡ a)  ↝⟨ →-cong (lower-extensionality b a ext) F.id (⊥↔uninhabited ⊥-elim)
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
    ; left-inverse-of = λ eq → lower-extensionality b b ext λ a →
        ⊥-elim (¬a a)
    }

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- Higher-lens A B is isomorphic to Iso-lens A B (assuming
-- extensionality and univalence).
--
-- (This proof was simplified following a suggestion by Paolo
-- Capriotti.)

Higher-lens↔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (lsuc (a ⊔ b))) →
  Univalence (lsuc (a ⊔ b)) →
  Higher-lens A B ↔ Iso-lens A B
Higher-lens↔Iso-lens {a} {b} {A} {B} ext univ =
  (∃ λ (g : A → B) → ∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
     ↑ _ ⊚ (g ⁻¹_) ≡ H ⊚ ∣_∣)                                      ↔⟨ Σ-cong lemma₂ (λ _ → ∃-cong (lemma₃ _)) ⟩

  (∃ λ (p : ∃ λ (P : Pow (lsuc ℓ) B) → A ≃ ∃ P) →
   ∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ ∃-comm ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   ∃ λ (p : ∃ λ (P : Pow (lsuc ℓ) B) → A ≃ ∃ P) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   ∃ λ (P : Pow (lsuc ℓ) B) →
      A ≃ ∃ P × P ≡ H ⊚ ∣_∣)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   ∃ λ (P : Pow (lsuc ℓ) B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ P)                                       ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq →
                                                                       Eq.≃-preserves
                                                                         (lower-extensionality (lsuc ℓ) _ ext)
                                                                         F.id
                                                                         (∃-cong λ x → ≡⇒↝ _ (cong (_$ x) eq))) ⟩
  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   ∃ λ (P : Pow (lsuc ℓ) B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ (H ⊚ ∣_∣))                               ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   (∃ λ (P : Pow (lsuc ℓ) B) → P ≡ H ⊚ ∣_∣) ×
   A ≃ ∃ (H ⊚ ∣_∣))                                                ↝⟨ (∃-cong λ _ →
                                                                       drop-⊤-left-× λ _ →
                                                                       inverse (_⇔_.to contractible⇔⊤↔ (singleton-contractible _))) ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) → A ≃ ∃ (H ⊚ ∣_∣))              ↔⟨ inverse $
                                                                      Σ-cong (inverse $ Pow↔Fam lzero ext univ) (λ _ →
                                                                      Eq.≃-preserves (lower-extensionality (lsuc ℓ) _ ext) F.id F.id) ⟩

  (∃ λ (H : Fam lzero (∥ B ∥ 1 ℓ)) → A ≃ ∃ ((proj₂ H ⁻¹_) ⊚ ∣_∣))  ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
   ∃ λ (f : R → ∥ B ∥ 1 ℓ) → A ≃ ∃ ((f ⁻¹_) ⊚ ∣_∣))                ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                                       Eq.≃-preserves (lower-extensionality (lsuc ℓ) _ ext) F.id
                                (∃ ((f ⁻¹_) ⊚ ∣_∣)                       ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                               inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                                 truncation-has-correct-h-level 1
                                                                                   (lower-extensionality (lsuc ℓ) _ ext) _ _) ⟩
                                 B × R                                   ↔⟨ ×-comm ⟩□
                                 R × B                                   □)) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
   (R → ∥ B ∥ 1 ℓ) × (A ≃ (R × B)))                                ↝⟨ (∃-cong λ _ → ×-comm) ⟩□

  (∃ λ (R : Set (lsuc ℓ)) →
   (A ≃ (R × B)) × (R → ∥ B ∥ 1 ℓ))                                □

  where
  ℓ = a ⊔ b

  lemma₁ : ∀ (g : A → B) b →
           ↑ (lsuc ℓ) (g ⁻¹ b) ↔ (g ⊚ lower {ℓ = lsuc ℓ}) ⁻¹ b
  lemma₁ g b = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ { (lift (a , ga≡b)) → lift a , ga≡b }
        ; from = λ { (lift a , ga≡b) → lift (a , ga≡b) }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  abstract

    lemma₂ : (A → B) ↔ ∃ λ (P : Pow (lsuc ℓ) B) → A ≃ ∃ P
    lemma₂ =
      →↔Σ≃Σ (lsuc ℓ) (lower-extensionality (lsuc ℓ) (lsuc ℓ) ext) univ

    lemma₃ :
      (g : A → B) (H : Pow lzero (∥ B ∥ 1 ℓ)) →
      (↑ _ ⊚ (g ⁻¹_) ≡ H ⊚ ∣_∣)
        ≃
      (proj₁ (_↔_.to lemma₂ g) ≡ H ⊚ ∣_∣)
    lemma₃ g H =
      ↑ _ ⊚ (g ⁻¹_) ≡ H ⊚ ∣_∣             ↝⟨ inverse $ Eq.extensionality-isomorphism
                                                         (lower-extensionality _ (lsuc ℓ) ext) ⟩
      (∀ b → ↑ _ (g ⁻¹ b) ≡ H ∣ b ∣)      ↝⟨ Eq.∀-preserves
                                               (lower-extensionality _ (lsuc ℓ) ext) (λ _ →
                                               ≡-preserves-≃
                                                 (lower-extensionality (lsuc ℓ) _ ext)
                                                 univ univ
                                                 (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ⊚ lower) ⁻¹ b ≡ H ∣ b ∣)  ↝⟨ Eq.extensionality-isomorphism
                                               (lower-extensionality _ (lsuc ℓ) ext) ⟩□
      ((g ⊚ lower) ⁻¹_) ≡ H ⊚ ∣_∣         □

-- There is a split surjection from "Iso-lens A B without the
-- inhabitance proof" to Iso-lens A B (assuming extensionality and
-- univalence).

Iso-lens-without-inhabitance↠Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∃ λ (R : Set (lsuc (a ⊔ b))) → A ≃ (R × B)) ↠ Iso-lens A B
Iso-lens-without-inhabitance↠Iso-lens {A = A} {B} ext univ = record
  { logical-equivalence = record
    { to   = λ { (R , A≃R×B) → isomorphism-to-lens
                                 ext′ (_≃_.bijection A≃R×B) }
    ; from = λ { (R , A≃R×B , _) → R , A≃R×B }
    }
  ; right-inverse-of = λ { (R , A≃R×B , inh) →
      _↔_.from (equality-characterisation₂ ext univ)
        ( (R × ∥ B ∥ 1 _  ↔⟨ drop-⊤-right (λ r → inhabited⇒∥∥↔⊤ ext′ (inh r)) ⟩□
           R              □)
        , λ _ → refl
        ) }
  }
  where
  ext′ = lower-extensionality lzero _ ext

-- However, there is in general no split surjection in the other
-- direction (assuming extensionality and univalence).

¬Iso-lens↠Iso-lens-without-inhabitance :
  ∀ {a b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  ¬ ({A : Set a} {B : Set b} →
     Iso-lens A B ↠ (∃ λ (R : Set (lsuc (a ⊔ b))) → A ≃ (R × B)))
¬Iso-lens↠Iso-lens-without-inhabitance ext univ surj =
  ⊥-elim (subst F.id ⊤≡⊥ _)
  where
  ⊤↠Set =
    ⊤                      ↔⟨ inverse $ lens-from-⊥↔⊤ ext univ ⟩
    Iso-lens ⊥ ⊥           ↝⟨ surj ⟩
    (∃ λ R → ⊥ ≃ (R × ⊥))  ↔⟨ (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id ×-right-zero) ⟩
    (∃ λ R → ⊥ ≃ ⊥₀)       ↔⟨ (∃-cong λ _ → ≃⊥≃¬ (lower-extensionality _ _ ext)) ⟩
    (∃ λ R → ¬ ⊥)          ↔⟨ drop-⊤-right (λ _ → ¬⊥↔⊤ (lower-extensionality _ _ ext)) ⟩□
    Set _                  □

  ⊤≡⊥ : ↑ _ ⊤ ≡ ⊥
  ⊤≡⊥ =
    ↑ _ ⊤              ≡⟨ sym $ right-inverse-of _ ⟩
    to (from (↑ _ ⊤))  ≡⟨⟩
    to (from ⊥)        ≡⟨ right-inverse-of _ ⟩∎
    ⊥                  ∎
    where
    open _↠_ ⊤↠Set

-- In general there is no split surjection from Iso-lens A B to
-- Traditional-lens A B (assuming extensionality and univalence).

¬Iso-lens↠Traditional-lens :
  Extensionality (# 2) (# 2) →
  Univalence (# 2) →
  Univalence (# 0) →
  ∃ λ (A : Set₁) →
    ¬ (Iso-lens A ⊤ ↠ Traditional-lens A ⊤)
¬Iso-lens↠Traditional-lens ext univ₂ univ₀ =
  let A = _ in

  A ,
  (λ surj →                               $⟨ _⇔_.from contractible⇔⊤↔ (inverse $ lens-to-contractible↔⊤
                                                                                   ext univ₂ ⊤-contractible) ⟩
     Contractible (Iso-lens A ⊤)          ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (Traditional-lens A ⊤)  ↝⟨ H-level.respects-surjection
                                               (_↔_.surjection $ traditional-lens-to-⊤↔ (lower-extensionality _ _ ext))
                                               0 ⟩
     Contractible ((a : A) → a ≡ a)       ↝⟨ mono₁ 0 ⟩
     Is-proposition ((a : A) → a ≡ a)     ↝⟨ proj₂ $ ¬-type-of-refl-propositional (lower-extensionality _ _ ext) univ₀ ⟩□
     ⊥                                    □)

-- If the domain A is a set, then there is a split surjection from
-- Iso-lens A B to Traditional-lens A B (assuming extensionality).

Iso-lens↠Traditional-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  Is-set A →
  Iso-lens A B ↠ Traditional-lens A B
Iso-lens↠Traditional-lens {ℓa} {ℓb} {A} {B} ext A-set = record
  { logical-equivalence = record
    { to   = Iso-lens.traditional-lens
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  from : Traditional-lens A B → Iso-lens A B
  from l = isomorphism-to-lens′
    {R = ∃ λ (f : B → A) → ∀ b b′ → set (f b) b′ ≡ f b′}
    ext
    (record
       { surjection = record
         { logical-equivalence = record
           { to   = λ a → (set a , set-set a) , get a
           ; from = λ { ((f , _) , b) → f b }
           }
         ; right-inverse-of = λ { ((f , h) , b) →

            let
              irr = {p q : ∀ b b′ → set (f b) b′ ≡ f b′} → p ≡ q
              irr =
                _⇔_.to propositional⇔irrelevant
                  (Π-closure (lower-extensionality _ lzero ext) 1 λ _ →
                   Π-closure (lower-extensionality _ ℓb    ext) 1 λ _ →
                   A-set _ _)
                  _ _

              lemma =
                get (f b)          ≡⟨ cong get (sym (h b b)) ⟩
                get (set (f b) b)  ≡⟨ get-set (f b) b ⟩∎
                b                  ∎
            in
            (set (f b) , set-set (f b)) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ (lower-extensionality _ ℓb ext (h b)) irr) lemma ⟩∎
            (f         , h            ) , b          ∎ }
         }
       ; left-inverse-of = λ a →
           set a (get a)  ≡⟨ set-get a ⟩∎
           a              ∎
       })
    where
    open Traditional-lens l

  to∘from : ∀ l → Iso-lens.traditional-lens (from l) ≡ l
  to∘from l =
    cong (λ proofs → get , set , proofs)
      (Σ-≡,≡→≡
         (_⇔_.to propositional⇔irrelevant
            (Π-closure (lower-extensionality _ ℓa ext) 1 λ a →
             Π-closure (lower-extensionality _ ℓa ext) 1 λ _ →
             B-set a _ _)
            _ _)
         (Σ-≡,≡→≡
           (_⇔_.to propositional⇔irrelevant
              (Π-closure (lower-extensionality _ ℓb ext) 1 λ _ →
               A-set _ _)
              _ _)
           (_⇔_.to propositional⇔irrelevant
              (Π-closure (lower-extensionality _ lzero ext) 1 λ _ →
               Π-closure (lower-extensionality _ lzero ext) 1 λ _ →
               Π-closure (lower-extensionality _ ℓb    ext) 1 λ _ →
               A-set _ _)
              _ _)))
    where
    open Traditional-lens l

    B-set : A → Is-set B
    B-set a =
      proj₂-closure (proj₁ $ _≃_.to eq a) 2 $
      H-level.respects-surjection (_≃_.surjection eq) 2 A-set
      where
      eq = Iso-lens.equiv (from l)

-- If the domain A is a set, then Traditional-lens A B and
-- Iso-lens A B are isomorphic (assuming extensionality, univalence
-- and a resizing function for the propositional truncation).

Iso-lens↔Traditional-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (lsuc (a ⊔ b))) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  Is-set A →
  Iso-lens A B ↔ Traditional-lens A B
Iso-lens↔Traditional-lens {a} {b} {A} {B} ext univ resize A-set = record
  { surjection      = surj
  ; left-inverse-of = from∘to
  }
  where
  surj = Iso-lens↠Traditional-lens (lower-extensionality _ _ ext) A-set

  open Traditional-lens
  open _↠_ surj

  from∘to : ∀ l → from (Iso-lens.traditional-lens l) ≡ l
  from∘to (R , l , inh) =
    _↔_.from (equality-characterisation₄
                (lower-extensionality _ lzero ext) univ)
             (lemma , λ _ → refl)
    where
    ℓ = a ⊔ b

    B-set : (B → R) → ∥ B ∥ 1 b → Is-set B
    B-set f =
      rec (H-level-propositional (lower-extensionality _ _ ext) 2)
          (λ b → proj₂-closure (f b) 2 $
                 H-level.respects-surjection (_≃_.surjection l) 2 A-set)

    R-set : ∥ B ∥ 1 (lsuc ℓ) → Is-set R
    R-set =
      rec (H-level-propositional
             (lower-extensionality _ (lsuc ℓ) ext)
             2)
          (λ b → proj₁-closure (const b) 2 $
                 H-level.respects-surjection (_≃_.surjection l) 2 A-set)

    lemma′ : (∥ B ∥ 1 ℓ × (∥ B ∥ 1 (lsuc ℓ) → R)) ↔ R
    lemma′ = record
      { surjection = record
        { logical-equivalence = record
          { to   = λ { (∥b∥ , f) → f (resize ∥b∥) }
          ; from = λ r → inh r , λ _ → r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (∥b∥ , f) →
          curry (_↔_.to ≡×≡↔≡)
            (_⇔_.to propositional⇔irrelevant
               (truncation-has-correct-h-level 1
                  (lower-extensionality _ _ ext))
               _ _)
            (ext λ ∥b∥′ →
               f (resize ∥b∥)  ≡⟨ cong f (_⇔_.to propositional⇔irrelevant
                                            (truncation-has-correct-h-level 1 ext)
                                            _ _) ⟩∎
               f ∥b∥′          ∎) }
      }

    lemma =
      ↑ _ (∃ λ (f : B → A) → ∀ b b′ →
               _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′)
        ×
      ∥ B ∥ 1 ℓ                                                   ↔⟨ Bij.↑↔ ×-cong F.id ⟩

      (∃ λ (f : B → A) → ∀ b b′ →
           _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′) ×
      ∥ B ∥ 1 ℓ                                                   ↔⟨ ×-comm ⟩

      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → A) → ∀ b b′ →
           _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′)       ↝⟨ (∃-cong λ _ →
                                                                      Σ-cong (→-cong (lower-extensionality _ lzero ext) F.id l) λ _ →
                                                                             Eq.Π-preserves (lower-extensionality _ _ ext) F.id λ _ →
                                                                             Eq.Π-preserves (lower-extensionality _ _ ext) F.id λ _ →
                                                                             ≡⇒↝ _ (cong (_≃_.from l _ ≡_)
                                                                                         (sym $ _≃_.left-inverse-of l _))) ⟩
      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R × B) → ∀ b b′ →
           _≃_.from l (proj₁ (f b) , b′) ≡ _≃_.from l (f b′))     ↝⟨ ∃-cong (λ _ → ∃-cong λ _ →
                                                                       Eq.Π-preserves (lower-extensionality _ lzero ext) F.id λ _ →
                                                                       Eq.Π-preserves (lower-extensionality _ b     ext) F.id λ _ →
                                                                       Eq.≃-≡ (inverse l)) ⟩
      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)  ↝⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ →
                                                                        Eq.Π-preserves (lower-extensionality _ (lsuc ℓ) ext) F.id λ _ →
                                                                        Eq.Π-preserves (lower-extensionality _ (lsuc ℓ) ext) F.id λ _ →
                                                                        inverse $ Eq.↔⇒≃ ≡×≡↔≡) ⟩
      (∥ B ∥ 1 ℓ ×
       ∃ λ (p : (B → R) × (B → B)) →
         ∀ b b′ → proj₁ p b ≡ proj₁ p b′ × b′ ≡ proj₂ p b′)       ↔⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         ∀ b b′ → f b ≡ f b′ × b′ ≡ g b′)                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                        Eq.Π-preserves (lower-extensionality _ (lsuc ℓ) ext) F.id λ _ →
                                                                        Eq.↔⇒≃ ΠΣ-comm) ⟩
      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         ∀ b → (∀ b′ → f b ≡ f b′) × (∀ b′ → b′ ≡ g b′))          ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ΠΣ-comm) ⟩

      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         Constant f × (B → ∀ b → b ≡ g b))                        ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

      (∥ B ∥ 1 ℓ ×
       ∃ λ (f : B → R) → Constant f ×
       ∃ λ (g : B → B) → B → ∀ b → b ≡ g b)                       ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

      (∥ B ∥ 1 ℓ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → B → ∀ b → b ≡ g b))                     ↔⟨ (∃-cong λ ∥b∥ → ∃-cong λ { (f , _) → ∃-cong λ _ → inverse $
                                                                        →-intro (lower-extensionality _ _ ext)
                                                                                (λ _ → B-set f (with-lower-level a ∥b∥) _ _) }) ⟩
      (∥ B ∥ 1 ℓ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → ∀ b → b ≡ g b))                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                        Eq.extensionality-isomorphism (lower-extensionality _ _ ext)) ⟩
      (∥ B ∥ 1 ℓ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → F.id ≡ g))                              ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                                        inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                        other-singleton-contractible _) ⟩
      (∥ B ∥ 1 ℓ × ∃ λ (f : B → R) → Constant f)                  ↝⟨ (∃-cong λ ∥b∥ → constant-function≃∥inhabited∥⇒inhabited
                                                                                       lzero ext (R-set (resize ∥b∥))) ⟩
      (∥ B ∥ 1 ℓ × (∥ B ∥ 1 (lsuc ℓ) → R))                        ↔⟨ lemma′ ⟩

      R                                                           □

------------------------------------------------------------------------
-- Some Traditional-lens results related to h-levels

-- If the domain of a Traditional-lens is inhabited and has h-level n,
-- then the codomain also has h-level n.

h-level-respects-Traditional-lens-from-inhabited :
  ∀ {n a b} {A : Set a} {B : Set b} →
  Traditional-lens A B → A → H-level n A → H-level n B
h-level-respects-Traditional-lens-from-inhabited {n} {A = A} {B} l a =
  H-level n A  ↝⟨ H-level.respects-surjection surj n ⟩
  H-level n B  □
  where
  open Traditional-lens l

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

-- If A and B have h-level n (where, in the case of B, one can assume
-- that A is inhabited), then Traditional-lens A B also has h-level n
-- (assuming extensionality).

Traditional-lens-preserves-h-level :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n → H-level n A → (A → H-level n B) →
  H-level n (Traditional-lens A B)
Traditional-lens-preserves-h-level {ℓa} {ℓb} ext n hA hB =
  Σ-closure n (Π-closure (lower-extensionality ℓb ℓa    ext) n λ a →
               hB a) λ _ →
  Σ-closure n (Π-closure (lower-extensionality ℓb lzero ext) n λ _ →
               Π-closure (lower-extensionality ℓa ℓb    ext) n λ _ →
               hA) λ _ →
  ×-closure n (Π-closure (lower-extensionality ℓb ℓa    ext) n λ a →
               Π-closure (lower-extensionality ℓa ℓa    ext) n λ _ →
               mono₁ n (hB a) _ _) $
  ×-closure n (Π-closure (lower-extensionality ℓb ℓb    ext) n λ _ →
               mono₁ n hA _ _)
              (Π-closure (lower-extensionality ℓb lzero ext) n λ _ →
               Π-closure (lower-extensionality ℓa lzero ext) n λ _ →
               Π-closure (lower-extensionality ℓa ℓb    ext) n λ _ →
               mono₁ n hA _ _)

-- If A has positive h-level n, then Traditional-lens A B also has
-- h-level n (assuming extensionality).

Traditional-lens-preserves-h-level-of-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Traditional-lens A B)
Traditional-lens-preserves-h-level-of-domain {ℓa} {ℓb} ext n hA =
  [inhabited⇒+]⇒+ n λ l →
    Traditional-lens-preserves-h-level ext (1 + n) hA λ a →
      h-level-respects-Traditional-lens-from-inhabited l a hA

-- There is a type A such that Traditional-lens A ⊤ is not
-- propositional (assuming extensionality and univalence).

¬-traditional-lens-to-⊤-propositional :
  Extensionality (# 1) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set₁) → ¬ Is-proposition (Traditional-lens A ⊤)
¬-traditional-lens-to-⊤-propositional ext univ =
  A , (
  Is-proposition (Traditional-lens A ⊤)  ↝⟨ H-level.respects-surjection (_↔_.surjection $ traditional-lens-to-⊤↔ ext) 1 ⟩
  Is-proposition ((a : A) → a ≡ a)       ↝⟨ proj₂ $ ¬-type-of-refl-propositional ext univ ⟩□
  ⊥₀                                     □)
  where
  A = _

------------------------------------------------------------------------
-- Some Iso-lens results related to h-levels

-- If the domain of an Iso-lens is inhabited and has h-level n, then
-- the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ {n a b} {A : Set a} {B : Set b} →
  Iso-lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {n} {A = A} {B} l a =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ proj₂-closure (remainder a) n ⟩□
  H-level n B        □
  where
  open Iso-lens l

-- This is not necessarily true for arbitrary domains (assuming
-- extensionality and univalence).

¬-h-level-respects-lens :
  ∀ {a b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  ¬ (∀ {n} {A : Set a} {B : Set b} →
     Iso-lens A B → H-level n A → H-level n B)
¬-h-level-respects-lens ext univ resp =
                             $⟨ ⊥-propositional ⟩
  Is-proposition ⊥           ↝⟨ resp (_↔_.from (lens-from-⊥↔⊤ ext univ) _) ⟩
  Is-proposition (↑ _ Bool)  ↝⟨ ↑⁻¹-closure 1 ⟩
  Is-proposition Bool        ↝⟨ ¬-Bool-propositional ⟩□
  ⊥₀                         □

-- In fact, there is an Iso-lens with a proposition as its domain and
-- a non-set as its codomain (assuming univalence).

lens-from-proposition-to-non-set :
  Univalence lzero →
  ∀ {a b} →
  ∃ λ (A : Set a) → ∃ λ (B : Set (lsuc lzero ⊔ b)) →
  Iso-lens A B × Is-proposition A × ¬ Is-set B
lens-from-proposition-to-non-set univ {b = b} =
  ⊥ ,
  ↑ b Set ,
  (⊥ ,
   (⊥            ↔⟨ inverse ×-left-zero ⟩□
    ⊥ × ↑ _ Set  □) ,
   ⊥-elim) ,
  ⊥-propositional ,
  ¬-Set-set univ ⊚ H-level.respects-surjection (_↔_.surjection Bij.↑↔) 2

-- Iso-lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Iso-lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited l (proj₁ c) c

-- If the domain type of an Iso-lens is contractible, then the
-- remainder type is also contractible (assuming extensionality).

domain-contractible⇒remainder-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  (l : Iso-lens A B) → Contractible A → Contractible (Iso-lens.R l)
domain-contractible⇒remainder-contractible {A = A} {B} ext l =
  Contractible A                   ↔⟨ H-level-cong ext 0 equiv ⟩
  Contractible (R × B)             ↔⟨ Contractible-commutes-with-× ext ⟩
  Contractible R × Contractible B  ↝⟨ proj₁ ⟩□
  Contractible R                   □
  where
  open Iso-lens l

-- If the domain type of an Iso-lens has h-level n, then the remainder
-- type also has h-level n (assuming extensionality and a resizing
-- function for the propositional truncation).

remainder-has-same-h-level-as-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  (l : Iso-lens A B) → ∀ n → H-level n A → H-level n (Iso-lens.R l)
remainder-has-same-h-level-as-domain ext _ l zero =
  domain-contractible⇒remainder-contractible ext l
remainder-has-same-h-level-as-domain {A = A} {B}
                                     ext resize l (suc n) h =
  [inhabited⇒+]⇒+ n λ r →
                             $⟨ h ⟩
    H-level (1 + n) A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) (1 + n) ⟩
    H-level (1 + n) (R × B)  ↝⟨ rec (Π-closure ext 1 λ _ → H-level-propositional ext (1 + n))
                                    (λ b → proj₁-closure (λ _ → b) (1 + n))
                                    (resize (inhabited r)) ⟩□
    H-level (1 + n) R        □
  where
  open Iso-lens l

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Iso-lens A B (assuming extensionality and
-- univalence).

¬-Contractible-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  ¬ ({A : Set a} {B : Set b} →
     Contractible A → Contractible (Iso-lens A B))
¬-Contractible-closed-domain ext univ closure =
                                     $⟨ ↑⊤-contractible ⟩
  Contractible (↑ _ ⊤)               ↝⟨ closure ⟩
  Contractible (Iso-lens (↑ _ ⊤) ⊥)  ↝⟨ H-level.respects-surjection
                                          (_↔_.surjection $ lens-from-contractible↔codomain-contractible
                                                              ext univ ↑⊤-contractible)
                                          0 ⟩
  Contractible (Contractible ⊥)      ↝⟨ proj₁ ⟩
  Contractible ⊥                     ↝⟨ proj₁ ⟩
  ⊥                                  ↝⟨ ⊥-elim ⟩□
  ⊥₀                                 □
  where
  ↑⊤-contractible = ↑-closure 0 ⊤-contractible

-- Contractible is closed under Iso-lens A (assuming extensionality
-- and univalence).

Contractible-closed-codomain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Contractible B → Contractible (Iso-lens A B)
Contractible-closed-codomain {A = A} {B} ext univ cB =
                               $⟨ lens-to-contractible↔⊤ ext univ cB ⟩
  Iso-lens A B ↔ ⊤             ↝⟨ _⇔_.from contractible⇔⊤↔ ⊚ inverse ⟩□
  Contractible (Iso-lens A B)  □

-- If B is a proposition, then Iso-lens A B is also a proposition
-- (assuming extensionality and univalence).

Is-proposition-closed-codomain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Is-proposition B → Is-proposition (Iso-lens A B)
Is-proposition-closed-codomain {A = A} {B} ext univ B-prop =
                                 $⟨ Π-closure (lower-extensionality _ _ ext) 1 (λ _ → B-prop) ⟩
  Is-proposition (A → B)         ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ lens-to-proposition↔get ext univ B-prop)
                                      1 ⟩□
  Is-proposition (Iso-lens A B)  □

private

  -- If A has h-level 1 + n and equivalence between certain remainder
  -- types has h-level n, then Iso-lens A B has h-level 1 + n
  -- (assuming extensionality and univalence).

  domain-1+-remainder-equivalence-0+⇒lens-1+ :
    ∀ {a b} {A : Set a} {B : Set b} →
    Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
    Univalence (lsuc (a ⊔ b)) →
    ∀ n →
    H-level (1 + n) A →
    ((l₁ l₂ : Iso-lens A B) →
       H-level n (Iso-lens.R l₁ ≃ Iso-lens.R l₂)) →
    H-level (1 + n) (Iso-lens A B)
  domain-1+-remainder-equivalence-0+⇒lens-1+
    {A = A} ext univ n hA hR l₁ l₂ =                            $⟨ Σ-closure n (hR l₁ l₂) (λ _ →
                                                                   Π-closure (lower-extensionality lzero _ ext) n λ _ →
                                                                   hA _ _) ⟩
    H-level n (∃ λ (eq : R l₁ ≃ R l₂) → ∀ p → _≡_ {A = A} _ _)  ↝⟨ H-level.respects-surjection
                                                                     (_↔_.surjection $ inverse $ equality-characterisation₄ ext univ)
                                                                     n ⟩□
    H-level n (l₁ ≡ l₂)                                         □
    where
    open Iso-lens

-- If A is a proposition, then Iso-lens A B is also a proposition
-- (assuming extensionality, univalence and a resizing function for
-- the propositional truncation).
--
-- Note that this could also be proved by going via Traditional-lens
-- (as in Is-set-closed-domain below), with slightly different
-- assumptions.

Is-proposition-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  Is-proposition A → Is-proposition (Iso-lens A B)
Is-proposition-closed-domain
  {b = b} {A} {B} ext univ resize A-prop =
                                          $⟨ R₁≃R₂ ⟩
  (∀ l₁ l₂ → R l₁ ≃ R l₂)                 ↝⟨ (λ hyp l₁ l₂ → propositional⇒inhabited⇒contractible
                                                              (Eq.left-closure ext 0 (R-prop l₁))
                                                              (hyp l₁ l₂)) ⟩
  (∀ l₁ l₂ → Contractible (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ ext univ 0 A-prop ⟩□
  Is-proposition (Iso-lens A B)           □
  where
  open Iso-lens

  R-prop : (l : Iso-lens A B) → Is-proposition (R l)
  R-prop l =
    remainder-has-same-h-level-as-domain ext resize l 1 A-prop

  remainder⁻¹ : (l : Iso-lens A B) → R l → A
  remainder⁻¹ l r =
    rec A-prop
        (λ b → _≃_.from (equiv l) (r , b))
        (with-lower-level b (inhabited l r))

  R-to-R : (l₁ l₂ : Iso-lens A B) → R l₁ → R l₂
  R-to-R l₁ l₂ = remainder l₂ ⊚ remainder⁻¹ l₁

  involutive : (l : Iso-lens A B) {f : R l → R l} → ∀ r → f r ≡ r
  involutive l _ = _⇔_.to propositional⇔irrelevant (R-prop l) _ _

  R₁≃R₂ : (l₁ l₂ : Iso-lens A B) → R l₁ ≃ R l₂
  R₁≃R₂ l₁ l₂ = Eq.↔⇒≃ $
    Bij.bijection-from-involutive-family
      R-to-R (λ l _ → involutive l) l₁ l₂

-- If A is a set, then Iso-lens A B is also a set (assuming
-- extensionality, univalence and a resizing function for the
-- propositional truncation).
--
-- TODO: Can one prove that the corresponding result does not hold for
-- codomains? Are there types A and B such that B is a set, but
-- Iso-lens A B is not?

Is-set-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (lsuc (a ⊔ b))) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  Is-set A → Is-set (Iso-lens A B)
Is-set-closed-domain {A = A} {B} ext univ resize A-set =
                                 $⟨ Traditional-lens-preserves-h-level-of-domain (lower-extensionality _ _ ext) 1 A-set ⟩
  Is-set (Traditional-lens A B)  ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ Iso-lens↔Traditional-lens ext univ resize A-set)
                                      2 ⟩□
  Is-set (Iso-lens A B)          □

-- If A has h-level n, then Iso-lens A B has h-level 1 + n (assuming
-- extensionality, univalence and a resizing function for the
-- propositional truncation).
--
-- TODO: Can this be improved? The corresponding result for
-- Traditional-lens (Traditional-lens-preserves-h-level-of-domain) is
-- stronger.

domain-0+⇒lens-1+ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
domain-0+⇒lens-1+ {A = A} {B} ext univ resize n hA =
                                                      $⟨ (λ l₁ l₂ → Eq.h-level-closure ext n (hR l₁) (hR l₂)) ⟩
  ((l₁ l₂ : Iso-lens A B) → H-level n (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ ext univ n (mono₁ n hA) ⟩□
  H-level (1 + n) (Iso-lens A B)                      □
  where
  open Iso-lens

  hR : ∀ l → H-level n (R l)
  hR l = remainder-has-same-h-level-as-domain ext resize l n hA

-- An alternative proof.

domain-0+⇒lens-1+′ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
domain-0+⇒lens-1+′ {A = A} {B} ext univ resize n hA =
                                                   $⟨ Σ-closure (1 + n)
                                                        (∃-H-level-H-level-1+ ext univ n)
                                                        (λ _ → ×-closure (1 + n)
                                                                 (Eq.left-closure ext n (mono₁ n hA))
                                                                 (Π-closure ext (1 + n) λ _ →
                                                                  mono (suc≤suc (zero≤ n)) $
                                                                  truncation-has-correct-h-level 1
                                                                    (lower-extensionality lzero _ ext))) ⟩
  H-level (1 + n)
    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥ 1 _))  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse iso) (1 + n) ⟩□

  H-level (1 + n) (Iso-lens A B)                   □
  where
  open Iso-lens

  iso =
    Iso-lens A B                                             ↝⟨ inverse $ drop-⊤-right (λ l →
                                                                  inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                    propositional⇒inhabited⇒contractible
                                                                      (H-level-propositional ext n)
                                                                      (remainder-has-same-h-level-as-domain ext resize l n hA)) ⟩
    (∃ λ (l : Iso-lens A B) → H-level n (R l))               ↝⟨ inverse Σ-assoc ⟩

    (∃ λ R → (A ≃ (R × B) × (R → ∥ B ∥ 1 _)) × H-level n R)  ↝⟨ (∃-cong λ _ → ×-comm) ⟩

    (∃ λ R → H-level n R × A ≃ (R × B) × (R → ∥ B ∥ 1 _))    ↝⟨ Σ-assoc ⟩□

    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥ 1 _))            □

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no Iso-lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∀ {a b} →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Iso-lens (Σ A B) A
no-first-projection-lens {b = b} =
  ↑ _ Bool ,
  (λ b → ↑ _ (lower b ≡ true)) ,
  λ l →                                           $⟨ singleton-contractible _ ⟩
     Contractible (Singleton true)                ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (∃ λ b → ↑ _ (lower b ≡ true))  ↝⟨ contractible-to-contractible l ⟩
     Contractible (↑ _ Bool)                      ↝⟨ H-level.respects-surjection (_↔_.surjection Bij.↑↔) 0 ⟩
     Contractible Bool                            ↝⟨ mono₁ 0 ⟩
     Is-proposition Bool                          ↝⟨ ¬-Bool-propositional ⟩□
     ⊥                                            □
  where
  surj : Singleton true ↠ ∃ λ b → ↑ _ (lower b ≡ true)
  surj = record
    { logical-equivalence = record
      { to   = λ { (b , b≡true) → lift b , lift b≡true }
      ; from = λ { (lift b , lift b≡true) → b , b≡true }
      }
    ; right-inverse-of = λ _ → refl
    }

------------------------------------------------------------------------
-- Iso-lens combinators

module Iso-lens-combinators where

  -- Identity lens (defined using extensionality).

  id : ∀ {a} {A : Set a} →
       Extensionality (lsuc a) a →
       Iso-lens A A
  id {A = A} ext =
    isomorphism-to-lens ext
      (A          ↝⟨ inverse $ drop-⊤-left-× (λ _ → Bij.↑↔) ⟩□
       ↑ _ ⊤ × A  □)

  -- Composition of lenses.
  --
  -- Note that the domains are required to be at least as large as the
  -- codomains; this should match many use-cases. Without this
  -- restriction I failed to find a satisfactory definition of
  -- composition. (I suspect that if Agda had had cumulativity, then
  -- the domain and codomain could have lived in the same universe
  -- without any problems.)

  infix 9 ⟨_,_⟩_∘_

  ⟨_,_⟩_∘_ :
    ∀ a b {c} {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Iso-lens B C → Iso-lens A B → Iso-lens A C
  ⟨_,_⟩_∘_ _ _ {A = A} {B} {C} l₁ l₂ =
    (R l₂ × R l₁) ,
    (A                  ↝⟨ equiv l₂ ⟩
     R l₂ × B           ↝⟨ F.id ×-cong equiv l₁ ⟩
     R l₂ × (R l₁ × C)  ↔⟨ ×-assoc ⟩□
     (R l₂ × R l₁) × C  □) ,
    ∥∥-map (get l₁) ⊚ inhabited l₂ ⊚ proj₁
    where
    open Iso-lens

  infixr 9 _∘_

  _∘_ :
    ∀ {a b c} {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Iso-lens B C → Iso-lens A B → Iso-lens A C
  _∘_ {a} {b} l₁ l₂ = ⟨ a , b ⟩ l₁ ∘ l₂

  -- Identity and composition form a kind of monoid (assuming
  -- extensionality and univalence).

  associativity :
    ∀ a b c {d}
      {A : Set (a ⊔ b ⊔ c ⊔ d)} {B : Set (b ⊔ c ⊔ d)}
      {C : Set (c ⊔ d)} {D : Set d} →
    Extensionality (lsuc (a ⊔ b ⊔ c ⊔ d)) (lsuc (a ⊔ b ⊔ c ⊔ d)) →
    Univalence (lsuc (a ⊔ b ⊔ c ⊔ d)) →
    (l₁ : Iso-lens C D)
    (l₂ : Iso-lens B C)
    (l₃ : Iso-lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ ext univ _ _ _ =
    _↔_.from (equality-characterisation₂ ext univ)
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl)

  left-identity :
    ∀ a {b} {A : Set (a ⊔ b)} {B : Set b} →
    (ext : Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b))) →
    let ext′ = lower-extensionality (lsuc a) _ ext in
    Univalence (lsuc (a ⊔ b)) →
    (l : Iso-lens A B) →
    ⟨ a , lzero ⟩ id ext′ ∘ l ≡ l
  left-identity a {b} {B = B} ext univ l =
    _↔_.from (equality-characterisation₂ ext univ)
      ( (R × ↑ _ ⊤ × ∥ B ∥ 1 b  ↔⟨ F.id ×-cong drop-⊤-left-× (λ _ → Bij.↑↔) ⟩
         R × ∥ B ∥ 1 b          ↔⟨ lemma ⟩□
         R                      □)
      , λ _ → refl
      )
    where
    open Iso-lens l

    lemma : R × ∥ B ∥ 1 b ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₁
          ; from = λ r → r , with-lower-level a (inhabited r)
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (r , _) →
          cong (λ x → r , x) $
            _⇔_.to propositional⇔irrelevant
              (truncation-has-correct-h-level 1
                 (lower-extensionality (lsuc a) _ ext))
              _ _ }
      }

  right-identity :
    ∀ a {b} {A : Set (a ⊔ b)} {B : Set b} →
    (ext : Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b))) →
    let ext′ = lower-extensionality lzero _ ext in
    Univalence (lsuc (a ⊔ b)) →
    (l : Iso-lens A B) →
    ⟨ lzero , a ⟩ l ∘ id ext′ ≡ l
  right-identity a {b} {A} ext univ l =
    _↔_.from (equality-characterisation₂ ext univ)
      ( ((↑ _ ⊤ × ∥ A ∥ 1 (a ⊔ b)) × R  ↔⟨ drop-⊤-left-× (λ _ → Bij.↑↔) ×-cong F.id ⟩
         ∥ A ∥ 1 (a ⊔ b) × R            ↔⟨ lemma ⟩□
         R                              □)
      , λ _ → refl
      )
    where
    open Iso-lens l

    lemma : ∥ A ∥ 1 (a ⊔ b) × R ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₂
          ; from = λ r →   ∥∥-map (λ b → _≃_.from equiv (r , b))
                                  (inhabited r)
                         , r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (_ , r) →
          cong (λ x → x , r) $
            _⇔_.to propositional⇔irrelevant
              (truncation-has-correct-h-level 1
                 (lower-extensionality lzero _ ext))
              _ _ }
      }
