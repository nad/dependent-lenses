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
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation equality-with-J
open import Preimage equality-with-J
open import Surjection equality-with-J using (_↠_; module _↠_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Lenses

record Lens {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor lens
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
  { get     = P.id
  ; set     = flip const
  ; get-set = λ _ _   → refl
  ; set-get = λ _     → refl
  ; set-set = λ _ _ _ → refl
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

                get l₁ (get l₂ (set l₂ a b))  ≡⟨ cong (get l₁) $ get-set l₂ a b ⟩
                get l₁ b                      ≡⟨ refl ⟩
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
                      set l₁ (get l₂ (set l₂ a b₁)) c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
                      set l₁ b₁                     c₂  ≡⟨ refl ⟩
                      set l₁ (set l₁ (get l₂ a) c₁) c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩
                      set l₁ (get l₂ a)             c₂  ≡⟨ refl ⟩∎
                      b₂                                ∎

                in
                set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ (set l₂ a b₁)) lemma ⟩
                set l₂ (set l₂ a b₁) b₂                                  ≡⟨ set-set l₂ a b₁ b₂ ⟩∎
                set l₂ a             b₂                                  ∎
  }
  where
  open Lens

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

-- Higher-lens is pointwise isomorphic to Iso-lens (assuming
-- extensionality and univalence).

Higher-lens↔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (lsuc (a ⊔ b))) →
  Univalence (lsuc (a ⊔ b)) →
  Higher-lens A B ↔ Iso-lens A B
Higher-lens↔Iso-lens {a} {b} {A} {B} ext univ =
  (∃ λ (g : A → B) → ∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
     ↑ _ ⊚ (g ⁻¹_) ≡ H ⊚ ∣_∣)                                             ↔⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                                Eq.extensionality-isomorphism $
                                                                                  lower-extensionality (lsuc ℓ) lzero ext) ⟩
  (∃ λ (g : A → B) → ∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
     ∀ b → ↑ _ (g ⁻¹ b) ≡ H ∣ b ∣)                                        ↔⟨ (∃-cong λ _ → Σ-cong (Pow↔Fam lzero ext univ) λ H →
                                                                                Eq.∀-preserves (lower-extensionality _ lzero ext) λ b →
                                                                                  ≡-preserves-≃ (lower-extensionality lzero _ ext) univ univ F.id (
          H ∣ b ∣                                                                   ↔⟨ ∃-intro _ _ ⟩
          (∃ λ ∥b∥ → H ∥b∥ × ∥b∥ ≡ ∣ b ∣)                                           ↔⟨ Σ-assoc ⟩□
          (∃ λ (p : ∃ H) → proj₁ p ≡ ∣ b ∣)                                         □)) ⟩

  (∃ λ (g : A → B) →
   ∃ λ (H : Fam lzero (∥ B ∥ 1 ℓ)) →
     ∀ b → ↑ _ (g ⁻¹ b) ≡ proj₂ H ⁻¹ ∣ b ∣)                               ↝⟨ ∃-cong (λ _ → inverse Σ-assoc) ⟩

  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
   ∃ λ (h : R → ∥ B ∥ 1 ℓ) →
     ∀ b → ↑ _ (g ⁻¹ b) ≡ h ⁻¹ ∣ b ∣)                                     ↔⟨ (∃-cong λ _ → ∃-cong λ R → ∃-cong λ h →
                                                                                Eq.∀-preserves (lower-extensionality _ lzero ext) λ b →
                                                                                  ≡-preserves-≃ (lower-extensionality lzero _ ext) univ univ F.id (
          (Σ R λ r → h r ≡ ∣ b ∣)                                                   ↔⟨ (∃-cong λ _ → inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                                          truncation-has-correct-h-level 1
                                                                                            (lower-extensionality lzero _ ext) _ _) ⟩
          R × ⊤                                                                     ↔⟨ ×-right-identity ⟩□
          R                                                                         □)) ⟩

  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∀ b → ↑ _ (g ⁻¹ b) ≡ R))                                            ↔⟨ (∃-cong λ _ → ∃-cong λ _ → F.id ×-cong
                                                                                Eq.∀-preserves (lower-extensionality _ lzero ext) λ _ →
                                                                                  ≡≃≃ univ) ⟩
  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∀ b → ↑ _ (g ⁻¹ b) ≃ R))                                            ↔⟨ (∃-cong λ _ → ∃-cong λ _ → F.id ×-cong
                                                                                Eq.∀-preserves (lower-extensionality _ _ ext) λ _ →
                                                                                  Eq.≃-preserves (lower-extensionality lzero _ ext)
                                                                                    (Eq.↔⇒≃ Bij.↑↔) F.id) ⟩
  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∀ b → g ⁻¹ b ≃ R))                                                  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → F.id ×-cong
                                                                                Eq.∀-preserves (lower-extensionality _ _ ext) λ _ →
                                                                                  Eq.↔⇒≃ Eq.≃-as-Σ) ⟩
  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∀ b → ∃ λ (f : g ⁻¹ b → R) → Eq.Is-equivalence f))                  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → F.id ×-cong ΠΣ-comm) ⟩

  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (f : (b : B) → g ⁻¹ b → R) →
      ∀ b → Eq.Is-equivalence (f b)))                                     ↔⟨ (∃-cong λ g → ∃-cong λ R → F.id ×-cong
                                                                                Σ-cong (
          ((b : B) → (∃ λ (a : A) → g a ≡ b) → R)                                 ↔⟨ Eq.∀-preserves (lower-extensionality _ _ ext) (λ _ →
                                                                                       Eq.↔⇒≃ currying) ⟩
          ((b : B) → (a : A) → g a ≡ b → R)                                       ↝⟨ Π-comm ⟩
          ((a : A) → (b : B) → g a ≡ b → R)                                       ↔⟨ Eq.∀-preserves (lower-extensionality _ _ ext) (λ _ →
                                                                                       inverse $ Eq.↔⇒≃ currying) ⟩
          ((a : A) → (∃ λ (b : B) → g a ≡ b) → R)                                 ↔⟨ Eq.∀-preserves (lower-extensionality _ _ ext) (λ _ →
                                                                                       →-cong (lower-extensionality _ _ ext)
                                                                                         (Eq.↔⇒≃ $ inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                                            other-singleton-contractible _)
                                                                                         F.id) ⟩
          (A → ⊤ → R)                                                             ↔⟨ Eq.∀-preserves (lower-extensionality _ _ ext) (λ _ →
                                                                                       Eq.↔⇒≃ Π-left-identity) ⟩□
          (A → R)                                                                 □)
                                                                                  (λ f → Eq.∀-preserves (lower-extensionality _ _ ext) λ b →
          Eq.Is-equivalence (f b)                                                    ↝⟨ Eq.Is-equivalence-preserves
                                                                                          (lower-extensionality lzero _ ext) (uncurry λ a →
                                                                                            elim¹
                                                                                              (λ {b} ga≡b → f b (a , ga≡b) ≡ f (g a) (a , refl))
                                                                                              refl) ⟩
          Eq.Is-equivalence (λ { (a , _) → f (g a) (a , refl) })                     □)) ⟩

  (∃ λ (g : A → B) →
   ∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (f : A → R) →
      ∀ b → Eq.Is-equivalence {A = g ⁻¹ b} (f ⊚ proj₁)))                  ↝⟨ ∃-comm ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
   ∃ λ (g : A → B) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (f : A → R) →
      ∀ b → Eq.Is-equivalence {A = g ⁻¹ b} (f ⊚ proj₁)))                  ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (g : A → B) →
        ∃ λ (f : A → R) →
        ∀ b → Eq.Is-equivalence {A = g ⁻¹ b} (f ⊚ proj₁)))                ↝⟨ (∃-cong λ _ → F.id ×-cong Σ-assoc) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (gf : (A → B) × (A → R)) →
        ∀ b → Eq.Is-equivalence {A = proj₁ gf ⁻¹ b} (proj₂ gf ⊚ proj₁)))  ↝⟨ (∃-cong λ _ → F.id ×-cong Σ-cong (inverse ΠΣ-comm) λ _ → F.id) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (f : A → B × R) →
      ∀ b → Eq.Is-equivalence {A = proj₁ ⊚ f ⁻¹ b} (proj₂ ⊚ f ⊚ proj₁)))  ↔⟨ (∃-cong λ _ → F.id ×-cong ∃-cong λ f →
                                                                                _↠_.from
                                                                                  (Eq.≃↠⇔ (Π-closure (lower-extensionality _ _ ext) 1 λ _ →
                                                                                             Eq.propositional (lower-extensionality lzero _ ext) _)
                                                                                          (Eq.propositional (lower-extensionality lzero _ ext) _))
                                                                                  (record { to = lemma₁ f; from = lemma₂ f })) ⟩
  (∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (∃ λ (f : A → B × R) → Eq.Is-equivalence f))                         ↝⟨ (∃-cong λ _ → F.id ×-cong inverse Eq.≃-as-Σ) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
     (R → ∥ B ∥ 1 ℓ) ×
     (A ≃ (B × R)))                                                       ↝⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
     (A ≃ (B × R)) ×
     (R → ∥ B ∥ 1 ℓ))                                                     ↔⟨ (∃-cong λ _ → Eq.≃-preserves (lower-extensionality lzero _ ext)
                                                                                                          F.id
                                                                                                          (Eq.↔⇒≃ ×-comm)
                                                                                             ×-cong
                                                                                           F.id) ⟩□
  (∃ λ (R : Set (lsuc ℓ)) →
     (A ≃ (R × B)) ×
     (R → ∥ B ∥ 1 ℓ))                                                     □

  where
  ℓ = a ⊔ b

  lemma₁ : {R : Set (lsuc ℓ)} (f : A → B × R) →
           (∀ b → Eq.Is-equivalence
                    {A = proj₁ ⊚ f ⁻¹ b} (proj₂ ⊚ f ⊚ proj₁)) →
           Eq.Is-equivalence f
  lemma₁ f eq′ = _≃_.is-equivalence $ Eq.↔⇒≃ $ record
    { surjection = record
      { logical-equivalence = record
        { from = λ { (b , r) → proj₁ (_≃_.from (eq b) r) }
        }
      ; right-inverse-of = λ { (b , r) →
          curry (_↔_.to ≡×≡↔≡)
            (proj₁ (f (proj₁ (_≃_.from (eq b) r)))  ≡⟨ proj₂ (_≃_.from (eq b) r) ⟩∎
             b                                      ∎)
            (proj₂ (f (proj₁ (_≃_.from (eq b) r)))  ≡⟨ _≃_.right-inverse-of (eq b) r ⟩∎
             r                                      ∎) }
      }
    ; left-inverse-of = λ a →
        proj₁ (uncurry (_≃_.from ⊚ eq) (f a))  ≡⟨ cong proj₁ $ _≃_.left-inverse-of (eq (proj₁ (f a))) (a , refl) ⟩∎
        a                                      ∎
    }
    where
    eq = λ b → Eq.⟨ _ , eq′ b ⟩

  lemma₂ : {R : Set (lsuc ℓ)} (f : A → B × R) →
           Eq.Is-equivalence f →
           ∀ b → Eq.Is-equivalence
                   {A = proj₁ ⊚ f ⁻¹ b} (proj₂ ⊚ f ⊚ proj₁)
  lemma₂ f eq′ b = _≃_.is-equivalence $ Eq.↔⇒≃ $ record
    { surjection = record
      { logical-equivalence = record
        { from = λ r →
              _≃_.from eq (b , r)
            , (proj₁ (f (_≃_.from eq (b , r)))  ≡⟨ cong proj₁ (_≃_.right-inverse-of eq (b , r)) ⟩∎
               b                                ∎)
        }
      ; right-inverse-of = λ r →
          proj₂ (f (_≃_.from eq (b , r)))  ≡⟨ cong proj₂ (_≃_.right-inverse-of eq (b , r)) ⟩∎
          r                                ∎
      }
    ; left-inverse-of = λ { (a , ≡b) →
        elim¹ (λ {b} ≡b →
                 ( _≃_.from eq (b , proj₂ (f a))
                 , cong proj₁
                     (_≃_.right-inverse-of eq (b , proj₂ (f a)))
                 ) ≡
                 (a , ≡b))

              (Σ-≡,≡→≡

                 (_≃_.from eq (f a)  ≡⟨ _≃_.left-inverse-of eq a ⟩∎
                  a                  ∎)

                 (subst (λ a′ → proj₁ (f a′) ≡ proj₁ (f a))
                        (_≃_.left-inverse-of eq a)
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ subst-∘ (_≡ proj₁ (f a)) (proj₁ ⊚ f) (_≃_.left-inverse-of eq a) ⟩

                  subst (λ a′ → a′ ≡ proj₁ (f a))
                        (cong (proj₁ ⊚ f) (_≃_.left-inverse-of eq a))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ cong (λ p → subst (λ a′ → a′ ≡ proj₁ (f a))
                                                                                               p
                                                                                               (cong proj₁ (_≃_.right-inverse-of eq (f a)))) $
                                                                               sym $ cong-∘ proj₁ f (_≃_.left-inverse-of eq a) ⟩
                  subst (λ a′ → a′ ≡ proj₁ (f a))
                        (cong proj₁ (cong f (_≃_.left-inverse-of eq a)))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ cong (λ p → subst (λ a′ → a′ ≡ proj₁ (f a))
                                                                                               (cong proj₁ p)
                                                                                               (cong proj₁ (_≃_.right-inverse-of eq (f a)))) $
                                                                               _≃_.left-right-lemma eq _ ⟩
                  subst (λ a′ → a′ ≡ proj₁ (f a))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ cong (λ p → subst (λ a′ → a′ ≡ proj₁ (f a))
                                                                                               p
                                                                                               (cong proj₁ (_≃_.right-inverse-of eq (f a)))) $
                                                                                sym $ sym-sym (cong proj₁ (_≃_.right-inverse-of eq (f a))) ⟩
                  subst (λ a′ → a′ ≡ proj₁ (f a))
                        (sym $ sym $
                           cong proj₁ (_≃_.right-inverse-of eq (f a)))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ subst-trans (sym $ cong proj₁ (_≃_.right-inverse-of eq (f a))) ⟩

                  trans (sym $
                           cong proj₁ (_≃_.right-inverse-of eq (f a)))
                        (cong proj₁ (_≃_.right-inverse-of eq (f a)))      ≡⟨ trans-symˡ (cong proj₁ (_≃_.right-inverse-of eq (f a))) ⟩∎

                  refl                                                    ∎))

              ≡b }
    }
    where
    eq = Eq.⟨ _ , eq′ ⟩

-- If the domain is a set, then Lens and Iso-lens are pointwise
-- logically equivalent (assuming extensionality).

Lens⇔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  Is-set A →
  Lens A B ⇔ Iso-lens A B
Lens⇔Iso-lens {a} {b} {A} {B} ext A-set = record
  { to   = to
  ; from = from
  }
  where
  open Lens

  ext′ = lower-extensionality _ b ext

  to : Lens A B → Iso-lens A B
  to l =
    (∥ B ∥ 1 (a ⊔ b) ×
     ∃ λ (f : B → A) → ∀ b b′ → set l (f b) b′ ≡ f b′) ,
    Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = λ a → (∣ get l a ∣ , set l a , set-set l a) , get l a
          ; from = λ { ((_ , f , _) , b) → set l (f b) b }
          }
        ; right-inverse-of = λ { ((∥b∥ , f , h) , b) →

           let irr = {p q : ∀ b b′ → set l (f b) b′ ≡ f b′} → p ≡ q
               irr =
                 _⇔_.to propositional⇔irrelevant
                   (Π-closure (lower-extensionality _ lzero ext) 1 λ _ →
                    Π-closure ext′                               1 λ _ →
                    A-set _ _)
                   _ _

               lemma =
                  set l (set l (f b) b)  ≡⟨ ext′ (set-set l (f b) b) ⟩
                  set l (f b)            ≡⟨ ext′ (h b) ⟩∎
                  f                      ∎
           in
           ( ( ∣ get l (set l (f b) b) ∣
             , set l (set l (f b) b) , set-set l (set l (f b) b)
             )
           , get l (set l (f b) b)
           )                                                      ≡⟨ cong₂ _,_ (cong₂ _,_ (_⇔_.to propositional⇔irrelevant
                                                                                             (truncation-has-correct-h-level 1 ext) _ _)
                                                                                          (Σ-≡,≡→≡ lemma irr))
                                                                               (get-set l _ _) ⟩∎
           ((∥b∥ , f , h) , b)                                    ∎ }
        }
      ; left-inverse-of = λ a →
          set l (set l a (get l a)) (get l a)  ≡⟨ cong (λ x → set l x (get l a)) (set-get l a) ⟩
          set l a (get l a)                    ≡⟨ set-get l a ⟩∎
          a                                    ∎
      }) ,
    proj₁

  from : Iso-lens A B → Lens A B
  from (_ , l , _) = record
    { get     = λ a   →             proj₂ (_≃_.to l a)
    ; set     = λ a b → _≃_.from l (proj₁ (_≃_.to l a) , b)
    ; get-set = λ a b →

        proj₂ (_≃_.to l (_≃_.from l (proj₁ (_≃_.to l a) , b)))  ≡⟨ cong proj₂ (_≃_.right-inverse-of l _) ⟩∎
        proj₂ (proj₁ (_≃_.to l a) , b)                          ∎

    ; set-get = λ a →

        _≃_.from l (_≃_.to l a)  ≡⟨ _≃_.left-inverse-of l _ ⟩∎
        a                        ∎

    ; set-set = λ a b₁ b₂ →
        let r = proj₁ (_≃_.to l a) in

        _≃_.from l (proj₁ (_≃_.to l (_≃_.from l (r , b₁))) , b₂)  ≡⟨ cong (λ x → _≃_.from l (proj₁ x , b₂)) (_≃_.right-inverse-of l _) ⟩∎
        _≃_.from l (r , b₂)                                       ∎
    }

-- If the domain is a set, then Lens and Iso-lens are pointwise
-- isomorphic (assuming extensionality, univalence and a resizing
-- function for the propositional truncation).

Lens↔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (lsuc (a ⊔ b))) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  Is-set A →
  Lens A B ↔ Iso-lens A B
Lens↔Iso-lens {a} {b} {A} {B} ext univ resize A-set = record
  { surjection = record
    { logical-equivalence = equiv
    ; right-inverse-of    = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  equiv = Lens⇔Iso-lens (lower-extensionality _ _ ext) A-set

  open Lens
  open _⇔_ equiv

  from∘to : ∀ l → from (to l) ≡ l
  from∘to l = lemma (λ a b → set-set l a b b)
    where
    lens-cong :
      ∀ {s₁ gs₁ sg₁ ss₁ s₂ gs₂ sg₂ ss₂}
      (eq : s₁ ≡ s₂) →
      subst (λ set → ∀ a b → get l (set a b) ≡ b) eq gs₁ ≡ gs₂ →
      subst (λ set → ∀ a → set a (get l a) ≡ a) eq sg₁ ≡ sg₂ →
      subst (λ set → ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) eq ss₁ ≡
        ss₂ →
      lens (get l) s₁ gs₁ sg₁ ss₁ ≡ lens (get l) s₂ gs₂ sg₂ ss₂
    lens-cong refl refl refl refl = refl

    B-set : A → Is-set B
    B-set a =
      proj₂-closure (proj₁ $ _≃_.to eq a) 2 $
      respects-surjection (_≃_.surjection eq) 2 A-set
      where
      eq = proj₁ $ proj₂ $ to l

    lemma : ∀ {s₁ gs₁ sg₁ ss₁ s₂ gs₂ sg₂ ss₂}
            (eq : ∀ a b → s₁ a b ≡ s₂ a b) →
            lens (get l) s₁ gs₁ sg₁ ss₁ ≡ lens (get l) s₂ gs₂ sg₂ ss₂
    lemma eq = lens-cong
      (lower-extensionality _ _ ext λ _ →
       lower-extensionality _ _ ext λ _ →
       eq _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality _ _ ext) 1 λ a →
          Π-closure (lower-extensionality _ _ ext) 1 λ _ →
          B-set a _ _)
         _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality _ _ ext)  1 λ _ →
          A-set _ _)
         _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality _ _ ext) 1 λ _ →
          Π-closure (lower-extensionality _ _ ext) 1 λ _ →
          Π-closure (lower-extensionality _ _ ext) 1 λ _ →
          A-set _ _)
         _ _)

  to∘from : ∀ l → to (from l) ≡ l
  to∘from (R , l , inh) =
    Σ-≡,≡→≡
      (≃⇒≡ univ lemma₁)
      (curry (_↔_.to ≡×≡↔≡)
         (Eq.lift-equality-inverse (lower-extensionality _ (lsuc ℓ) ext)
            (lower-extensionality _ _ ext lemma₂))
         (_⇔_.to propositional⇔irrelevant
            (Π-closure (lower-extensionality _ (lsuc ℓ) ext) 1 λ _ →
             truncation-has-correct-h-level 1
               (lower-extensionality _ _ ext))
            _ _))
    where
    ℓ = a ⊔ b

    B-set : (B → R) → ∥ B ∥ 1 b → Is-set B
    B-set f =
      rec (H-level-propositional (lower-extensionality _ _ ext) 2)
          (λ b → proj₂-closure (f b) 2 $
                 respects-surjection (_≃_.surjection l) 2 A-set)

    R-set : ∥ B ∥ 1 (lsuc ℓ) → Is-set R
    R-set =
      rec (H-level-propositional
             (lower-extensionality _ (lsuc ℓ) ext)
             2)
          (λ b → proj₁-closure (const b) 2 $
                 respects-surjection (_≃_.surjection l) 2 A-set)

    lemma₁′ : (∥ B ∥ 1 ℓ × (∥ B ∥ 1 (lsuc ℓ) → R)) ↔ R
    lemma₁′ = record
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

    lemma₁ =
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
       (∃ λ (g : B → B) → F.id ≡ g))                              ↔⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                        inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                        other-singleton-contractible _) ⟩
      (∥ B ∥ 1 ℓ ×
       (∃ λ (f : B → R) → Constant f) ×
       ⊤)                                                         ↔⟨ (∃-cong λ _ → ×-right-identity) ⟩

      (∥ B ∥ 1 ℓ × ∃ λ (f : B → R) → Constant f)                  ↝⟨ (∃-cong λ ∥b∥ → constant-function≃∥inhabited∥⇒inhabited
                                                                                       lzero ext (R-set (resize ∥b∥))) ⟩
      (∥ B ∥ 1 ℓ × (∥ B ∥ 1 (lsuc ℓ) → R))                        ↔⟨ lemma₁′ ⟩

      R                                                           □

    resp : ∀ {X Y} → X ≃ Y → A ≃ (X × B) → A ≃ (Y × B)
    resp {X} {Y} X≃Y A≃X×B =
      A      ↝⟨ A≃X×B ⟩
      X × B  ↝⟨ X≃Y ×-cong F.id ⟩□
      Y × B  □

    lemma₂ = λ p →
      _≃_.from (proj₁ (subst (λ R → A ≃ (R × B) × (R → ∥ B ∥ 1 ℓ))
                             (≃⇒≡ univ lemma₁)
                             (proj₂ (to (from (R , l , inh)))))) p        ≡⟨ cong (λ eq → _≃_.from (proj₁ eq) p)
                                                                                  (push-subst-, {y≡z = ≃⇒≡ univ lemma₁} _ _) ⟩
      _≃_.from (subst (λ R → A ≃ (R × B)) (≃⇒≡ univ lemma₁)
                      (proj₁ (proj₂ (to (from (R , l , inh)))))) p        ≡⟨ sym $ cong (λ eq → _≃_.from eq p) $
                                                                               transport-theorem
                                                                                 (λ R → A ≃ (R × B)) resp
                                                                                 (λ _ → Eq.lift-equality
                                                                                          (lower-extensionality _ (lsuc ℓ) ext)
                                                                                          refl)
                                                                                 univ _ _ ⟩
      _≃_.from (resp lemma₁ (proj₁ (proj₂ (to (from (R , l , inh)))))) p  ≡⟨⟩

      _≃_.from l (proj₁ (_≃_.to l (_≃_.from l p)) , proj₂ p)              ≡⟨ cong (λ p′ → _≃_.from l (proj₁ p′ , proj₂ p))
                                                                                  (_≃_.right-inverse-of l _) ⟩∎
      _≃_.from l p                                                        ∎

------------------------------------------------------------------------
-- Some existence results

-- Iso-lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Iso-lens A B → Contractible A → Contractible B
contractible-to-contractible {A = A} {B} l c =
                              $⟨ c ⟩
  Contractible A              ↝⟨ respects-surjection (_≃_.surjection eq) 0 ⟩
  Contractible (proj₁ l × B)  ↝⟨ proj₂-closure (proj₁ $ _≃_.to eq (proj₁ c)) 0 ⟩□
  Contractible B              □
  where
  eq = proj₁ $ proj₂ l

-- There is an Iso-lens with a proposition as its domain and a non-set
-- as its codomain (assuming univalence).

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
  ¬-Set-set univ ⊚ respects-surjection (_↔_.surjection Bij.↑↔) 2

-- There is, in general, no Iso-lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∀ {a b} →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Iso-lens (Σ A B) A
no-first-projection-lens =
  ↑ _ Bool ,
  (λ b → ↑ _ (lower b ≡ true)) ,
  λ l →                                           $⟨ singleton-contractible _ ⟩
     Contractible (Singleton true)                ↝⟨ respects-surjection surj 0 ⟩
     Contractible (∃ λ b → ↑ _ (lower b ≡ true))  ↝⟨ contractible-to-contractible l ⟩
     Contractible (↑ _ Bool)                      ↝⟨ respects-surjection (_↔_.surjection Bij.↑↔) 0 ⟩
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
