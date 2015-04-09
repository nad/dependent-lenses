------------------------------------------------------------------------
-- Non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lens.Non-dependent where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_; module _≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
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
-- Alternative formulation of lenses

-- TODO: Find a definition which works (is isomorphic to the other
-- one, under certain assumptions) when B is empty.

Iso-lens : ∀ {a b} → Set a → Set b → Set (lsuc (a ⊔ b))
Iso-lens {a} {b} A B = ∃ λ (R : Set (a ⊔ b)) → A ≃ (R × B)

-- If the domain is a set, then Lens and Iso-lens are logically
-- equivalent (assuming extensionality).

logically-equivalent :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality b (a ⊔ b) →
  Is-set A →
  Lens A B ⇔ Iso-lens A B
logically-equivalent {b = b} {A} {B} ext A-set = record
  { to   = to
  ; from = from
  }
  where
  open Lens

  ext′ = lower-extensionality lzero b ext

  to : Lens A B → Iso-lens A B
  to l =
    (∃ λ (f : B → A) → ∀ b b′ → set l (f b) b′ ≡ f b′) ,
    Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = λ a → (set l a , set-set l a) , get l a
          ; from = λ { ((f , _) , b) → set l (f b) b }
          }
        ; right-inverse-of = λ { ((f , h) , b) →

           let irr = {p q : ∀ b b′ → set l (f b) b′ ≡ f b′} → p ≡ q
               irr =
                 _⇔_.to propositional⇔irrelevant
                   (Π-closure ext  1 λ _ →
                    Π-closure ext′ 1 λ _ →
                    A-set _ _)
                   _ _

               lemma =
                  set l (set l (f b) b)  ≡⟨ ext′ (set-set l (f b) b) ⟩
                  set l (f b)            ≡⟨ ext′ (h b) ⟩∎
                  f                      ∎
           in
           ((set l (set l (f b) b) , set-set l (set l (f b) b)) , get l (set l (f b) b))  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma irr) (get-set l _ _) ⟩∎
           ((f                     , h)                         , b)                      ∎ }
        }
      ; left-inverse-of = λ a →
          set l (set l a (get l a)) (get l a)  ≡⟨ cong (λ x → set l x (get l a)) (set-get l a) ⟩
          set l a (get l a)                    ≡⟨ set-get l a ⟩∎
          a                                    ∎
      })

  from : Iso-lens A B → Lens A B
  from (R , l) = record
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

-- If the domain and codomain are sets, and B is non-empty, then Lens
-- and Iso-lens are isomorphic (assuming extensionality and
-- univalence).

isomorphic : ∀ {a b} {A : Set a} {B : Set b} →
             Extensionality (a ⊔ b) (a ⊔ b) →
             Univalence (a ⊔ b) →
             Is-set A → Is-set B → B →
             Lens A B ↔ Iso-lens A B
isomorphic {a} {b} {A} {B} ext univ A-set B-set witness = record
  { surjection = record
    { logical-equivalence = equiv
    ; right-inverse-of    = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  equiv = logically-equivalent (lower-extensionality a lzero ext) A-set

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

    lemma : ∀ {s₁ gs₁ sg₁ ss₁ s₂ gs₂ sg₂ ss₂}
            (eq : ∀ a b → s₁ a b ≡ s₂ a b) →
            lens (get l) s₁ gs₁ sg₁ ss₁ ≡ lens (get l) s₂ gs₂ sg₂ ss₂
    lemma eq = lens-cong
      (lower-extensionality b lzero ext λ _ →
       lower-extensionality a b     ext λ _ →
       eq _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality b a ext) 1 λ _ →
          Π-closure (lower-extensionality a a ext) 1 λ _ →
          B-set _ _)
         _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality b b ext)  1 λ _ →
          A-set _ _)
         _ _)
      (_⇔_.to propositional⇔irrelevant
         (Π-closure (lower-extensionality b lzero ext) 1 λ _ →
          Π-closure (lower-extensionality a lzero ext) 1 λ _ →
          Π-closure (lower-extensionality a b     ext) 1 λ _ →
          A-set _ _)
         _ _)

  to∘from : ∀ l → to (from l) ≡ l
  to∘from (R , l) =
    Σ-≡,≡→≡
      (≃⇒≡ univ lemma₁)
      (Eq.lift-equality ext (lower-extensionality b lzero ext lemma₂))
    where
    -- Note the use of witness in lemma₀.
    lemma₀ :
      (∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′) ↔ R
    lemma₀ = record
      { surjection = record
        { logical-equivalence = record
          { to   = λ { (f , _) → proj₁ (f witness) }
          ; from = λ r → (r ,_) , λ _ _ → refl
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (f , h) → Σ-≡,≡→≡
          ((proj₁ (f witness) ,_)  ≡⟨ lower-extensionality a lzero ext (h witness) ⟩∎
           f                       ∎)
          (_⇔_.to propositional⇔irrelevant
             (Π-closure (lower-extensionality a lzero ext) 1 λ _ →
              Π-closure (lower-extensionality a lzero ext) 1 λ _ →
              respects-surjection (_≃_.surjection l) 2 A-set _ _)
             _ _) }
      }

    lemma₁ : (∃ λ (f : B → A) → ∀ b b′ →
                _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′) ≃
             R
    lemma₁ =
      (∃ λ (f : B → A) → ∀ b b′ →
           _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′)       ↝⟨ Σ-cong (→-cong (lower-extensionality a lzero ext) F.id l) (λ _ →
                                                                            Eq.Π-preserves (lower-extensionality a lzero ext) F.id λ _ →
                                                                            Eq.Π-preserves (lower-extensionality a b     ext) F.id λ _ →
                                                                            ≡⇒↝ _ (cong (_≃_.from l _ ≡_)
                                                                                        (sym $ _≃_.left-inverse-of l _))) ⟩
      (∃ λ (f : B → R × B) → ∀ b b′ →
           _≃_.from l (proj₁ (f b) , b′) ≡ _≃_.from l (f b′))     ↝⟨ ∃-cong (λ _ →
                                                                       Eq.Π-preserves (lower-extensionality a lzero ext) F.id λ _ →
                                                                       Eq.Π-preserves (lower-extensionality a b     ext) F.id λ _ →
                                                                       Eq.≃-≡ (inverse l)) ⟩
      (∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)  ↔⟨ lemma₀ ⟩□

      R                                                           □

    resp : ∀ {X Y} → X ≃ Y → A ≃ (X × B) → A ≃ (Y × B)
    resp {X} {Y} X≃Y A≃X×B =
      A      ↝⟨ A≃X×B ⟩
      X × B  ↝⟨ X≃Y ×-cong F.id ⟩□
      Y × B  □

    lemma₂ :
      ∀ a →
      _≃_.to (subst (λ R → A ≃ (R × B))
                    (≃⇒≡ univ lemma₁)
                    (proj₂ (to (from (R , l))))) a ≡
      _≃_.to l a
    lemma₂ a =
      _≃_.to (subst (λ R → A ≃ (R × B)) (≃⇒≡ univ lemma₁)
                    (proj₂ (to (from (R , l))))) a                     ≡⟨ sym $ cong (λ eq → _≃_.to eq a) $
                                                                            transport-theorem (λ R → A ≃ (R × B)) resp
                                                                                              (λ _ → Eq.lift-equality ext refl)
                                                                                              univ _ _ ⟩
      _≃_.to (resp lemma₁ (proj₂ (to (from (R , l))))) a               ≡⟨⟩

      (proj₁ (_≃_.to l (_≃_.from l (proj₁ (_≃_.to l a) , witness))) ,
       proj₂ (_≃_.to l a))                                             ≡⟨ cong (λ x → proj₁ x , proj₂ (_≃_.to l a))
                                                                               (_≃_.right-inverse-of l _) ⟩
      (proj₁ (proj₁ (_≃_.to l a) , witness) , proj₂ (_≃_.to l a))      ≡⟨ refl ⟩∎

      _≃_.to l a                                                       ∎
