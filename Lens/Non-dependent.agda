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

record Traditional-lens
         {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor traditional-lens
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
-- Traditional lens combinators

module Traditional-lens-combinators where

  -- Identity lens.

  id : ∀ {a} {A : Set a} → Traditional-lens A A
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
        Traditional-lens B C → Traditional-lens A B →
        Traditional-lens A C
  l₁ ∘ l₂ = record
    { get     = get l₁ ⊚ get l₂
    ; set     = λ a c → let b = set l₁ (get l₂ a) c in
                        set l₂ a b
    ; get-set = λ a c → let b = set l₁ (get l₂ a) c in

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
                        set l₁ (get l₂ (set l₂ a b₁)) c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
                        set l₁ b₁                     c₂  ≡⟨⟩
                        set l₁ (set l₁ (get l₂ a) c₁) c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩∎
                        set l₁ (get l₂ a)             c₂  ∎

                  in
                  set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ (set l₂ a b₁)) lemma ⟩
                  set l₂ (set l₂ a b₁) b₂                                  ≡⟨ set-set l₂ a b₁ b₂ ⟩∎
                  set l₂ a             b₂                                  ∎
    }
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

equality-characterisation₁ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₁ {A = A} {B} {l₁} {l₂} ext =
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

private

  -- Equality of Iso-lenses is isomorphic to certain pairs (assuming
  -- extensionality and univalence).

  equality-characterisation₀ :
    ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
    let open Iso-lens in
    Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
    Univalence (lsuc (a ⊔ b)) →
    l₁ ≡ l₂
      ↔
    ∃ λ (eq : R l₁ ≃ R l₂) →
      (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂
  equality-characterisation₀ {A = A} {B} {l₁} {l₂} ext univ =
    l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₁ ext ⟩

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
  l₁ ≡ l₂                                             ↝⟨ equality-characterisation₀ ext univ ⟩

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
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₀ ext univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)                      ↝⟨ (∃-cong λ _ → inverse $ ≃-from-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃_.from (equiv l₂) p)                                   □
  where
  open Iso-lens

------------------------------------------------------------------------
-- Isomorphisms between different kinds of lenses

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
                                                                       inverse (_⇔_.to contractible⇔⊤↔ (singleton-contractible _))
                                                                         ×-cong
                                                                       F.id) ⟩
  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) →
   ⊤ ×
   A ≃ ∃ (H ⊚ ∣_∣))                                                ↝⟨ (∃-cong λ _ → ×-left-identity) ⟩

  (∃ λ (H : Pow lzero (∥ B ∥ 1 ℓ)) → A ≃ ∃ (H ⊚ ∣_∣))              ↔⟨ inverse $
                                                                      Σ-cong (inverse $ Pow↔Fam lzero ext univ) (λ _ →
                                                                      Eq.≃-preserves (lower-extensionality (lsuc ℓ) _ ext) F.id F.id) ⟩

  (∃ λ (H : Fam lzero (∥ B ∥ 1 ℓ)) → A ≃ ∃ ((proj₂ H ⁻¹_) ⊚ ∣_∣))  ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set (lsuc ℓ)) →
   ∃ λ (f : R → ∥ B ∥ 1 ℓ) → A ≃ ∃ ((f ⁻¹_) ⊚ ∣_∣))                ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                                       Eq.≃-preserves (lower-extensionality (lsuc ℓ) _ ext) F.id
                                (∃ ((f ⁻¹_) ⊚ ∣_∣)                       ↔⟨ (∃-cong λ b → ∃-cong λ r →
                                                                               inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                                 truncation-has-correct-h-level 1
                                                                                   (lower-extensionality (lsuc ℓ) _ ext) _ _) ⟩
                                 B × R × ⊤                               ↔⟨ (∃-cong λ _ → ×-right-identity) ⟩
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

-- If the domain A is a set, then Traditional-lens A B and
-- Iso-lens A B are logically equivalent (assuming extensionality).

Traditional-lens⇔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  Is-set A →
  Traditional-lens A B ⇔ Iso-lens A B
Traditional-lens⇔Iso-lens {b = b} {A} {B} ext A-set = record
  { to   = to
  ; from = from
  }
  where

  ext′ = lower-extensionality _ b ext

  from : Iso-lens A B → Traditional-lens A B
  from l = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }
    where
    open Iso-lens l

  to : Traditional-lens A B → Iso-lens A B
  to l = isomorphism-to-lens′
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
                   Π-closure ext′                               1 λ _ →
                   A-set _ _)
                  _ _

              lemma =
                get (f b)          ≡⟨ cong get (sym (h b b)) ⟩
                get (set (f b) b)  ≡⟨ get-set (f b) b ⟩∎
                b                  ∎
            in
            (set (f b) , set-set (f b)) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ (ext′ (h b)) irr) lemma ⟩∎
            (f         , h            ) , b          ∎ }
         }
       ; left-inverse-of = λ a →
           set a (get a)  ≡⟨ set-get a ⟩∎
           a              ∎
       })
    where
    open Traditional-lens l

-- If the domain A is a set, then Traditional-lens A B and
-- Iso-lens A B are isomorphic (assuming extensionality, univalence
-- and a resizing function for the propositional truncation).

Traditional-lens↔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (lsuc (a ⊔ b))) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 (a ⊔ b) → ∥ B ∥ 1 (lsuc (a ⊔ b))) →
  Is-set A →
  Traditional-lens A B ↔ Iso-lens A B
Traditional-lens↔Iso-lens {a} {b} {A} {B} ext univ resize A-set = record
  { surjection = record
    { logical-equivalence = equiv
    ; right-inverse-of    = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  equiv = Traditional-lens⇔Iso-lens (lower-extensionality _ _ ext) A-set

  open Traditional-lens
  open _⇔_ equiv

  from∘to : ∀ l → from (to l) ≡ l
  from∘to l = lens-cong
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
    where
    lens-cong :
      ∀ {gs₁ sg₁ ss₁ gs₂ sg₂ ss₂} →
      gs₁ ≡ gs₂ → sg₁ ≡ sg₂ → ss₁ ≡ ss₂ →
      traditional-lens (get l) (set l) gs₁ sg₁ ss₁ ≡
      traditional-lens (get l) (set l) gs₂ sg₂ ss₂
    lens-cong refl refl refl = refl

    B-set : A → Is-set B
    B-set a =
      proj₂-closure (proj₁ $ _≃_.to eq a) 2 $
      H-level.respects-surjection (_≃_.surjection eq) 2 A-set
      where
      eq = proj₁ $ proj₂ $ to l

  to∘from : ∀ l → to (from l) ≡ l
  to∘from (R , l , inh) =
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
       (∃ λ (g : B → B) → F.id ≡ g))                              ↔⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                        inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                        other-singleton-contractible _) ⟩
      (∥ B ∥ 1 ℓ ×
       (∃ λ (f : B → R) → Constant f) ×
       ⊤)                                                         ↔⟨ (∃-cong λ _ → ×-right-identity) ⟩

      (∥ B ∥ 1 ℓ × ∃ λ (f : B → R) → Constant f)                  ↝⟨ (∃-cong λ ∥b∥ → constant-function≃∥inhabited∥⇒inhabited
                                                                                       lzero ext (R-set (resize ∥b∥))) ⟩
      (∥ B ∥ 1 ℓ × (∥ B ∥ 1 (lsuc ℓ) → R))                        ↔⟨ lemma′ ⟩

      R                                                           □

------------------------------------------------------------------------
-- Some existence results

-- If the domain of an Iso-lens is inhabited and has h-level n, then
-- the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ {n a b} {A : Set a} {B : Set b} →
  Iso-lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {n} {A = A} {B} l x =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ proj₂-closure (remainder x) n ⟩□
  H-level n B        □
  where
  open Iso-lens l

-- In particular, Iso-lenses with contractible domains have
-- contractible codomains.

contractible-to-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Iso-lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited l (proj₁ c) c

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
  ¬-Set-set univ ⊚ H-level.respects-surjection (_↔_.surjection Bij.↑↔) 2

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
      (A          ↝⟨ inverse ×-left-identity ⟩
       ⊤ × A      ↝⟨ inverse Bij.↑↔ ×-cong F.id ⟩□
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
      ( (R × ↑ _ ⊤ × ∥ B ∥ 1 b  ↔⟨ F.id ×-cong Bij.↑↔ ×-cong F.id ⟩
         R × ⊤ × ∥ B ∥ 1 b      ↔⟨ F.id ×-cong ×-left-identity ⟩
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
      ( ((↑ _ ⊤ × ∥ A ∥ 1 (a ⊔ b)) × R  ↔⟨ (Bij.↑↔ ×-cong F.id) ×-cong F.id ⟩
         (⊤ × ∥ A ∥ 1 (a ⊔ b)) × R      ↔⟨ ×-left-identity ×-cong F.id ⟩
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
