------------------------------------------------------------------------
-- Small coinductive higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Small
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
import H-level.Truncation.Propositional.One-step eq as O
open import Preimage equality-with-J using (_⁻¹_)
open import Univalence-axiom equality-with-J
import Univalence-axiom P.equality-with-J as PU

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Capriotti eq as Higher
import Lens.Non-dependent.Higher.Coinductive eq as Coinductive
open import Lens.Non-dependent.Higher.Coinductive.Coherently eq

private
  variable
    a b c p q : Level
    A B C     : Set a
    z         : A

------------------------------------------------------------------------
-- The lens type family

-- A variant of Constant for type-valued functions.

Constant-≃ :
  {A : Set a} →
  (A → Set p) → Set (a ⊔ p)
Constant-≃ P = ∀ x y → P x ≃ P y

-- Coherently constant type-valued functions.

Coherently-constant :
  Univalence p →
  {A : Set a} → (A → Set p) → Set (a ⊔ p)
Coherently-constant univ =
  Coherently
    Constant-≃
    (λ P c → O.rec′ P (λ x y → ≃⇒≡ univ (c x y)))

-- Small coinductive lenses, based on an idea due to Paolo Capriotti.
--
-- The lenses are defined as a record type to make it easier for Agda
-- to infer the argument univ from a value of type Lens univ A B.

record Lens (univ : Univalence (a ⊔ b)) (A : Set a) (B : Set b) :
            Set (a ⊔ b) where
  field

    -- A getter.
    get : A → B

    -- The family of fibres of the getter is coherently constant.
    get⁻¹-coherently-constant : Coherently-constant univ (get ⁻¹_)

  -- All the getter's fibres are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant = get⁻¹-coherently-constant .property

  -- A setter.

  set : A → B → A
  set a b =                    $⟨ _≃_.to (get⁻¹-constant (get a) b) ⟩
    (get ⁻¹ get a → get ⁻¹ b)  ↝⟨ _$ (a , refl _) ⟩
    get ⁻¹ b                   ↝⟨ proj₁ ⟩□
    A                          □

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    {univ : Univalence (a ⊔ b)} →
    Has-getter-and-setter (Lens {a = a} {b = b} univ)
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Some conversion functions

-- Constant and Constant-≃ are pointwise equivalent (assuming
-- univalence).

Constant≃Constant-≃ :
  {P : A → Set p} →
  Univalence p → Constant P ≃ Constant-≃ P
Constant≃Constant-≃ univ =
  ∀-cong ext λ _ →
  ∀-cong ext λ _ →
  ≡≃≃ univ

-- Two variants of Coherently-constant are pointwise equivalent
-- (when applicable, assuming univalence).

Coinductive-coherently-constant≃Coherently-constant :
  {A : Set a} {P : A → Set p} →
  PU.Univalence (a ⊔ lsuc p) →
  (univ : Univalence p) →
  Coinductive.Coherently-constant P ≃ Coherently-constant univ P
Coinductive-coherently-constant≃Coherently-constant univ′ univ =
  Coherently-cong
    univ′
    (λ _ → Constant≃Constant-≃ univ)
    (λ _ _ → refl _)

-- Two variants of Coherently-constant are pointwise equivalent
-- (when applicable, assuming univalence).

Higher-coherently-constant≃Coherently-constant :
  {A : Set a} {P : A → Set p} →
  PU.Univalence (a ⊔ lsuc p) →
  (univ : Univalence p) →
  Higher.Coherently-constant P ≃ Coherently-constant univ P
Higher-coherently-constant≃Coherently-constant {P = P} univ′ univ =
  Higher.Coherently-constant P       ↝⟨ Coinductive.Coherently-constant≃Coherently-constant univ′ ⟩
  Coinductive.Coherently-constant P  ↝⟨ Coinductive-coherently-constant≃Coherently-constant univ′ univ ⟩□
  Coherently-constant univ P         □

-- Lens is pointwise equivalent to Coinductive.Lens (assuming
-- univalence).

Coinductive-lens≃Lens :
  {A : Set a} {B : Set b} →
  PU.Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  Coinductive.Lens A B ≃ Lens univ A B
Coinductive-lens≃Lens {A = A} {B = B} univ₁ univ₂ =
  Coinductive.Lens A B                                             ↔⟨⟩

  (∃ λ (get : A → B) → Coinductive.Coherently-constant (get ⁻¹_))  ↝⟨ (∃-cong λ _ →
                                                                       Coinductive-coherently-constant≃Coherently-constant univ₁ univ₂) ⟩

  (∃ λ (get : A → B) → Coherently-constant univ₂ (get ⁻¹_))        ↝⟨ Eq.↔→≃
                                                                        (λ (g , c) → record { get = g; get⁻¹-coherently-constant = c })
                                                                        (λ l → Lens.get l , Lens.get⁻¹-coherently-constant l)
                                                                        refl
                                                                        refl ⟩□
  Lens univ₂ A B                                                   □

-- The equivalence preserves getters and setters.

Coinductive-lens≃Lens-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (univ₁ : PU.Univalence (lsuc (a ⊔ b)))
  (univ₂ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Coinductive-lens≃Lens univ₁ univ₂))
Coinductive-lens≃Lens-preserves-getters-and-setters univ₁ univ₂ =
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (Coinductive-lens≃Lens univ₁ univ₂))
    (λ _ → refl _ , refl _)

------------------------------------------------------------------------
-- Composition

-- A fibre of a composition can be expressed as a pair of fibres.

∘⁻¹≃ :
  (f : B → C) (g : A → B) →
  f ∘ g ⁻¹ z ≃ ∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y
∘⁻¹≃ {z = z} f g =
  f ∘ g ⁻¹ z                                  ↔⟨⟩
  (∃ λ a → f (g a) ≡ z)                       ↔⟨ (∃-cong λ _ → ∃-intro _ _) ⟩
  (∃ λ a → ∃ λ y → f y ≡ z × y ≡ g a)         ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩
  (∃ λ a → ∃ λ ((y , _) : f ⁻¹ z) → y ≡ g a)  ↔⟨ ∃-comm ⟩
  (∃ λ ((y , _) : f ⁻¹ z) → ∃ λ a → y ≡ g a)  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ≡-comm) ⟩□
  (∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y)           □

-- A map lemma for Coherently-constant.

Coherently-constant-map :
  {P : A → Set p} {Q : B → Set q}
  (univ₁ : Univalence p) →
  (univ₂ : Univalence q) →
  (f : B → A) →
  (∀ x → P (f x) ≃ Q x) →
  Coherently-constant univ₁ P → Coherently-constant univ₂ Q
Coherently-constant-map {P = P} {Q = Q} _ _ f P≃Q c .property x y =
  Q x      ↝⟨ inverse $ P≃Q x ⟩
  P (f x)  ↝⟨ c .property (f x) (f y) ⟩
  P (f y)  ↝⟨ P≃Q y ⟩□
  Q y      □
Coherently-constant-map {P = P} {Q = Q} univ₁ univ₂ f P≃Q c .coherent =
  Coherently-constant-map univ₁ univ₂ (O.∥∥¹-map f)
    (O.elim λ where
       .O.Elim.∣∣ʳ → P≃Q
       .O.Elim.∣∣-constantʳ x y → Eq.lift-equality ext
         (_≃_.to (subst (λ z → O.rec′ P g (O.∥∥¹-map f z) ≃
                               O.rec′ Q h z)
                    (O.∣∣-constant x y) (P≃Q x))                       ≡⟨ Eq.to-subst ⟩

          subst (λ z → O.rec′ P g (O.∥∥¹-map f z) → O.rec′ Q h z)
            (O.∣∣-constant x y) (_≃_.to (P≃Q x))                       ≡⟨ (⟨ext⟩ λ _ → subst-→) ⟩

          subst (O.rec′ Q h) (O.∣∣-constant x y) ∘
          _≃_.to (P≃Q x) ∘
          subst (O.rec′ P g ∘ O.∥∥¹-map f) (sym (O.∣∣-constant x y))   ≡⟨ cong₂ (λ f g → f ∘ _≃_.to (P≃Q x) ∘ g)
                                                                            (⟨ext⟩ λ q → subst-∘ id (O.rec′ Q h) (O.∣∣-constant x y) {p = q})
                                                                            (⟨ext⟩ λ p →
                                                                             trans (subst-∘ id (O.rec′ P g ∘ O.∥∥¹-map f)
                                                                                      (sym (O.∣∣-constant x y)) {p = p}) $
                                                                             cong (λ eq → subst id eq p) $
                                                                             trans (cong-sym _ _) $
                                                                             cong sym $ sym $ cong-∘ _ _ _) ⟩
          subst id (cong (O.rec′ Q h) (O.∣∣-constant x y)) ∘
          _≃_.to (P≃Q x) ∘
          subst id (sym (cong (O.rec′ P g)
                           (cong (O.∥∥¹-map f) (O.∣∣-constant x y))))  ≡⟨ cong₂ (λ p q → subst id p ∘ _≃_.to (P≃Q x) ∘ subst id (sym q))
                                                                            O.rec-∣∣-constant
                                                                            (trans (cong (cong (O.rec′ P g)) O.rec-∣∣-constant) $
                                                                             O.rec-∣∣-constant) ⟩

          subst id (h x y) ∘
          _≃_.to (P≃Q x) ∘
          subst id (sym (g (f x) (f y)))                               ≡⟨ cong₂ (λ p q → p ∘ _≃_.to (P≃Q x) ∘ q)
                                                                            (trans (⟨ext⟩ λ _ → subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                             cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₂) _)
                                                                            (trans (⟨ext⟩ λ _ → subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                             cong _≃_.from $ _≃_.right-inverse-of (≡≃≃ univ₁) _) ⟩
          _≃_.to (P≃Q y) ∘
          _≃_.to (c .property (f x) (f y)) ∘
          _≃_.from (P≃Q x) ∘
          _≃_.to (P≃Q x) ∘
          _≃_.from (c .property (f x) (f y))                           ≡⟨ (⟨ext⟩ λ _ → cong (_≃_.to (P≃Q y) ∘ _≃_.to (c .property (f x) (f y))) $
                                                                          _≃_.left-inverse-of (P≃Q x) _) ⟩
          _≃_.to (P≃Q y) ∘
          _≃_.to (c .property (f x) (f y)) ∘
          _≃_.from (c .property (f x) (f y))                           ≡⟨ (⟨ext⟩ λ _ → cong (_≃_.to (P≃Q y)) $
                                                                           _≃_.right-inverse-of (c .property (f x) (f y)) _) ⟩∎
          _≃_.to (P≃Q y)                                               ∎))
    (c .coherent)
  where
  g = λ x y → ≃⇒≡ univ₁ (c .property x y)
  h = λ x y → ≃⇒≡ univ₂ ((P≃Q y F.∘ c .property (f x) (f y)) F.∘
                         inverse (P≃Q x))

-- Coherently-constant is, in a certain sense, closed under Σ.
--
-- This lemma is based on a lemma due to Paolo Capriotti.

Coherently-constant-Σ :
  {A : Set a} {P : A → Set p} {Q : ∃ P → Set q}
  (univ₁ : Univalence p)
  (univ₂ : Univalence q)
  (univ₃ : Univalence (p ⊔ q)) →
  PU.Univalence (a ⊔ lsuc p) →
  PU.Univalence (a ⊔ p ⊔ lsuc q) →
  PU.Univalence (a ⊔ lsuc (p ⊔ q)) →
  Coherently-constant univ₁ P →
  Coherently-constant univ₂ Q →
  Coherently-constant univ₃ (λ x → ∃ λ (y : P x) → Q (x , y))
Coherently-constant-Σ {P = P} {Q = Q}
  univ₁ univ₂ univ₃ univ₄ univ₅ univ₆ =
  curry
    (Coherently-constant univ₁ P × Coherently-constant univ₂ Q     ↔⟨ inverse (Higher-coherently-constant≃Coherently-constant univ₄ univ₁ ×-cong
                                                                               Higher-coherently-constant≃Coherently-constant univ₅ univ₂) ⟩
     Higher.Coherently-constant P × Higher.Coherently-constant Q   ↝⟨ uncurry Higher.Coherently-constant-Σ ⟩
     Higher.Coherently-constant (λ x → ∃ λ (y : P x) → Q (x , y))  ↔⟨ Higher-coherently-constant≃Coherently-constant univ₆ univ₃ ⟩□
     Coherently-constant univ₃ (λ x → ∃ λ (y : P x) → Q (x , y))   □)

-- Composition.
--
-- Paolo Capriotti came up with the idea to use Coherently-constant-Σ.
-- At first we had a problem related to universe levels. Andrea
-- Vezzosi came up with a first workaround (involving lifting), and
-- later I found a more direct solution.

infix 9 ⟨_,_,_,_,_⟩_∘_

⟨_,_,_,_,_⟩_∘_ :
  {A : Set a} {B : Set b} {C : Set c}
  {univ₁ : Univalence (b ⊔ c)}
  {univ₂ : Univalence (a ⊔ b)}
  (univ₃ : Univalence (a ⊔ c)) →
  Univalence (a ⊔ b ⊔ c) →
  PU.Univalence (lsuc (b ⊔ c)) →
  PU.Univalence (lsuc (a ⊔ b) ⊔ c) →
  PU.Univalence (lsuc (a ⊔ b ⊔ c)) →
  Lens univ₁ B C → Lens univ₂ A B → Lens univ₃ A C
(⟨ _ , _ , _ , _ , _ ⟩ l₁ ∘ l₂) .Lens.get = get l₁ ∘ get l₂
  where
  open Lens
⟨_,_,_,_,_⟩_∘_ {b = ℓb} {univ₁ = univ₁} {univ₂ = univ₂}
  univ₃ univ₄ univ₅ univ₆ univ₇ l₁ l₂
  .Lens.get⁻¹-coherently-constant =
                                                       $⟨ Coherently-constant-Σ
                                                            {P = get l₁ ⁻¹_}
                                                            {Q = λ (_ , b , _) → get l₂ ⁻¹ b}
                                                            univ₁ univ₂ univ₄ univ₅ univ₆ univ₇
                                                            (get⁻¹-coherently-constant l₁)
                                                            (Coherently-constant-map univ₂ univ₂
                                                               (proj₁ ∘ proj₂) (λ _ → F.id)
                                                               (get⁻¹-coherently-constant l₂)) ⟩
  Coherently-constant univ₄
    (λ c → ∃ λ ((b , _) : get l₁ ⁻¹ c) → get l₂ ⁻¹ b)  ↝⟨ Coherently-constant-map univ₄ univ₃ id
                                                            (λ _ → inverse $ ∘⁻¹≃ (get l₁) (get l₂)) ⟩□
  Coherently-constant univ₃ ((get l₁ ∘ get l₂) ⁻¹_)    □
  where
  open Lens
