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
open import Equality.Path.Isomorphisms eq using (ext)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J
import H-level.Truncation.Propositional.One-step eq as O
open import Preimage equality-with-J using (_⁻¹_)
open import Univalence-axiom equality-with-J
import Univalence-axiom P.equality-with-J as PU

open import Lens.Non-dependent eq
open import Lens.Non-dependent.Higher.Coinductive eq as Coinductive
  using (Coherently; property)

private
  variable
    a b p : Level
    A     : Set a

-- A variant of Constant for type-valued functions.

Constant-≃ :
  {A : Set a} →
  (A → Set p) → Set (a ⊔ p)
Constant-≃ P = ∀ x y → P x ≃ P y

-- Constant and Constant-≃ are pointwise equivalent (assuming
-- univalence).

Constant≃Constant-≃ :
  {P : A → Set p} →
  Univalence p → Constant P ≃ Constant-≃ P
Constant≃Constant-≃ univ =
  ∀-cong ext λ _ →
  ∀-cong ext λ _ →
  ≡≃≃ univ

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
                                                                       Coinductive.Coherently-cong
                                                                         univ₁
                                                                         (λ _ → Constant≃Constant-≃ univ₂)
                                                                         (λ _ _ → refl _)) ⟩

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
