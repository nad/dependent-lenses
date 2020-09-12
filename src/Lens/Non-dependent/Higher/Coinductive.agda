------------------------------------------------------------------------
-- Coinductive higher lenses
------------------------------------------------------------------------

-- Paolo Capriotti came up with these lenses, and provided an informal
-- proof showing that this lens type is pointwise equivalent to his
-- higher lenses. I turned this proof into the proof presented below,
-- with help from Andrea Vezzosi.

{-# OPTIONS --cubical --safe --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Colimit.Sequential eq as C using (∣_∣)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
import H-level.Truncation.Propositional.Non-recursive eq as N
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥₁; ∥_∥₁-out-^; ∥_∥₁-in-^; ∣_∣; ∣_,_∣-in-^)
open import Preimage equality-with-J using (_⁻¹_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Capriotti eq as Higher

private
  variable
    a b p : Level
    A B C : Set a
    x y   : A

------------------------------------------------------------------------
-- Weakly constant functions

-- A variant of Constant.

Constant′ :
  {A : Set a} {B : Set b} →
  (A → B) → Set (a ⊔ b)
Constant′ {A = A} {B = B} f =
  ∃ λ (g : ∥ A ∥₁ → B) → ∀ x → g ∣ x ∣ ≡ f x

-- Constant and Constant′ are pointwise equivalent.

Constant≃Constant′ : (f : A → B) → Constant f ≃ Constant′ f
Constant≃Constant′ f = Eq.↔→≃
  (λ c → O.rec′ f c
       , λ x → O.rec′ f c ∣ x ∣  ≡⟨⟩
               f x               ∎)
  (λ (g , h) x y →
     f x      ≡⟨ sym (h x) ⟩
     g ∣ x ∣  ≡⟨ cong g (O.∣∣-constant x y) ⟩
     g ∣ y ∣  ≡⟨ h y ⟩∎
     f y      ∎)
  (λ (g , h) →
     let lem = O.elim λ where
           .O.Elim.∣∣ʳ x →
             f x      ≡⟨ sym (h x) ⟩∎
             g ∣ x ∣  ∎
           .O.Elim.∣∣-constantʳ x y →
             let g′ = O.rec′ f λ x y →
                        trans (sym (h x))
                          (trans (cong g (O.∣∣-constant x y))
                             (h y))
             in
             subst (λ z → g′ z ≡ g z) (O.∣∣-constant x y) (sym (h x))  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

             trans (sym (cong g′ (O.∣∣-constant x y)))
               (trans (sym (h x)) (cong g (O.∣∣-constant x y)))        ≡⟨ cong (flip trans _) $ cong sym
                                                                          O.rec-∣∣-constant ⟩
             trans (sym (trans (sym (h x))
                           (trans (cong g (O.∣∣-constant x y))
                              (h y))))
               (trans (sym (h x)) (cong g (O.∣∣-constant x y)))        ≡⟨ trans (cong (flip trans _) $
                                                                                 trans (cong sym $ sym $ trans-assoc _ _ _) $
                                                                                 sym-trans _ _) $
                                                                          trans-[trans-sym]- _ _ ⟩∎
             sym (h y)                                                 ∎
     in
     Σ-≡,≡→≡
       (⟨ext⟩ lem)
       (⟨ext⟩ λ x →

        subst (λ g → ∀ x → g ∣ x ∣ ≡ f x)
          (⟨ext⟩ lem) (λ x → refl (f x)) x                         ≡⟨ sym $ push-subst-application _ _ ⟩

        subst (λ g → g ∣ x ∣ ≡ f x) (⟨ext⟩ lem) (refl (f x))       ≡⟨ subst-∘ _ _ _ ⟩

        subst (_≡ f x) (cong (_$ ∣ x ∣) (⟨ext⟩ lem)) (refl (f x))  ≡⟨ subst-trans-sym ⟩

        trans (sym (cong (_$ ∣ x ∣) (⟨ext⟩ lem))) (refl (f x))     ≡⟨ trans-reflʳ _ ⟩

        sym (cong (_$ ∣ x ∣) (⟨ext⟩ lem))                          ≡⟨ cong sym $ cong-ext _ ⟩

        sym (lem ∣ x ∣)                                            ≡⟨⟩

        sym (sym (h x))                                            ≡⟨ sym-sym _ ⟩∎

        h x                                                        ∎))
  (λ c → ⟨ext⟩ λ x → ⟨ext⟩ λ y →
     trans (sym (refl _))
       (trans (cong (O.rec′ f c) (O.∣∣-constant x y)) (refl _))  ≡⟨ trans (cong₂ trans sym-refl (trans-reflʳ _)) $
                                                                    trans-reflˡ _ ⟩

     cong (O.rec′ f c) (O.∣∣-constant x y)                       ≡⟨ O.rec-∣∣-constant ⟩∎

     c x y                                                       ∎)

------------------------------------------------------------------------
-- Coherently constant functions

-- Coherently P step f means that f and all variants of f built using
-- step (in a certain way) satisfy the property P.

record Coherently
         {A : Set a} {B : Set b}
         (P : {A : Set a} → (A → B) → Set p)
         (step : {A : Set a} (f : A → B) → P f → ∥ A ∥₁ → B)
         (f : A → B) : Set p where
  coinductive
  field
    property : P f
    coherent : Coherently P step (step f property)

open Coherently public

-- A "computation rule".

subst-Coherently-property :
  ∀ {B : Set b} {P : C → {A : Set a} → (A → B) → Set p}
    {step : (c : C) {A : Set a} (f : A → B) → P c f → ∥ A ∥₁ → B}
    {f : C → A → B} {eq : x ≡ y} {c} →
  subst (λ x → Coherently (P x) (step x) (f x)) eq c .property ≡
  subst (λ x → P x (f x)) eq (c .property)
subst-Coherently-property
  {P = P} {step = step} {f = f} {eq = eq} {c = c} =
  elim¹
    (λ eq →
       subst (λ x → Coherently (P x) (step x) (f x)) eq c .property ≡
       subst (λ x → P x (f x)) eq (c .property))
    (subst (λ x → Coherently (P x) (step x) (f x)) (refl _) c .property  ≡⟨ cong property $ subst-refl _ _ ⟩
     c .property                                                         ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → P x (f x)) (refl _) (c .property)                      ∎)
    eq

-- Coherently constant functions.

Coherently-constant :
  {A : Set a} {B : Set b} (f : A → B) → Set (a ⊔ b)
Coherently-constant = Coherently Constant O.rec′

-- An alternative to Coherently-constant.

Coherently-constant′ :
  {A : Set a} {B : Set b} (f : A → B) → Set (a ⊔ b)
Coherently-constant′ = Coherently Constant′ (λ _ → proj₁)

-- Coherently-constant and Coherently-constant′ are pointwise equal
-- (assuming univalence).

Coherently-constant≡Coherently-constant′ :
  {A : Set a} {B : Set b} {f : A → B} →
  Univalence (a ⊔ b) →
  Coherently-constant f ≡ Coherently-constant′ f
Coherently-constant≡Coherently-constant′
  {a = a} {b = b} {A = A} {B = B} {f = f} univ =

  cong (λ ((P , step) :
           ∃ λ (P : (A : Set a) → (A → B) → Set (a ⊔ b)) →
               {A : Set a} (f : A → B) → P A f → ∥ A ∥₁ → B) →
          Coherently (P _) step f) $

  Σ-≡,≡→≡

    (⟨ext⟩ λ A → ⟨ext⟩ λ (f : A → B) →
     ≃⇒≡ univ (Constant≃Constant′ f))

    (implicit-extensionality ext λ A → ⟨ext⟩ λ f →
       subst (λ P → {A : Set a} (f : A → B) → P A f → ∥ A ∥₁ → B)
         (⟨ext⟩ λ A → ⟨ext⟩ λ (f : A → B) →
          ≃⇒≡ univ (Constant≃Constant′ f))
         O.rec′ f                                                  ≡⟨ trans (cong (_$ f) $ sym $
                                                                             push-subst-implicit-application _ _) $
                                                                      sym $ push-subst-application _ _ ⟩
       subst (λ P → P A f → ∥ A ∥₁ → B)
         (⟨ext⟩ λ A → ⟨ext⟩ λ (f : A → B) →
          ≃⇒≡ univ (Constant≃Constant′ f))
         (O.rec′ f)                                                ≡⟨ subst-ext _ _ ⟩

       subst (λ P → P f → ∥ A ∥₁ → B)
         (⟨ext⟩ λ (f : A → B) →
          ≃⇒≡ univ (Constant≃Constant′ f))
         (O.rec′ f)                                                ≡⟨ subst-ext {x = f} _ _ ⟩

       subst (λ P → P → ∥ A ∥₁ → B)
         (≃⇒≡ univ (Constant≃Constant′ f))
         (O.rec′ f)                                                ≡⟨ sym $
                                                                      transport-theorem
                                                                        (λ P → P → ∥ A ∥₁ → B)
                                                                        (→-cong₁ _)
                                                                        refl
                                                                        univ
                                                                        (Constant≃Constant′ f)
                                                                        (O.rec′ f) ⟩
       →-cong₁ _ (Constant≃Constant′ f) (O.rec′ f)                 ≡⟨⟩

       O.rec′ f ∘ _≃_.from (Constant≃Constant′ f)                  ≡⟨⟩

       proj₁ ∘ _≃_.to (Constant≃Constant′ f) ∘
       _≃_.from (Constant≃Constant′ f)                             ≡⟨ cong (proj₁ ∘_) $ ⟨ext⟩ $
                                                                      _≃_.right-inverse-of (Constant≃Constant′ f) ⟩∎
       proj₁                                                       ∎)

-- Coherently-constant and Coherently-constant′ are pointwise
-- equivalent (assuming univalence).
--
-- This lemma is defined in such a way that the "outermost" property
-- fields are transformed using Constant≃Constant′.

Coherently-constant≃Coherently-constant′ :
  {A : Set a} {B : Set b} {f : A → B} →
  Univalence (a ⊔ b) →
  Coherently-constant f ≃ Coherently-constant′ f
Coherently-constant≃Coherently-constant′ {a = a} {b = b} {f = f} univ =
  block λ bl →
  Eq.↔→≃
    to
    (from bl)
    (_↔_.from ≡↔≡ ∘ to-from bl)
    (_↔_.from ≡↔≡ ∘ from-to bl)
  where
  c≡c :
    {A : Set a} {B : Set b} {f : A → B} →
    Coherently-constant f ≡ Coherently-constant′ f
  c≡c = Coherently-constant≡Coherently-constant′ univ

  to : Coherently-constant f → Coherently-constant′ f
  to c .property = _≃_.to (Constant≃Constant′ f) (c .property)
  to c .coherent = ≡⇒→ c≡c (c .coherent)

  from-lemma :
    Block "from-lemma" →
    ∀ c → proj₁ c P.≡ O.rec′ f (_≃_.from (Constant≃Constant′ f) c)
  from-lemma ⊠ c =
    proj₁ c                                        P.≡⟨ P.sym $ P.cong proj₁ $ _↔_.to ≡↔≡ $
                                                        _≃_.right-inverse-of (Constant≃Constant′ f) c ⟩∎
    proj₁ (_≃_.to (Constant≃Constant′ f)
             (_≃_.from (Constant≃Constant′ f) c))  ∎

  from :
    Block "from-lemma" →
    Coherently-constant′ f → Coherently-constant f
  from _  c .property = _≃_.from (Constant≃Constant′ f) (c .property)
  from bl c .coherent =
    P.subst Coherently-constant (from-lemma bl (c .property)) $
    _≃_.from (≡⇒≃ c≡c) (c .coherent)

  to-from-property :
    ∀ c →
    _≃_.to (Constant≃Constant′ f)
      (_≃_.from (Constant≃Constant′ f) c) P.≡
    c
  to-from-property c =
    _↔_.to ≡↔≡ (_≃_.right-inverse-of (Constant≃Constant′ f) c)

  from-lemma-lemma₁ :
    ∀ bl c →
    P.cong proj₁ (to-from-property c) ≡ P.sym (from-lemma bl c)
  from-lemma-lemma₁ ⊠ c =
    P.cong proj₁
      (_↔_.to ≡↔≡ (_≃_.right-inverse-of (Constant≃Constant′ f) c))  ≡⟨ sym $ _↔_.from ≡↔≡ $ P.sym-sym _ ⟩∎

    (P.sym $ P.sym $ P.cong proj₁ $ _↔_.to ≡↔≡ $
     _≃_.right-inverse-of (Constant≃Constant′ f) c)                 ∎

  to-from : ∀ bl (c : Coherently-constant′ f) → to (from bl c) P.≡ c
  to-from bl c i .property = to-from-property (c .property) i
  to-from bl c i .coherent = lemma i
    where
    lemma :
      P.[ (λ i → Coherently-constant′
                   (proj₁ (to-from-property (c .property) i))) ]
        ≡⇒→ c≡c (P.subst Coherently-constant
                   (from-lemma bl (c .property))
                   (_≃_.from (≡⇒≃ c≡c) (c .coherent))) ≡
        c .coherent
    lemma =
      PB._↔_.from (P.heterogeneous↔homogeneous _) $ _↔_.to ≡↔≡
        (P.subst Coherently-constant′
           (P.cong proj₁ (to-from-property (c .property)))
           (≡⇒→ c≡c
              (P.subst Coherently-constant (from-lemma bl (c .property))
                 (_≃_.from (≡⇒≃ c≡c) (c .coherent))))                     ≡⟨ cong (λ eq →
                                                                                     P.subst Coherently-constant′
                                                                                       (P.cong proj₁ (to-from-property (c .property)))
                                                                                       (≡⇒→ (eq _)
                                                                                          (P.subst Coherently-constant
                                                                                             (from-lemma bl (c .property))
                                                                                             (_≃_.from (≡⇒≃ (eq _)) (c .coherent))))) $ sym $
                                                                             _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext)
                                                                               (λ f → c≡c {f = f}) ⟩
         P.subst Coherently-constant′
           (P.cong proj₁ (to-from-property (c .property)))
           (≡⇒→ (ext⁻¹ (⟨ext⟩ λ f → c≡c {f = f}) _)
              (P.subst Coherently-constant (from-lemma bl (c .property))
                 (_≃_.from (≡⇒≃ (ext⁻¹ (⟨ext⟩ λ f → c≡c {f = f}) _))
                    (c .coherent))))                                      ≡⟨ cong (P.subst Coherently-constant′
                                                                                     (P.cong proj₁ (to-from-property (c .property)))) $
                                                                             elim₁
                                                                               (λ {C} c≡c →
                                                                                  ≡⇒→ (ext⁻¹ c≡c _)
                                                                                    (P.subst C (from-lemma bl (c .property))
                                                                                       (_≃_.from (≡⇒≃ (ext⁻¹ c≡c _)) (c .coherent))) ≡
                                                                                  P.subst Coherently-constant′ (from-lemma bl (c .property))
                                                                                    (c .coherent))
                                                                               (
           ≡⇒→ (ext⁻¹ (refl Coherently-constant′) _)
             (P.subst Coherently-constant′ (from-lemma bl (c .property))
                (_≃_.from (≡⇒≃ (ext⁻¹ (refl Coherently-constant′) _))
                   (c .coherent)))                                              ≡⟨ cong (_$ P.subst Coherently-constant′
                                                                                              (from-lemma bl (c .property))
                                                                                              (_≃_.from (≡⇒≃ (ext⁻¹ (refl Coherently-constant′) _))
                                                                                                 (c .coherent))) $
                                                                                   trans (cong ≡⇒→ $ ext⁻¹-refl _) $
                                                                                   ≡⇒→-refl ⟩
           P.subst Coherently-constant′ (from-lemma bl (c .property))
             (_≃_.from (≡⇒≃ (ext⁻¹ (refl Coherently-constant′) _))
                (c .coherent))                                                  ≡⟨ cong (λ eq → P.subst Coherently-constant′
                                                                                                  (from-lemma bl (c .property))
                                                                                                  (_≃_.from eq (c .coherent))) $
                                                                                   trans (cong ≡⇒≃ $ ext⁻¹-refl _) $
                                                                                   ≡⇒≃-refl ⟩∎
           P.subst Coherently-constant′ (from-lemma bl (c .property))
             (c .coherent)                                                      ∎)
                                                                               _ ⟩
         P.subst Coherently-constant′
           (P.cong proj₁ (to-from-property (c .property)))
           (P.subst Coherently-constant′ (from-lemma bl (c .property))
              (c .coherent))                                              ≡⟨ cong (λ eq → P.subst Coherently-constant′ eq
                                                                                            (P.subst Coherently-constant′
                                                                                               (from-lemma bl (c .property)) (c .coherent))) $
                                                                             from-lemma-lemma₁ bl _ ⟩
         P.subst Coherently-constant′
           (P.sym (from-lemma bl (c .property)))
           (P.subst Coherently-constant′ (from-lemma bl (c .property))
              (c .coherent))                                              ≡⟨ _↔_.from ≡↔≡ $
                                                                             P.subst-subst-sym Coherently-constant′ _ _ ⟩∎
         c .coherent                                                      ∎)

  from-to-property :
    ∀ (c : Constant f) →
    _≃_.from (Constant≃Constant′ f)
      (_≃_.to (Constant≃Constant′ f) c) P.≡
    c
  from-to-property c =
    _↔_.to ≡↔≡ (_≃_.left-inverse-of (Constant≃Constant′ f) c)

  from-lemma-lemma₂ :
    ∀ bl c →
    from-lemma bl (_≃_.to (Constant≃Constant′ f) c) ≡
    (P.sym $ P.cong (O.rec′ f) $ from-to-property c)
  from-lemma-lemma₂ ⊠ c =
    P.sym $ P.cong proj₁ $ _↔_.to ≡↔≡ $
    _≃_.right-inverse-of (Constant≃Constant′ f) $
    _≃_.to (Constant≃Constant′ f) c                        ≡⟨ cong (P.sym ∘ P.cong proj₁ ∘ _↔_.to ≡↔≡) $ sym $
                                                              _≃_.left-right-lemma (Constant≃Constant′ f) _ ⟩
    P.sym $ P.cong proj₁ $ _↔_.to ≡↔≡ $
    cong (_≃_.to (Constant≃Constant′ f)) $
    _≃_.left-inverse-of (Constant≃Constant′ f) c           ≡⟨ cong (P.sym ∘ P.cong proj₁ ∘ _↔_.to ≡↔≡ ∘
                                                                    cong (_≃_.to (Constant≃Constant′ f))) $ sym $
                                                              _↔_.left-inverse-of ≡↔≡ _ ⟩
    P.sym $ P.cong proj₁ $ _↔_.to ≡↔≡ $
    cong (_≃_.to (Constant≃Constant′ f)) $
    _↔_.from ≡↔≡ $ _↔_.to ≡↔≡ $
    _≃_.left-inverse-of (Constant≃Constant′ f) c           ≡⟨ cong (P.sym ∘ P.cong proj₁) $ _↔_.from-to ≡↔≡ $ sym
                                                              cong≡cong ⟩
    P.sym $ P.cong proj₁ $
    P.cong (_≃_.to (Constant≃Constant′ f)) $ _↔_.to ≡↔≡ $
    _≃_.left-inverse-of (Constant≃Constant′ f) c           ≡⟨ cong P.sym $ _↔_.from ≡↔≡ $
                                                              P.cong-∘ proj₁ (_≃_.to (Constant≃Constant′ f))
                                                                (_↔_.to ≡↔≡ $ _≃_.left-inverse-of (Constant≃Constant′ f) c) ⟩∎
    P.sym $ P.cong (O.rec′ f) $ _↔_.to ≡↔≡ $
    _≃_.left-inverse-of (Constant≃Constant′ f) c           ∎

  from-to : ∀ bl (c : Coherently-constant f) → from bl (to c) P.≡ c
  from-to bl c i .property = from-to-property (c .property) i
  from-to bl c i .coherent = lemma i
    where
    lemma :
      P.[ (λ i → Coherently-constant
                   (O.rec′ f (from-to-property (c .property) i))) ]
        P.subst Coherently-constant
          (from-lemma bl (_≃_.to (Constant≃Constant′ f) (c .property)))
          (_≃_.from (≡⇒≃ c≡c) (≡⇒→ c≡c (c .coherent))) ≡
        c .coherent
    lemma =
      PB._↔_.from (P.heterogeneous↔homogeneous _) $ _↔_.to ≡↔≡
        (P.subst Coherently-constant
           (P.cong (O.rec′ f) (from-to-property (c .property)))
           (P.subst Coherently-constant
              (from-lemma bl
                 (_≃_.to (Constant≃Constant′ f) (c .property)))
              (_≃_.from (≡⇒≃ c≡c) (≡⇒→ c≡c (c .coherent))))         ≡⟨ cong (λ eq → P.subst Coherently-constant (P.cong (O.rec′ f) _)
                                                                                      (P.subst Coherently-constant eq _)) $
                                                                       from-lemma-lemma₂ bl _ ⟩
         P.subst Coherently-constant
           (P.cong (O.rec′ f) $ from-to-property (c .property))
           (P.subst Coherently-constant
              (P.sym $ P.cong (O.rec′ f) $
               from-to-property (c .property))
              (_≃_.from (≡⇒≃ c≡c) (≡⇒→ c≡c (c .coherent))))         ≡⟨ _↔_.from ≡↔≡ $ P.subst-subst-sym Coherently-constant _ _ ⟩

         _≃_.from (≡⇒≃ c≡c) (≡⇒→ c≡c (c .coherent))                 ≡⟨ _≃_.left-inverse-of (≡⇒≃ c≡c) _ ⟩∎

         c .coherent                                                ∎)

-- "Functions from A to B that are coherently constant" can be
-- expressed in a different way.

∃Coherently-constant′≃ :
  (∃ λ (f : A → B) → Coherently-constant′ f)
    ≃
  (∃ λ (f : ∀ n → ∥ A ∥₁-in-^ n → B) →
     ∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x)
∃Coherently-constant′≃ = Eq.↔→≃
  (λ (f , c) → to₁ f c , to₂ f c)
  (λ (f , c) → f 0 , from f c)
  (λ (f , c) → Σ-≡,≡→≡
     (⟨ext⟩ λ n → ⟨ext⟩ λ x → to₁-from f c n x)
     (⟨ext⟩ λ n → ⟨ext⟩ λ x →
        subst (λ f → ∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x)
          (⟨ext⟩ λ n → ⟨ext⟩ λ x → to₁-from f c n x)
          (to₂ (f 0) (from f c))
          n x                                                       ≡⟨ trans (cong (_$ x) $ sym $
                                                                              push-subst-application _ _) $
                                                                       sym $ push-subst-application _ _ ⟩
        subst (λ f → f (suc n) ∣ n , x ∣-in-^ ≡ f n x)
          (⟨ext⟩ λ n → ⟨ext⟩ λ x → to₁-from f c n x)
          (to₂ (f 0) (from f c) n x)                                ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans (sym (cong (λ f → f (suc n) ∣ n , x ∣-in-^)
                      (⟨ext⟩ λ n → ⟨ext⟩ λ x → to₁-from f c n x)))
          (trans (to₂ (f 0) (from f c) n x)
             (cong (λ f → f n x)
                (⟨ext⟩ λ n → ⟨ext⟩ λ x → to₁-from f c n x)))        ≡⟨ cong₂ (λ p q → trans (sym p) (trans (to₂ (f 0) (from f c) n x) q))
                                                                         (trans (sym $ cong-∘ _ _ _) $
                                                                          trans (cong (cong _) $ cong-ext _) $
                                                                          cong-ext _)
                                                                         (trans (sym $ cong-∘ _ _ _) $
                                                                          trans (cong (cong _) $ cong-ext _) $
                                                                          cong-ext _) ⟩
        trans (sym (to₁-from f c (suc n) ∣ n , x ∣-in-^))
          (trans (to₂ (f 0) (from f c) n x)
             (to₁-from f c n x))                                    ≡⟨ to₂-from f c n x ⟩∎

        c n x                                                       ∎))
  (λ (f , c) → cong (f ,_) $ _↔_.from ≡↔≡ $ from-to f c)
  where
  to₁ :
    (f : A → B) → Coherently-constant′ f →
    ∀ n → ∥ A ∥₁-in-^ n → B
  to₁ f c zero    = f
  to₁ f c (suc n) = to₁ (proj₁ (c .property)) (c .coherent) n

  to₂ :
    ∀ (f : A → B) (c : Coherently-constant′ f) n x →
    to₁ f c (suc n) ∣ n , x ∣-in-^ ≡ to₁ f c n x
  to₂ f c zero    = proj₂ (c .property)
  to₂ f c (suc n) = to₂ (proj₁ (c .property)) (c .coherent) n

  from :
    (f : ∀ n → ∥ A ∥₁-in-^ n → B) →
    (∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x) →
    Coherently-constant′ (f 0)
  from f c .property = f 1 , c 0
  from f c .coherent = from (f ∘ suc) (c ∘ suc)

  from-to :
    (f : A → B) (c : Coherently-constant′ f) →
    from (to₁ f c) (to₂ f c) P.≡ c
  from-to f c i .property = (c .property  P.∎) i
  from-to f c i .coherent =
    from-to (proj₁ (c .property)) (c .coherent) i

  to₁-from :
    (f : ∀ n → ∥ A ∥₁-in-^ n → B)
    (c : ∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x) →
    ∀ n x → to₁ (f 0) (from f c) n x ≡ f n x
  to₁-from f c zero    = refl ∘ f 0
  to₁-from f c (suc n) = to₁-from (f ∘ suc) (c ∘ suc) n

  to₂-from :
    (f : ∀ n → ∥ A ∥₁-in-^ n → B)
    (c : ∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x) →
    ∀ n x →
    trans (sym (to₁-from f c (suc n) ∣ n , x ∣-in-^))
      (trans (to₂ (f 0) (from f c) n x)
         (to₁-from f c n x)) ≡
    c n x
  to₂-from f c (suc n) = to₂-from (f ∘ suc) (c ∘ suc) n
  to₂-from f c zero    = λ x →
    trans (sym (refl _)) (trans (c 0 x) (refl _))  ≡⟨ trans (cong (flip trans _) sym-refl) $
                                                      trans-reflˡ _ ⟩
    trans (c 0 x) (refl _)                         ≡⟨ trans-reflʳ _ ⟩∎
    c 0 x                                          ∎

-- Functions from ∥ A ∥ can be expressed as coherently constant
-- functions from A (assuming univalence).

∥∥→≃ :
  ∀ {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (∥ A ∥ → B)
    ≃
  (∃ λ (f : A → B) → Coherently-constant f)
∥∥→≃ {A = A} {B = B} univ =
  (∥ A ∥ → B)                                         ↝⟨ →-cong ext (inverse N.∥∥≃∥∥) F.id ⟩

  (N.∥ A ∥ → B)                                       ↝⟨ C.universal-property ⟩

  (∃ λ (f : ∀ n → ∥ A ∥₁-out-^ n → B) →
     ∀ n x → f (suc n) ∣ x ∣ ≡ f n x)                 ↝⟨ (Σ-cong {k₁ = equivalence} (∀-cong ext λ n → →-cong₁ ext (O.∥∥₁-out-^≃∥∥₁-in-^ n)) λ f →
                                                          ∀-cong ext λ n →
                                                          Π-cong-contra ext (inverse $ O.∥∥₁-out-^≃∥∥₁-in-^ n) λ x →
                                                          ≡⇒↝ _ $ cong (λ y → f (suc n) y ≡ f n (_≃_.from (O.∥∥₁-out-^≃∥∥₁-in-^ n) x)) (
    ∣ _≃_.from (O.∥∥₁-out-^≃∥∥₁-in-^ n) x ∣                 ≡⟨ sym $ O.∣,∣-in-^≡∣∣ n ⟩∎

    _≃_.from (O.∥∥₁-out-^≃∥∥₁-in-^ (suc n))
      ∣ n , x ∣-in-^                                        ∎)) ⟩

  (∃ λ (f : ∀ n → ∥ A ∥₁-in-^ n → B) →
     ∀ n x → f (suc n) ∣ n , x ∣-in-^ ≡ f n x)        ↝⟨ inverse ∃Coherently-constant′≃ ⟩

  (∃ λ (f : A → B) → Coherently-constant′ f)          ↝⟨ (∃-cong λ _ → inverse $ Coherently-constant≃Coherently-constant′ univ) ⟩□

  (∃ λ (f : A → B) → Coherently-constant f)           □

-- A function used in the statement of proj₂-to-∥∥→≃-property≡.

proj₁-to-∥∥→≃-constant :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b)) →
  (f : ∥ A ∥ → B) →
  Constant (proj₁ (_≃_.to (∥∥→≃ univ) f))
proj₁-to-∥∥→≃-constant _ f x y =
  f ∣ x ∣  ≡⟨ cong f (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ⟩∎
  f ∣ y ∣  ∎

-- A "computation rule" for ∥∥→≃.

proj₂-to-∥∥→≃-property≡ :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b)) →
  {f : ∥ A ∥ → B} →
  proj₂ (_≃_.to (∥∥→≃ univ) f) .property ≡
  proj₁-to-∥∥→≃-constant univ f
proj₂-to-∥∥→≃-property≡ univ {f = f} = ⟨ext⟩ λ x → ⟨ext⟩ λ y →

  let g , c = _≃_.to C.universal-property (f ∘ _≃_.to N.∥∥≃∥∥) in

  proj₂ (_≃_.to (∥∥→≃ univ) f) .property x y                             ≡⟨⟩

  _≃_.from (Coherently-constant≃Coherently-constant′ univ)
    (proj₂
       (_≃_.from ∃Coherently-constant′≃
          (Σ-map (λ g n → g n ∘ _≃_.from (oi n))
                 (λ {g} c n x →
                    ≡⇒→ (cong (λ y → g (suc n) y ≡
                                     g n (_≃_.from (oi n) x))
                           (sym $ O.∣,∣-in-^≡∣∣ n))
                      (c n (_≃_.from (oi n) x)))
             (_≃_.to C.universal-property (f ∘ _≃_.to N.∥∥≃∥∥)))))
    .property x y                                                        ≡⟨⟩

  _≃_.from (Constant≃Constant′ _)
    (proj₂
       (_≃_.from ∃Coherently-constant′≃
          (Σ-map (λ g n → g n ∘ _≃_.from (oi n))
                 (λ {g} c n x →
                    ≡⇒→ (cong (λ y → g (suc n) y ≡
                                     g n (_≃_.from (oi n) x))
                           (sym $ O.∣,∣-in-^≡∣∣ n))
                      (c n (_≃_.from (oi n) x)))
             (_≃_.to C.universal-property (f ∘ _≃_.to N.∥∥≃∥∥))))
       .property)
     x y                                                                 ≡⟨⟩

  _≃_.from (Constant≃Constant′ _)
    ( g 1
    , λ x → ≡⇒→ (cong (λ z → g 1 z ≡ g 0 x) (sym $ refl ∣ _ ∣)) (c 0 x)
    ) x y                                                                ≡⟨⟩

  trans (sym (≡⇒→ (cong (λ z → g 1 z ≡ g 0 x) (sym $ refl ∣ _ ∣))
                (c 0 x)))
    (trans (cong (g 1) (O.∣∣-constant x y))
       (≡⇒→ (cong (λ z → g 1 z ≡ g 0 y) (sym $ refl ∣ _ ∣)) (c 0 y)))    ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong (g 1) (O.∣∣-constant x y)) q))
                                                                              (trans (cong (λ eq → ≡⇒→ (cong (λ z → g 1 z ≡ g 0 x) eq) (c 0 x))
                                                                                      sym-refl) $
                                                                               trans (cong (λ eq → ≡⇒→ eq (c 0 x)) $
                                                                                      cong-refl _) $
                                                                               cong (_$ c 0 x) ≡⇒→-refl)
                                                                              (trans (cong (λ eq → ≡⇒→ (cong (λ z → g 1 z ≡ g 0 y) eq) (c 0 y))
                                                                                      sym-refl) $
                                                                               trans (cong (λ eq → ≡⇒→ eq (c 0 y)) $
                                                                                      cong-refl _) $
                                                                               cong (_$ c 0 y) ≡⇒→-refl) ⟩
  trans (sym (c 0 x)) (trans (cong (g 1) (O.∣∣-constant x y)) (c 0 y))   ≡⟨⟩

  trans (sym (cong (f ∘ _≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ x)))
    (trans (cong (f ∘ _≃_.to N.∥∥≃∥∥ ∘ ∣_∣) (O.∣∣-constant x y))
       (cong (f ∘ _≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ y)))                          ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                              (sym $ cong-∘ _ _ _)
                                                                              (cong₂ trans
                                                                                 (sym $ cong-∘ _ _ _)
                                                                                 (sym $ cong-∘ _ _ _)) ⟩
  trans (sym (cong f (cong (_≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ x))))
    (trans (cong f (cong (_≃_.to N.∥∥≃∥∥ ∘ ∣_∣) (O.∣∣-constant x y)))
       (cong f (cong (_≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ y))))                     ≡⟨ trans (cong₂ trans
                                                                                     (sym $ cong-sym _ _)
                                                                                     (sym $ cong-trans _ _ _)) $
                                                                            sym $ cong-trans _ _ _ ⟩
  cong f
    (trans (sym (cong (_≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ x)))
      (trans (cong (_≃_.to N.∥∥≃∥∥ ∘ ∣_∣) (O.∣∣-constant x y))
         (cong (_≃_.to N.∥∥≃∥∥) (C.∣∣≡∣∣ y))))                           ≡⟨ cong (cong f) $
                                                                            mono₁ 1 T.truncation-is-proposition _ _ ⟩∎
  cong f (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)                       ∎
  where
  oi = O.∥∥₁-out-^≃∥∥₁-in-^

------------------------------------------------------------------------
-- Lenses, defined as getters with coherently constant fibres

-- The lens type family.

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹_)

-- Some derived definitions.

module Lens {A : Set a} {B : Set b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- The family of fibres of the getter is coherently constant.

  get⁻¹-coherently-constant : Coherently-constant (get ⁻¹_)
  get⁻¹-coherently-constant = proj₂ l

  -- All the getter's fibres are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant b₁ b₂ =
    ≡⇒≃ (get⁻¹-coherently-constant .property b₁ b₂)

  -- A setter.

  set : A → B → A
  set a b =                    $⟨ _≃_.to (get⁻¹-constant (get a) b) ⟩
    (get ⁻¹ get a → get ⁻¹ b)  ↝⟨ _$ (a , refl _) ⟩
    get ⁻¹ b                   ↝⟨ proj₁ ⟩□
    A                          □

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens is pointwise equivalent to Higher.Lens (assuming univalence).

Higher-lens≃Lens :
  {A : Set a} {B : Set b} →
  Block "Higher-lens≃Lens" →
  Univalence (lsuc (a ⊔ b)) →
  Higher.Lens A B ≃ Lens A B
Higher-lens≃Lens {a = a} {A = A} {B = B} ⊠ univ =
  Higher.Lens A B                                                    ↔⟨⟩

  (∃ λ (get : A → B) → ∃ λ (H : Pow a ∥ B ∥) → (get ⁻¹_) ≡ H ∘ ∣_∣)  ↝⟨ (∃-cong λ _ → Σ-cong (∥∥→≃ univ) λ _ → F.id) ⟩

  (∃ λ (get : A → B) →
   ∃ λ ((H , _) : ∃ λ (H : Pow a B) → Coherently-constant H) →
     (get ⁻¹_) ≡ H)                                                  ↔⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (get : A → B) → ∃ λ (H : Pow a B) →
     Coherently-constant H × (get ⁻¹_) ≡ H)                          ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-cong₁ λ eq → ≡⇒↝ _ $
                                                                         cong Coherently-constant $ sym eq) ⟩
  (∃ λ (get : A → B) → ∃ λ (H : Pow a B) →
     Coherently-constant (get ⁻¹_) × (get ⁻¹_) ≡ H)                  ↔⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (get : A → B) → Coherently-constant (get ⁻¹_) ×
   ∃ λ (H : Pow a B) → (get ⁻¹_) ≡ H)                                ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                                         _⇔_.to contractible⇔↔⊤ (other-singleton-contractible _)) ⟩□
  (∃ λ (get : A → B) → Coherently-constant (get ⁻¹_))                □

-- The equivalence preserves getters and setters.

Higher-lens≃Lens-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (bl : Block "Higher-lens≃Lens")
  (univ : Univalence (lsuc (a ⊔ b))) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Higher-lens≃Lens bl univ))
Higher-lens≃Lens-preserves-getters-and-setters {A = A} {B = B} bl univ =
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (Higher-lens≃Lens bl univ))
    (λ l → get-lemma bl l , set-lemma bl l)
  where
  get-lemma :
    ∀ bl (l : Higher.Lens A B) →
    Lens.get (_≃_.to (Higher-lens≃Lens bl univ) l) ≡ Higher.Lens.get l
  get-lemma ⊠ _ = refl _

  set-lemma :
    ∀ bl (l : Higher.Lens A B) →
    Lens.set (_≃_.to (Higher-lens≃Lens bl univ) l) ≡ Higher.Lens.set l
  set-lemma bl@⊠ l = ⟨ext⟩ λ a → ⟨ext⟩ λ b →
    Lens.set (_≃_.to (Higher-lens≃Lens bl univ) l) a b               ≡⟨⟩

    proj₁ (≡⇒→ (≡⇒→ (cong Coherently-constant (sym get⁻¹-≡))
                    (proj₂ (_≃_.to (∥∥→≃ univ) H))
                    .property (get a) b)
               (a , refl (get a)))                                   ≡⟨ cong (λ (c : Coherently-constant (get ⁻¹_)) →
                                                                                proj₁ (≡⇒→ (c .property (get a) b) (a , refl _))) $ sym $
                                                                        subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
    proj₁ (≡⇒→ (subst Coherently-constant (sym get⁻¹-≡)
                  (proj₂ (_≃_.to (∥∥→≃ univ) H))
                  .property (get a) b)
               (a , refl (get a)))                                   ≡⟨ cong (λ (c : Constant (get ⁻¹_)) →
                                                                                proj₁ (≡⇒→ (c (get a) b) (a , refl _)))
                                                                        subst-Coherently-property ⟩
    proj₁ (≡⇒→ (subst Constant (sym get⁻¹-≡)
                  (proj₂ (_≃_.to (∥∥→≃ univ) H) .property)
                  (get a) b)
               (a , refl (get a)))                                   ≡⟨ cong (λ c → proj₁ (≡⇒→ (subst Constant (sym get⁻¹-≡) c (get a) b)
                                                                                             (a , refl _))) $
                                                                        proj₂-to-∥∥→≃-property≡ univ ⟩
    proj₁ (≡⇒→ (subst Constant (sym get⁻¹-≡)
                  (proj₁-to-∥∥→≃-constant univ H)
                  (get a) b)
               (a , refl (get a)))                                   ≡⟨ cong (λ eq → proj₁ (≡⇒→ eq (a , refl _))) $
                                                                        trans (cong (_$ b) $ sym $
                                                                               push-subst-application _ _) $
                                                                        sym $ push-subst-application _ _ ⟩
    proj₁ (≡⇒→ (subst (λ f → f (get a) ≡ f b) (sym get⁻¹-≡)
                  (proj₁-to-∥∥→≃-constant univ H (get a) b))
               (a , refl (get a)))                                   ≡⟨ cong (λ eq → proj₁ (≡⇒→ eq (a , refl _))) $
                                                                        subst-in-terms-of-trans-and-cong ⟩
    proj₁ (≡⇒→ (trans (sym (cong (_$ get a) (sym get⁻¹-≡)))
                  (trans (proj₁-to-∥∥→≃-constant univ H (get a) b)
                     (cong (_$ b) (sym get⁻¹-≡))))
               (a , refl (get a)))                                   ≡⟨⟩

    proj₁ (≡⇒→ (trans (sym (cong (_$ get a) (sym get⁻¹-≡)))
                  (trans (cong H (T.truncation-is-proposition _ _))
                     (cong (_$ b) (sym get⁻¹-≡))))
               (a , refl (get a)))                                   ≡⟨ cong (λ f → proj₁ (f (a , refl _))) $
                                                                        ≡⇒↝-trans equivalence ⟩
    proj₁ (≡⇒→ (trans (cong H (T.truncation-is-proposition _ _))
                  (cong (_$ b) (sym get⁻¹-≡)))
             (≡⇒→ (sym (cong (_$ get a) (sym get⁻¹-≡)))
                (a , refl (get a))))                                 ≡⟨ cong (λ f → proj₁ (f (≡⇒→ (sym (cong (_$ get a) (sym get⁻¹-≡)))
                                                                                                (a , refl _)))) $
                                                                        ≡⇒↝-trans equivalence ⟩
    proj₁ (≡⇒→ (cong (_$ b) (sym get⁻¹-≡))
             (≡⇒→ (cong H (T.truncation-is-proposition _ _))
                (≡⇒→ (sym (cong (_$ get a) (sym get⁻¹-≡)))
                   (a , refl (get a)))))                             ≡⟨ cong₂ (λ p q → proj₁ (≡⇒→ p
                                                                                                (≡⇒→ (cong H (T.truncation-is-proposition _ _))
                                                                                                   (≡⇒→ q (a , refl _)))))
                                                                          (cong-sym _ _)
                                                                          (trans (cong sym $ cong-sym _ _) $
                                                                           sym-sym _) ⟩
    proj₁ (≡⇒→ (sym $ cong (_$ b) get⁻¹-≡)
             (≡⇒→ (cong H (T.truncation-is-proposition _ _))
                (≡⇒→ (cong (_$ get a) get⁻¹-≡)
                   (a , refl (get a)))))                             ≡⟨ cong (λ f → proj₁ (f (≡⇒→ (cong H (T.truncation-is-proposition _ _))
                                                                                                (≡⇒→ (cong (_$ get a) get⁻¹-≡)
                                                                                                   (a , refl _))))) $
                                                                        ≡⇒↝-sym equivalence ⟩
    proj₁ (_≃_.from (≡⇒≃ (cong (_$ b) get⁻¹-≡))
             (≡⇒→ (cong H (T.truncation-is-proposition _ _))
                (≡⇒→ (cong (_$ get a) get⁻¹-≡)
                   (a , refl (get a)))))                             ≡⟨⟩

    set a b                                                          ∎
    where
    open Higher.Lens l
