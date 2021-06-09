------------------------------------------------------------------------
-- Small coinductive higher lenses
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Small
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id)

open import Bijection equality-with-J as B using (_↔_)
import Coherently-constant eq as CC
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq using (∥_∥)
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹; ∣_∣)
open import Preimage equality-with-J as Preimage using (_⁻¹_)
open import Tactic.Sigma-cong equality-with-J
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher
import Lens.Non-dependent.Higher.Combinators eq as HC
import Lens.Non-dependent.Higher.Capriotti eq as Capriotti
import Lens.Non-dependent.Higher.Coinductive eq as Coinductive
open import Lens.Non-dependent.Higher.Coherently.Coinductive eq
import Lens.Non-dependent.Higher.Coherently.Not-coinductive eq as NC

private
  variable
    a b c d p q : Level
    A B C       : Type a
    P           : A → Type p
    z           : A
    n           : ℕ

------------------------------------------------------------------------
-- Constant-≃

-- A variant of Constant for type-valued functions.

Constant-≃ :
  {A : Type a} →
  (A → Type p) → Type (a ⊔ p)
Constant-≃ P = ∀ x y → P x ≃ P y

-- Constant and Constant-≃ are pointwise equivalent (assuming
-- univalence).

Constant≃Constant-≃ :
  {P : A → Type p} →
  Univalence p → Constant P ≃ Constant-≃ P
Constant≃Constant-≃ univ =
  ∀-cong ext λ _ →
  ∀-cong ext λ _ →
  ≡≃≃ univ

-- The right-to-left direction of Constant-≃-get-⁻¹-≃ (which is
-- defined below).

Constant-≃-get-⁻¹-≃⁻¹ :
  {get : A → B} →
  (∃ λ (set : A → B → A) →
   ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
   ∀ b₁ b₂ →
   let f : get ⁻¹ b₁ → get ⁻¹ b₂
       f = λ (a , _) → set a b₂ , get-set a b₂
   in
   Is-equivalence f) →
  Constant-≃ (get ⁻¹_)
Constant-≃-get-⁻¹-≃⁻¹ (_ , _ , eq) b₁ b₂ = Eq.⟨ _ , eq b₁ b₂ ⟩

-- Constant-≃ (get ⁻¹_) can be expressed in terms of a "setter" and a
-- "get-set" law that form a family of equivalences in a certain way.
--
-- This lemma was suggested by Andrea Vezzosi when we discussed
-- coinductive lenses with erased "proofs".
--
-- The left-to-right direction of the lemma is not blocked, but the
-- rest is.

Constant-≃-get-⁻¹-≃ :
  Block "Constant-≃-get-⁻¹-≃" →
  {A : Type a} {B : Type b} {get : A → B} →
  Constant-≃ (get ⁻¹_) ≃
  (∃ λ (set : A → B → A) →
   ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
   ∀ b₁ b₂ →
   let f : get ⁻¹ b₁ → get ⁻¹ b₂
       f = λ (a , _) → set a b₂ , get-set a b₂
   in
   Is-equivalence f)
Constant-≃-get-⁻¹-≃ bl {A = A} {B = B} {get = get} =
  inverse (equiv₃ bl)
  where
  equiv₁ =
    Constant-≃ (get ⁻¹_)                                            ↔⟨⟩

    (∀ b₁ b₂ → get ⁻¹ b₁ ≃ get ⁻¹ b₂)                               ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        Eq.≃-as-Σ) ⟩
    (∀ b₁ b₂ →
     ∃ λ (f : get ⁻¹ b₁ → get ⁻¹ b₂) →
     Is-equivalence f)                                              ↔⟨ Π-comm ⟩

    (∀ b₂ b₁ →
     ∃ λ (f : get ⁻¹ b₁ → get ⁻¹ b₂) →
     Is-equivalence f)                                              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        Σ-cong-id currying) ⟩
    (∀ b₂ b₁ →
     ∃ λ (f : ∀ a → get a ≡ b₁ → get ⁻¹ b₂) →
     Is-equivalence (uncurry f))                                    ↔⟨ (∀-cong ext λ _ →
                                                                        ΠΣ-comm) ⟩
    (∀ b₂ →
     ∃ λ (f : ∀ b₁ a → get a ≡ b₁ → get ⁻¹ b₂) →
     ∀ b₁ → Is-equivalence (uncurry (f b₁)))                        ↝⟨ (∀-cong ext λ _ →
                                                                        Σ-cong-id Π-comm) ⟩
    (∀ b₂ →
     ∃ λ (f : ∀ a b₁ → get a ≡ b₁ → get ⁻¹ b₂) →
     ∀ b₁ → Is-equivalence (uncurry (flip f b₁)))                   ↝⟨ (∀-cong ext λ _ →
                                                                        Σ-cong (∀-cong ext λ _ → inverse $ ∀-intro {k = equivalence} ext _) λ f →
                                                                        ∀-cong ext λ b₁ →
                                                                        Is-equivalence-cong {k = equivalence} ext λ (a , eq) →
        uncurry (f a) (b₁ , eq)                                           ≡⟨ cong (uncurry (f a)) $ sym $
                                                                             proj₂ (other-singleton-contractible _) _ ⟩∎
        uncurry (f a) (get a , refl _)                                    ∎) ⟩

    (∀ b₂ →
     ∃ λ (f : A → get ⁻¹ b₂) →
     ∀ b₁ → Is-equivalence (f ∘ proj₁))                             ↔⟨ ΠΣ-comm ⟩

    (∃ λ (f : (b : B) → A → get ⁻¹ b) →
     ∀ b₂ b₁ → Is-equivalence (f b₂ ∘ proj₁))                       ↝⟨ Σ-cong-refl Π-comm (λ _ → Π-comm) ⟩

    (∃ λ (f : A → (b : B) → get ⁻¹ b) →
     ∀ b₁ b₂ → Is-equivalence ((_$ b₂) ∘ f ∘ proj₁))                ↝⟨ Σ-cong-refl (∀-cong ext λ _ → ΠΣ-comm) (λ _ → Eq.id) ⟩

    (∃ λ (f : A → ∃ λ (set : B → A) → (b : B) → get (set b) ≡ b) →
     ∀ b₁ b₂ → Is-equivalence (Σ-map (_$ b₂) (_$ b₂) ∘ f ∘ proj₁))  ↝⟨ Σ-cong-id ΠΣ-comm ⟩

    (∃ λ ((set , get-set) :
          ∃ λ (set : A → B → A) →
            (a : A) (b : B) → get (set a b) ≡ b) →
     ∀ b₁ b₂ → Is-equivalence λ (a , _) → set a b₂ , get-set a b₂)  ↔⟨ inverse Σ-assoc ⟩□

    (∃ λ (set : A → B → A) →
     ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
     ∀ b₁ b₂ → Is-equivalence λ (a , _) → set a b₂ , get-set a b₂)  □

  equiv₂ =
    Eq.with-other-function
      (inverse equiv₁)
      Constant-≃-get-⁻¹-≃⁻¹
      (λ (set , get-set , _) → ⟨ext⟩ λ b₁ → ⟨ext⟩ λ b₂ →
         Eq.lift-equality ext $ ⟨ext⟩ λ (a , _) →
           subst (λ _ → get ⁻¹ b₂) _ (set a b₂ , get-set a b₂)  ≡⟨ subst-const _ ⟩∎
           (set a b₂ , get-set a b₂)                            ∎)

  equiv₃ : Unit → _ ≃ _
  equiv₃ _ ._≃_.to             = _≃_.to equiv₂
  equiv₃ ⊠ ._≃_.is-equivalence = _≃_.is-equivalence equiv₂

-- Constant-≃-get-⁻¹-≃ computes in a certain way.

_ :
  ∀ {bl : Block "Constant-≃-get-⁻¹-≃"}
    {get : A → B} {set : A → B → A}
    {get-set : (a : A) (b : B) → get (set a b) ≡ b}
    {eq :
     ∀ b₁ b₂ →
     let f : get ⁻¹ b₁ → get ⁻¹ b₂
         f = λ (a , _) → set a b₂ , get-set a b₂
     in
     Is-equivalence f}
    {b₁ b₂} →
  _≃_.to (_≃_.from (Constant-≃-get-⁻¹-≃ bl) (set , get-set , eq) b₁ b₂) ≡
  (λ (a , _) → set a b₂ , get-set a b₂)
_ = refl _

------------------------------------------------------------------------
-- Coherently-constant

-- Coherently constant type-valued functions.

Coherently-constant :
  Univalence p →
  {A : Type a} → (A → Type p) → Type (a ⊔ p)
Coherently-constant univ =
  Coherently
    Constant-≃
    (λ P c → O.rec′ P (λ x y → ≃⇒≡ univ (c x y)))

-- Two variants of Coherently-constant are pointwise equivalent
-- (when applicable, assuming univalence).

Coinductive-coherently-constant≃Coherently-constant :
  {A : Type a} {P : A → Type p} →
  Univalence (a ⊔ lsuc p) →
  (univ : Univalence p) →
  Coinductive.Coherently-constant P ≃ Coherently-constant univ P
Coinductive-coherently-constant≃Coherently-constant univ′ univ =
  Coherently-cong
    univ′
    (λ _ → Constant≃Constant-≃ univ)
    (λ _ _ → refl _)

-- Two variants of Coherently-constant are pointwise equivalent
-- (when applicable, assuming univalence).

Coherently-constant≃Coherently-constant :
  {A : Type a} {P : A → Type p} →
  Univalence (a ⊔ lsuc p) →
  (univ : Univalence p) →
  CC.Coherently-constant P ≃ Coherently-constant univ P
Coherently-constant≃Coherently-constant {P = P} univ′ univ =
  CC.Coherently-constant P           ↝⟨ Coinductive.Coherently-constant≃Coherently-constant univ′ ⟩
  Coinductive.Coherently-constant P  ↝⟨ Coinductive-coherently-constant≃Coherently-constant univ′ univ ⟩□
  Coherently-constant univ P         □

-- A map lemma for Coherently-constant.

Coherently-constant-map :
  {P : A → Type p} {Q : B → Type q}
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
                    (O.∣∣-constant x y) (P≃Q x))                         ≡⟨ Eq.to-subst ⟩

          subst (λ z → O.rec′ P g (O.∥∥¹-map f z) → O.rec′ Q h z)
            (O.∣∣-constant x y) (_≃_.to (P≃Q x))                         ≡⟨ (⟨ext⟩ λ _ → subst-→) ⟩

          subst (O.rec′ Q h) (O.∣∣-constant x y) ∘
          _≃_.to (P≃Q x) ∘
          subst (O.rec′ P g ∘ O.∥∥¹-map f) (sym (O.∣∣-constant x y))     ≡⟨ cong₂ (λ f g → f ∘ _≃_.to (P≃Q x) ∘ g)
                                                                              (⟨ext⟩ λ q → subst-∘ P.id (O.rec′ Q h) (O.∣∣-constant x y) {p = q})
                                                                              (⟨ext⟩ λ p →
                                                                               trans (subst-∘ P.id (O.rec′ P g ∘ O.∥∥¹-map f)
                                                                                        (sym (O.∣∣-constant x y)) {p = p}) $
                                                                               cong (λ eq → subst P.id eq p) $
                                                                               trans (cong-sym _ _) $
                                                                               cong sym $ sym $ cong-∘ _ _ _) ⟩
          subst P.id (cong (O.rec′ Q h) (O.∣∣-constant x y)) ∘
          _≃_.to (P≃Q x) ∘
          subst P.id (sym (cong (O.rec′ P g)
                             (cong (O.∥∥¹-map f) (O.∣∣-constant x y))))  ≡⟨ cong₂ (λ p q → subst P.id p ∘ _≃_.to (P≃Q x) ∘ subst P.id (sym q))
                                                                              O.rec-∣∣-constant
                                                                              (trans (cong (cong (O.rec′ P g)) O.rec-∣∣-constant) $
                                                                               O.rec-∣∣-constant) ⟩

          subst P.id (h x y) ∘
          _≃_.to (P≃Q x) ∘
          subst P.id (sym (g (f x) (f y)))                               ≡⟨ cong₂ (λ p q → p ∘ _≃_.to (P≃Q x) ∘ q)
                                                                              (trans (⟨ext⟩ λ _ → subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                               cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₂) _)
                                                                              (trans (⟨ext⟩ λ _ → subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                               cong _≃_.from $ _≃_.right-inverse-of (≡≃≃ univ₁) _) ⟩
          _≃_.to (P≃Q y) ∘
          _≃_.to (c .property (f x) (f y)) ∘
          _≃_.from (P≃Q x) ∘
          _≃_.to (P≃Q x) ∘
          _≃_.from (c .property (f x) (f y))                             ≡⟨ (⟨ext⟩ λ _ → cong (_≃_.to (P≃Q y) ∘ _≃_.to (c .property (f x) (f y))) $
                                                                            _≃_.left-inverse-of (P≃Q x) _) ⟩
          _≃_.to (P≃Q y) ∘
          _≃_.to (c .property (f x) (f y)) ∘
          _≃_.from (c .property (f x) (f y))                             ≡⟨ (⟨ext⟩ λ _ → cong (_≃_.to (P≃Q y)) $
                                                                             _≃_.right-inverse-of (c .property (f x) (f y)) _) ⟩∎
          _≃_.to (P≃Q y)                                                 ∎))
    (c .coherent)
  where
  g = λ x y → ≃⇒≡ univ₁ (c .property x y)
  h = λ x y → ≃⇒≡ univ₂ ((P≃Q y F.∘ c .property (f x) (f y)) F.∘
                         inverse (P≃Q x))

private

  -- A lemma used below.

  elim-Σ-≡,≡→≡-∣∣-constant :
    ∀ (e : O.Elim (λ x → P x → A)) {x y p} →

    let p′ = subst P (O.∣∣-constant x y) p in

    cong (uncurry $ O.elim e) (Σ-≡,≡→≡ (O.∣∣-constant x y) (refl p′)) ≡

    trans
      (O.∣∣ʳ e x p                                            ≡⟨ cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _ ⟩

       O.∣∣ʳ e x
         (subst P (sym (O.∣∣-constant x y))
            (subst P (O.∣∣-constant x y) p))                  ≡⟨ sym $ subst-→-domain _ _ ⟩∎

       subst (λ x → P x → A) (O.∣∣-constant x y) (O.∣∣ʳ e x)
         (subst P (O.∣∣-constant x y) p)                      ∎)
      (cong (_$ p′) (e .O.∣∣-constantʳ x y))

  elim-Σ-≡,≡→≡-∣∣-constant {P = P} {A = A} e {x = x} {y = y} {p = p} =

    cong (uncurry $ O.elim e)
      (Σ-≡,≡→≡ (O.∣∣-constant x y) (refl _))                 ≡⟨ elim¹
                                                                  (λ eq →
                                                                     cong (uncurry $ O.elim e) (Σ-≡,≡→≡ eq (refl _)) ≡
                                                                     trans
                                                                       (trans (cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _)
                                                                          (sym $ subst-→-domain _ _))
                                                                       (cong (_$ subst P eq p) (dcong (O.elim e) eq)))
                                                                  (
      cong (uncurry $ O.elim e)
        (Σ-≡,≡→≡ (refl ∣ x ∣) (refl _))                            ≡⟨ cong (cong (uncurry $ O.elim e)) Σ-≡,≡→≡-refl-refl ⟩

      cong (uncurry $ O.elim e)
        (cong (∣ x ∣ ,_) (sym (subst-refl _ _)))                   ≡⟨ cong-∘ _ _ _ ⟩

      cong (O.elim e ∣ x ∣) (sym (subst-refl _ _))                 ≡⟨⟩

      cong (O.∣∣ʳ e x) (sym (subst-refl _ _))                      ≡⟨ sym $
                                                                      trans (cong (flip trans _) $
                                                                             trans (sym $ trans-assoc _ _ _) $
                                                                             trans (cong (flip trans _) $
                                                                                    trans-[trans]-sym _ _) $
                                                                             trans (sym $ trans-assoc _ _ _) $
                                                                             cong (flip trans _) $
                                                                             trans-[trans]-sym _ _) $
                                                                      trans-[trans-sym]- _ _ ⟩
      trans
        (trans (trans (trans (cong (O.∣∣ʳ e x)
                                (sym (subst-refl _ _)))
                         (cong (O.∣∣ʳ e x)
                            (sym (subst-refl _ _))))
                  (cong (O.∣∣ʳ e x) $
                   sym (cong (flip (subst P) _) sym-refl)))
           (trans
              (sym $
               cong (O.∣∣ʳ e x) $
               sym (cong (flip (subst P) _) sym-refl))
              (trans
                 (sym $
                  cong (O.∣∣ʳ e x) (sym (subst-refl _ _)))
                 (sym $
                  cong (_$ subst P (refl _) p)
                    (subst-refl _ _)))))
        (cong (_$ subst P (refl _) p) (subst-refl _ _))            ≡⟨ sym $
                                                                      cong (flip trans _) $
                                                                      cong₂ trans
                                                                        (trans (cong (cong (O.∣∣ʳ e x)) $ sym-trans _ _) $
                                                                         trans (cong-trans _ _ _) $
                                                                         cong (flip trans _) $
                                                                         trans (cong (cong (O.∣∣ʳ e x)) $ sym-trans _ _) $
                                                                         cong-trans _ _ _)
                                                                        (trans (sym-trans _ _) $
                                                                         trans (cong (flip trans _) $
                                                                                trans (sym-trans _ _) $
                                                                                cong (flip trans _) $ cong sym $
                                                                                trans (sym $ cong-∘ _ _ _) $
                                                                                cong (cong (O.∣∣ʳ e x)) $ cong-sym _ _) $
                                                                         trans-assoc _ _ _) ⟩
      trans
        (trans (cong (O.∣∣ʳ e x) $ sym $
                trans (cong (flip (subst P) _) sym-refl)
                  (trans (subst-refl _ _)
                     (subst-refl _ _)))
           (sym $
            trans (cong (_$ subst P (refl _) p)
                     (subst-refl _ _))
              (trans (cong (O.∣∣ʳ e x)
                        (sym (subst-refl _ _)))
                 (cong (O.∣∣ʳ e x ∘ flip (subst P) _)
                    (sym sym-refl)))))
        (cong (_$ subst P (refl _) p) (subst-refl _ _))            ≡⟨ sym $
                                                                      cong₂ (λ eq₁ eq₂ → trans
                                                                                 (trans (cong (O.∣∣ʳ e x) $ sym eq₁) (sym eq₂))
                                                                                 (cong (_$ subst P (refl _) p) (subst-refl _ _)))
                                                                        (subst-sym-subst-refl _)
                                                                        subst-→-domain-refl ⟩
      trans
        (trans (cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _)
           (sym $ subst-→-domain _ _))
        (cong (_$ subst P (refl _) p) (subst-refl _ _))            ≡⟨ cong (trans _) $ cong (cong _) $ sym $
                                                                      dcong-refl _ ⟩∎
      trans
        (trans (cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _)
           (sym $ subst-→-domain _ _))
        (cong (_$ subst P (refl _) p)
           (dcong (O.elim e) (refl _)))                            ∎)
                                                                  _ ⟩
    trans
      (trans (cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _)
         (sym $ subst-→-domain _ _))
      (cong (_$ subst P (O.∣∣-constant x y) p)
         (dcong (O.elim e) (O.∣∣-constant x y)))             ≡⟨ cong (trans _) $ cong (cong _)
                                                                O.elim-∣∣-constant ⟩∎
    trans
      (trans (cong (O.∣∣ʳ e x) $ sym $ subst-sym-subst _)
         (sym $ subst-→-domain _ _))
      (cong (_$ subst P (O.∣∣-constant x y) p)
         (e .O.∣∣-constantʳ x y))                            ∎

-- Coherently-constant is, in a certain sense, closed under Σ.
--
-- This lemma is based on a lemma due to Paolo Capriotti (see
-- Capriotti.Coherently-constant-Σ).
--
-- TODO: Can the ".coherent" clause be simplified?

Coherently-constant-Σ :
  {P : A → Type p} {Q : ∃ P → Type q}
  (univ₁ : Univalence p)
  (univ₂ : Univalence q)
  (univ₃ : Univalence (p ⊔ q)) →
  Coherently-constant univ₁ P →
  Coherently-constant univ₂ Q →
  Coherently-constant univ₃ (λ x → ∃ λ (y : P x) → Q (x , y))
Coherently-constant-Σ {p = p} {q = q} univ₁ univ₂ univ₃ =
  Coherently-constant-Σ′ (λ _ → F.id)
  where
  Coherently-constant-Σ′ :
    {P : A → Type p} {Q : ∃ P → Type q} {R : A → Type (p ⊔ q)} →
    (∀ x → R x ≃ ∃ λ (p : P x) → Q (x , p)) →
    Coherently-constant univ₁ P →
    Coherently-constant univ₂ Q →
    Coherently-constant univ₃ R
  Coherently-constant-Σ′
    {P = P} {Q = Q} {R = R} R≃ c₁ c₂ .property x y =

    R x                          ↝⟨ R≃ _ ⟩
    (∃ λ (p : P x) → Q (x , p))  ↝⟨ (Σ-cong (c₁ .property _ _) λ _ → c₂ .property _ _) ⟩
    (∃ λ (p : P y) → Q (y , p))  ↝⟨ inverse $ R≃ _ ⟩□
    R y                          □

  Coherently-constant-Σ′ {P = P} {Q = Q} {R = R} R≃ c₁ c₂ .coherent =
    Coherently-constant-Σ′
      {P = P′}
      {Q = Q′}
      (O.elim λ where
         .O.Elim.∣∣ʳ → R≃
         .O.Elim.∣∣-constantʳ x y → Eq.lift-equality ext $ ⟨ext⟩ λ r →
           let
             p′ , q′ = _≃_.from (Σ-cong (c₁ .property _ _) λ p →
                                 c₂ .property (_ , p) _)
                                (_≃_.to (R≃ y) r)

             lemma₁ =
               subst P′ (O.∣∣-constant x y) p′               ≡⟨ subst-∘ _ _ _ ⟩
               subst P.id (cong P′ (O.∣∣-constant x y)) p′   ≡⟨ cong (λ eq → subst P.id eq _) O.rec-∣∣-constant ⟩
               subst P.id (≃⇒≡ univ₁ (c₁ .property x y)) p′  ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
               ≡⇒→ (≃⇒≡ univ₁ (c₁ .property x y)) p′         ≡⟨ cong (λ eq → _≃_.to eq p′) $ _≃_.right-inverse-of (≡≃≃ univ₁) _ ⟩∎
               _≃_.to (c₁ .property x y) p′                  ∎

             lemma₂ =
               subst (λ p → Q (y , p)) lemma₁
                 (subst Q′ (Σ-≡,≡→≡ (O.∣∣-constant x y) (refl _)) q′)    ≡⟨ cong (subst (λ p → Q (y , p)) lemma₁) $
                                                                            subst-∘ _ _ _ ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                    (cong f (Σ-≡,≡→≡ (O.∣∣-constant x y) (refl _))) q′)  ≡⟨ cong (λ eq →
                                                                                    subst (λ p → Q (y , p)) lemma₁
                                                                                      (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                                                                                             eq q′)) $
                                                                            elim-Σ-≡,≡→≡-∣∣-constant e ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                    (trans
                       (trans (cong (λ p → ∣ x , p ∣)
                                 (sym (subst-sym-subst _)))
                          (sym (subst-→-domain _ _)))
                       (cong (_$ subst P′ (O.∣∣-constant x y) p′)
                          (⟨ext⟩ λ p →
                           trans (subst-→-domain _ _)
                             (O.∣∣-constant _ (_ , p)))))
                    q′)                                                  ≡⟨ cong (λ eq →
                                                                                    subst (λ p → Q (y , p))
                                                                                      lemma₁
                                                                                      (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                                                                                         (trans
                                                                                            (trans (cong (λ p → ∣ x , p ∣)
                                                                                                      (sym (subst-sym-subst _)))
                                                                                               (sym $ subst-→-domain _ _))
                                                                                            eq)
                                                                                         q′)) $
                                                                            cong-ext
                                                                              (λ p → trans (subst-→-domain P′ {f = λ p → ∣ x , p ∣}
                                                                                              (O.∣∣-constant x y))
                                                                                       (O.∣∣-constant _ (_ , p))) ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                    (trans
                       (trans (cong (λ p → ∣ x , p ∣)
                                 (sym (subst-sym-subst _)))
                          (sym (subst-→-domain _ _)))
                       (trans (subst-→-domain _ _)
                          (O.∣∣-constant _ _)))
                    q′)                                                  ≡⟨ cong (λ eq → subst (λ p → Q (y , p))
                                                                                           lemma₁
                                                                                           (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                                                                                              eq q′)) $
                                                                            trans (trans-assoc _ _ _) $
                                                                            cong (trans (cong (λ p → ∣ x , p ∣) $ sym $ subst-sym-subst _)) $
                                                                            trans-sym-[trans] _ (O.∣∣-constant _ _) ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (subst (O.rec′ Q λ x y → ≃⇒≡ univ₂ (c₂ .property x y))
                    (trans (cong (λ p → ∣ x , p ∣)
                              (sym (subst-sym-subst _)))
                       (O.∣∣-constant _ _))
                    q′)                                                  ≡⟨ cong (λ q → subst (λ p → Q (y , p)) lemma₁ q) $
                                                                            trans (subst-∘ _ _ _) $
                                                                            cong (λ eq → subst P.id eq q′) $
                                                                            trans (cong-trans _ _ _) $
                                                                            cong₂ trans
                                                                              (cong-∘ _ _ _)
                                                                              O.rec-∣∣-constant ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (subst P.id
                    (trans
                       (cong (λ p → Q (x , p))
                          (sym (subst-sym-subst _)))
                       (≃⇒≡ univ₂ (c₂ .property _ _)))
                    q′)                                                  ≡⟨ cong (subst (λ p → Q (y , p)) lemma₁) $
                                                                            trans (subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                            trans (cong (_$ q′) $ ≡⇒↝-trans equivalence) $
                                                                            trans (cong (λ eq → _≃_.to eq (≡⇒→ (cong (λ p → Q (x , p))
                                                                                                                  (sym (subst-sym-subst _)))
                                                                                                             q′)) $
                                                                                   _≃_.right-inverse-of (≡≃≃ univ₂) _) $
                                                                            cong (_≃_.to (c₂ .property _ _)) $ sym $
                                                                            subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (_≃_.to (c₂ .property _ _) $
                  subst (λ p → Q (x , p)) (sym (subst-sym-subst _)) q′)  ≡⟨⟩

               subst (λ p → Q (y , p)) lemma₁
                 (_≃_.to (c₂ .property
                            (x , subst P′ (sym (O.∣∣-constant x y))
                                   (subst P′ (O.∣∣-constant x y) p′))
                            (y , subst P′ (O.∣∣-constant x y) p′)) $
                  subst (λ p → Q (x , p)) (sym (subst-sym-subst _)) q′)  ≡⟨ elim¹
                                                                              (λ {p″} eq →
                                                                                 subst (λ p → Q (y , p)) lemma₁
                                                                                   (_≃_.to (c₂ .property (x , p″)
                                                                                              (y , subst P′ (O.∣∣-constant x y) p′)) $
                                                                                    subst (λ p → Q (x , p)) eq q′) ≡
                                                                                 subst (λ p → Q (y , p)) lemma₁
                                                                                   (_≃_.to (c₂ .property (x , p′)
                                                                                              (y , subst P′ (O.∣∣-constant x y) p′)) q′))
                                                                              (cong (λ q → subst (λ p → Q (y , p)) lemma₁
                                                                                             (_≃_.to (c₂ .property _ _) q)) $
                                                                               subst-refl _ _)
                                                                              _ ⟩
               subst (λ p → Q (y , p)) lemma₁
                 (_≃_.to (c₂ .property
                            (x , p′)
                            (y , subst P′ (O.∣∣-constant x y) p′)) q′)   ≡⟨ elim₁
                                                                              (λ {p″} eq →
                                                                                 subst (λ p → Q (y , p)) eq
                                                                                   (_≃_.to (c₂ .property (x , p′) (y , p″)) q′) ≡
                                                                                 _≃_.to (c₂ .property _ _) q′)
                                                                              (subst-refl _ _)
                                                                              _ ⟩∎
               _≃_.to (c₂ .property
                         (x , p′)
                         (y , _≃_.to (c₁ .property x y) p′)) q′          ∎
           in
           _≃_.to (subst (λ x →
                            O.rec′ R (λ x y → ≃⇒≡ univ₃ (pr x y)) x ≃
                            ∃ λ (p : P′ x) → Q′ (x , p))
                     (O.∣∣-constant x y) (R≃ x))
                  r                                                       ≡⟨ cong (_$ r) Eq.to-subst ⟩

           subst (λ x → O.rec′ R (λ x y → ≃⇒≡ univ₃ (pr x y)) x →
                        ∃ λ (p : P′ x) → Q′ (x , p))
             (O.∣∣-constant x y) (_≃_.to (R≃ x)) r                        ≡⟨ subst-→ ⟩

           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (_≃_.to (R≃ x)
                (subst (O.rec′ R (λ x y → ≃⇒≡ univ₃ (pr x y)))
                   (sym (O.∣∣-constant x y)) r))                          ≡⟨ cong (subst (λ x → ∃ λ p → Q′ (x , p)) (O.∣∣-constant x y)) $
                                                                             cong (_≃_.to (R≃ x)) $
                                                                             trans (subst-∘ _ _ _) $
                                                                             cong (flip (subst P.id) r) $
                                                                             trans (cong-sym _ _) $
                                                                             cong sym O.rec-∣∣-constant ⟩
           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (_≃_.to (R≃ x) (subst P.id (sym (≃⇒≡ univ₃ (pr x y))) r))    ≡⟨ cong (subst (λ x → ∃ λ p → Q′ (x , p)) (O.∣∣-constant x y)) $
                                                                             cong (_≃_.to (R≃ x)) $
                                                                             trans (subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                             cong (λ eq → _≃_.from eq r) $ _≃_.right-inverse-of (≡≃≃ univ₃) _ ⟩
           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (_≃_.to (R≃ x) (_≃_.from (pr x y) r))                        ≡⟨⟩

           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (_≃_.to (R≃ x) $ _≃_.from (R≃ x) $
              _≃_.from (Σ-cong (c₁ .property _ _) λ _ →
                        c₂ .property _ _) $
              _≃_.to (R≃ y) r)                                            ≡⟨⟩

           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (_≃_.to (R≃ x) (_≃_.from (R≃ x) (p′ , q′)))                  ≡⟨ cong (subst (λ x → ∃ λ p → Q′ (x , p)) (O.∣∣-constant x y)) $
                                                                             _≃_.right-inverse-of (R≃ x) _ ⟩
           subst (λ x → ∃ λ (p : P′ x) → Q′ (x , p)) (O.∣∣-constant x y)
             (p′ , q′)                                                    ≡⟨ push-subst-pair _ _ ⟩

           subst P′ (O.∣∣-constant x y) p′ ,
           subst Q′ (Σ-≡,≡→≡ (O.∣∣-constant x y) (refl _)) q′             ≡⟨ Σ-≡,≡→≡ lemma₁ lemma₂ ⟩

           _≃_.to (c₁ .property _ _) p′ ,
           _≃_.to (c₂ .property _ _) q′                                   ≡⟨⟩

           _≃_.to (Σ-cong (c₁ .property _ _) λ p →
                   c₂ .property (x , p) _)
             (_≃_.from (Σ-cong (c₁ .property _ _) λ _ →
                        c₂ .property _ _)
                (_≃_.to (R≃ y) r))                                        ≡⟨ _≃_.right-inverse-of
                                                                               (Σ-cong (c₁ .property _ _) λ p →
                                                                                c₂ .property (_ , p) _)
                                                                               _ ⟩∎
           _≃_.to (R≃ y) r                                                ∎)
      (c₁ .coherent)
      (Coherently-constant-map
         univ₂ univ₂ f (λ _ → F.id)
         (c₂ .coherent))

    where

    mutual

      P′ = O.rec′ P (λ x y → ≃⇒≡ univ₁ (c₁ .property x y))
      Q′ = O.rec′ Q (λ x y → ≃⇒≡ univ₂ (c₂ .property x y)) ∘ f

      e = λ where
        .O.Elim.∣∣ʳ x p → ∣ x , p ∣
        .O.Elim.∣∣-constantʳ x y → ⟨ext⟩ λ p →
          subst (λ x → P′ x → ∥ ∃ P ∥¹) (O.∣∣-constant x y)
             (λ p → ∣ x , p ∣) p                             ≡⟨ subst-→-domain _ _ ⟩

          ∣ x , subst P′ (sym (O.∣∣-constant x y)) p ∣       ≡⟨ O.∣∣-constant _ _ ⟩∎

          ∣ y , p ∣                                          ∎

      f = uncurry $ O.elim e

    pr : ∀ _ _ → _
    pr x y =
      (inverse (R≃ y) F.∘
       (Σ-cong (c₁ .property _ _) λ _ → c₂ .property _ _)) F.∘
      R≃ x

private

  -- A unit test that ensures that Coherently-constant-Σ satisfies a
  -- certain definitional equality.

  _ :
    ∀ {P : A → Type p} {Q : ∃ P → Type q}
      {univ₁ : Univalence p}
      {univ₂ : Univalence q}
      {univ₃ : Univalence (p ⊔ q)}
      {c₁ : Coherently-constant univ₁ P}
      {c₂ : Coherently-constant univ₂ Q}
      {x y} →
    _≃_.to (Coherently-constant-Σ
              univ₁ univ₂ univ₃ c₁ c₂ .property x y) ≡
    Σ-map (_≃_.to (c₁ .property _ _)) (_≃_.to (c₂ .property _ _))
  _ = refl _

-- A different proof of Coherently-constant-Σ, with three extra
-- univalence assumptions.
--
-- This proof does not, at the time of writing, satisfy the
-- definitional equality above (rephrased in an obvious way).

Coherently-constant-Σ′ :
  {A : Type a} {P : A → Type p} {Q : ∃ P → Type q}
  (univ₁ : Univalence p)
  (univ₂ : Univalence q)
  (univ₃ : Univalence (p ⊔ q)) →
  Univalence (a ⊔ lsuc p) →
  Univalence (a ⊔ p ⊔ lsuc q) →
  Univalence (a ⊔ lsuc (p ⊔ q)) →
  Coherently-constant univ₁ P →
  Coherently-constant univ₂ Q →
  Coherently-constant univ₃ (λ x → ∃ λ (y : P x) → Q (x , y))
Coherently-constant-Σ′ {P = P} {Q = Q}
  univ₁ univ₂ univ₃ univ₄ univ₅ univ₆ =
  curry
    (Coherently-constant univ₁ P × Coherently-constant univ₂ Q    ↔⟨ inverse
                                                                       (Coherently-constant≃Coherently-constant univ₄ univ₁ ×-cong
                                                                        Coherently-constant≃Coherently-constant univ₅ univ₂) ⟩
     CC.Coherently-constant P × CC.Coherently-constant Q          ↝⟨ uncurry Capriotti.Coherently-constant-Σ ⟩
     CC.Coherently-constant (λ x → ∃ λ (y : P x) → Q (x , y))     ↔⟨ Coherently-constant≃Coherently-constant univ₆ univ₃ ⟩□
     Coherently-constant univ₃ (λ x → ∃ λ (y : P x) → Q (x , y))  □)

------------------------------------------------------------------------
-- The lens type family

-- Small coinductive lenses, based on an idea due to Paolo Capriotti.
--
-- The lenses are defined as a record type to make it easier for Agda
-- to infer the argument univ from a value of type Lens univ A B.

record Lens (univ : Univalence (a ⊔ b)) (A : Type a) (B : Type b) :
            Type (a ⊔ b) where
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

  -- The setter could have been defined using Constant-≃-get-⁻¹-≃.

  set≡ :
    ∀ bl →
    set ≡ proj₁ (_≃_.to (Constant-≃-get-⁻¹-≃ bl) get⁻¹-constant)
  set≡ ⊠ = refl _

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    {univ : Univalence (a ⊔ b)} →
    Has-getter-and-setter (Lens {a = a} {b = b} univ)
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens can be expressed as a Σ-type.

Lens-as-Σ :
  {A : Type a} {B : Type b} {univ : Univalence (a ⊔ b)} →
  Lens univ A B ≃
  (∃ λ (get : A → B) → Coherently-constant univ (get ⁻¹_))
Lens-as-Σ = Eq.↔→≃
  (λ l → Lens.get l , Lens.get⁻¹-coherently-constant l)
  (λ (g , c) → record { get = g; get⁻¹-coherently-constant = c })
  refl
  refl

-- Lens is pointwise equivalent to Coinductive.Lens (assuming
-- univalence).

Coinductive-lens≃Lens :
  Block "Coinductive-lens≃Lens" →
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  Coinductive.Lens A B ≃ Lens univ A B
Coinductive-lens≃Lens ⊠ {A = A} {B = B} univ₁ univ₂ =
  Coinductive.Lens A B                                             ↔⟨⟩
  (∃ λ (get : A → B) → Coinductive.Coherently-constant (get ⁻¹_))  ↝⟨ (∃-cong λ _ →
                                                                       Coinductive-coherently-constant≃Coherently-constant univ₁ univ₂) ⟩
  (∃ λ (get : A → B) → Coherently-constant univ₂ (get ⁻¹_))        ↝⟨ inverse Lens-as-Σ ⟩□
  Lens univ₂ A B                                                   □

-- The equivalence preserves getters and setters.

Coinductive-lens≃Lens-preserves-getters-and-setters :
  (bl : Block "Coinductive-lens≃Lens")
  {A : Type a} {B : Type b}
  (univ₁ : Univalence (lsuc (a ⊔ b)))
  (univ₂ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Coinductive-lens≃Lens bl univ₁ univ₂))
Coinductive-lens≃Lens-preserves-getters-and-setters ⊠ univ₁ univ₂ =
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (Coinductive-lens≃Lens ⊠ univ₁ univ₂))
    (λ _ → refl _ , refl _)

private

  -- A lemma used to implement Higher-lens≃Lens and
  -- Higher-lens≃Lens-preserves-getters-and-setters.

  Higher-lens≃Lens′ :
    Block "Higher-lens≃Lens" →
    {A : Type a} {B : Type b} →
    Univalence (lsuc (a ⊔ b)) →
    (univ : Univalence (a ⊔ b)) →
    ∃ λ (eq : Higher.Lens A B ≃ Lens univ A B) →
    Preserves-getters-and-setters-⇔ A B (_≃_.logical-equivalence eq)
  Higher-lens≃Lens′ ⊠ {A = A} {B = B} univ₁ univ₂ =
    block λ b →

      (Higher.Lens A B       ↝⟨ inverse $ Capriotti.Lens≃Higher-lens b univ₂ ⟩
       Capriotti.Lens A B    ↝⟨ Coinductive.Higher-lens≃Lens b univ₁ ⟩
       Coinductive.Lens A B  ↝⟨ Coinductive-lens≃Lens b univ₁ univ₂ ⟩□
       Lens univ₂ A B        □)
    , Preserves-getters-and-setters-⇔-∘
        {f = _≃_.logical-equivalence
               (Coinductive-lens≃Lens b univ₁ univ₂) F.∘
             _≃_.logical-equivalence
               (Coinductive.Higher-lens≃Lens b univ₁)}
        {g = inverse $ _≃_.logical-equivalence $
             Capriotti.Lens≃Higher-lens b univ₂}
        (Preserves-getters-and-setters-⇔-∘
           {f = _≃_.logical-equivalence
                  (Coinductive-lens≃Lens b univ₁ univ₂)}
           {g = _≃_.logical-equivalence
                  (Coinductive.Higher-lens≃Lens b univ₁)}
           (Coinductive-lens≃Lens-preserves-getters-and-setters
              b univ₁ univ₂)
           (Coinductive.Higher-lens≃Lens-preserves-getters-and-setters
              b univ₁))
        (Preserves-getters-and-setters-⇔-inverse
           {f = _≃_.logical-equivalence
                  (Capriotti.Lens≃Higher-lens b univ₂)} $
         Capriotti.Lens≃Higher-lens-preserves-getters-and-setters
           b univ₂)

-- Lens is pointwise equivalent to Higher.Lens (assuming univalence).

Higher-lens≃Lens :
  Block "Higher-lens≃Lens" →
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  Higher.Lens A B ≃ Lens univ A B
Higher-lens≃Lens b univ₁ univ₂ =
  proj₁ $ Higher-lens≃Lens′ b univ₁ univ₂

-- The equivalence preserves getters and setters.

Higher-lens≃Lens-preserves-getters-and-setters :
  (bl : Block "Higher-lens≃Lens")
  {A : Type a} {B : Type b}
  (univ₁ : Univalence (lsuc (a ⊔ b)))
  (univ₂ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Higher-lens≃Lens bl univ₁ univ₂))
Higher-lens≃Lens-preserves-getters-and-setters b univ₁ univ₂ =
  proj₂ $ Higher-lens≃Lens′ b univ₁ univ₂

-- Lenses with stable view types are equal if their setters are equal
-- (assuming univalence).

lenses-equal-if-setters-equal :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  (l₁ l₂ : Lens univ A B) →
  (∥ B ∥ → B) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal univ′ univ l₁ l₂ stable =
  block λ bl →
  let equiv = Higher-lens≃Lens bl univ′ univ in

  Lens.set l₁ ≡ Lens.set l₂              ↔⟨ ≡⇒≃ $ sym $ cong₂ _≡_
                                              (proj₂ $ proj₂ (Higher-lens≃Lens-preserves-getters-and-setters bl univ′ univ) l₁)
                                              (proj₂ $ proj₂ (Higher-lens≃Lens-preserves-getters-and-setters bl univ′ univ) l₂) ⟩
  Higher.Lens.set (_≃_.from equiv l₁) ≡
  Higher.Lens.set (_≃_.from equiv l₂)    ↝⟨ Higher.lenses-equal-if-setters-equal univ _ _ (λ _ → stable) ⟩

  _≃_.from equiv l₁ ≡ _≃_.from equiv l₂  ↔⟨ Eq.≃-≡ (inverse equiv) ⟩□

  l₁ ≡ l₂                                □

------------------------------------------------------------------------
-- Identity

-- An identity lens.

id :
  {A : Type a}
  (univ : Univalence a) →
  Lens univ A A
id univ .Lens.get                       = P.id
id univ .Lens.get⁻¹-coherently-constant =
  coherently-constant λ x →
                              $⟨ Preimage.id⁻¹-contractible x ⟩
    Contractible (P.id ⁻¹ x)  ↝⟨ Eq.↔⇒≃ ∘ _⇔_.to contractible⇔↔⊤ ⟩□
    P.id ⁻¹ x ≃ ⊤             □
  where
  coherently-constant :
    (∀ x → P x ≃ ⊤) →
    Coherently-constant univ P
  coherently-constant {P = P} P≃⊤ .property x y =
    P x  ↝⟨ P≃⊤ x ⟩
    ⊤    ↝⟨ inverse $ P≃⊤ y ⟩□
    P y  □
  coherently-constant P≃⊤ .coherent =
    coherently-constant
      (O.elim λ where
         .O.Elim.∣∣ʳ → P≃⊤
         .O.Elim.∣∣-constantʳ _ _ →
           Eq.lift-equality ext $ refl (λ _ → tt))

------------------------------------------------------------------------
-- Composition

-- Composition.
--
-- Paolo Capriotti came up with the idea to use Coherently-constant-Σ.
-- At first we had a problem related to universe levels. Andrea
-- Vezzosi came up with a first workaround (involving lifting), and
-- later I found a more direct solution.

infix 9 ⟨_,_⟩_∘_

⟨_,_⟩_∘_ :
  {A : Type a} {B : Type b} {C : Type c}
  {univ₁ : Univalence (b ⊔ c)}
  {univ₂ : Univalence (a ⊔ b)}
  (univ₃ : Univalence (a ⊔ c)) →
  Univalence (a ⊔ b ⊔ c) →
  Lens univ₁ B C → Lens univ₂ A B → Lens univ₃ A C
(⟨ _ , _ ⟩ l₁ ∘ l₂) .Lens.get = get l₁ ∘ get l₂
  where
  open Lens
⟨_,_⟩_∘_ {b = ℓb} {univ₁ = univ₁} {univ₂ = univ₂} univ₃ univ₄ l₁ l₂
  .Lens.get⁻¹-coherently-constant =
                                                       $⟨ Coherently-constant-Σ
                                                            {P = get l₁ ⁻¹_}
                                                            {Q = λ (_ , b , _) → get l₂ ⁻¹ b}
                                                            univ₁ univ₂ univ₄
                                                            (get⁻¹-coherently-constant l₁)
                                                            (Coherently-constant-map univ₂ univ₂
                                                               (proj₁ ∘ proj₂) (λ _ → F.id)
                                                               (get⁻¹-coherently-constant l₂)) ⟩
  Coherently-constant univ₄
    (λ c → ∃ λ ((b , _) : get l₁ ⁻¹ c) → get l₂ ⁻¹ b)  ↝⟨ Coherently-constant-map univ₄ univ₃ P.id
                                                            (λ _ → inverse $ ∘⁻¹≃ (get l₁) (get l₂)) ⟩□
  Coherently-constant univ₃ ((get l₁ ∘ get l₂) ⁻¹_)    □
  where
  open Lens

-- The setter of a lens formed using composition is defined in the
-- "right" way.

set-∘ :
  ∀ {A : Type a} {B : Type b} {C : Type c}
    {univ₁ : Univalence (b ⊔ c)}
    {univ₂ : Univalence (a ⊔ b)}
  (univ₃ : Univalence (a ⊔ c))
  (univ₄ : Univalence (a ⊔ b ⊔ c))
  (l₁ : Lens univ₁ B C) (l₂ : Lens univ₂ A B) {a c} →
  Lens.set (⟨ univ₃ , univ₄ ⟩ l₁ ∘ l₂) a c ≡
  Lens.set l₂ a (Lens.set l₁ (Lens.get l₂ a) c)
set-∘ _ _ _ _ = refl _

-- Composition is associative if the view type of the resulting lens
-- is stable (assuming univalence).

associativity :
  {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
  (∥ D ∥ → D) →
  (univ₁  : Univalence (c ⊔ d))
  (univ₂  : Univalence (b ⊔ c))
  (univ₃  : Univalence (a ⊔ b))
  (univ₄  : Univalence (a ⊔ d))
  (univ₅  : Univalence (a ⊔ c ⊔ d))
  (univ₆  : Univalence (a ⊔ c))
  (univ₇  : Univalence (a ⊔ b ⊔ c))
  (univ₈  : Univalence (a ⊔ b ⊔ d))
  (univ₉  : Univalence (b ⊔ d))
  (univ₁₀ : Univalence (b ⊔ c ⊔ d)) →
  Univalence (lsuc (a ⊔ d)) →
  (l₁ : Lens univ₁ C D) (l₂ : Lens univ₂ B C) (l₃ : Lens univ₃ A B) →
  ⟨ univ₄ , univ₅ ⟩ l₁ ∘ (⟨ univ₆ , univ₇ ⟩ l₂ ∘ l₃) ≡
  ⟨ univ₄ , univ₈ ⟩ (⟨ univ₉ , univ₁₀ ⟩ l₁ ∘ l₂) ∘ l₃
associativity stable _ _ _ univ₄ _ _ _ _ _ _ univ₁₁ l₁ l₂ l₃ =
  lenses-equal-if-setters-equal
    univ₁₁
    univ₄
    _
    _
    stable
    (refl _)

-- The identity lens is a left identity of composition if the view
-- type of the resulting lens is stable (assuming univalence).

left-identity :
  {A : Type a} {B : Type b} →
  (∥ B ∥ → B) →
  (univ₁ : Univalence (a ⊔ b))
  (univ₂ : Univalence (a ⊔ b))
  (univ₃ : Univalence b) →
  Univalence (lsuc (a ⊔ b)) →
  (l : Lens univ₁ A B) →
  ⟨ univ₁ , univ₂ ⟩ id univ₃ ∘ l ≡ l
left-identity stable univ₁ univ₂ univ₃ univ₄ l =
  lenses-equal-if-setters-equal
    univ₄
    univ₁
    _
    _
    stable
    (refl _)

-- The identity lens is a right identity of composition if the view
-- type of the resulting lens is stable (assuming univalence).

right-identity :
  {A : Type a} {B : Type b} →
  (∥ B ∥ → B) →
  (univ₁ : Univalence (a ⊔ b))
  (univ₂ : Univalence (a ⊔ b))
  (univ₃ : Univalence a) →
  Univalence (lsuc (a ⊔ b)) →
  (l : Lens univ₁ A B) →
  ⟨ univ₁ , univ₂ ⟩ l ∘ id univ₃ ≡ l
right-identity stable univ₁ univ₂ univ₃ univ₄ l =
  lenses-equal-if-setters-equal
    univ₄
    univ₁
    _
    _
    stable
    (refl _)

-- The definitions in the following module use seven instances of
-- univalence.

module _
  {A : Type a} {B : Type b} {C : Type c}
  (univ₁ : Univalence (b ⊔ c))
  (univ₂ : Univalence (lsuc (b ⊔ c)))
  (univ₃ : Univalence (a ⊔ b))
  (univ₄ : Univalence (lsuc (a ⊔ b)))
  (univ₅ : Univalence (a ⊔ c))
  (univ₆ : Univalence (lsuc (a ⊔ c)))
  (univ₇ : Univalence (a ⊔ b ⊔ c))
  where

  -- An unrestricted composition operator for Higher.Lens (defined using
  -- univalence).

  infix 9 ⟨_,_,_,_,_,_,_,_⟩_⊚_

  ⟨_,_,_,_,_,_,_,_⟩_⊚_ :
    Block "Higher-lens≃Lens" →
    Higher.Lens B C → Higher.Lens A B → Higher.Lens A C
  ⟨_,_,_,_,_,_,_,_⟩_⊚_ b l₁ l₂ =
    _≃_.from (Higher-lens≃Lens b univ₆ univ₅)
      (⟨ univ₅ , univ₇ ⟩
         _≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁ ∘
         _≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂)

  -- The setter of a lens formed using composition is defined in the
  -- "right" way.

  set-⊚ :
    (b : Block "Higher-lens≃Lens") →
    ∀ (l₁ : Higher.Lens B C) (l₂ : Higher.Lens A B) a c →
    Higher.Lens.set (⟨_,_,_,_,_,_,_,_⟩_⊚_ b l₁ l₂) a c ≡
    Higher.Lens.set l₂ a (Higher.Lens.set l₁ (Higher.Lens.get l₂ a) c)
  set-⊚ b l₁ l₂ a c =
    Higher.Lens.set
      (_≃_.from (Higher-lens≃Lens b univ₆ univ₅)
         (⟨ univ₅ , univ₇ ⟩
            _≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁ ∘
            _≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂))
      a c                                                               ≡⟨ cong (λ f → f a c) $
                                                                           proj₂ $
                                                                           proj₂ (Higher-lens≃Lens-preserves-getters-and-setters b univ₆ univ₅)
                                                                             (⟨ univ₅ , univ₇ ⟩
                                                                                _≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁ ∘
                                                                                _≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂) ⟩
    Lens.set
      (⟨ univ₅ , univ₇ ⟩
         _≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁ ∘
         _≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂)
      a c                                                               ≡⟨⟩

    Lens.set (_≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂)
      a
      (Lens.set (_≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁)
         (Lens.get (_≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂) a) c)   ≡⟨ cong (λ f →
                                                                                   f a (Lens.set (_≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁)
                                                                                          (Lens.get (_≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂) a)
                                                                                          c)) $
                                                                           proj₂ $
                                                                           proj₁ (Higher-lens≃Lens-preserves-getters-and-setters b univ₄ univ₃) l₂ ⟩
    Higher.Lens.set l₂
      a
      (Lens.set (_≃_.to (Higher-lens≃Lens b univ₂ univ₁) l₁)
         (Lens.get (_≃_.to (Higher-lens≃Lens b univ₄ univ₃) l₂) a) c)   ≡⟨ cong (Higher.Lens.set l₂ a) $
                                                                           cong₂ (λ f g → f (g a) c)
                                                                             (proj₂ $
                                                                              proj₁ (Higher-lens≃Lens-preserves-getters-and-setters b univ₂ univ₁)
                                                                                l₁)
                                                                             (proj₁ $
                                                                              proj₁ (Higher-lens≃Lens-preserves-getters-and-setters b univ₄ univ₃)
                                                                                l₂) ⟩∎
    Higher.Lens.set l₂ a (Higher.Lens.set l₁ (Higher.Lens.get l₂ a) c)  ∎

-- If the view type of the resulting lens is stable, then the
-- definition of composition above matches the one in higher (when
-- applicable).

⊚≡∘ :
  (bl : Block "Higher-lens≃Lens") →
  ∀ a b {A : Type (a ⊔ b ⊔ c)} {B : Type (b ⊔ c)} {C : Type c}
  (univ₁ : Univalence (b ⊔ c))
  (univ₂ : Univalence (lsuc (b ⊔ c)))
  (univ₃ : Univalence (a ⊔ b ⊔ c))
  (univ₄ : Univalence (lsuc (a ⊔ b ⊔ c)))
  (univ₅ : Univalence (a ⊔ b ⊔ c))
  (univ₆ : Univalence (lsuc (a ⊔ b ⊔ c)))
  (univ₇ : Univalence (a ⊔ b ⊔ c))
  (l₁ : Higher.Lens B C) (l₂ : Higher.Lens A B) →
  (∥ C ∥ → C) →
  ⟨ univ₁ , univ₂ , univ₃ , univ₄ , univ₅ , univ₆ , univ₇ , bl ⟩
    l₁ ⊚ l₂ ≡
  HC.⟨ a , b ⟩ l₁ ∘ l₂
⊚≡∘ bl a b univ₁ univ₂ univ₃ univ₄ univ₅ univ₆ univ₇ l₁ l₂ stable =
  cong (λ f → f l₁ l₂) $
  HC.composition≡∘ a b univ₇ stable
    ⟨ univ₁ , univ₂ , univ₃ , univ₄ , univ₅ , univ₆ , univ₇ , bl ⟩_⊚_
    (set-⊚ univ₁ univ₂ univ₃ univ₄ univ₅ univ₆ univ₇ bl)

------------------------------------------------------------------------
-- An alternative definition that does not make use of coinduction

-- A variant of Lens.
--
-- This definition does not make use of coinduction, but it is not
-- small.

Not-coinductive-lens :
  Univalence (a ⊔ b) → Type a → Type b → Type (lsuc (a ⊔ b))
Not-coinductive-lens univ A B =
  ∃ λ (get : A → B) →
    NC.Coherently
      Constant-≃
      (λ P c → O.rec′ P (λ x y → ≃⇒≡ univ (c x y)))
      (get ⁻¹_)

-- Not-coinductive-lens is pointwise equivalent to Lens (assuming
-- univalence).

Not-coinductive-lens≃Lens :
  {univ : Univalence (a ⊔ b)} {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  Not-coinductive-lens univ A B ≃ Lens univ A B
Not-coinductive-lens≃Lens {univ = univ} {A = A} {B = B} univ′ =
  Not-coinductive-lens univ A B                             ↝⟨ (∃-cong λ _ → inverse $ Coherently≃Not-coinductive-coherently univ′ univ′) ⟩
  (∃ λ (get : A → B) → Coherently-constant univ (get ⁻¹_))  ↝⟨ inverse Lens-as-Σ ⟩□
  Lens univ A B                                             □

------------------------------------------------------------------------
-- H-levels

-- If P has h-level n (pointwise), then Coherently-constant univ P has
-- h-level n (assuming univalence).
--
-- I think that Paolo Capriotti suggested that something like this
-- could be proved by using the result (due to Ahrens, Capriotti and
-- Spadotti, see "Non-wellfounded trees in Homotopy Type Theory") that
-- M-types for indexed containers have h-level n if all shapes have
-- h-level n.

H-level-Coherently-constant :
  {A : Type a} {P : A → Type p} →
  Univalence (lsuc (a ⊔ p)) →
  (univ : Univalence p) →
  ((a : A) → H-level n (P a)) →
  H-level n (Coherently-constant univ P)
H-level-Coherently-constant {a = a} {p = p} {n = n} univ _ h =
  H-level-Coherently-→Type univ univ h lemma P.id
  where
  lemma :
    {A : Type a} {P : A → Type p} →
    ((a : A) → H-level n (P a)) →
    H-level n (Constant-≃ P)
  lemma h =
    Π-closure ext n λ _ →
    Π-closure ext n λ _ →
    Eq.h-level-closure ext n (h _) (h _)

-- If P has h-level n (pointwise), then
-- Coinductive.Coherently-constant P has h-level n (assuming
-- univalence).

H-level-Coinductive-Coherently-constant :
  {A : Type a} {P : A → Type p} →
  Univalence (lsuc (a ⊔ p)) →
  Univalence (a ⊔ lsuc p) →
  Univalence p →
  ((a : A) → H-level n (P a)) →
  H-level n (Coinductive.Coherently-constant P)
H-level-Coinductive-Coherently-constant {n = n} {P = P} univ₁ univ₂ univ₃ =
  (∀ a → H-level n (P a))                        ↝⟨ H-level-Coherently-constant univ₁ univ₃ ⟩
  H-level n (Coherently-constant univ₃ P)        ↝⟨ H-level-cong _ n (inverse $ Coinductive-coherently-constant≃Coherently-constant univ₂ univ₃) ⟩□
  H-level n (Coinductive.Coherently-constant P)  □

-- If A and B have h-level n given the assumption that the other type
-- is inhabited, then Lens univ A B has h-level n (assuming
-- univalence).
--
-- I do not remember who came up with the idea to prove this for the
-- coinductive lenses (rather than the ones in
-- Lens.Non-dependent.Higher). It may have been Paolo Capriotti or
-- Andrea Vezzosi.

lens-preserves-h-level :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  ∀ n → (B → H-level n A) → (A → H-level n B) →
  H-level n (Lens univ A B)
lens-preserves-h-level univ′ univ n hA hB =
  H-level-cong _ n (inverse Lens-as-Σ) $
  Σ-closure n
    (Π-closure ext n λ a →
     hB a) λ _ →
  H-level-Coherently-constant univ′ univ λ b →
  Σ-closure n (hA b) λ a →
  H-level.⇒≡ n (hB a)

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n (assuming univalence).

h-level-respects-lens-from-inhabited :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  ∀ n → Lens univ A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited univ′ univ n =
  Higher.h-level-respects-lens-from-inhabited n ∘
  _≃_.from (Higher-lens≃Lens ⊠ univ′ univ)

-- If A has positive h-level n, then Lens univ A B also has h-level n
-- (assuming univalence).

lens-preserves-h-level-of-domain :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens univ A B)
lens-preserves-h-level-of-domain univ′ univ n hA =
  H-level.[inhabited⇒+]⇒+ n λ l →
  lens-preserves-h-level univ′ univ (1 + n) (λ _ → hA) λ a →
  h-level-respects-lens-from-inhabited univ′ univ _ l a hA
