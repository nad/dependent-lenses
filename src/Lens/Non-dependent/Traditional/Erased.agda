------------------------------------------------------------------------
-- Traditional non-dependent lenses with erased lens laws
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical #-}

import Equality.Path as P

module Lens.Non-dependent.Traditional.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

import Bi-invertibility.Erased
open import Bijection equality-with-J as Bij using (_↔_)
open import Circle eq using (𝕊¹)
open import Circle.Erased eq as CE using (𝕊¹ᴱ)
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq using (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages equality-with-J
  as ECP using (Contractibleᴱ; _⁻¹ᴱ_)
open import Erased.Cubical eq
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F
  hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT using (∥_∥)
open import H-level.Truncation.Propositional.Erased eq as TE
  using (∥_∥ᴱ; ∣_∣)
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J as Surjection using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)
import Lens.Non-dependent.Traditional eq as T
import Lens.Non-dependent.Traditional.Combinators eq as TC

private
  variable
    a b c p             : Level
    A A₁ A₂ B B₁ B₂ C D : Type a
    u v x₁ x₂ y₁ y₂     : A

------------------------------------------------------------------------
-- Traditional lenses

-- Lenses with erased lens laws.

record Lens (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  pattern
  field
    -- Getter and setter.
    get : A → B
    set : A → B → A

    -- Lens laws.
    @0 get-set : ∀ a b → get (set a b) ≡ b
    @0 set-get : ∀ a → set a (get a) ≡ a
    @0 set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

instance

  -- Traditional lenses with erased laws have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens A B is isomorphic to a nested Σ-type.

Lens-as-Σ :
  Lens A B ↔
  ∃ λ (get : A → B) →
  ∃ λ (set : A → B → A) →
  Erased ((∀ a b → get (set a b) ≡ b) ×
          (∀ a → set a (get a) ≡ a) ×
          (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))
Lens-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ l → get l , set l
                   , [ get-set l , set-get l , set-set l ]
      ; from = λ (get , set , [ get-set , set-get , set-set ]) →
                 record
                   { get     = get
                   ; set     = set
                   ; get-set = get-set
                   ; set-get = set-get
                   ; set-set = set-set
                   }
      }
    ; right-inverse-of = λ { (_ , _ , [ _ ]) → refl _ }
    }
  ; left-inverse-of = λ { (record {}) → refl _ }
  }
  where
  open Lens

-- In erased contexts Lens A B is equivalent to T.Lens A B.

@0 Lens≃Traditional-lens : Lens A B ≃ T.Lens A B
Lens≃Traditional-lens {A = A} {B = B} =
  Lens A B                                               ↔⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
   Erased ((∀ a b → get (set a b) ≡ b) ×
           (∀ a → set a (get a) ≡ a) ×
           (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → erased Erased↔) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
   (∀ a b → get (set a b) ≡ b) ×
   (∀ a → set a (get a) ≡ a) ×
   (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))           ↔⟨ inverse T.Lens-as-Σ ⟩□

  T.Lens A B                                             □

-- Lenses without erased proofs can be turned into lenses with erased
-- proofs (in erased contexts).

@0 Traditional-lens→Lens : T.Lens A B → Lens A B
Traditional-lens→Lens = _≃_.from Lens≃Traditional-lens

private

  -- The forward direction of Lens≃Traditional-lens.

  @0 trad : Lens A B → T.Lens A B
  trad = _≃_.to Lens≃Traditional-lens

private
  variable
    l₁ l₂ : Lens A B

------------------------------------------------------------------------
-- Somewhat coherent lenses

-- Traditional lenses with erased lens laws that satisfy some extra
-- coherence properties (that are also erased).

record Coherent-lens (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  pattern
  field
    lens : Lens A B

  open Lens lens public

  field
    @0 get-set-get : ∀ a → cong get (set-get a) ≡ get-set a (get a)
    @0 get-set-set :
      ∀ a b₁ b₂ →
      cong get (set-set a b₁ b₂) ≡
      trans (get-set (set a b₁) b₂) (sym (get-set a b₂))

instance

  -- Somewhat coherent lenses have getters and setters.

  coherent-has-getter-and-setter :
    Has-getter-and-setter (Coherent-lens {a = a} {b = b})
  coherent-has-getter-and-setter = record
    { get = Coherent-lens.get
    ; set = Coherent-lens.set
    }

-- Coherent-lens A B is equivalent to a nested Σ-type.

Coherent-lens-as-Σ :
  Coherent-lens A B ≃
  ∃ λ (l : Lens A B) →
    let open Lens l in
    Erased
      ((∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
       (∀ a b₁ b₂ →
        cong get (set-set a b₁ b₂) ≡
        trans (get-set (set a b₁) b₂) (sym (get-set a b₂))))
Coherent-lens-as-Σ = Eq.↔→≃
  (λ l → lens l , [ get-set-get l , get-set-set l ])
  (λ (l , [ get-set-get , get-set-set ]) → record
     { lens        = l
     ; get-set-get = get-set-get
     ; get-set-set = get-set-set
     })
  (λ { (_ , [ _ ]) → refl _ })
  (λ { (record {}) → refl _ })
  where
  open Coherent-lens

-- In erased contexts Coherent-lens A B is equivalent to
-- T.Coherent-lens A B.

@0 Coherent-lens≃Traditional-coherent-lens :
  Coherent-lens A B ≃ T.Coherent-lens A B
Coherent-lens≃Traditional-coherent-lens {A = A} {B = B} =
  Coherent-lens A B                                           ↔⟨ Coherent-lens-as-Σ ⟩

  (∃ λ (l : Lens A B) →
   let open Lens l in
   Erased
     ((∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
      (∀ a b₁ b₂ →
       cong get (set-set a b₁ b₂) ≡
       trans (get-set (set a b₁) b₂) (sym (get-set a b₂)))))  ↔⟨ (Σ-cong Lens≃Traditional-lens λ _ → erased Erased↔) ⟩

  (∃ λ (l : T.Lens A B) →
   let open T.Lens l in
   (∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
   (∀ a b₁ b₂ →
    cong get (set-set a b₁ b₂) ≡
    trans (get-set (set a b₁) b₂) (sym (get-set a b₂))))      ↔⟨ inverse T.Coherent-lens-as-Σ ⟩

  T.Coherent-lens A B                                         □

------------------------------------------------------------------------
-- Some lemmas

-- If two lenses have equal setters, then they also have equal
-- getters (in erased contexts).

@0 getters-equal-if-setters-equal :
  let open Lens in
  (l₁ l₂ : Lens A B) →
  set l₁ ≡ set l₂ →
  get l₁ ≡ get l₂
getters-equal-if-setters-equal l₁ l₂ =
  Lens.set l₁ ≡ Lens.set l₂                    ↔⟨⟩
  T.Lens.set (trad l₁) ≡ T.Lens.set (trad l₂)  ↝⟨ T.getters-equal-if-setters-equal (trad l₁) (trad l₂) ⟩
  T.Lens.get (trad l₁) ≡ T.Lens.get (trad l₂)  ↔⟨⟩
  Lens.get l₁ ≡ Lens.get l₂                    □

-- If the forward direction of an equivalence with erased proofs is
-- Lens.get l, then the setter of l can be expressed using the other
-- direction of the equivalence (in erased contexts).

@0 from≡set :
  ∀ (l : Lens A B) is-equiv →
  let open Lens
      A≃B = EEq.⟨ get l , is-equiv ⟩
  in
  ∀ a b → _≃ᴱ_.from A≃B b ≡ set l a b
from≡set l is-equiv =
  T.from≡set (trad l) (EEq.Is-equivalenceᴱ→Is-equivalence is-equiv)

-- If A and B are "very stable n levels up" (given certain
-- assumptions), then Lens A B is "very stable n levels up".

Very-stable-Lensⁿ :
  ∀ n →
  (A → B → For-iterated-equality n Very-stable A) →
  (A → For-iterated-equality n Very-stable B) →
  For-iterated-equality n Very-stable (Lens A B)
Very-stable-Lensⁿ {A = A} {B = B} n A-s B-s =
  Very-stable-congⁿ _ n (inverse Lens-as-Σ) $
  Very-stable-Σⁿ n (Very-stable-Πⁿ ext n λ a →
                    B-s a) λ _ →
  Very-stable-Σⁿ n (Very-stable-Πⁿ ext n λ a →
                    Very-stable-Πⁿ ext n λ b →
                    A-s a b) λ _ →
  Very-stable→Very-stableⁿ n
  Very-stable-Erased

------------------------------------------------------------------------
-- Some lens isomorphisms

-- Lens preserves equivalences.

Lens-cong : A₁ ≃ A₂ → B₁ ≃ B₂ → Lens A₁ B₁ ≃ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁≃A₂ B₁≃B₂ =
  Lens A₁ B₁                                             ↔⟨ Lens-as-Σ ⟩

  (∃ λ (get : A₁ → B₁) →
   ∃ λ (set : A₁ → B₁ → A₁) →
   Erased ((∀ a b → get (set a b) ≡ b) ×
           (∀ a → set a (get a) ≡ a) ×
           (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))  ↝⟨ (Σ-cong (→-cong ext A₁≃A₂ B₁≃B₂) λ get →
                                                             Σ-cong (→-cong ext A₁≃A₂ $ →-cong ext B₁≃B₂ A₁≃A₂) λ set →
                                                             Erased-cong (
                                                             (Π-cong ext A₁≃A₂ λ a → Π-cong ext B₁≃B₂ λ b →
                                                              inverse (Eq.≃-≡ B₁≃B₂) F.∘
                                                              (≡⇒≃ $ cong (_≡ _)
      (get (set a b)                                            ≡⟨ sym $ cong₂ (λ a b → get (set a b))
                                                                     (_≃_.left-inverse-of A₁≃A₂ _)
                                                                     (_≃_.left-inverse-of B₁≃B₂ _) ⟩
       get (set (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂ a))
              (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ b)))                ≡⟨ cong get $ sym $ _≃_.left-inverse-of A₁≃A₂ _ ⟩∎

       get (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂
              (set (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂ a))
                 (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ b)))))           ∎)))
                                                               ×-cong
                                                             (Π-cong ext A₁≃A₂ λ a →
                                                              inverse (Eq.≃-≡ A₁≃A₂) F.∘
                                                              (≡⇒≃ $ cong (_≡ _)
      (set a (get a)                                             ≡⟨ cong (set a) $ sym $ _≃_.left-inverse-of B₁≃B₂ _ ⟩

       set a (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ (get a)))             ≡⟨ cong (λ a → set a (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ (get a)))) $ sym $
                                                                    _≃_.left-inverse-of A₁≃A₂ _ ⟩∎
       set (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂ a))
         (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂
            (get (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂ a)))))            ∎)))
                                                               ×-cong
                                                             (inverse $ Π-cong ext (inverse A₁≃A₂) λ a →
                                                              inverse $ Π-cong ext B₁≃B₂ λ b₁ →
                                                              inverse $ Π-cong ext (inverse B₁≃B₂) λ b₂ →
                                                              (≡⇒≃ $ cong (λ a′ → set a′ (_≃_.from B₁≃B₂ b₂) ≡
                                                                                  set (_≃_.from A₁≃A₂ a) (_≃_.from B₁≃B₂ b₂))
      (_≃_.from A₁≃A₂ (_≃_.to A₁≃A₂
         (set (_≃_.from A₁≃A₂ a)
            (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ b₁))))                 ≡⟨ _≃_.left-inverse-of A₁≃A₂ _ ⟩

       set (_≃_.from A₁≃A₂ a)
         (_≃_.from B₁≃B₂ (_≃_.to B₁≃B₂ b₁))                      ≡⟨ cong (set (_≃_.from A₁≃A₂ a)) $
                                                                    _≃_.left-inverse-of B₁≃B₂ _ ⟩∎

       set (_≃_.from A₁≃A₂ a) b₁                                 ∎)) F.∘
                                                              Eq.≃-≡ A₁≃A₂))) ⟩
  (∃ λ (get : A₂ → B₂) →
   ∃ λ (set : A₂ → B₂ → A₂) →
   Erased ((∀ a b → get (set a b) ≡ b) ×
           (∀ a → set a (get a) ≡ a) ×
           (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))  ↔⟨ inverse Lens-as-Σ ⟩□

  Lens A₂ B₂                                             □

-- If B is a proposition (when A is inhabited), then Lens A B is
-- equivalent (with erased proofs) to
-- (A → B) × Erased ((a : A) → a ≡ a).

lens-to-proposition≃ᴱ :
  @0 (A → Is-proposition B) →
  Lens A B ≃ᴱ ((A → B) × Erased ((a : A) → a ≡ a))
lens-to-proposition≃ᴱ {A = A} {B = B} B-prop =
  Lens A B                                                          ↔⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     Erased
       ((∀ a b → get (set a b) ≡ b) ×
        (∀ a → set a (get a) ≡ a) ×
        (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))                ↔⟨ (∃-cong λ _ → ∃-cong λ _ → Erased-cong (
                                                                        drop-⊤-left-× λ _ →
                                                                        _⇔_.to contractible⇔↔⊤ $
                                                                        Π-closure ext 0 λ a →
                                                                        Π-closure ext 0 λ _ →
                                                                        +⇒≡ (B-prop a))) ⟩
  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     Erased
       ((∀ a → set a (get a) ≡ a) ×
        (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))                ↔⟨ (∃-cong λ get → ∃-cong λ set → Erased-cong (∃-cong λ _ →
                                                                        ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                        ≡⇒≃ (
       (set (set a b₁)                         b₂ ≡ set a b₂)             ≡⟨ cong (λ b → set (set a b) b₂ ≡ _) (B-prop a _ _) ⟩
       (set (set a (get a))                    b₂ ≡ set a b₂)             ≡⟨ cong (λ b → set (set a (get a)) b ≡ _) (B-prop a _ _) ⟩
       (set (set a (get a)) (get (set a (get a))) ≡ set a b₂)             ≡⟨ cong (λ b → _ ≡ set a b) (B-prop a _ _) ⟩∎
       (set (set a (get a)) (get (set a (get a))) ≡ set a (get a))        ∎))) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     Erased
       ((∀ a → set a (get a) ≡ a) ×
        (∀ a → B → B →
           set (set a (get a)) (get (set a (get a))) ≡
           set a (get a))))                                         ↝⟨ (∃-cong λ get →
                                                                        EEq.Σ-cong-≃ᴱ-Erased (A→B→A≃ᴱA→A get) λ _ → F.id) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     Erased
       ((∀ a → f a ≡ a) ×
        (∀ a → B → B → f (f a) ≡ f a)))                             ↝⟨ (∃-cong λ get → ∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                        ∀-cong [ ext ] λ a →
                                                                        EEq.drop-⊤-left-Π-≃ᴱ-Erased ext (B≃ᴱ⊤ get a) F.∘
                                                                        EEq.drop-⊤-left-Π-≃ᴱ-Erased ext (B≃ᴱ⊤ get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     Erased
       ((∀ a → f a ≡ a) ×
        (∀ a → f (f a) ≡ f a)))                                     ↔⟨ (∃-cong λ _ → ∃-cong λ f → Erased-cong (
                                                                        Σ-cong (Eq.extensionality-isomorphism ext) λ f≡id →
                                                                        ∀-cong ext λ a →
                                                                        ≡⇒≃ (cong₂ _≡_ (trans (f≡id (f a)) (f≡id a)) (f≡id a)))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     Erased
       (f ≡ P.id ×
        ((a : A) → a ≡ a)))                                         ↔⟨ (∃-cong λ _ → ∃-cong λ _ → Erased-Σ↔Σ) ⟩

  ((A → B) ×
   ∃ λ (f : A → A) →
     Erased (f ≡ P.id) ×
     Erased ((a : A) → a ≡ a))                                      ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (A → B) ×
  (∃ λ (f : A → A) → Erased (f ≡ P.id)) ×
  Erased ((a : A) → a ≡ a)                                          ↝⟨ (∃-cong λ _ → EEq.drop-⊤-left-Σ-≃ᴱ-Erased $
                                                                        _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ Contractibleᴱ-Erased-singleton) ⟩□
  (A → B) × Erased ((a : A) → a ≡ a)                                □
  where
  B≃ᴱ⊤ : (A → B) → A → B ≃ᴱ ⊤
  B≃ᴱ⊤ get a = EEq.inhabited→Is-proposition→≃ᴱ⊤ (get a) (B-prop a)

  A→B→A≃ᴱA→A : (A → B) → (A → B → A) ≃ᴱ (A → A)
  A→B→A≃ᴱA→A get =
    (A → B → A)  ↝⟨ ∀-cong [ ext ] (λ a → EEq.drop-⊤-left-Π-≃ᴱ-Erased ext $ B≃ᴱ⊤ get a) ⟩□
    (A → A)      □

-- If equality is very stable for A (when B is inhabited) and B is a
-- proposition (when A is inhabited), then Lens A B is equivalent to
-- (A → B) × Erased ((a : A) → a ≡ a).

Very-stable-≡→lens-to-proposition≃ :
  (B → Very-stable-≡ A) →
  (A → Is-proposition B) →
  Lens A B ≃ ((A → B) × Erased ((a : A) → a ≡ a))
Very-stable-≡→lens-to-proposition≃ {B = B} {A = A} A-s B-prop =
  Stable-≡→≃ᴱ→≃ stable₁ stable₂ (lens-to-proposition≃ᴱ B-prop)
  where
  stable₁ : Stable-≡ (Lens A B)
  stable₁ =
    Very-stable→Stable 1 $
    Very-stable-Lensⁿ 1
      (λ _ → A-s)
      (H-level→Very-stable 1 ⊚ B-prop)

  stable₂ : Stable-≡ ((A → B) × Erased ((a : A) → a ≡ a))
  stable₂ =
    Very-stable→Stable 1 $
    Very-stable-×ⁿ 1
      (Very-stable-Πⁿ ext 1 λ a →
       H-level→Very-stable 1 (B-prop a))
      (Very-stable→Very-stable-≡ 0
       Very-stable-Erased)

-- Lens A ⊤ is equivalent (with erased proofs) to
-- Erased ((a : A) → a ≡ a).

lens-to-⊤≃ᴱ : Lens A ⊤ ≃ᴱ Erased ((a : A) → a ≡ a)
lens-to-⊤≃ᴱ {A = A} =
  Lens A ⊤                            ↝⟨ lens-to-proposition≃ᴱ (λ _ → mono₁ 0 ⊤-contractible) ⟩
  (A → ⊤) × Erased ((a : A) → a ≡ a)  ↔⟨ drop-⊤-left-× (λ _ → →-right-zero) ⟩□
  Erased ((a : A) → a ≡ a)            □

-- Lens A ⊥ is equivalent to ¬ A.

lens-to-⊥≃ : Lens A (⊥ {ℓ = b}) ≃ (¬ A)
lens-to-⊥≃ {A = A} =
  Lens A ⊥                            ↝⟨ Very-stable-≡→lens-to-proposition≃ (λ ()) (λ _ → ⊥-propositional) ⟩
  (A → ⊥) × Erased ((a : A) → a ≡ a)  ↔⟨ (×-cong₁ λ _ → →-cong ext F.id (Bij.⊥↔uninhabited ⊥-elim)) ⟩
  ¬ A × Erased ((a : A) → a ≡ a)      ↔⟨ (drop-⊤-right λ ¬a →
                                          _⇔_.to contractible⇔↔⊤ $
                                          propositional⇒inhabited⇒contractible
                                            (H-level-Erased 1 (
                                             Π-closure ext 1 λ a →
                                             ⊥-elim (¬a a)))
                                            [ refl ]) ⟩□
  ¬ A                                 □

-- See also lens-from-⊥≃⊤ and lens-from-⊤≃codomain-contractible below.

------------------------------------------------------------------------
-- Some lens results related to h-levels

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n (in erased contexts).

@0 h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited n l =
  T.h-level-respects-lens-from-inhabited n (trad l)

-- Lenses with contractible domains have contractible codomains (in
-- erased contexts).

@0 contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l =
  T.contractible-to-contractible (trad l)

-- A variant for Contractibleᴱ.

Contractibleᴱ→Contractibleᴱ :
  Lens A B → Contractibleᴱ A → Contractibleᴱ B
Contractibleᴱ→Contractibleᴱ l c@(a , _) =
  ECP.Contractibleᴱ-respects-surjection
    (Lens.get l)
    (λ b → Lens.set l a b
         , (Lens.get l (Lens.set l a b)  ≡⟨ Lens.get-set l _ _ ⟩∎
            b                            ∎))
    c

-- If A and B have h-level n given the assumption that A is inhabited,
-- then Lens A B also has h-level n.

lens-preserves-h-level :
  ∀ n → (A → H-level n A) → (A → H-level n B) →
  H-level n (Lens A B)
lens-preserves-h-level n hA hB =
  H-level.respects-surjection (_↔_.surjection (inverse Lens-as-Σ)) n $
  Σ-closure n (Π-closure ext n λ a →
               hB a) λ _ →
  Σ-closure n (Π-closure ext n λ a →
               Π-closure ext n λ _ →
               hA a) λ _ →
  H-level-Erased n
    (×-closure n (Π-closure ext n λ a →
                  Π-closure ext n λ _ →
                  +⇒≡ $ mono₁ n (hB a)) $
     ×-closure n (Π-closure ext n λ a →
                  +⇒≡ $ mono₁ n (hA a))
                 (Π-closure ext n λ a →
                  Π-closure ext n λ _ →
                  Π-closure ext n λ _ →
                  +⇒≡ $ mono₁ n (hA a)))

-- If A has positive h-level n, then Lens A B also has h-level n (in
-- erased contexts).

@0 lens-preserves-h-level-of-domain :
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain {A = A} {B = B} n =
  H-level (1 + n) A             ↝⟨ T.lens-preserves-h-level-of-domain n ⟩
  H-level (1 + n) (T.Lens A B)  ↝⟨ H-level-cong _ (1 + n) (inverse Lens≃Traditional-lens) ⟩□
  H-level (1 + n) (Lens A B)    □

-- Lens 𝕊¹ᴱ ⊤ is not propositional.

¬-lens-to-⊤-propositional : ¬ Is-proposition (Lens 𝕊¹ᴱ ⊤)
¬-lens-to-⊤-propositional =
  Stable-¬
    [ Is-proposition (Lens 𝕊¹ᴱ ⊤)   ↝⟨ H-level-cong _ 1 (Lens-cong (inverse CE.𝕊¹≃𝕊¹ᴱ) Eq.id) ⟩
      Is-proposition (Lens 𝕊¹ ⊤)    ↝⟨ H-level-cong _ 1 Lens≃Traditional-lens ⟩
      Is-proposition (T.Lens 𝕊¹ ⊤)  ↝⟨ T.¬-lens-to-⊤-propositional univ ⟩□
      ⊥₀                            □
    ]

------------------------------------------------------------------------
-- Some equality characterisation lemmas

opaque

  -- An equality characterisation lemma.

  equality-characterisation₁ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      Erased
        ((∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                    (subst (λ set → get l₁ (set a b) ≡ b) s
                       (get-set l₁ a b)) ≡
                  get-set l₂ a b)
           ×
         (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
                  (subst (λ set → set a (get l₁ a) ≡ a) s
                     (set-get l₁ a)) ≡
                set-get l₂ a)
           ×
         (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                        (set-set l₁ a b₁ b₂) ≡
                      set-set l₂ a b₁ b₂))

  equality-characterisation₁
    {l₁ = l₁@(record {})} {l₂ = l₂@(record {})} =
    let l₁′ = _↔_.to Lens-as-Σ l₁
        l₂′ = _↔_.to Lens-as-Σ l₂
    in

    l₁ ≡ l₂                                                            ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Lens-as-Σ)) ⟩

    l₁′ ≡ l₂′                                                          ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Σ-assoc)) ⟩

    ((get l₁ , set l₁) , proj₂ (proj₂ l₁′))
      ≡
    ((get l₂ , set l₂) , proj₂ (proj₂ l₂′))                            ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
     subst (λ (get , set) →
              Erased
                ((∀ a b → get (set a b) ≡ b) ×
                 (∀ a → set a (get a) ≡ a) ×
                 (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))
           gs (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ Σ-cong (inverse ≡×≡↔≡) (λ gs → ≡⇒↝ _ $
                                                                          cong (λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
                                                                                  subst (λ (get , set) →
                                                                                           Erased
                                                                                             ((∀ a b → get (set a b) ≡ b) ×
                                                                                              (∀ a → set a (get a) ≡ a) ×
                                                                                              (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))
                                                                                        gs (proj₂ (proj₂ l₁′))
                                                                                    ≡
                                                                                  proj₂ (proj₂ l₂′))
                                                                               (sym $ _↔_.right-inverse-of ≡×≡↔≡ gs)) ⟩
    (∃ λ (gs : get l₁ ≡ get l₂ × set l₁ ≡ set l₂) →
     subst (λ (get , set) →
              Erased
                ((∀ a b → get (set a b) ≡ b) ×
                 (∀ a → set a (get a) ≡ a) ×
                 (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))
           (_↔_.to ≡×≡↔≡ gs) (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ inverse Σ-assoc ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ (get , set) →
              Erased
                ((∀ a b → get (set a b) ≡ b) ×
                 (∀ a → set a (get a) ≡ a) ×
                 (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)))
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ (∃-cong λ g → ∃-cong λ s → ≡⇒↝ _ $ cong (_≡ proj₂ (proj₂ l₂′))
                                                                           push-subst-[]) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     [ subst (λ (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))
             (_↔_.to ≡×≡↔≡ (g , s)) (erased (proj₂ (proj₂ l₁′))) ] ≡
     [ erased (proj₂ (proj₂ l₂′)) ])                                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse Erased-≡↔[]≡[]) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       (subst (λ (get , set) →
                 (∀ a b → get (set a b) ≡ b) ×
                 (∀ a → set a (get a) ≡ a) ×
                 (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))
              (_↔_.to ≡×≡↔≡ (g , s)) (erased (proj₂ (proj₂ l₁′))) ≡
        erased (proj₂ (proj₂ l₂′))))                                   ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (≡⇒↝ _ $
                                                                           cong (λ x → x ≡ erased (proj₂ (proj₂ l₂′)))
                                                                                (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       (( subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
                (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
        , subst (λ { (get , set) →
                     (∀ a → set a (get a) ≡ a) ×
                     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
                (_↔_.to ≡×≡↔≡ (g , s))
                (proj₂ (erased (proj₂ (proj₂ l₁′))))
        ) ≡
        erased (proj₂ (proj₂ l₂′))))                                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → Erased-cong (inverse ≡×≡↔≡)) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       (subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
              (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
        get-set l₂
          ×
        subst (λ { (get , set) →
                   (∀ a → set a (get a) ≡ a) ×
                   (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
              (_↔_.to ≡×≡↔≡ (g , s))
              (proj₂ (erased (proj₂ (proj₂ l₁′)))) ≡
        proj₂ (erased (proj₂ (proj₂ l₂′)))))                           ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (∃-cong λ _ → ≡⇒↝ _ $
                                                                           cong (λ x → x ≡ proj₂ (erased (proj₂ (proj₂ l₂′))))
                                                                                (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       (subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
              (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
        get-set l₂
          ×
        ( subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
                (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁)
        , subst (λ { (get , set) →
                     ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁)
        ) ≡
        proj₂ (erased (proj₂ (proj₂ l₂′)))))                           ↝⟨ (∃-cong λ _ → ∃-cong λ _ → Erased-cong (∃-cong λ _ → inverse ≡×≡↔≡)) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       (subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
              (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
        get-set l₂
          ×
        subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
              (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁) ≡
        set-get l₂
          ×
        subst (λ { (get , set) →
                   ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
              (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁) ≡
          set-set l₂))                                                 ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (
                                                                           lemma₁ (λ { (get , set) a → ∀ b → get (set a b) ≡ b })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))
                                                                             ×-cong
                                                                           lemma₁ (λ { (get , set) a → set a (get a) ≡ a })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))
                                                                             ×-cong
                                                                           lemma₁ (λ { (get , set) a → ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s)))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a → subst (λ { (get , set) → ∀ b → get (set a b) ≡ b })
                     (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a) ≡
               get-set l₂ a)
          ×
        (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
               set-get l₂ a)
          ×
        (∀ a → subst (λ { (get , set) →
                          ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a) ≡
               set-set l₂ a)))                                         ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (
                                                                           (∀-cong ext λ a →
                                                                              lemma₁ (λ { (get , set) b → get (set a b) ≡ b })
                                                                                     (_↔_.to ≡×≡↔≡ (g , s)))
                                                                             ×-cong
                                                                           F.id
                                                                             ×-cong
                                                                           (∀-cong ext λ a →
                                                                              lemma₁ (λ { (get , set) b₁ → ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                     (_↔_.to ≡×≡↔≡ (g , s))))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                       (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b) ≡
                 get-set l₂ a b)
          ×
        (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
               set-get l₂ a)
          ×
        (∀ a b₁ → subst (λ { (get , set) →
                             ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                        (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁) ≡
                  set-set l₂ a b₁)))                                   ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (∃-cong λ _ → ∃-cong λ _ →
                                                                           ∀-cong ext λ a → ∀-cong ext λ b₁ →
                                                                             lemma₁ (λ { (get , set) b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                    (_↔_.to ≡×≡↔≡ (g , s)))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                       (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b) ≡
                 get-set l₂ a b)
          ×
        (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
               set-get l₂ a)
          ×
        (∀ a b₁ b₂ → subst (λ { (get , set) →
                                set (set a b₁) b₂ ≡ set a b₂ })
                           (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁ b₂) ≡
                     set-set l₂ a b₁ b₂)))                             ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (
                                                                           (∀-cong ext λ a → ∀-cong ext λ b →
                                                                            lemma₂ (λ { (get , set) → get (set a b) ≡ b }) g s)
                                                                             ×-cong
                                                                           (∀-cong ext λ a →
                                                                            lemma₂ (λ { (get , set) → set a (get a) ≡ a }) g s)
                                                                             ×-cong
                                                                           (∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                            lemma₂ (λ { (get , set) → set (set a b₁) b₂ ≡ set a b₂ }) g s))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                   (subst (λ set → get l₁ (set a b) ≡ b) s
                      (get-set l₁ a b)) ≡
                 get-set l₂ a b)
          ×
        (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
                 (subst (λ set → set a (get l₁ a) ≡ a) s
                    (set-get l₁ a)) ≡
               set-get l₂ a)
          ×
        (∀ a b₁ b₂ →
           subst (λ get → set l₂ (set l₂ a b₁) b₂ ≡ set l₂ a b₂) g
             (subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                (set-set l₁ a b₁ b₂)) ≡
           set-set l₂ a b₁ b₂)))                                       ↝⟨ (∃-cong λ g → ∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ _ →
                                                                           ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (λ x → x ≡ _) $ subst-const g)) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                   (subst (λ set → get l₁ (set a b) ≡ b) s
                      (get-set l₁ a b)) ≡
                 get-set l₂ a b)
          ×
        (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
                 (subst (λ set → set a (get l₁ a) ≡ a) s
                    (set-get l₁ a)) ≡
               set-get l₂ a)
          ×
        (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                       (set-set l₁ a b₁ b₂) ≡
                     set-set l₂ a b₁ b₂)))                             □
    where
    open Lens

    opaque

      lemma₁ :
        ∀ (C : A → B → Type c) (eq : u ≡ v) {f g} →
        (subst (λ x → ∀ y → C x y) eq f ≡ g)
          ↔
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)
      lemma₁ C eq {f} {g} =
        subst (λ x → ∀ y → C x y) eq f ≡ g              ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (∀ y → subst (λ x → ∀ y → C x y) eq f y ≡ g y)  ↝⟨ (∀-cong ext λ y → ≡⇒↝ _ $
                                                            cong (λ x → x ≡ _) (sym $ push-subst-application eq _)) ⟩□
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)      □

    lemma₂ :
      (P : A × B → Type p) (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : y₁ ≡ y₂) →
      ∀ {p p′} →
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡ p′)
        ↔
      (subst (λ x → P (x , y₂)) x₁≡x₂ (subst (λ y → P (x₁ , y)) y₁≡y₂ p)
         ≡
       p′)
    lemma₂ P x₁≡x₂ y₁≡y₂ {p = p} = ≡⇒↝ _ $ cong (_≡ _) $ elim¹
      (λ y₁≡y₂ →
         subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡
         subst (λ x → P (x , _)) x₁≡x₂
           (subst (λ y → P (_ , y)) y₁≡y₂ p))
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , refl _)) p                     ≡⟨⟩

       subst P (cong₂ _,_ x₁≡x₂ (refl _)) p                          ≡⟨⟩

       subst P (trans (cong (_, _) x₁≡x₂) (cong (_ ,_) (refl _))) p  ≡⟨ cong (λ eq → subst P (trans (cong (_, _) x₁≡x₂) eq) p) $ cong-refl _ ⟩

       subst P (trans (cong (_, _) x₁≡x₂) (refl _)) p                ≡⟨ cong (λ eq → subst P eq p) $ trans-reflʳ _ ⟩

       subst P (cong (_, _) x₁≡x₂) p                                 ≡⟨ sym $ subst-∘ _ _ _ ⟩

       subst (λ x → P (x , _)) x₁≡x₂ p                               ≡⟨ cong (subst (λ x → P (x , _)) x₁≡x₂) $ sym $ subst-refl _ _ ⟩∎

       subst (λ x → P (x , _)) x₁≡x₂
         (subst (λ y → P (_ , y)) (refl _) p)                        ∎)
      _

  -- Another equality characterisation lemma.

  equality-characterisation₂ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      Erased
        ((∀ a b →
            trans (sym (cong₂ (λ set get → get (set a b)) s g))
              (get-set l₁ a b) ≡
            get-set l₂ a b) ×
         (∀ a →
            trans (sym (cong₂ (λ set get → set a (get a)) s g))
              (set-get l₁ a) ≡
            set-get l₂ a) ×
         (∀ a b₁ b₂ →
            subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
              (set-set l₁ a b₁ b₂) ≡
            set-set l₂ a b₁ b₂))

  equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                   (subst (λ set → get l₁ (set a b) ≡ b) s
                      (get-set l₁ a b)) ≡
                 get-set l₂ a b)
          ×
        (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
                 (subst (λ set → set a (get l₁ a) ≡ a) s
                    (set-get l₁ a)) ≡
               set-get l₂ a)
          ×
        (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                       (set-set l₁ a b₁ b₂) ≡
                     set-set l₂ a b₁ b₂)))                            ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (
                                                                          (∀-cong ext λ a → ∀-cong ext λ b → ≡⇒↝ _ $ cong (_≡ _) $
                                                                           lemma₁ g s a b)
                                                                            ×-cong
                                                                          (∀-cong ext λ a → ≡⇒↝ _ $ cong (_≡ _) $
                                                                           lemma₂ g s a)
                                                                            ×-cong
                                                                          F.id)) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                   (get-set l₁ a b) ≡
                 get-set l₂ a b) ×
        (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                 (set-get l₁ a) ≡
               set-get l₂ a) ×
        (∀ a b₁ b₂ →
           subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
             (set-set l₁ a b₁ b₂) ≡
           set-set l₂ a b₁ b₂)))                                      □
    where
    open Lens

    @0 lemma₁ :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a b →
      subst (λ get → get (set l₂ a b) ≡ b) g
        (subst (λ set → get l₁ (set a b) ≡ b) s
           (get-set l₁ a b)) ≡
      trans (sym (cong₂ (λ set get → get (set a b)) s g))
        (get-set l₁ a b)
    lemma₁ g s a b =
      subst (λ get → get (set l₂ a b) ≡ b) g
        (subst (λ set → get l₁ (set a b) ≡ b) s
           (get-set l₁ a b))                                     ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g eq) $
                                                                    subst-in-terms-of-trans-and-cong
                                                                      {f = λ set → get l₁ (set a b)} {g = λ _ → b}
                                                                      {x≡y = s} {fx≡gx = (get-set l₁ a b)} ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (trans (get-set l₁ a b) (cong (const b) s)))          ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g
                                                                                   (trans (sym (cong (λ set → get l₁ (set a b)) s))
                                                                                      (trans _ eq))) $
                                                                    cong-const s ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (trans (get-set l₁ a b) (refl _)))                    ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g
                                                                                   (trans (sym (cong (λ set → get l₁ (set a b)) s)) eq)) $
                                                                    trans-reflʳ _ ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (get-set l₁ a b))                                     ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = g}
                                                                      {fx≡gx = trans _ (get-set l₁ a b)} ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                  (get-set l₁ a b))
           (cong (const b) g))                                   ≡⟨ cong (λ eq → trans (sym (cong (λ get → get (set l₂ a b)) g))
                                                                                   (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                                                                                             (get-set l₁ a b))
                                                                                      eq)) $
                                                                    cong-const g ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                  (get-set l₁ a b))
           (refl _))                                             ≡⟨ cong (trans _) $
                                                                    trans-reflʳ _ ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (get-set l₁ a b))                                     ≡⟨ sym $ trans-assoc _ _ (get-set l₁ a b) ⟩

      trans (trans (sym (cong (λ get → get (set l₂ a b)) g))
               (sym (cong (λ set → get l₁ (set a b)) s)))
        (get-set l₁ a b)                                         ≡⟨ cong (λ eq → trans eq (get-set l₁ a b)) $ sym $
                                                                    sym-trans _ (cong (λ get → get (set l₂ a b)) g) ⟩
      trans (sym (trans (cong (λ set → get l₁ (set a b)) s)
                    (cong (λ get → get (set l₂ a b)) g)))
        (get-set l₁ a b)                                         ≡⟨⟩

      trans (sym (cong₂ (λ set get → get (set a b)) s g))
        (get-set l₁ a b)                                         ∎

    @0 lemma₂ :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a →
      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a)) ≡
      trans (sym (cong₂ (λ set get → set a (get a)) s g))
        (set-get l₁ a)
    lemma₂ g s a =
      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a))                                       ≡⟨⟩

      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a))                                       ≡⟨ cong (subst (λ get → set l₂ a (get a) ≡ a) g) $
                                                                    subst-in-terms-of-trans-and-cong {x≡y = s} {fx≡gx = set-get l₁ a} ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (trans (set-get l₁ a) (cong (const a) s)))            ≡⟨ cong (λ eq → subst (λ get → set l₂ a (get a) ≡ a) g
                                                                                    (trans (sym (cong (λ set → set a (get l₁ a)) s))
                                                                                       (trans _ eq))) $
                                                                    cong-const s ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (trans (set-get l₁ a) (refl _)))                      ≡⟨ cong (λ eq → subst (λ get → set l₂ a (get a) ≡ a) g
                                                                                   (trans (sym (cong (λ set → set a (get l₁ a)) s)) eq)) $
                                                                    trans-reflʳ _ ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (set-get l₁ a))                                       ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = g}
                                                                      {fx≡gx = trans (sym (cong (λ set → set a (get l₁ a)) s)) (set-get l₁ a)} ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                  (set-get l₁ a))
           (cong (const a) g))                                   ≡⟨ cong (λ eq → trans (sym (cong (λ get → set l₂ a (get a)) g))
                                                                                   (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                                                                                             (set-get l₁ a))
                                                                                      eq)) $
                                                                    cong-const g ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                  (set-get l₁ a))
           (refl _))                                             ≡⟨ cong (trans _) $
                                                                    trans-reflʳ _ ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (set-get l₁ a))                                       ≡⟨ sym $ trans-assoc _ _ (set-get l₁ a) ⟩

      trans (trans (sym (cong (λ get → set l₂ a (get a)) g))
               (sym (cong (λ set → set a (get l₁ a)) s)))
        (set-get l₁ a)                                           ≡⟨ cong (λ eq → trans eq (set-get l₁ a)) $ sym $
                                                                    sym-trans _ (cong (λ get → set l₂ a (get a)) g) ⟩
      trans (sym (trans (cong (λ set → set a (get l₁ a)) s)
                    (cong (λ get → set l₂ a (get a)) g)))
        (set-get l₁ a)                                           ≡⟨⟩

      trans (sym (cong₂ (λ set get → set a (get a)) s g))
        (set-get l₁ a)                                           ∎

  -- And another one.

  equality-characterisation₃ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      Erased
        ((∀ a b →
            trans (sym (cong₂ (λ set get → get (set a b)) s g))
              (get-set l₁ a b) ≡
            get-set l₂ a b) ×
         (∀ a →
            trans (sym (cong₂ (λ set get → set a (get a)) s g))
              (set-get l₁ a) ≡
            set-get l₂ a) ×
         (∀ a b₁ b₂ →
            trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
            trans (cong (λ set → set (set a b₁) b₂) s)
              (set-set l₂ a b₁ b₂)))

  equality-characterisation₃ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₂ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                   (get-set l₁ a b) ≡
                 get-set l₂ a b) ×
        (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                 (set-get l₁ a) ≡
               set-get l₂ a) ×
        (∀ a b₁ b₂ →
           subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
             (set-set l₁ a b₁ b₂) ≡
           set-set l₂ a b₁ b₂)))                                      ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (∃-cong λ _ → ∃-cong λ _ →
                                                                          ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ → ≡⇒↝ _ $
                                                                          lemma g s a b₁ b₂)) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                   (get-set l₁ a b) ≡
                 get-set l₂ a b) ×
        (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                 (set-get l₁ a) ≡
               set-get l₂ a) ×
        (∀ a b₁ b₂ →
           trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
           trans (cong (λ set → set (set a b₁) b₂) s)
             (set-set l₂ a b₁ b₂))))                                  □
    where
    open Lens

    @0 lemma :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a b₁ b₂ →
      (subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
         (set-set l₁ a b₁ b₂) ≡
       set-set l₂ a b₁ b₂) ≡
      (trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
       trans (cong (λ set → set (set a b₁) b₂) s)
         (set-set l₂ a b₁ b₂))
    lemma g s a b₁ b₂ =
      subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
        (set-set l₁ a b₁ b₂) ≡
      set-set l₂ a b₁ b₂                                        ≡⟨ cong (_≡ _) $
                                                                   subst-in-terms-of-trans-and-cong {x≡y = s} {fx≡gx = set-set l₁ a b₁ b₂} ⟩
      trans (sym (cong (λ set → set (set a b₁) b₂) s))
        (trans (set-set l₁ a b₁ b₂)
           (cong (λ set → set a b₂) s)) ≡
      set-set l₂ a b₁ b₂                                        ≡⟨ [trans≡]≡[≡trans-symˡ] _ _ _ ⟩

      trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
      trans (sym (sym (cong (λ set → set (set a b₁) b₂) s)))
        (set-set l₂ a b₁ b₂)                                    ≡⟨ cong (λ eq → trans _ (cong (λ set → set a b₂) s) ≡
                                                                                trans eq (set-set l₂ a b₁ b₂)) $
                                                                   sym-sym (cong (λ set → set (set a b₁) b₂) s) ⟩
      trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
      trans (cong (λ set → set (set a b₁) b₂) s)
        (set-set l₂ a b₁ b₂)                                    ∎

  -- And yet another one.

  equality-characterisation₄ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
    ∃ λ (s : ∀ a b → set l₁ a b ≡ set l₂ a b) →
      Erased
        ((∀ a b →
            trans (sym (trans (cong (get l₁) (s a b))
                          (g (set l₂ a b))))
              (get-set l₁ a b) ≡
            get-set l₂ a b) ×
         (∀ a →
            trans (sym (trans (s a (get l₁ a))
                          (cong (set l₂ a) (g a))))
              (set-get l₁ a) ≡
            set-get l₂ a) ×
         (∀ a b₁ b₂ →
            trans (set-set l₁ a b₁ b₂) (s a b₂) ≡
            trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
              (set-set l₂ a b₁ b₂)))

  equality-characterisation₄ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                              ↝⟨ equality-characterisation₃ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     Erased
       ((∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                   (get-set l₁ a b) ≡
                 get-set l₂ a b) ×
        (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                 (set-get l₁ a) ≡
               set-get l₂ a) ×
        (∀ a b₁ b₂ →
           trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
           trans (cong (λ set → set (set a b₁) b₂) s)
             (set-set l₂ a b₁ b₂))))                                     ↝⟨ (Σ-cong (inverse $ Eq.extensionality-isomorphism ext) λ g →
                                                                             Σ-cong (inverse $
                                                                                     Eq.extensionality-isomorphism ext F.∘
                                                                                     ∀-cong ext λ _ → Eq.extensionality-isomorphism ext) λ s →
                                                                             Erased-cong (
                                                                             (∀-cong ext λ a → ∀-cong ext λ b →
                                                                              ≡⇒↝ _ $ cong (λ eq → trans (sym eq) (get-set l₁ a b) ≡ _) (
        cong₂ (λ set get → get (set a b)) s g                                   ≡⟨⟩

        trans (cong (λ set → get l₁ (set a b)) s)
          (cong (λ get → get (set l₂ a b)) g)                                   ≡⟨ cong (λ eq → trans eq (ext⁻¹ g (set l₂ a b))) $ sym $
                                                                                   cong-∘ _ _ s ⟩
        trans (cong (get l₁ ⊚ (_$ b)) (ext⁻¹ s a))
          (ext⁻¹ g (set l₂ a b))                                                ≡⟨ cong (λ eq → trans eq (ext⁻¹ g (set l₂ a b))) $ sym $
                                                                                   cong-∘ _ _ (ext⁻¹ s a) ⟩∎
        trans (cong (get l₁) (ext⁻¹ (ext⁻¹ s a) b))
          (ext⁻¹ g (set l₂ a b))                                                ∎))
                                                                               ×-cong
                                                                             (∀-cong ext λ a →
                                                                              ≡⇒↝ _ $ cong (λ eq → trans (sym eq) (set-get l₁ a) ≡ _) (
        cong₂ (λ set get → set a (get a)) s g                                   ≡⟨⟩

        trans (cong (λ set → set a (get l₁ a)) s)
          (cong (λ get → set l₂ a (get a)) g)                                   ≡⟨ sym $ cong₂ trans (cong-∘ _ _ s) (cong-∘ _ _ g) ⟩

        trans (ext⁻¹ (ext⁻¹ s a) (get l₁ a))
          (cong (set l₂ a) (ext⁻¹ g a))                                         ∎))
                                                                               ×-cong
                                                                             ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                              ≡⇒↝ _ $
                                                                              cong₂ (λ p q → trans _ p ≡
                                                                                             trans (cong (λ set → set (set a b₁) b₂) q)
                                                                                               (set-set l₂ a b₁ b₂)) (
        cong (λ set → set a b₂) s                                               ≡⟨ sym $ cong-∘ _ _ s ⟩∎

        ext⁻¹ (ext⁻¹ s a) b₂                                                    ∎)
                                                                                (
        s                                                                       ≡⟨ sym $ _≃_.right-inverse-of
                                                                                           (Eq.extensionality-isomorphism ext) _ ⟩
        ⟨ext⟩ (ext⁻¹ s)                                                         ≡⟨ (cong ⟨ext⟩ $ ⟨ext⟩ λ _ → sym $
                                                                                    _≃_.right-inverse-of
                                                                                      (Eq.extensionality-isomorphism ext) _) ⟩∎
        ⟨ext⟩ (⟨ext⟩ ⊚ ext⁻¹ ⊚ ext⁻¹ s)                                         ∎))) ⟩□

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (s : ∀ a b → set l₁ a b ≡ set l₂ a b) →
     Erased
       ((∀ a b →
           trans (sym (trans (cong (get l₁) (s a b))
                         (g (set l₂ a b))))
             (get-set l₁ a b) ≡
           get-set l₂ a b) ×
        (∀ a →
           trans (sym (trans (s a (get l₁ a))
                         (cong (set l₂ a) (g a))))
             (set-get l₁ a) ≡
           set-get l₂ a) ×
        (∀ a b₁ b₂ →
           trans (set-set l₁ a b₁ b₂) (s a b₂) ≡
           trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
             (set-set l₂ a b₁ b₂))))                                     □
    where
    open Lens

  -- A lemma that can be used to prove that two lenses with
  -- definitionally equal getters and setters are equal.

  equal-laws→≡ :
    {get : A → B} {set : A → B → A}
    (l₁′ l₂′ : Erased ((∀ a b → get (set a b) ≡ b) ×
                       (∀ a → set a (get a) ≡ a) ×
                       (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))) →

    let l₁ = _↔_.from Lens-as-Σ (get , set , l₁′)
        l₂ = _↔_.from Lens-as-Σ (get , set , l₂′)
        open Lens
    in

    @0 (∀ a b → get-set l₁ a b ≡ get-set l₂ a b) →
    @0 (∀ a → set-get l₁ a ≡ set-get l₂ a) →
    @0 (∀ a b₁ b₂ → set-set l₁ a b₁ b₂ ≡ set-set l₂ a b₁ b₂) →
    l₁ ≡ l₂
  equal-laws→≡ l₁′ l₂′ hyp₁ hyp₂ hyp₃ =
    let l₁″ = _↔_.from Lens-as-Σ (_ , _ , l₁′)
        l₂″ = _↔_.from Lens-as-Σ (_ , _ , l₂′)
    in
    _↔_.from equality-characterisation₂
      ( refl _
      , refl _
      , [ (λ a b →
             trans (sym (cong₂ (λ set get → get (set a b))
                           (refl _) (refl _)))
               (get-set l₁″ a b)                            ≡⟨ cong (λ eq → trans (sym eq) _) $ cong₂-refl _ ⟩

             trans (sym (refl _)) (get-set l₁″ a b)         ≡⟨ cong (flip trans _) sym-refl ⟩

             trans (refl _) (get-set l₁″ a b)               ≡⟨ trans-reflˡ _ ⟩

             get-set l₁″ a b                                ≡⟨ hyp₁ _ _ ⟩∎

             get-set l₂″ a b                                ∎)
        , (λ a →
             trans (sym (cong₂ (λ set get → set a (get a))
                           (refl _) (refl _)))
               (set-get l₁″ a)                              ≡⟨ cong (λ eq → trans (sym eq) _) $ cong₂-refl _ ⟩

             trans (sym (refl _)) (set-get l₁″ a)           ≡⟨ cong (flip trans _) sym-refl ⟩

             trans (refl _) (set-get l₁″ a)                 ≡⟨ trans-reflˡ _ ⟩

             set-get l₁″ a                                  ≡⟨ hyp₂ _ ⟩∎

             set-get l₂″ a                                  ∎)
        , (λ a b₁ b₂ →
             subst (λ set → set (set a b₁) b₂ ≡ set a b₂) (refl _)
               (set-set l₁″ a b₁ b₂)                                ≡⟨ subst-refl _ _ ⟩

             set-set l₁″ a b₁ b₂                                    ≡⟨ hyp₃ _ _ _ ⟩∎

             set-set l₂″ a b₁ b₂                                    ∎)
        ]
      )
    where
    open Lens

-- An equality characterisation lemma for lenses from sets.

@0 equality-characterisation-for-sets :
  let open Lens in

  {l₁ l₂ : Lens A B} →

  Is-set A →

  l₁ ≡ l₂
    ↔
  set l₁ ≡ set l₂
equality-characterisation-for-sets
  {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} A-set =

  l₁ ≡ l₂            ↔⟨ inverse $ Eq.≃-≡ Lens≃Traditional-lens ⟩
  trad l₁ ≡ trad l₂  ↝⟨ T.equality-characterisation-for-sets A-set ⟩□
  set l₁ ≡ set l₂    □
  where
  open Lens

------------------------------------------------------------------------
-- More isomorphisms/equivalences related to lenses

-- Lens ⊤ B is equivalent (with erased proofs) to Contractibleᴱ B.

lens-from-⊤≃codomain-contractible :
  Lens ⊤ B ≃ᴱ Contractibleᴱ B
lens-from-⊤≃codomain-contractible = EEq.⇔→≃ᴱ
  (lens-preserves-h-level-of-domain 0 (mono₁ 0 ⊤-contractible))
  (ECP.Contractibleᴱ-propositional ext)
  (λ l → Contractibleᴱ→Contractibleᴱ l
           (ECP.Contractible→Contractibleᴱ ⊤-contractible))
  (λ (b , irrB) → record
     { get     = λ _ → b
     ; get-set = λ _ → erased irrB
     ; set-get = refl
     ; set-set = λ _ _ _ → refl _
     })

-- Lens ⊥ B is equivalent to the unit type.

lens-from-⊥≃⊤ : Lens (⊥ {ℓ = a}) B ≃ ⊤
lens-from-⊥≃⊤ =
  Eq.↔⇒≃ $ _⇔_.to contractible⇔↔⊤ $
    record
      { get = ⊥-elim
      ; set = ⊥-elim
      ; get-set = λ a → ⊥-elim a
      ; set-get = λ a → ⊥-elim a
      ; set-set = λ a → ⊥-elim a
      } ,
    λ l → _↔_.from equality-characterisation₁
            ( ⟨ext⟩ (λ a → ⊥-elim a)
            , ⟨ext⟩ (λ a → ⊥-elim a)
            , [ (λ a → ⊥-elim a)
              , (λ a → ⊥-elim a)
              , (λ a → ⊥-elim a)
              ]
            )

-- If A is a set and there is a lens from A to B, then A is equivalent
-- (with erased proofs) to the cartesian product of some type (that
-- can be expressed using the setter of l) and B.
--
-- This result is based on Theorem 2.3.9 from "Lenses and View Update
-- Translation" by Pierce and Schmitt.

≃ᴱΣ∥set⁻¹ᴱ∥ᴱ× :
  @0 Is-set A →
  (l : Lens A B) →
  A ≃ᴱ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ᴱ f ∥ᴱ) × B)
≃ᴱΣ∥set⁻¹ᴱ∥ᴱ× {A = A} {B = B} A-set l = EEq.↔→≃ᴱ
  (λ a → (set a , ∣ a , [ refl _ ] ∣) , get a)
  (λ ((f , _) , b) → f b)
  to-from
  (λ a →
     set a (get a)  ≡⟨ set-get a ⟩∎
     a              ∎)
  where
  open Lens l

  @0 B-set : A → Is-set B
  B-set a =
    h-level-respects-lens-from-inhabited 2 l a A-set

  @0 to-from : ∀ _ → _
  to-from ((f , p) , b) = flip TE.rec p λ @0 where
    .TE.truncation-is-propositionʳ →
      ×-closure 2
        (Σ-closure 2
           (Π-closure ext 2 λ _ → A-set) λ _ →
           mono₁ 1 TE.truncation-is-proposition)
        (B-set (f b))
    .TE.∣∣ʳ (a , [ q ]) →
      let
        lemma₁ =
          set (f b)      ≡⟨ cong (λ f → set (f b)) $ sym q ⟩
          set (set a b)  ≡⟨ ⟨ext⟩ $ set-set a b ⟩
          set a          ≡⟨ q ⟩∎
          f              ∎

        lemma₂ =
          get (f b)      ≡⟨ cong (λ f → get (f b)) $ sym q ⟩
          get (set a b)  ≡⟨ get-set _ _ ⟩∎
          b              ∎
      in
      (set (f b) , ∣ f b , [ refl _ ] ∣) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma₁ (TE.truncation-is-proposition _ _)) lemma₂ ⟩∎
      (f         , p)                    , b          ∎

-- If B is an inhabited set and there is a lens from A to B, then A is
-- equivalent (with erased proofs) to the cartesian product of some
-- type (that can be expressed using the getter of l) and B.
--
-- This result is based on Corollary 13 from "Algebras and Update
-- Strategies" by Johnson, Rosebrugh and Wood.

≃ᴱget⁻¹ᴱ× :
  @0 Is-set B →
  (b : B)
  (l : Lens A B) →
  A ≃ᴱ (Lens.get l ⁻¹ᴱ b × B)
≃ᴱget⁻¹ᴱ× {B = B} {A = A} B-set b₀ l = EEq.↔→≃ᴱ
  (λ a → (set a b₀ , [ get-set a b₀ ]) , get a)
  (λ ((a , _) , b) → set a b)
  (λ @0 { ((a , [ h ]) , b) →
          let
            lemma =
              set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
              set a b₀          ≡⟨ cong (set a) (sym h) ⟩
              set a (get a)     ≡⟨ set-get a ⟩∎
              a                 ∎
          in
          (set (set a b) b₀ , [ get-set (set a b) b₀ ]) , get (set a b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma (H-level-Erased 1 B-set _ _)) (get-set a b) ⟩∎
          (a                , [ h                    ]) , b              ∎ })
  (λ a →
     set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
     set a (get a)           ≡⟨ set-get a ⟩∎
     a                       ∎)
  where
  open Lens l

-- For somewhat coherent lenses the previous result can be proved
-- without the assumption that the codomain is a set.

≃ᴱget⁻¹ᴱ×-coherent :
  (b : B)
  (l : Coherent-lens A B) →
  A ≃ᴱ (Coherent-lens.get l ⁻¹ᴱ b × B)
≃ᴱget⁻¹ᴱ×-coherent {B = B} {A = A} b₀ l = EEq.↔→≃ᴱ
  (λ a → (set a b₀ , [ get-set a b₀ ]) , get a)
  (λ ((a , _) , b) → set a b)
  (λ @0 { ((a , [ h ]) , b) →
          let
            lemma₁ =
              set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
              set a b₀          ≡⟨ cong (set a) (sym h) ⟩
              set a (get a)     ≡⟨ set-get a ⟩∎
              a                 ∎

            lemma₂₁ =
              cong get (trans (set-set a b b₀)
                          (trans (cong (set a) (sym h))
                             (set-get a)))               ≡⟨ trans (cong-trans _ _ _) $
                                                            cong (trans _) $
                                                            trans (cong-trans _ _ _) $
                                                            cong (flip trans _) $
                                                            cong-∘ _ _ _ ⟩
              trans (cong get (set-set a b b₀))
                (trans (cong (get ⊚ set a) (sym h))
                   (cong get (set-get a)))               ≡⟨ cong₂ (λ p q → trans p (trans (cong (get ⊚ set a) (sym h)) q))
                                                              (get-set-set _ _ _)
                                                              (get-set-get _) ⟩∎
              trans (trans (get-set (set a b) b₀)
                       (sym (get-set a b₀)))
                (trans (cong (get ⊚ set a) (sym h))
                   (get-set a (get a)))                  ∎

            lemma₂₂ =
              sym (trans (trans (get-set (set a b) b₀)
                            (sym (get-set a b₀)))
                     (trans (cong (get ⊚ set a) (sym h))
                        (get-set a (get a))))               ≡⟨ trans (sym-trans _ _) $
                                                               cong₂ trans
                                                                 (sym-trans _ _)
                                                                 (sym-trans _ _) ⟩
              trans (trans (sym (get-set a (get a)))
                       (sym (cong (get ⊚ set a) (sym h))))
                (trans (sym (sym (get-set a b₀)))
                   (sym (get-set (set a b) b₀)))            ≡⟨ cong₂ (λ p q → trans (trans (sym (get-set a (get a))) p)
                                                                                (trans q (sym (get-set (set a b) b₀))))
                                                                 (trans (cong sym $ cong-sym _ _) $
                                                                  sym-sym _)
                                                                 (sym-sym _) ⟩
              trans (trans (sym (get-set a (get a)))
                       (cong (get ⊚ set a) h))
                (trans (get-set a b₀)
                   (sym (get-set (set a b) b₀)))            ≡⟨ trans (sym $ trans-assoc _ _ _) $
                                                               cong (flip trans _) $ trans-assoc _ _ _ ⟩∎
              trans (trans (sym (get-set a (get a)))
                       (trans (cong (get ⊚ set a) h)
                          (get-set a b₀)))
                (sym (get-set (set a b) b₀))                ∎

            lemma₂′ =
              subst (λ a → get a ≡ b₀)
                (trans (set-set a b b₀)
                   (trans (cong (set a) (sym h)) (set-get a)))
                (get-set (set a b) b₀)                            ≡⟨ subst-∘ _ _ _ ⟩

              subst (_≡ b₀)
                (cong get (trans (set-set a b b₀)
                             (trans (cong (set a) (sym h))
                                (set-get a))))
                (get-set (set a b) b₀)                            ≡⟨ subst-trans-sym ⟩

              trans
                (sym (cong get (trans (set-set a b b₀)
                                  (trans (cong (set a) (sym h))
                                     (set-get a)))))
                (get-set (set a b) b₀)                            ≡⟨ cong (flip (trans ⊚ sym) _) lemma₂₁ ⟩

              trans
                (sym (trans (trans (get-set (set a b) b₀)
                               (sym (get-set a b₀)))
                        (trans (cong (get ⊚ set a) (sym h))
                           (get-set a (get a)))))
                (get-set (set a b) b₀)                            ≡⟨ cong (flip trans _) lemma₂₂ ⟩

              trans
                (trans (trans (sym (get-set a (get a)))
                          (trans (cong (get ⊚ set a) h)
                             (get-set a b₀)))
                   (sym (get-set (set a b) b₀)))
                (get-set (set a b) b₀)                            ≡⟨ trans-[trans-sym]- _ _ ⟩

              trans (sym (get-set a (get a)))
                (trans (cong (get ⊚ set a) h)
                   (get-set a b₀))                                ≡⟨ cong (λ f → trans (sym (f (get a))) (trans (cong (get ⊚ set a) h) (f b₀))) $ sym $
                                                                     _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) (get-set a) ⟩
              trans (sym (ext⁻¹ (⟨ext⟩ (get-set a)) (get a)))
                (trans (cong (get ⊚ set a) h)
                   (ext⁻¹ (⟨ext⟩ (get-set a)) b₀))                ≡⟨ elim₁
                                                                       (λ {f} eq →
                                                                          trans (sym (ext⁻¹ eq (get a)))
                                                                            (trans (cong f h) (ext⁻¹ eq b₀)) ≡
                                                                            h)
                                                                       (
                  trans (sym (ext⁻¹ (refl P.id) (get a)))
                    (trans (cong P.id h) (ext⁻¹ (refl P.id) b₀))        ≡⟨ cong₂ (λ p q → trans p (trans (cong P.id h) q))
                                                                             (trans (cong sym (ext⁻¹-refl _)) sym-refl)
                                                                             (ext⁻¹-refl _) ⟩

                  trans (refl _) (trans (cong P.id h) (refl _))         ≡⟨ trans-reflˡ _ ⟩

                  trans (cong P.id h) (refl _)                          ≡⟨ trans-reflʳ _ ⟩

                  cong P.id h                                           ≡⟨ sym $ cong-id _ ⟩∎

                  h                                                     ∎)
                                                                       _ ⟩∎
              h                                                   ∎

            lemma₂ =
              subst (λ a → Erased (get a ≡ b₀))
                (trans (set-set a b b₀)
                   (trans (cong (set a) (sym h)) (set-get a)))
                [ get-set (set a b) b₀ ]                          ≡⟨ push-subst-[] ⟩

              [ subst (λ a → get a ≡ b₀)
                  (trans (set-set a b b₀)
                     (trans (cong (set a) (sym h)) (set-get a)))
                  (get-set (set a b) b₀)
              ]                                                   ≡⟨ []-cong [ lemma₂′ ] ⟩∎

              [ h ]                                               ∎
          in
          (set (set a b) b₀ , [ get-set (set a b) b₀ ]) , get (set a b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma₁ lemma₂) (get-set a b) ⟩∎
          (a                , [ h                    ]) , b              ∎ })
  (λ a →
     set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
     set a (get a)           ≡⟨ set-get a ⟩∎
     a                       ∎)
  where
  open Coherent-lens l

------------------------------------------------------------------------
-- A conversion function

-- If A is a set, then Lens A B is equivalent to Coherent-lens A B.

≃coherent : @0 Is-set A → Lens A B ≃ Coherent-lens A B
≃coherent {A = A} {B = B} A-set = Eq.↔→≃
  to
  Coherent-lens.lens
  (λ l → let l′ = Coherent-lens.lens l in
                          $⟨ H-level-Erased 1
                               (×-closure 1
                                  (Π-closure ext 1 λ a →
                                   mono₁ 2 (B-set l′ a))
                                  (Π-closure ext 1 λ a →
                                   Π-closure ext 1 λ _ →
                                   Π-closure ext 1 λ _ →
                                   mono₁ 2 (B-set l′ a))) ⟩
     Is-proposition _     ↝⟨ (λ p → cong (l′ ,_) (p _ _)) ⦂ (_ → _) ⟩
     (l′ , _) ≡ (l′ , _)  ↔⟨ Eq.≃-≡ Coherent-lens-as-Σ ⟩□
     to l′ ≡ l            □)
  refl
  where
  @0 B-set : Lens A B → A → Is-set B
  B-set l a =
    h-level-respects-lens-from-inhabited 2 l a A-set

  to : Lens A B → Coherent-lens A B
  to l = record
    { lens        = l
    ; get-set-get = λ a → B-set l a _ _
    ; get-set-set = λ a _ _ → B-set l a _ _
    }

-- The conversion preserves getters and setters.

≃coherent-preserves-getters-and-setters :
  {A : Type a}
  (@0 s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (≃coherent s))
≃coherent-preserves-getters-and-setters _ =
    (λ _ → refl _ , refl _)
  , (λ _ → refl _ , refl _)

------------------------------------------------------------------------
-- Lens combinators

module Lens-combinators where

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

  -- If there is an equivalence with erased proofs between two types,
  -- then there is a lens between them.

  ≃ᴱ→lens : A ≃ᴱ B → Lens A B
  ≃ᴱ→lens A≃B = record
    { get     = to
    ; set     = const from
    ; get-set = const right-inverse-of
    ; set-get = left-inverse-of
    ; set-set = λ _ _ _ → refl _
    }
    where
    open _≃ᴱ_ A≃B

  -- Identity lens.

  id : Lens A A
  id = ≃ᴱ→lens F.id

  -- The identity lens is equal to the one obtained from the
  -- traditional identity lens without erased proofs.

  Traditional-lens-id≡id :
    Traditional-lens→Lens TC.id ≡ id {A = A}
  Traditional-lens-id≡id = refl _

  -- Composition of lenses.

  infixr 9 _∘_

  _∘_ : Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = record
    { get     = λ a → get l₁ (get l₂ a)
    ; set     = λ a c →
                let b = set l₁ (get l₂ a) c in
                set l₂ a b
    ; get-set = T.Lens.get-set l₁∘l₂
    ; set-get = T.Lens.set-get l₁∘l₂
    ; set-set = T.Lens.set-set l₁∘l₂
    }
    where
    open Lens

    @0 l₁∘l₂ : _
    l₁∘l₂ = trad l₁ TC.∘ trad l₂

  -- Traditional-lens→Lens commutes with composition.

  @0 Traditional-lens-∘≡∘ :
    {l₁ : T.Lens B C} {l₂ : T.Lens A B} →
    Traditional-lens→Lens (l₁ TC.∘ l₂) ≡
    Traditional-lens→Lens l₁ ∘ Traditional-lens→Lens l₂
  Traditional-lens-∘≡∘ = refl _

  -- Note that composition can be defined in several different ways.
  -- Here are two alternative implementations.

  infixr 9 _∘′_ _∘″_

  _∘′_ : Lens B C → Lens A B → Lens A C
  l₁ ∘′ l₂ = record (l₁ ∘ l₂)
    { set-set = T.Lens.set-set l₁∘′l₂
    }
    where
    @0 l₁∘′l₂ : _
    l₁∘′l₂ = trad l₁ TC.∘′ trad l₂

  _∘″_ : Lens B C → Lens A B → Lens A C
  l₁ ∘″ l₂ = record (l₁ ∘ l₂)
    { set-set = T.Lens.set-set l₁∘″l₂
    }
    where
    @0 l₁∘″l₂ : _
    l₁∘″l₂ = trad l₁ TC.∘″ trad l₂

  -- These two implementations are pointwise equal to the other one.
  -- However, I don't know if there is some other definition that is
  -- distinct from these two (if we require that the definitions are
  -- polymorphic, that get and set are implemented in the same way as
  -- for _∘_, and that the three composition laws below hold).

  ∘≡∘′ : l₁ ∘ l₂ ≡ l₁ ∘′ l₂
  ∘≡∘′ {l₁ = l₁} {l₂ = l₂} = equal-laws→≡
    (_↔_.to Lens-as-Σ (l₁ ∘  l₂) .proj₂ .proj₂)
    (_↔_.to Lens-as-Σ (l₁ ∘′ l₂) .proj₂ .proj₂)
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
                                                                                    (cong (λ b → set l₂ a (set l₁ b c₂)) eq) ≡
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
    (_↔_.to Lens-as-Σ (l₁ ∘  l₂) .proj₂ .proj₂)
    (_↔_.to Lens-as-Σ (l₁ ∘″ l₂) .proj₂ .proj₂)
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
  left-identity l@(record {}) = equal-laws→≡
    (_↔_.to Lens-as-Σ (id ∘ l) .proj₂ .proj₂)
    (_↔_.to Lens-as-Σ l        .proj₂ .proj₂)
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
  right-identity l@(record {}) = equal-laws→≡
    (_↔_.to Lens-as-Σ (l ∘ id) .proj₂ .proj₂)
    (_↔_.to Lens-as-Σ l        .proj₂ .proj₂)
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
  associativity l₁ l₂ l₃ = equal-laws→≡
    (_↔_.to Lens-as-Σ (l₁ ∘ (l₂ ∘ l₃)) .proj₂ .proj₂)
    (_↔_.to Lens-as-Σ ((l₁ ∘ l₂) ∘ l₃) .proj₂ .proj₂)
    lemma₁ lemma₂ lemma₃
    where
    open Lens

    @0 lemma₁ : _
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

    @0 lemma₂ : _
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

    @0 lemma₃ : _
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
      Erased
        ((∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
         (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
         (∀ a b₁ b₂ →
            trans (set-set a b₁ b₂) (s a b₂) ≡
            cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))
  equality-characterisation-id {l = l} =
    l ≡ id                                                               ↝⟨ equality-characterisation₄ ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
     Erased
       ((∀ a b →
           trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
           refl _) ×
        (∀ a →
           trans (sym (trans (s a (get a)) (cong P.id (g a))))
             (set-get a) ≡
           refl _) ×
        (∀ a b₁ b₂ →
           trans (set-set a b₁ b₂) (s a b₂) ≡
           trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
             (refl _))))                                                 ↝⟨ (∃-cong λ g → ∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                             (∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → trans (sym (trans _ eq)) (set-get _) ≡ _) $ sym $
                                                                              cong-id (g _))
                                                                              ×-cong
                                                                             ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (_ ≡_) $ trans-reflʳ _)) ⟩
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
     Erased
       ((∀ a b →
           trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
           refl _) ×
        (∀ a →
           trans (sym (trans (s a (get a)) (g a))) (set-get a) ≡
           refl _) ×
        (∀ a b₁ b₂ →
           trans (set-set a b₁ b₂) (s a b₂) ≡
           cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))))       ↝⟨ (∃-cong λ g → ∃-cong λ s → Erased-cong (
                                                                             (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                              ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                               ×-cong
                                                                             (∀-cong ext λ _ →
                                                                              ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                              ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                               ×-cong
                                                                             F.id)) ⟩□
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
     Erased
       ((∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
        (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
        (∀ a b₁ b₂ →
           trans (set-set a b₁ b₂) (s a b₂) ≡
           cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))))       □
    where
    open Lens l

  -- A lemma that can be used to show that a lens with a constant
  -- setter (such as the ones produced by getter-equivalence→lens
  -- below) is equal to the identity lens.

  constant-setter→≡id :
    (l′ : ∃ λ (get : A → A) →
          ∃ λ (set : A → A) →
            Erased
              ((A → ∀ a → get (set a) ≡ a) ×
               (∀ a → set (get a) ≡ a) ×
               (A → A → ∀ a → set a ≡ set a))) →

    let l   = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
        set = proj₁ (proj₂ l′)
        open Lens l hiding (set)
    in

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
       Erased
         ((∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
          (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
          (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _))) →
    l ≡ id
  constant-setter→≡id {A = A} l′ =
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
     Erased
       ((∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
        (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
        (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _)))                         ↝⟨ (Σ-map P.id $ Σ-map P.id λ {s} → Erased-cong (
                                                                             Σ-map P.id $ Σ-map P.id λ hyp a a₁ a₂ →
        trans (set-set a a₁ a₂) (s a₂)                                         ≡⟨ cong (λ eq → trans eq (s a₂)) $ hyp _ _ _ ⟩
        trans (refl _) (s a₂)                                                  ≡⟨ trans-reflˡ (s _) ⟩∎
        s a₂                                                                   ∎)) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
     Erased
       ((∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
        (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
        (∀ a a₁ a₂ → trans (set-set a a₁ a₂) (s a₂) ≡ s a₂)))            ↔⟨ (∃-cong λ _ → ∃-cong λ s → Erased-cong (∃-cong λ _ → ∃-cong λ _ →
                                                                             ∀-cong ext λ a → ∀-cong ext λ a₁ → ∀-cong ext λ a₂ →
                                                                             ≡⇒↝ F.equivalence $ cong (trans _ (s _) ≡_) (
        s a₂                                                                   ≡⟨ sym $ cong-ext ext ⟩
        cong (λ set → set a₂) (⟨ext⟩ s)                                        ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ s) ⟩
        cong (λ set → set (set a a₁) a₂) (cong const (⟨ext⟩ s))                ≡⟨ cong (cong (λ set → set (set a a₁) a₂)) $ sym $
                                                                                  ext-const ext ⟩∎
        cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s)                 ∎))) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
     Erased
       ((∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
        (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
        (∀ a a₁ a₂ →
           trans (set-set a a₁ a₂) (s a₂) ≡
           cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s))))     ↝⟨ Σ-map P.id (Σ-map const P.id) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : A → ∀ a → set a ≡ a) →
     Erased
       ((∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₁ a₂)) (g a₂)) ×
        (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
        (∀ a a₁ a₂ →
           trans (set-set a a₁ a₂) (s a a₂) ≡
           cong (λ set → set (set a a₁) a₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))))       ↔⟨ inverse equality-characterisation-id ⟩□

    l″ ≡ id                                                              □
    where
    l″  = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
    set = proj₁ (proj₂ l′)

    open Lens l″ hiding (set)

  -- An identity function for lenses for which the forward direction
  -- is an equivalence (with erased proofs).
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
    Is-equivalenceᴱ (Lens.get l) →
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
    A≃B = EEq.⟨ _ , is-equiv ⟩

    open _≃ᴱ_ A≃B
    open Lens l

  -- In erased contexts it can be proved that the function
  -- getter-equivalence→lens returns its input.

  @0 getter-equivalence→lens≡ :
    ∀ (l : Lens A B) is-equiv →
    getter-equivalence→lens l is-equiv ≡ l
  getter-equivalence→lens≡ l@(record {}) is-equiv =         $⟨ TC.getter-equivalence→lens≡ (trad l) is-equiv′ ⟩
    TC.getter-equivalence→lens (trad l) is-equiv′ ≡ trad l  ↝⟨ cong Traditional-lens→Lens ⟩□
    getter-equivalence→lens l is-equiv ≡ l                  □
    where
    is-equiv′ = EEq.Is-equivalenceᴱ→Is-equivalence is-equiv

------------------------------------------------------------------------
-- Some existence results

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ¬ Lens (∃ λ (b : Bool) → b ≡ true) Bool
no-first-projection-lens =
  Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

-- There are two lenses with equal setters that are not equal.

equal-setters-but-not-equal :
  ∃ λ (A : Type) →
  ∃ λ (B : Type) →
  ∃ λ (l₁ : Lens A B) →
  ∃ λ (l₂ : Lens A B) →
    Lens.set l₁ ≡ Lens.set l₂ ×
    l₁ ≢ l₂
equal-setters-but-not-equal =
  𝕊¹ᴱ , ⊤ , l₁′ , l₂′ , refl _ , l₁′≢l₂′
  where
  open Lens

  opaque

    @0 not-refl : (x : 𝕊¹ᴱ) → x ≡ x
    not-refl = CE.not-refl

    @0 not-refl≢refl : not-refl ≢ refl
    not-refl≢refl = CE.not-refl≢refl

  l₁′ : Lens 𝕊¹ᴱ ⊤
  l₁′ = _≃ᴱ_.from lens-to-⊤≃ᴱ [ not-refl ]

  l₂′ : Lens 𝕊¹ᴱ ⊤
  l₂′ = _≃ᴱ_.from lens-to-⊤≃ᴱ [ refl ]

  l₁′≢l₂′ : l₁′ ≢ l₂′
  l₁′≢l₂′ =
    Stable-¬
      [ l₁′ ≡ l₂′                ↔⟨ Eq.≃-≡ (EEq.≃ᴱ→≃ $ inverse lens-to-⊤≃ᴱ)
                                      {x = [ not-refl ]} {y = [ refl ]} ⟩
        [ not-refl ] ≡ [ refl ]  ↝⟨ cong erased ⟩
        not-refl ≡ refl          ↝⟨ not-refl≢refl ⟩□
        ⊥                        □
      ]

-- A lens which is used in some counterexamples below.

bad : (a : Level) → Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)
bad a = record
  { get     = P.id
  ; set     = const P.id
  ; get-set = λ _ → cong lift ⊚ CE.not-refl ⊚ lower
  ; set-get = refl
  ; set-set = λ _ _ → cong lift ⊚ CE.not-refl ⊚ lower
  }

-- The lens bad a has a getter which is an equivalence, but it does
-- not satisfy either of the coherence laws that Coherent-lens lenses
-- must satisfy.

getter-equivalence-but-not-coherent :
  let open Lens (bad a) in
  Is-equivalence get ×
  ¬ (∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
  ¬ (∀ a₁ a₂ a₃ →
     cong get (set-set a₁ a₂ a₃) ≡
     trans (get-set (set a₁ a₂) a₃) (sym (get-set a₁ a₃)))
getter-equivalence-but-not-coherent {a = a} =
    _≃_.is-equivalence F.id
  , Stable-¬
      [ ((x : ↑ a 𝕊¹ᴱ) → cong get (set-get x) ≡ get-set x (get x))    ↔⟨⟩

        ((x : ↑ a 𝕊¹ᴱ) →
         cong P.id (refl _) ≡ cong lift (CE.not-refl (lower x)))      ↔⟨ (Π-cong ext Bij.↑↔ λ _ → Eq.id) ⟩

        ((x : 𝕊¹ᴱ) → cong P.id (refl _) ≡ cong lift (CE.not-refl x))  ↝⟨ trans (trans (cong-refl _) (cong-id _)) ⊚_ ⟩

        ((x : 𝕊¹ᴱ) → cong lift (refl x) ≡ cong lift (CE.not-refl x))  ↔⟨ (∀-cong ext λ _ →
                                                                         Eq.≃-≡ $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse Bij.↑↔) ⟩

        ((x : 𝕊¹ᴱ) → refl x ≡ CE.not-refl x)                          ↔⟨ Eq.extensionality-isomorphism ext ⟩

        refl ≡ CE.not-refl                                            ↝⟨ CE.not-refl≢refl ⊚ sym ⟩□

        ⊥                                                             □
      ]
  , Stable-¬
      [ ((x y z : ↑ a 𝕊¹ᴱ) →
         cong get (set-set x y z) ≡
         trans (get-set (set x y) z) (sym (get-set x z)))  ↔⟨⟩

        ((x y z : ↑ a 𝕊¹ᴱ) →
         cong P.id (cong lift (CE.not-refl (lower z))) ≡
         trans (cong lift (CE.not-refl (lower z)))
           (sym (cong lift (CE.not-refl (lower z)))))      ↔⟨ (Π-cong ext Bij.↑↔ λ _ →
                                                               Π-cong ext Bij.↑↔ λ _ →
                                                               Π-cong ext Bij.↑↔ λ _ →
                                                               Eq.id) ⟩
        ((x y z : 𝕊¹ᴱ) →
         cong P.id (cong lift (CE.not-refl z)) ≡
         trans (cong lift (CE.not-refl z))
           (sym (cong lift (CE.not-refl z))))              ↝⟨ (λ hyp → hyp CE.base CE.base) ⟩

        ((x : 𝕊¹ᴱ) →
         cong P.id (cong lift (CE.not-refl x)) ≡
         trans (cong lift (CE.not-refl x))
           (sym (cong lift (CE.not-refl x))))              ↔⟨ (∀-cong ext λ _ → ≡⇒≃ $ cong₂ _≡_
                                                                 (sym $ cong-id _)
                                                                 (trans (trans-symʳ _) $
                                                                  sym $ cong-refl _)) ⟩
        ((x : 𝕊¹ᴱ) →
         cong lift (CE.not-refl x) ≡ cong lift (refl x))   ↔⟨ (∀-cong ext λ _ →
                                                               Eq.≃-≡ $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse Bij.↑↔) ⟩

        ((x : 𝕊¹ᴱ) → CE.not-refl x ≡ refl x)               ↔⟨ Eq.extensionality-isomorphism ext ⟩

        CE.not-refl ≡ refl                                 ↝⟨ CE.not-refl≢refl ⟩□

        ⊥                                                  □
      ]
  where
  open Lens (bad a)

-- The lenses bad a and Lens-combinators.id {A = ↑ a 𝕊¹ᴱ} have equal
-- setters, and their getters are equivalences, but they are not
-- equal.

equal-setters-and-equivalences-as-getters-but-not-equal :
  let l₁ = bad a
      l₂ = Lens-combinators.id {A = ↑ a 𝕊¹ᴱ}
  in
  Is-equivalence (Lens.get l₁) ×
  Is-equivalence (Lens.get l₂) ×
  Lens.set l₁ ≡ Lens.set l₂ ×
  l₁ ≢ l₂
equal-setters-and-equivalences-as-getters-but-not-equal {a = ℓa} =
  let is-equiv , not-coherent , _ =
        getter-equivalence-but-not-coherent
  in
    is-equiv
  , _≃_.is-equivalence F.id
  , refl _
  , Stable-¬
      [ bad ℓa ≡ id                                        ↝⟨ (λ eq → subst (λ l → ∀ a → cong (get l) (set-get l a) ≡
                                                                                         get-set l a (get l a))
                                                                            (sym eq)
                                                                            (λ _ → cong-refl _)) ⟩
        (∀ a → cong (get (bad ℓa)) (set-get (bad ℓa) a) ≡
               get-set (bad ℓa) a (get (bad ℓa) a))        ↝⟨ not-coherent ⟩□
        ⊥                                                  □
      ]
  where
  open Lens
  open Lens-combinators

-- There is in general no split surjection from equivalences with
-- erased proofs to lenses with getters that are equivalences with
-- erased proofs, if the right-to-left direction of the split
-- surjection is required to return the lens's getter plus some proof.

¬-≃ᴱ-↠-Σ-Lens-Is-equivalenceᴱ-get :
  ¬ ∃ λ (f : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠
             (∃ λ (l : Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)) →
                Is-equivalenceᴱ (Lens.get l))) →
      ∀ p → _≃ᴱ_.to (_↠_.from f p) ≡ Lens.get (proj₁ p)
¬-≃ᴱ-↠-Σ-Lens-Is-equivalenceᴱ-get {a = a} =
  Stable-¬
    [ (let is-equiv₁′ , is-equiv₂′ , setters-equal , bad≢id =
             equal-setters-and-equivalences-as-getters-but-not-equal

           is-equiv₁ = EEq.Is-equivalence→Is-equivalenceᴱ is-equiv₁′
           is-equiv₂ = EEq.Is-equivalence→Is-equivalenceᴱ is-equiv₂′
       in
       λ (f , hyp) →                                 $⟨ setters-equal ⟩

         Lens.set (bad a) ≡ Lens.set id              ↝⟨ getters-equal-if-setters-equal (bad a) id ⟩

         Lens.get (bad a) ≡ Lens.get id              ↝⟨ (λ eq → trans (hyp _) (trans eq (sym (hyp _)))) ⟩

         _≃ᴱ_.to (_↠_.from f (bad a , is-equiv₁)) ≡
         _≃ᴱ_.to (_↠_.from f (id , is-equiv₂))       ↝⟨ EEq.to≡to→≡ ext ⟩

         _↠_.from f (bad a , is-equiv₁) ≡
         _↠_.from f (id , is-equiv₂)                 ↝⟨ _↠_.to (Surjection.↠-≡ f) ⟩

         (bad a , is-equiv₁) ≡ (id , is-equiv₂)      ↝⟨ cong proj₁ ⟩

         bad a ≡ id                                  ↝⟨ bad≢id ⟩□

         ⊥                                           □)
    ]
  where
  open Lens-combinators

-- There is in general no equivalence with erased proofs from
-- equivalences with erased proofs to lenses with getters that are
-- equivalences with erased proofs, if the right-to-left direction of
-- the equivalence is required to return the lens's getter plus some
-- proof.

¬-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalence-get :
  ¬ ∃ λ (f : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ≃ᴱ
             (∃ λ (l : Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)) →
                Is-equivalenceᴱ (Lens.get l))) →
      ∀ p → _≃ᴱ_.to (_≃ᴱ_.from f p) ≡ Lens.get (proj₁ p)
¬-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalence-get {a = a} =
  Stable-¬
    [ (∃ λ (f : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ≃ᴱ
           (∃ λ (l : Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)) →
              Is-equivalenceᴱ (Lens.get l))) →
         ∀ p → _≃ᴱ_.to (_≃ᴱ_.from f p) ≡ Lens.get (proj₁ p))  ↝⟨ Σ-map (_≃_.surjection ⊚ EEq.≃ᴱ→≃) P.id ⟩

      (∃ λ (f : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠
           (∃ λ (l : Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)) →
              Is-equivalenceᴱ (Lens.get l))) →
         ∀ p → _≃ᴱ_.to (_↠_.from f p) ≡ Lens.get (proj₁ p))   ↝⟨ ¬-≃ᴱ-↠-Σ-Lens-Is-equivalenceᴱ-get ⟩□

      ⊥                                                       □
    ]

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private

  module B {a} =
    Bi-invertibility.Erased
      equality-with-J (Type a) Lens
      Lens-combinators.id Lens-combinators._∘_
  module BM {a} =
    B.More {a = a}
      Lens-combinators.left-identity
      Lens-combinators.right-identity
      Lens-combinators.associativity

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≅ᴱ_ to _≅ᴱ_; Has-quasi-inverseᴱ to Has-quasi-inverseᴱ)

-- In erased contexts Has-quasi-inverseᴱ (Traditional-lens→Lens l) is
-- equivalent to TC.Has-quasi-inverse l.

@0 Has-quasi-inverseᴱ≃Has-quasi-inverse :
  (l : T.Lens A B) →
  Has-quasi-inverseᴱ (Traditional-lens→Lens l) ≃ TC.Has-quasi-inverse l
Has-quasi-inverseᴱ≃Has-quasi-inverse l =
  (∃ λ l⁻¹ → Erased (l′ LC.∘ l⁻¹ ≡ LC.id × l⁻¹ LC.∘ l′ ≡ LC.id))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′ LC.∘ l⁻¹ ≡ LC.id × l⁻¹ LC.∘ l′ ≡ LC.id )  ↝⟨ (Σ-cong Lens≃Traditional-lens λ _ →
                                                                      inverse (Eq.≃-≡ Lens≃Traditional-lens)
                                                                        ×-cong
                                                                      inverse (Eq.≃-≡ Lens≃Traditional-lens)) ⟩□
  (∃ λ l⁻¹ →         l  TC.∘ l⁻¹ ≡ TC.id × l⁻¹ TC.∘ l  ≡ TC.id )  □
  where
  module LC = Lens-combinators

  l′ = Traditional-lens→Lens l

-- In erased contexts A ≅ᴱ B is equivalent to A TC.≅ B.

@0 ≅ᴱ≃≅ : (A ≅ᴱ B) ≃ (A TC.≅ B)
≅ᴱ≃≅ {A = A} {B = B} =
  (∃ λ (l : Lens A B) → Has-quasi-inverseᴱ l)      ↝⟨ Σ-cong-contra (inverse Lens≃Traditional-lens) Has-quasi-inverseᴱ≃Has-quasi-inverse ⟩□
  (∃ λ (l : T.Lens A B) → TC.Has-quasi-inverse l)  □

-- An equality characterisation lemma for A ≅ B that applies when A is
-- a set.

@0 equality-characterisation-for-sets-≅ᴱ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≅ᴱ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≅ᴱ
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂                          ↔⟨ inverse $ Eq.≃-≡ ≅ᴱ≃≅ ⟩
  _≃_.to ≅ᴱ≃≅ f₁ ≡ _≃_.to ≅ᴱ≃≅ f₂  ↝⟨ TC.equality-characterisation-for-sets-≅ A-set ⟩□
  set l₁₁ ≡ set l₁₂                □
  where
  open Lens

-- There is a logical equivalence between A ≃ᴱ B and A ≅ᴱ B.

≃ᴱ⇔≅ᴱ : (A ≃ᴱ B) ⇔ (A ≅ᴱ B)
≃ᴱ⇔≅ᴱ {A = A} {B = B} = record
  { to   = λ A≃B → ≃ᴱ→lens A≃B
                 , ≃ᴱ→lens (inverse A≃B)
                 , [ lemma A≃B
                   , (≃ᴱ→lens (inverse A≃B) ∘ ≃ᴱ→lens A≃B  ≡⟨ cong {x = A≃B} {y = inverse $ inverse A≃B}
                                                                (λ A≃B′ → ≃ᴱ→lens (inverse A≃B) ∘ ≃ᴱ→lens A≃B′) $
                                                              sym $ EEq.to≡to→≡ ext (refl _) ⟩
                      ≃ᴱ→lens (inverse A≃B) ∘
                      ≃ᴱ→lens (inverse $ inverse A≃B)      ≡⟨ lemma (inverse A≃B) ⟩∎

                      id                                   ∎)
                   ]
  ; from = λ (l₁ , l₂ , [ eq₁ , eq₂ ]) → EEq.↔→≃ᴱ
             (get l₁)
             (get l₂)
             (ext⁻¹ $
              getters-equal-if-setters-equal (l₁ ∘ l₂) id
                (cong set eq₁))
             (ext⁻¹ $
              getters-equal-if-setters-equal (l₂ ∘ l₁) id
                (cong set eq₂))
  }
  where
  open Lens
  open Lens-combinators

  @0 lemma :
    (C≃D : C ≃ᴱ D) → ≃ᴱ→lens C≃D ∘ ≃ᴱ→lens (inverse C≃D) ≡ id
  lemma C≃D = _↔_.from equality-characterisation₂
    ( ⟨ext⟩ (_≃ᴱ_.right-inverse-of C≃D)
    , (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)
    , [ lemma₁
      , lemma₂
      , lemma₃
      ]
    )
    where
    @0 lemma₁ : _
    lemma₁ = λ d₁ d₂ →
      let lemma =
            cong (λ set → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D (set d₁ d₂)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)       ≡⟨ cong (cong (λ set → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D (set d₁ d₂)))) $
                                                                       ext-const ext ⟩

            cong (λ set → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D (set d₁ d₂)))
              (cong const $ ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)      ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D) ⟩

            cong (λ set → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D (set d₂)))
              (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)                   ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D) ⟩

            cong (_≃ᴱ_.to C≃D ⊚ _≃ᴱ_.from C≃D)
              (cong (λ set → set d₂)
                 (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D))               ≡⟨ cong (cong (_≃ᴱ_.to C≃D ⊚ _≃ᴱ_.from C≃D)) $ cong-ext ext ⟩

            cong (_≃ᴱ_.to C≃D ⊚ _≃ᴱ_.from C≃D)
              (_≃ᴱ_.right-inverse-of C≃D _)                         ≡⟨ sym $ cong-∘ _ _ (_≃ᴱ_.right-inverse-of C≃D _) ⟩

            cong (_≃ᴱ_.to C≃D)
              (cong (_≃ᴱ_.from C≃D) (_≃ᴱ_.right-inverse-of C≃D _))  ≡⟨ cong (cong (_≃ᴱ_.to C≃D)) $ _≃ᴱ_.right-left-lemma C≃D _ ⟩∎

            cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _)         ∎
      in

      trans (sym
        (trans (cong (λ set → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D (set d₁ d₂)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D))
           (cong (λ get → get d₂)
              (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D))))
      (trans (cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _))
         (_≃ᴱ_.right-inverse-of C≃D _))                                 ≡⟨ cong₂ (λ p q → trans (sym (trans p q))
                                                                                            (trans (cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _))
                                                                                               (_≃ᴱ_.right-inverse-of C≃D _)))
                                                                             lemma
                                                                             (cong-ext ext) ⟩
      trans (sym
        (trans (cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _))
           (_≃ᴱ_.right-inverse-of C≃D _)))
      (trans (cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _))
         (_≃ᴱ_.right-inverse-of C≃D _))                                 ≡⟨ trans-symˡ (trans _ (_≃ᴱ_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                            ∎

    @0 lemma₂ : _
    lemma₂ = λ d →
      let lemma =
            cong (λ set → set d (_≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)     ≡⟨ cong (cong (λ set → set d (_≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d)))) $
                                                                     ext-const ext ⟩

            cong (λ set → set d (_≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d)))
              (cong const $ ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)    ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D) ⟩

            cong (λ set → set (_≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d)))
              (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)                 ≡⟨ cong-ext ext ⟩∎

            _≃ᴱ_.right-inverse-of C≃D _                           ∎
      in
      trans (sym
        (trans (cong (λ set → set d (_≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D))
           (cong (λ get → get d)
              (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D))))
        (trans
           (cong (_≃ᴱ_.to C≃D) (_≃ᴱ_.left-inverse-of C≃D _))
           (_≃ᴱ_.left-inverse-of (inverse C≃D) _))                    ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                           (cong₂ trans lemma (cong-ext ext))
                                                                           (cong₂ trans
                                                                              (_≃ᴱ_.left-right-lemma C≃D _)
                                                                              (EEq.left-inverse-of∘inverse C≃D)) ⟩
      trans (sym (trans (_≃ᴱ_.right-inverse-of C≃D _)
                    (_≃ᴱ_.right-inverse-of C≃D _)))
        (trans (_≃ᴱ_.right-inverse-of C≃D _)
           (_≃ᴱ_.right-inverse-of C≃D _))                             ≡⟨ trans-symˡ (trans _ (_≃ᴱ_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                          ∎

    @0 lemma₃ : _
    lemma₃ = λ d d₁ d₂ →
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
         (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)
         (trans (refl _)
            (trans
               (cong (λ _ → _≃ᴱ_.to C≃D (_≃ᴱ_.from C≃D d₂))
                  (_≃ᴱ_.right-inverse-of (inverse C≃D)
                     (_≃ᴱ_.from C≃D d₁)))
               (cong (_≃ᴱ_.to C≃D) (refl _))))               ≡⟨ cong (subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
                                                                         (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)) $
                                                                trans (trans-reflˡ _) $
                                                                trans (cong (flip trans _) $ cong-const _) $
                                                                trans (trans-reflˡ _) $
                                                                cong-refl _ ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
         (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)
         (refl _)                                            ≡⟨ cong (flip (subst (λ set → set (set d d₁) d₂ ≡ set d d₂)) _) $
                                                                ext-const ext ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
        (cong const $ ⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)
        (refl _)                                             ≡⟨ sym $ subst-∘ _ _ _ ⟩

      subst (λ set → set d₂ ≡ set d₂)
        (⟨ext⟩ $ _≃ᴱ_.right-inverse-of C≃D)
        (refl _)                                             ≡⟨ subst-ext ext ⟩

      subst (λ set → set ≡ set)
        (_≃ᴱ_.right-inverse-of C≃D d₂)
        (refl _)                                             ≡⟨ ≡⇒↝ _ (sym [subst≡]≡[trans≡trans]) (

          trans (refl _) (_≃ᴱ_.right-inverse-of C≃D d₂)           ≡⟨ trans-reflˡ _ ⟩
          _≃ᴱ_.right-inverse-of C≃D d₂                            ≡⟨ sym $ trans-reflʳ _ ⟩
          trans (_≃ᴱ_.right-inverse-of C≃D d₂) (refl _)           ∎) ⟩

      refl _                                                 ∎

-- In erased contexts the left-to-right direction of ≃ᴱ⇔≅ᴱ is a right
-- inverse of the right-to-left direction.

@0 ≃ᴱ⇔≅ᴱ∘≃ᴱ⇔≅ᴱ :
  (A≃B : A ≃ᴱ B) → _⇔_.from ≃ᴱ⇔≅ᴱ (_⇔_.to ≃ᴱ⇔≅ᴱ A≃B) ≡ A≃B
≃ᴱ⇔≅ᴱ∘≃ᴱ⇔≅ᴱ _ = EEq.to≡to→≡ ext (refl _)

-- The forward direction of ≃ᴱ⇔≅ᴱ maps identity to an isomorphism for
-- which the first projection is the identity.

≃ᴱ⇔≅ᴱ-id≡id :
  let open Lens-combinators in
  proj₁ (_⇔_.to ≃ᴱ⇔≅ᴱ F.id) ≡ id {A = A}
≃ᴱ⇔≅ᴱ-id≡id = equal-laws→≡
  (_↔_.to Lens-as-Σ (proj₁ (_⇔_.to ≃ᴱ⇔≅ᴱ F.id)) .proj₂ .proj₂)
  (_↔_.to Lens-as-Σ id                          .proj₂ .proj₂)
  (λ _ _ → refl _)
  (λ a →
     _≃ᴱ_.left-inverse-of F.id a               ≡⟨ sym $ _≃ᴱ_.right-left-lemma F.id _ ⟩
     cong P.id (_≃ᴱ_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                        ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                    ∎)
  (λ _ _ _ → refl _)
  where
  open Lens-combinators

-- If A is a set, then there is an equivalence with erased proofs
-- between A ≃ᴱ B and A ≅ᴱ B.

≃ᴱ≃ᴱ≅ᴱ :
  @0 Is-set A →
  (A ≃ᴱ B) ≃ᴱ (A ≅ᴱ B)
≃ᴱ≃ᴱ≅ᴱ A-set = EEq.↔→≃ᴱ
  (_⇔_.to   ≃ᴱ⇔≅ᴱ)
  (_⇔_.from ≃ᴱ⇔≅ᴱ)
  (λ (l₁ , l₂ , [ eq₁ , eq₂ ]) →
     _↔_.from (equality-characterisation-for-sets-≅ᴱ A-set) $
     ⟨ext⟩ λ a → ⟨ext⟩ λ b →
       get l₂ b                                            ≡⟨ sym $ ext⁻¹ (ext⁻¹ (cong set eq₂) _) _ ⟩

       set l₁ (set l₁ a b)
         (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))         ≡⟨ set-set l₁ _ _ _ ⟩

       set l₁ a (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))  ≡⟨ cong (λ b′ → set l₁ a (set l₂ b′ (get l₂ b))) $ get-set l₁ _ _ ⟩

       set l₁ a (set l₂ b (get l₂ b))                      ≡⟨ cong (set l₁ a) $ set-get l₂ _ ⟩∎

       set l₁ a b                                          ∎)
  ≃ᴱ⇔≅ᴱ∘≃ᴱ⇔≅ᴱ
  where
  open Lens
  open Lens-combinators

-- The equivalence maps identity to an isomorphism for which the first
-- projection is the identity.

≃ᴱ≃ᴱ≅ᴱ-id≡id :
  let open Lens-combinators in
  (@0 A-set : Is-set A) →
  proj₁ (_≃ᴱ_.to (≃ᴱ≃ᴱ≅ᴱ A-set) F.id) ≡ id
≃ᴱ≃ᴱ≅ᴱ-id≡id _ = ≃ᴱ⇔≅ᴱ-id≡id

-- The type Has-quasi-inverseᴱ id is not necessarily a proposition.

Has-quasi-inverseᴱ-id-not-proposition :
  let open Lens-combinators in
  ∃ λ (A : Type a) →
    ¬ Is-proposition (Has-quasi-inverseᴱ (id {A = A}))
Has-quasi-inverseᴱ-id-not-proposition =
    _
  , Stable-¬
      [ Is-proposition (Has-quasi-inverseᴱ Lens-combinators.id)  ↝⟨ H-level-cong _ 1 $ Has-quasi-inverseᴱ≃Has-quasi-inverse TC.id ⟩
        Is-proposition (TC.Has-quasi-inverse TC.id)              ↝⟨ proj₂ $ TC.Has-quasi-inverse-id-not-proposition univ ⟩□
        ⊥                                                        □
      ]

-- There is not necessarily a split surjection from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe.

¬Is-equivalenceᴱ↠Has-quasi-inverseᴱ :
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ l)
¬Is-equivalenceᴱ↠Has-quasi-inverseᴱ {a = a} =
  Stable-¬
    [ ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ l)     ↝⟨ (λ hyp l →
                                                                      from-equivalence (Has-quasi-inverseᴱ≃Has-quasi-inverse l) F.∘
                                                                      hyp (Traditional-lens→Lens l) F.∘
                                                                      from-equivalence EEq.Is-equivalence≃Is-equivalenceᴱ) ⟩
      ({A B : Type a}
       (l : T.Lens A B) →
       Is-equivalence (T.Lens.get l) ↠ TC.Has-quasi-inverse l)  ↝⟨ TC.¬Is-equivalence↠Has-quasi-inverse univ ⟩□

      ⊥                                                         □
    ]

-- There is not necessarily an equivalence with erased proofs from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe.

¬Is-equivalenceᴱ≃Has-quasi-inverseᴱ :
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ l)
¬Is-equivalenceᴱ≃Has-quasi-inverseᴱ {a = a} =
  Stable-¬
    [ ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ l)  ↝⟨ (λ hyp → _≃_.surjection ⊚ EEq.≃ᴱ→≃ ⊚ hyp) ⟩

      ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ l)   ↝⟨ ¬Is-equivalenceᴱ↠Has-quasi-inverseᴱ ⟩□

      ⊥                                                       □
    ]

------------------------------------------------------------------------
-- Isomorphisms expressed using bi-invertibility for lenses

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≊ᴱ_ to _≊ᴱ_;
            Has-left-inverseᴱ to Has-left-inverseᴱ;
            Has-right-inverseᴱ to Has-right-inverseᴱ;
            Is-bi-invertibleᴱ to Is-bi-invertibleᴱ)

open BM public
  using ()
  renaming (Is-bi-invertibleᴱ-propositional to
            Is-bi-invertibleᴱ-propositional)

-- In erased contexts Has-left-inverseᴱ (Traditional-lens→Lens l) is
-- equivalent to TC.Has-left-inverse l.

@0 Has-left-inverseᴱ≃Has-left-inverse :
  (l : T.Lens A B) →
  Has-left-inverseᴱ (Traditional-lens→Lens l) ≃ TC.Has-left-inverse l
Has-left-inverseᴱ≃Has-left-inverse l =
  (∃ λ l⁻¹ → Erased (l⁻¹ LC.∘ l′ ≡ LC.id))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l⁻¹ LC.∘ l′ ≡ LC.id )  ↝⟨ (Σ-cong Lens≃Traditional-lens λ _ → inverse $ Eq.≃-≡ Lens≃Traditional-lens) ⟩□
  (∃ λ l⁻¹ →         l⁻¹ TC.∘ l  ≡ TC.id )  □
  where
  module LC = Lens-combinators

  l′ = Traditional-lens→Lens l

-- In erased contexts Has-right-inverseᴱ (Traditional-lens→Lens l) is
-- equivalent to TC.Has-right-inverse l.

@0 Has-right-inverseᴱ≃Has-right-inverse :
  (l : T.Lens A B) →
  Has-right-inverseᴱ (Traditional-lens→Lens l) ≃ TC.Has-right-inverse l
Has-right-inverseᴱ≃Has-right-inverse l =
  (∃ λ l⁻¹ → Erased (l′ LC.∘ l⁻¹ ≡ LC.id))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′ LC.∘ l⁻¹ ≡ LC.id )  ↝⟨ (Σ-cong Lens≃Traditional-lens λ _ → inverse $ Eq.≃-≡ Lens≃Traditional-lens) ⟩□
  (∃ λ l⁻¹ →         l  TC.∘ l⁻¹ ≡ TC.id )  □
  where
  module LC = Lens-combinators

  l′ = Traditional-lens→Lens l

-- In erased contexts Is-bi-invertibleᴱ (Traditional-lens→Lens l) is
-- equivalent to TC.Is-bi-invertible l.

@0 Is-bi-invertibleᴱ≃Is-bi-invertible :
  (l : T.Lens A B) →
  Is-bi-invertibleᴱ (Traditional-lens→Lens l) ≃ TC.Is-bi-invertible l
Is-bi-invertibleᴱ≃Is-bi-invertible l =
  Is-bi-invertibleᴱ l′                            ↔⟨⟩
  Has-left-inverseᴱ l′ × Has-right-inverseᴱ l′    ↝⟨ Has-left-inverseᴱ≃Has-left-inverse l ×-cong
                                                     Has-right-inverseᴱ≃Has-right-inverse l ⟩
  TC.Has-left-inverse l × TC.Has-right-inverse l  ↔⟨⟩
  TC.Is-bi-invertible l                           □
  where
  l′ = Traditional-lens→Lens l

-- In erased contexts A ≊ᴱ B is equivalent to A TC.≊ B.

@0 ≊ᴱ≃≊ : (A ≊ᴱ B) ≃ (A TC.≊ B)
≊ᴱ≃≊ {A = A} {B = B} =
  (∃ λ (l : Lens A B) → Is-bi-invertibleᴱ l)      ↝⟨ (inverse $
                                                      Σ-cong (inverse Lens≃Traditional-lens) λ l →
                                                      inverse $ Is-bi-invertibleᴱ≃Is-bi-invertible l) ⟩□
  (∃ λ (l : T.Lens A B) → TC.Is-bi-invertible l)  □

-- An equality characterisation lemma for A ≊ᴱ B that applies when A
-- is a set.

@0 equality-characterisation-for-sets-≊ᴱ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≊ᴱ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≊ᴱ
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂                          ↔⟨ inverse $ Eq.≃-≡ ≊ᴱ≃≊ ⟩
  _≃_.to ≊ᴱ≃≊ f₁ ≡ _≃_.to ≊ᴱ≃≊ f₂  ↝⟨ TC.equality-characterisation-for-sets-≊ A-set ⟩□
  set l₁₁ ≡ set l₁₂                □
  where
  open Lens

-- There is a logical equivalence between A ≃ᴱ B and A ≊ᴱ B.

≃ᴱ⇔≊ᴱ : (A ≃ᴱ B) ⇔ (A ≊ᴱ B)
≃ᴱ⇔≊ᴱ = record
  { to   = _⇔_.to BM.≅ᴱ⇔≊ᴱ ⊚ _⇔_.to ≃ᴱ⇔≅ᴱ
  ; from = _⇔_.from ≃ᴱ⇔≅ᴱ ⊚ _⇔_.from BM.≅ᴱ⇔≊ᴱ
  }

-- In erased contexts the left-to-right direction of ≃ᴱ⇔≊ᴱ is a right
-- inverse of the right-to-left direction.

@0 ≃ᴱ⇔≊ᴱ∘≃ᴱ⇔≊ᴱ :
  (A≃B : A ≃ᴱ B) → _⇔_.from ≃ᴱ⇔≊ᴱ (_⇔_.to ≃ᴱ⇔≊ᴱ A≃B) ≡ A≃B
≃ᴱ⇔≊ᴱ∘≃ᴱ⇔≊ᴱ _ = EEq.to≡to→≡ ext (refl _)

-- The forward direction of ≃ᴱ⇔≊ᴱ maps identity to an isomorphism for
-- which the first projection is the identity.

≃ᴱ⇔≊ᴱ-id≡id :
  let open Lens-combinators in
  proj₁ (_⇔_.to ≃ᴱ⇔≊ᴱ F.id) ≡ id {A = A}
≃ᴱ⇔≊ᴱ-id≡id = equal-laws→≡
  (_↔_.to Lens-as-Σ (proj₁ (_⇔_.to ≃ᴱ⇔≊ᴱ F.id)) .proj₂ .proj₂)
  (_↔_.to Lens-as-Σ id                          .proj₂ .proj₂)
  (λ _ _ → refl _)
  (λ a →
     _≃ᴱ_.left-inverse-of F.id a               ≡⟨ sym $ _≃ᴱ_.right-left-lemma F.id _ ⟩
     cong P.id (_≃ᴱ_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                        ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                    ∎)
  (λ _ _ _ → refl _)
  where
  open Lens-combinators

-- If A is a set, then there is an equivalence between A ≃ᴱ B and
-- A ≊ᴱ B.

≃ᴱ≃ᴱ≊ᴱ : @0 Is-set A → (A ≃ᴱ B) ≃ᴱ (A ≊ᴱ B)
≃ᴱ≃ᴱ≊ᴱ {A = A} {B = B} A-set =
  A ≃ᴱ B  ↝⟨ ≃ᴱ≃ᴱ≅ᴱ A-set ⟩
  A ≅ᴱ B  ↝⟨ inverse $ BM.≊ᴱ≃ᴱ≅ᴱ-domain (lens-preserves-h-level-of-domain 1 A-set) ⟩□
  A ≊ᴱ B  □

-- The equivalence ≃ᴱ≃ᴱ≊ᴱ maps identity to an isomorphism for which the
-- first projection is the identity.

≃ᴱ≃ᴱ≊ᴱ-id≡id :
  let open Lens-combinators in
  (@0 A-set : Is-set A) →
  proj₁ (_≃ᴱ_.to (≃ᴱ≃ᴱ≊ᴱ A-set) F.id) ≡ id
≃ᴱ≃ᴱ≊ᴱ-id≡id _ = ≃ᴱ⇔≊ᴱ-id≡id
  where
  open Lens-combinators

-- The right-to-left direction of ≃ᴱ≃ᴱ≊ᴱ maps bi-invertible lenses to
-- their getter functions.

to-from-≃ᴱ≃ᴱ≊ᴱ≡get :
  (@0 A-set : Is-set A) (A≊B@(l , _) : A ≊ᴱ B) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ A-set) A≊B) ≡ Lens.get l
to-from-≃ᴱ≃ᴱ≊ᴱ≡get _ _ = refl _

-- The getter function of a bi-invertible lens is an equivalence (with
-- erased proofs).

Is-bi-invertibleᴱ→Is-equivalenceᴱ-get :
  (l : Lens A B) →
  Is-bi-invertibleᴱ l → Is-equivalenceᴱ (Lens.get l)
Is-bi-invertibleᴱ→Is-equivalenceᴱ-get l is-bi-inv =
  _≃ᴱ_.is-equivalence (_⇔_.from ≃ᴱ⇔≊ᴱ (l , is-bi-inv))

-- If the getter function is an equivalence (with erased proofs), then
-- the lens is bi-invertible (with erased proofs).

Is-equivalenceᴱ-get→Is-bi-invertibleᴱ :
  (l : Lens A B) →
  Is-equivalenceᴱ (Lens.get l) → Is-bi-invertibleᴱ l
Is-equivalenceᴱ-get→Is-bi-invertibleᴱ {A = A} {B = B} l′ is-equiv =
                        $⟨ l⁻¹ , [ l∘l⁻¹≡id , l⁻¹∘l≡id ] ⟩
  Has-quasi-inverseᴱ l  ↝⟨ B.Has-quasi-inverseᴱ→Is-bi-invertibleᴱ l ⟩
  Is-bi-invertibleᴱ l   ↝⟨ subst (λ l → Is-bi-invertibleᴱ (erased l)) ([]-cong [ getter-equivalence→lens≡ l′ is-equiv ]) ⟩□
  Is-bi-invertibleᴱ l′  □
  where
  open Lens
  open Lens-combinators

  -- A lens that is equal to l′.

  l : Lens A B
  l = getter-equivalence→lens l′ is-equiv

  A≃B = EEq.⟨ get l , is-equiv ⟩

  open _≃ᴱ_ A≃B

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

    @0 l∘l⁻¹≡id : l ∘ l⁻¹ ≡ id
    l∘l⁻¹≡id = constant-setter→≡id
      (_ , _ , _↔_.to Lens-as-Σ (l ∘ l⁻¹) .proj₂ .proj₂)
      ( right-inverse-of
      , right-inverse-of
      , [ (λ b₁ b₂ →
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
             set-set (l ∘ l⁻¹) b b₁ b₂                                ≡⟨⟩

             trans (set-set l⁻¹ b (from b₁) (from b₂))
               (trans (cong (λ _ → get l (from b₂))
                         (get-set l⁻¹ b (from b₁)))
                  (cong (get l) (set-set l (from b) b₁ b₂)))          ≡⟨ cong (trans _) $
                                                                         trans (cong (flip trans _) $ cong-const _) $
                                                                         trans-reflˡ _ ⟩
             trans (set-set l⁻¹ b (from b₁) (from b₂))
               (cong (get l) (set-set l (from b) b₁ b₂))              ≡⟨⟩

             trans (trans (sym (right-inverse-of _))
                      (trans (sym (cong (get l)
                                     (set-set l (from b)
                                        (get l (from b₁))
                                        (get l (from b₂)))))
                         (right-inverse-of _)))
               (cong (get l) (set-set l (from b) b₁ b₂))              ≡⟨ cong (λ b′ → trans (trans (sym (right-inverse-of _))
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
               (cong (get l) (set-set l (from b) b₁ b₂))              ≡⟨ cong (λ f → trans (trans (sym (f _))
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
               (cong (get l) (set-set l (from b) b₁ b₂))              ≡⟨ elim₁
                                                                           (λ {f} (p : f ≡ P.id) →
                                                                              (q : ∀ b → f b ≡ f b) →
                                                                              trans (trans (sym (ext⁻¹ p (f b₂)))
                                                                                       (trans (sym (q (f b₂))) (ext⁻¹ p (f b₂))))
                                                                                (q b₂) ≡
                                                                              refl _)
                                                                           (λ q →
                 trans (trans (sym (ext⁻¹ (refl P.id) _))
                          (trans (sym (q _)) (ext⁻¹ (refl P.id) _)))
                   (q _)                                                      ≡⟨ cong (λ eq → trans (trans (sym eq) (trans (sym (q _)) eq))
                                                                                                (q _)) $
                                                                                 ext⁻¹-refl _ ⟩
                 trans (trans (sym (refl _))
                          (trans (sym (q _)) (refl _)))
                   (q _)                                                      ≡⟨ cong₂ (λ p r → trans (trans p r) (q _))
                                                                                   sym-refl
                                                                                   (trans-reflʳ _) ⟩

                 trans (trans (refl _) (sym (q _))) (q _)                     ≡⟨ cong (λ eq → trans eq (q _)) $ trans-reflˡ (sym (q _)) ⟩

                 trans (sym (q _)) (q _)                                      ≡⟨ trans-symˡ (q _) ⟩∎

                 refl _                                                       ∎)
                                                                           (⟨ext⟩ right-inverse-of)
                                                                           (cong (get l) ⊚ set-set l (from b) b₁) ⟩
             refl _                                                   ∎)
        ]
      )

    -- The lens l⁻¹ is a left inverse of l.

    @0 l⁻¹∘l≡id : l⁻¹ ∘ l ≡ id
    l⁻¹∘l≡id = constant-setter→≡id
      (_ , _ , _↔_.to Lens-as-Σ (l⁻¹ ∘ l) .proj₂ .proj₂)
      ( left-inverse-of
      , left-inverse-of
      , [ (λ a₁ a₂ →
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
                           (right-inverse-of _)))                   ≡⟨ cong-trans _ _ (trans _ (right-inverse-of _)) ⟩

                   trans (cong from $ sym $ cong (get l) $
                          set-get l (from (get l a)))
                     (cong from (trans (right-inverse-of _)
                                   (right-inverse-of _)))           ≡⟨ cong (λ eq → trans (cong from eq)
                                                                                      (cong from (trans (right-inverse-of _)
                                                                                                    (right-inverse-of _)))) $ sym $
                                                                       cong-sym _ (set-get l (from (get l a))) ⟩
                   trans (cong from $ cong (get l) $
                          sym (set-get l (from (get l a))))
                     (cong from (trans (right-inverse-of _)
                                   (right-inverse-of _)))           ≡⟨ cong₂ trans
                                                                         (cong-∘ _ _ (sym (set-get l (from (get l a)))))
                                                                         (cong-trans _ _ (right-inverse-of _)) ⟩
                   trans (cong (from ⊚ get l)
                            (sym (set-get l (from (get l a)))))
                     (trans (cong from (right-inverse-of _))
                        (cong from (right-inverse-of _)))           ≡⟨ cong₂ (λ p q → trans (cong (from ⊚ get l)
                                                                                               (sym (set-get l (from (get l a)))))
                                                                                        (trans p q))
                                                                         (right-left-lemma _)
                                                                         (right-left-lemma _) ⟩∎
                   trans (cong (from ⊚ get l)
                            (sym (set-get l (from (get l a)))))
                     (trans (left-inverse-of _)
                        (left-inverse-of _))                        ∎

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
                           (right-inverse-of _)))                 ≡⟨ cong-trans _ _ (trans (sym (cong (get l) q)) (right-inverse-of _)) ⟩

                   trans (cong from (sym (right-inverse-of _)))
                     (cong from (trans (sym (cong (get l) q))
                                   (right-inverse-of _)))         ≡⟨ cong₂ trans
                                                                       (cong-sym _ (right-inverse-of _))
                                                                       (cong-trans _ _ (right-inverse-of _)) ⟩
                   trans (sym (cong from (right-inverse-of _)))
                     (trans (cong from (sym (cong (get l) q)))
                        (cong from (right-inverse-of _)))         ≡⟨ cong₂ (λ p r → trans (sym p) (trans (cong from (sym (cong (get l) q))) r))
                                                                       (right-left-lemma _)
                                                                       (right-left-lemma _) ⟩
                   trans (sym (left-inverse-of _))
                     (trans (cong from (sym (cong (get l) q)))
                        (left-inverse-of _))                      ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                    (trans eq (left-inverse-of _))) $
                                                                     cong-sym _ (cong (get l) q) ⟩
                   trans (sym (left-inverse-of _))
                     (trans (sym (cong from (cong (get l) q)))
                        (left-inverse-of _))                      ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                    (trans (sym eq) (left-inverse-of _))) $
                                                                     cong-∘ _ _ q ⟩
                   trans (sym (left-inverse-of _))
                     (trans (sym (cong (from ⊚ get l) q))
                        (left-inverse-of _))                      ≡⟨ cong (λ g → trans (sym (g _))
                                                                                   (trans (sym (cong (from ⊚ get l) q)) (g _))) $ sym $
                                                                     _≃_.left-inverse-of (Eq.extensionality-isomorphism ext)
                                                                       left-inverse-of ⟩∎
                   trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) _))
                     (trans (sym (cong (from ⊚ get l) q))
                        (ext⁻¹ (⟨ext⟩ left-inverse-of) _))        ∎

                 f = from ⊚ get l
             in
             set-set (l⁻¹ ∘ l) a a₁ a₂                              ≡⟨⟩

             trans (set-set l a (get l a₁) (get l a₂))
               (trans (cong (λ _ → from (get l a₂))
                         (right-inverse-of (get l a₁)))
                  (cong from (set-set l⁻¹ (get l a) a₁ a₂)))        ≡⟨ cong (trans _) $
                                                                       trans (cong (flip trans _) $ cong-const _) $
                                                                       trans-reflˡ _ ⟩
             trans (set-set l a (get l a₁) (get l a₂))
               (cong from (set-set l⁻¹ (get l a) a₁ a₂))            ≡⟨⟩

             trans (set-set l a (get l a₁) (get l a₂))
               (cong from
                  (trans (sym (right-inverse-of _))
                     (trans (sym (cong (get l)
                                    (set-set l (from (get l a))
                                       (get l a₁) (get l a₂))))
                        (right-inverse-of _))))                     ≡⟨ cong (λ a′ → trans q
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
                        (right-inverse-of _))))                     ≡⟨ cong (trans q) lemma ⟩

             trans q
               (trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂)))
                  (trans (sym (cong f q))
                     (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂))))       ≡⟨ elim₁
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
                         (ext⁻¹ (refl P.id) a₂)))                         ≡⟨ cong (λ eq → trans q (trans (sym eq)
                                                                                                     (trans (sym (cong P.id q)) eq))) $
                                                                             ext⁻¹-refl _ ⟩
                 trans q (trans (sym (refl _))
                            (trans (sym (cong P.id q)) (refl _)))         ≡⟨ cong₂ (λ p r → trans q (trans p r))
                                                                               sym-refl
                                                                               (trans-reflʳ _) ⟩

                 trans q (trans (refl _) (sym (cong P.id q)))             ≡⟨ cong (trans q) $ trans-reflˡ (sym (cong P.id q)) ⟩

                 trans q (sym (cong P.id q))                              ≡⟨ cong (λ eq → trans q (sym eq)) $ sym $ cong-id q ⟩

                 trans q (sym q)                                          ≡⟨ trans-symʳ q ⟩∎

                 refl _                                                   ∎)
                                                                       (⟨ext⟩ left-inverse-of)
                                                                       q ⟩

             refl _                                                 ∎)
        ]
      )

-- There is an equivalence with erased proofs between "l is
-- bi-invertible (with erased proofs) " and "the getter of l is an
-- equivalence (with erased proofs)".

Is-bi-invertibleᴱ≃ᴱIs-equivalenceᴱ-get :
  (l : Lens A B) →
  Is-bi-invertibleᴱ l ≃ᴱ Is-equivalenceᴱ (Lens.get l)
Is-bi-invertibleᴱ≃ᴱIs-equivalenceᴱ-get l = EEq.⇔→≃ᴱ
  (BM.Is-bi-invertibleᴱ-propositional l)
  (EEq.Is-equivalenceᴱ-propositional ext _)
  (Is-bi-invertibleᴱ→Is-equivalenceᴱ-get l)
  (Is-equivalenceᴱ-get→Is-bi-invertibleᴱ l)

-- There is in general no split surjection from equivalences (with
-- erased proofs) to lenses that are bi-invertible (with erased
-- proofs), if the right-to-left direction of the split surjection is
-- required to map bi-invertible lenses to their getter functions.

¬≃ᴱ↠≊ᴱ :
  ¬ ∃ λ (≃ᴱ↠≊ᴱ : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠ (↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ)) →
      (x@(l , _) : ↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ) →
      _≃ᴱ_.to (_↠_.from ≃ᴱ↠≊ᴱ x) ≡ Lens.get l
¬≃ᴱ↠≊ᴱ {a = a} =
  Stable-¬
    [ (∃ λ (≃ᴱ↠≊ᴱ : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠ (↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ)) →
         (x@(l , _) : ↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ) →
         _≃ᴱ_.to (_↠_.from ≃ᴱ↠≊ᴱ x) ≡ Lens.get l)                   ↝⟨ Σ-map
                                                                        ((∃-cong λ l → _≃_.surjection $ EEq.≃ᴱ→≃ $ Is-bi-invertibleᴱ≃ᴱIs-equivalenceᴱ-get l) F.∘_)
                                                                        (λ hyp _ → hyp _) ⟩
      (∃ λ (f : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠
                (∃ λ (l : Lens (↑ a 𝕊¹ᴱ) (↑ a 𝕊¹ᴱ)) →
                   Is-equivalenceᴱ (Lens.get l))) →
         ∀ p → _≃ᴱ_.to (_↠_.from f p) ≡ Lens.get (proj₁ p))         ↝⟨ ¬-≃ᴱ-↠-Σ-Lens-Is-equivalenceᴱ-get ⟩□

      ⊥                                                             □
    ]

-- There is in general no equivalence with erased proofs between
-- equivalences (with erased proofs) and lenses that are bi-invertible
-- (with erased proofs), if the right-to-left direction of the
-- equivalence is required to map bi-invertible lenses to their getter
-- functions.

¬≃ᴱ≃ᴱ≊ᴱ :
  ¬ ∃ λ (≃ᴱ≃ᴱ≊ᴱ : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ≃ᴱ (↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ)) →
      (x@(l , _) : ↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ) →
      _≃ᴱ_.to (_≃ᴱ_.from ≃ᴱ≃ᴱ≊ᴱ x) ≡ Lens.get l
¬≃ᴱ≃ᴱ≊ᴱ {a = a} =
  Stable-¬
    [ (∃ λ (≃ᴱ≃ᴱ≊ᴱ : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ≃ᴱ (↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ)) →
         (x@(l , _) : ↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ) →
         _≃ᴱ_.to (_≃ᴱ_.from ≃ᴱ≃ᴱ≊ᴱ x) ≡ Lens.get l)                   ↝⟨ Σ-map (_≃_.surjection ⊚ EEq.≃ᴱ→≃) P.id ⟩

      (∃ λ (≃ᴱ↠≊ᴱ : (↑ a 𝕊¹ᴱ ≃ᴱ ↑ a 𝕊¹ᴱ) ↠ (↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ)) →
         (x@(l , _) : ↑ a 𝕊¹ᴱ ≊ᴱ ↑ a 𝕊¹ᴱ) →
         _≃ᴱ_.to (_↠_.from ≃ᴱ↠≊ᴱ x) ≡ Lens.get l)                     ↝⟨ ¬≃ᴱ↠≊ᴱ ⟩□

      ⊥                                                               □
    ]

-- The lemma ≃ᴱΣ∥set⁻¹ᴱ∥ᴱ× does not hold in general if the requirement
-- that A is a set is dropped.

≄ᴱΣ∥set⁻¹ᴱ∥ᴱ× :
  ¬ ({A B : Type a} (l : Lens A B) →
     A ≃ᴱ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ᴱ f ∥ᴱ) × B))
≄ᴱΣ∥set⁻¹ᴱ∥ᴱ× {a = a} =
  Stable-¬
    [ ({A B : Type a} (l : Lens A B) →
       A ≃ᴱ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ᴱ f ∥ᴱ) × B))  ↝⟨ EEq.≃ᴱ→≃ ⊚_ ⟩

      ({A B : Type a} (l : Lens A B) →
       A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ᴱ f ∥ᴱ) × B))   ↝⟨ ((×-cong₁ λ _ → ∃-cong λ _ → PT.∥∥ᴱ≃∥∥) F.∘_) ⊚_ ⟩

      ({A B : Type a} (l : Lens A B) →
       A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ᴱ f ∥) × B))    ↝⟨ ((×-cong₁ λ _ → ∃-cong λ _ → PT.∥∥-cong $ inverse ECP.⁻¹≃⁻¹ᴱ) F.∘_) ⊚_ ⟩

      ({A B : Type a} (l : Lens A B) →
       A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ f ∥) × B))     ↝⟨ _⊚ Traditional-lens→Lens ⟩

      ({A B : Type a} (l : T.Lens A B) →
       A ≃ ((∃ λ (f : B → A) → ∥ T.Lens.set l ⁻¹ f ∥) × B))   ↝⟨ TC.≄Σ∥set⁻¹∥× univ ⟩□

      ⊥                                                       □
    ]
