------------------------------------------------------------------------
-- Lenses defined in terms of a getter, equivalences between the
-- getter's "preimages", and a coherence property
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Equivalent-preimages where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as B using (_↔_)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths as PT
  using (∥_∥; ∣_∣)
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent.Higher as Higher
import Lens.Non-dependent.Traditional as Traditional

private
  variable
    ℓ       : Level
    A B C   : Set ℓ
    a b c z : A

------------------------------------------------------------------------
-- The lens type family

-- Lenses defined in terms of a getter, equivalences between the
-- getter's "preimages", and a coherence property.
--
-- This definition is based on a suggestion from Andrea Vezzosi.

record Lens (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  pattern
  constructor lens
  field
    -- A getter.
    get : A → B

    -- A function from one "preimage" of get to another.
    get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂

    -- This function is an equivalence.
    get⁻¹-const-equivalence :
      (b₁ b₂ : B) → Is-equivalence (get⁻¹-const b₁ b₂)

    -- A coherence property.
    get⁻¹-const-∘ :
      (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
      get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p

  -- All the getter's "preimages" are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant b₁ b₂ = Eq.⟨ _ , get⁻¹-const-equivalence b₁ b₂ ⟩

  -- The inverse of get⁻¹-const.

  get⁻¹-const⁻¹ : (b₁ b₂ : B) → get ⁻¹ b₂ → get ⁻¹ b₁
  get⁻¹-const⁻¹ b₁ b₂ = _≃_.from (get⁻¹-constant b₁ b₂)

  -- Some derived coherence properties.

  get⁻¹-const-id :
    (b : B) (p : get ⁻¹ b) → get⁻¹-const b b p ≡ p
  get⁻¹-const-id b p =
    get⁻¹-const b b p                                        ≡⟨ sym $ _≃_.left-inverse-of (get⁻¹-constant _ _) _ ⟩
    get⁻¹-const⁻¹ b b (get⁻¹-const b b (get⁻¹-const b b p))  ≡⟨ cong (get⁻¹-const⁻¹ b b) $ get⁻¹-const-∘ _ _ _ _ ⟩
    get⁻¹-const⁻¹ b b (get⁻¹-const b b p)                    ≡⟨ _≃_.left-inverse-of (get⁻¹-constant _ _) _ ⟩∎
    p                                                        ∎

  get⁻¹-const-inverse :
    (b₁ b₂ : B) (p : get ⁻¹ b₁) →
    get⁻¹-const b₁ b₂ p ≡ get⁻¹-const⁻¹ b₂ b₁ p
  get⁻¹-const-inverse b₁ b₂ p =
    sym $ _≃_.to-from (get⁻¹-constant _ _) (
      get⁻¹-const b₂ b₁ (get⁻¹-const b₁ b₂ p)  ≡⟨ get⁻¹-const-∘ _ _ _ _ ⟩
      get⁻¹-const b₁ b₁ p                      ≡⟨ get⁻¹-const-id _ _ ⟩∎
      p                                        ∎)

  -- A setter.

  set : A → B → A
  set a b =       $⟨ a , refl ⟩
    get ⁻¹ get a  ↝⟨ get⁻¹-const (get a) b ⟩
    get ⁻¹ b      ↝⟨ proj₁ ⟩□
    A             □

  -- The lens laws can be proved.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    get (proj₁ (get⁻¹-const (get a) b (a , refl)))  ≡⟨ proj₂ (get⁻¹-const (get a) b (a , refl)) ⟩∎
    b                                               ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    proj₁ (get⁻¹-const (get a) (get a) (a , refl))  ≡⟨ cong proj₁ $ get⁻¹-const-id _ _ ⟩∎
    a                                               ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl))  ≡⟨ elim¹
                                                                    (λ {b} eq →
                                                                       proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl)) ≡
                                                                       proj₁ (get⁻¹-const b b₂ (set a b₁ , eq)))
                                                                    refl
                                                                    (get-set a b₁) ⟩

    proj₁ (get⁻¹-const b₁ b₂ (set a b₁ , get-set a b₁))        ≡⟨⟩

    proj₁ (get⁻¹-const b₁ b₂
             (get⁻¹-const (get a) b₁ (a , refl)))              ≡⟨ cong proj₁ $ get⁻¹-const-∘ _ _ _ _ ⟩∎

    proj₁ (get⁻¹-const (get a) b₂ (a , refl))                  ∎

  -- A traditional lens.

  traditional-lens : Traditional.Lens A B
  traditional-lens = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }

-- The record type above is equivalent to a nested Σ-type.

Lens-as-Σ :
  Lens A B ≃
  ∃ λ (get : A → B) →
  ∃ λ (get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂) →
    ((b₁ b₂ : B) → Is-equivalence (get⁻¹-const b₁ b₂)) ×
    ((b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
     get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p)
Lens-as-Σ = Eq.↔→≃
  (λ l → get l
       , get⁻¹-const l
       , get⁻¹-const-equivalence l
       , get⁻¹-const-∘ l)
  (λ (g , c , c-e , c-∘) → record
     { get                     = g
     ; get⁻¹-const             = c
     ; get⁻¹-const-equivalence = c-e
     ; get⁻¹-const-∘           = c-∘
     })
  (λ _ → refl)
  (λ { (lens _ _ _ _) → refl })
  where
  open Lens

-- A variant of Lens-as-Σ.

Lens-as-Σ′ :
  Lens A B ≃
  ∃ λ (get : A → B) →
  ∃ λ (get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂) →
    let get⁻¹-const : ∀ _ _ → _
        get⁻¹-const = λ b₁ b₂ → _≃_.to (get⁻¹-constant b₁ b₂) in
    (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
    get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p
Lens-as-Σ′ {A = A} {B = B} =
  Lens A B                                                             ↝⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂) →
     ((b₁ b₂ : B) → Is-equivalence (get⁻¹-const b₁ b₂)) ×
     ((b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
      get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p))  ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (get : A → B) →
   ∃ λ ((get⁻¹-const , _) :
        ∃ λ (get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂) →
          (b₁ b₂ : B) → Is-equivalence (get⁻¹-const b₁ b₂)) →
     (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
     get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p)    ↝⟨ (∃-cong λ _ →
                                                                           Σ-cong-contra (ΠΣ-comm F.∘ ∀-cong ext (λ _ → ΠΣ-comm)) λ _ → F.id) ⟩
  (∃ λ (get : A → B) →
   ∃ λ (f :
        (b₁ b₂ : B) →
        ∃ λ (get⁻¹-const : get ⁻¹ b₁ → get ⁻¹ b₂) →
          Is-equivalence get⁻¹-const) →
     let get⁻¹-const : ∀ _ _ → _
         get⁻¹-const = λ b₁ b₂ → proj₁ (f b₁ b₂) in
     (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
     get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p)    ↝⟨ (∃-cong λ _ →
                                                                           Σ-cong-contra (∀-cong ext λ _ → ∀-cong ext λ _ → Eq.≃-as-Σ) λ _ →
                                                                                         F.id) ⟩□
  (∃ λ (get : A → B) →
   ∃ λ (get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂) →
     let get⁻¹-const : ∀ _ _ → _
         get⁻¹-const = λ b₁ b₂ → _≃_.to (get⁻¹-constant b₁ b₂) in
     (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
     get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p)    □

------------------------------------------------------------------------
-- Some results related to h-levels

-- If the domain of a lens is inhabited and has h-level n,
-- then the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} n l a =
  H-level n A  ↝⟨ H-level.respects-surjection surj n ⟩□
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

-- If A and B have h-level n given the assumption that the other type
-- is inhabited, then Lens A B has h-level n.

lens-preserves-h-level :
  ∀ n → (B → H-level n A) → (A → H-level n B) →
  H-level n (Lens A B)
lens-preserves-h-level {B = B} {A = A} n hA hB =
  H-level-cong _ n (inverse Lens-as-Σ′) $
  Σ-closure n (Π-closure ext n λ a →
               hB a) λ _ →
  Σ-closure n (Π-closure ext n λ b →
               Π-closure ext n λ _ →
               Eq.h-level-closure ext n
                 (⁻¹-closure (hA b) hB)
                 (⁻¹-closure (hA b) hB)) λ _ →
              (Π-closure ext n λ b →
               Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               ⇒≡ n (⁻¹-closure (hA b) hB))
  where
  ⁻¹-closure :
    {f : A → B} {x : B} →
    H-level n A → (A → H-level n B) →
    H-level n (f ⁻¹ x)
  ⁻¹-closure hA hB =
    Σ-closure n hA λ a →
    ⇒≡ n (hB a)

-- If A has positive h-level n, then Lens A B also has h-level n.

lens-preserves-h-level-of-domain :
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain n hA =
  [inhabited⇒+]⇒+ n λ l →
    lens-preserves-h-level (1 + n) (λ _ → hA) λ a →
      h-level-respects-lens-from-inhabited _ l a hA

------------------------------------------------------------------------
-- Some equality characterisation lemmas

-- An equality characterisation lemma.

equality-characterisation :
  let open Lens in
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (gc : ∀ b₁ b₂ p →
             subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p ≡
             get⁻¹-const l₂ b₁ b₂ p) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (Σ-≡,≡→≡ (⟨ext⟩ g)
          (⟨ext⟩ λ b₁ → ⟨ext⟩ λ b₂ → ⟨ext⟩ λ p → gc b₁ b₂ p))
       (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)
equality-characterisation {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                      ↝⟨ inverse $ Eq.≃-≡ (lemma₁ F.∘ Lens-as-Σ) ⟩

  ( ((get l₁ , get⁻¹-const l₁) , get⁻¹-const-∘ l₁)
  , get⁻¹-const-equivalence l₁
  ) ≡
  ( ((get l₂ , get⁻¹-const l₂) , get⁻¹-const-∘ l₂)
  , get⁻¹-const-equivalence l₂
  )                                                            ↔⟨ inverse $
                                                                  ignore-propositional-component
                                                                    (Π-closure ext 1 λ _ →
                                                                     Π-closure ext 1 λ _ →
                                                                     Eq.propositional ext _) ⟩
  ((get l₁ , get⁻¹-const l₁) , get⁻¹-const-∘ l₁) ≡
  ((get l₂ , get⁻¹-const l₂) , get⁻¹-const-∘ l₂)               ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

  (∃ λ (p : (get l₁ , get⁻¹-const l₁) ≡
            (get l₂ , get⁻¹-const l₂)) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       p (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                         ↝⟨ (Σ-cong-contra B.Σ-≡,≡↔≡ λ _ → F.id) ⟩

  (∃ λ (p : ∃ λ (g : get l₁ ≡ get l₂) →
              subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
                g (get⁻¹-const l₁) ≡
              get⁻¹-const l₂) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (uncurry Σ-≡,≡→≡ p) (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                         ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (gc : subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               g (get⁻¹-const l₁) ≡
             get⁻¹-const l₂) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (Σ-≡,≡→≡ g gc) (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                         ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ → F.id) ⟩

  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (gc : subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               (⟨ext⟩ g) (get⁻¹-const l₁) ≡
             get⁻¹-const l₂) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (Σ-≡,≡→≡ (⟨ext⟩ g) gc) (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                         ↝⟨ (∃-cong λ _ → Σ-cong-contra (inverse $ lemma₂ _) λ _ → F.id) ⟩□

  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (gc : ∀ b₁ b₂ p →
             subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p ≡
             get⁻¹-const l₂ b₁ b₂ p) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (Σ-≡,≡→≡ (⟨ext⟩ g)
          (⟨ext⟩ λ b₁ → ⟨ext⟩ λ b₂ → ⟨ext⟩ λ p → gc b₁ b₂ p))
       (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                         □
  where
  open Lens

  lemma₁ :
    {P : A → Set ℓ} {Q R : (x : A) → P x → Set ℓ} →
    (∃ λ (x : A) → ∃ λ (y : P x) → Q x y × R x y) ≃
    (∃ λ (((x , y) , _) : Σ (Σ A P) (uncurry R)) → Q x y)
  lemma₁ {A = A} {P = P} {Q = Q} {R = R} =
    (∃ λ (x : A) → ∃ λ (y : P x) → Q x y × R x y)                      ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩
    (∃ λ (x : A) → ∃ λ (y : P x) → R x y × Q x y)                      ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩
    (∃ λ (x : A) → ∃ λ ((y , _) : ∃ λ (y : P x) → R x y) → Q x y)      ↔⟨ Σ-assoc ⟩
    (∃ λ ((x , y , _) : ∃ λ (x : A) → ∃ λ (y : P x) → R x y) → Q x y)  ↝⟨ (Σ-cong Σ-assoc λ _ → F.id) ⟩□
    (∃ λ (((x , y) , _) : Σ (Σ A P) (uncurry R)) → Q x y)              □

  lemma₂ : (g : ∀ a → get l₁ a ≡ get l₂ a) → _
  lemma₂ g =
    subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
      (⟨ext⟩ g) (get⁻¹-const l₁) ≡
    get⁻¹-const l₂                                              ↝⟨ inverse $ Eq.extensionality-isomorphism bad-ext ⟩

    (∀ b₁ → subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               (⟨ext⟩ g) (get⁻¹-const l₁) b₁ ≡
            get⁻¹-const l₂ b₁)                                  ↝⟨ (∀-cong ext λ _ → inverse $ Eq.extensionality-isomorphism bad-ext) ⟩

    (∀ b₁ b₂ → subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
                 (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ ≡
               get⁻¹-const l₂ b₁ b₂)                            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse $ Eq.extensionality-isomorphism bad-ext) ⟩□

    (∀ b₁ b₂ p →
     subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
       (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p ≡
     get⁻¹-const l₂ b₁ b₂ p)                                    □

-- An equality characterisation lemma for lenses between sets.

equality-characterisation-for-sets :
  let open Lens in
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →

  Is-set A →

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∀ b₁ b₂ p →
     proj₁ (get⁻¹-const l₁ b₁ b₂ (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p)) ≡
     proj₁ (get⁻¹-const l₂ b₁ b₂ p))
equality-characterisation-for-sets
  {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} A-set =
  l₁ ≡ l₂                                                                 ↝⟨ equality-characterisation ⟩

  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (gc : ∀ b₁ b₂ p →
             subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
               (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p ≡
             get⁻¹-const l₂ b₁ b₂ p) →
     subst
       (λ (get , gc) →
          ∀ b₁ b₂ b₃ (p : get ⁻¹ b₁) →
          gc b₂ b₃ (gc b₁ b₂ p) ≡ gc b₁ b₃ p)
       (Σ-≡,≡→≡
          (⟨ext⟩ g)
          (⟨ext⟩ λ b₁ → ⟨ext⟩ λ b₂ → ⟨ext⟩ λ p → gc b₁ b₂ p))
       (get⁻¹-const-∘ l₁) ≡
     get⁻¹-const-∘ l₂)                                                    ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $ +⇒≡ $
                                                                              Π-closure ext 1 λ _ →
                                                                              Π-closure ext 1 λ _ →
                                                                              Π-closure ext 1 λ _ →
                                                                              Π-closure ext 1 λ _ →
                                                                              ⁻¹-set) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∀ b₁ b₂ p →
     subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
       (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p ≡
     get⁻¹-const l₂ b₁ b₂ p)                                              ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (_≡ _) $ lemma₁ _ _ _ _) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∀ b₁ b₂ p →
     subst (_⁻¹ b₂) (⟨ext⟩ g)
       (get⁻¹-const l₁ b₁ b₂ (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p)) ≡
     get⁻¹-const l₂ b₁ b₂ p)                                              ↔⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ p →
                                                                              drop-⊤-right (λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                                                  +⇒≡ (B-set (proj₁ p))) F.∘
                                                                              inverse B.Σ-≡,≡↔≡) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∀ b₁ b₂ p →
     proj₁ (subst (_⁻¹ b₂) (⟨ext⟩ g)
              (get⁻¹-const l₁ b₁ b₂
                 (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p))) ≡
     proj₁ (get⁻¹-const l₂ b₁ b₂ p))                                      ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (_≡ _) $ lemma₂ _ _ _ _) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∀ b₁ b₂ p →
     proj₁ (get⁻¹-const l₁ b₁ b₂ (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p)) ≡
     proj₁ (get⁻¹-const l₂ b₁ b₂ p))                                      □
  where
  open Lens

  B-set : A → Is-set B
  B-set a = h-level-respects-lens-from-inhabited 2 l₁ a A-set

  ⁻¹-set : Is-set (get l₂ ⁻¹ b)
  ⁻¹-set =
    Σ-closure 2 A-set λ a →
    mono₁ 1 (B-set a)

  lemma₁ : ∀ g b₁ b₂ p → _
  lemma₁ g b₁ b₂ p =
    subst (λ get → ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
      (⟨ext⟩ g) (get⁻¹-const l₁) b₁ b₂ p                         ≡⟨ cong (λ f → f b₂ p) $ sym $
                                                                    push-subst-application (⟨ext⟩ g) (λ get b₁ → ∀ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂) ⟩
    subst (λ get → ∀ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂)
      (⟨ext⟩ g) (get⁻¹-const l₁ b₁) b₂ p                         ≡⟨ cong (λ f → f p) $ sym $
                                                                    push-subst-application (⟨ext⟩ g) (λ get b₂ → get ⁻¹ b₁ → get ⁻¹ b₂) ⟩
    subst (λ get → get ⁻¹ b₁ → get ⁻¹ b₂)
      (⟨ext⟩ g) (get⁻¹-const l₁ b₁ b₂) p                         ≡⟨ subst-→ {x₁≡x₂ = ⟨ext⟩ g} ⟩∎

    subst (_⁻¹ b₂) (⟨ext⟩ g)
      (get⁻¹-const l₁ b₁ b₂ (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p))  ∎

  lemma₂ : ∀ g b₁ b₂ p → _
  lemma₂ g b₁ b₂ p =
    proj₁ (subst (_⁻¹ b₂) (⟨ext⟩ g)
             (get⁻¹-const l₁ b₁ b₂
                (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p)))                 ≡⟨ cong proj₁ $
                                                                        push-subst-pair {y≡z = ⟨ext⟩ g} _ _ ⟩
    subst (λ _ → A) (⟨ext⟩ g)
      (proj₁ (get⁻¹-const l₁ b₁ b₂
                (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p)))                 ≡⟨ subst-const (⟨ext⟩ g) ⟩∎

    proj₁ (get⁻¹-const l₁ b₁ b₂ (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ g) p))  ∎

------------------------------------------------------------------------
-- Conversions between different kinds of lenses

-- Higher lenses can be converted to the ones defined above.

higher→ : Higher.Lens A B → Lens A B
higher→ l@(Higher.⟨ _ , _ , _ ⟩) = _≃_.from Lens-as-Σ′
  ( Higher.Lens.get l
  , Higher.get⁻¹-constant l
  , Higher.get⁻¹-constant-∘ l
  )

-- The conversion preserves getters and setters.

get-higher→≡get :
  (l : Higher.Lens A B) →
  Lens.get (higher→ l) a ≡ Higher.Lens.get l a
get-higher→≡get Higher.⟨ _ , _ , _ ⟩ = refl

set-higher→≡set :
  (l : Higher.Lens A B) →
  Lens.set (higher→ l) a b ≡ Higher.Lens.set l a b
set-higher→≡set Higher.⟨ _ , _ , _ ⟩ = refl

-- A lens of the kind defined above can be converted to a higher one
-- if the codomain is inhabited when it is merely inhabited.

→higher : (∥ B ∥ → B) → Lens A B → Higher.Lens A B
→higher {B = B} {A = A} ∥B∥→B l@(lens _ _ _ _) = record
  { R     = ∃ λ (b : ∥ B ∥) → Lens.get l ⁻¹ (∥B∥→B b)
  ; equiv =
      A                                                      ↔⟨ (inverse $ drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                 other-singleton-contractible _) ⟩
      (∃ λ a → ∃ λ b → Lens.get l a ≡ b)                     ↔⟨ ∃-comm ⟩
      (∃ λ b → Lens.get l ⁻¹ b)                              ↝⟨ (Σ-cong (inverse PT.∥∥×≃) λ _ → Lens.get⁻¹-constant l _ _) ⟩
      (∃ λ ((b , _) : ∥ B ∥ × B) → Lens.get l ⁻¹ (∥B∥→B b))  ↔⟨ inverse Σ-assoc ⟩
      (∃ λ (b : ∥ B ∥) → B × Lens.get l ⁻¹ (∥B∥→B b))        ↔⟨ (∃-cong λ _ → ×-comm) ⟩
      (∃ λ (b : ∥ B ∥) → Lens.get l ⁻¹ (∥B∥→B b) × B)        ↔⟨ Σ-assoc ⟩□
      (∃ λ (b : ∥ B ∥) → Lens.get l ⁻¹ (∥B∥→B b)) × B        □
  ; inhabited = proj₁
  }

-- The conversion preserves getters and setters.

get-→higher≡get :
  ∀ ∥B∥→B (l : Lens A B) →
  Higher.Lens.get (→higher ∥B∥→B l) a ≡ Lens.get l a
get-→higher≡get _ (lens _ _ _ _) = refl

set-→higher≡set :
  ∀ ∥B∥→B (l : Lens A B) →
  Higher.Lens.set (→higher ∥B∥→B l) a b ≡ Lens.set l a b
set-→higher≡set {A = A} {a = a} {b = b} ∥B∥→B l@(lens _ _ _ _) =
  _≃_.to-from (Higher.Lens.equiv (→higher ∥B∥→B l)) $ cong₂ _,_
    (∣ get a′ ∣ , get⁻¹-const (get a′) (∥B∥→B ∣ get a′ ∣) (a′ , refl)  ≡⟨ Σ-≡,≡→≡ (PT.truncation-is-proposition _ _)
                                                                            (
         subst (λ b → get ⁻¹ ∥B∥→B b)
           (PT.truncation-is-proposition _ _)
           (get⁻¹-const (get a′) (∥B∥→B ∣ get a′ ∣) (a′ , refl))             ≡⟨ elim¹
                                                                                  (λ {f} _ →
                                                                                     subst (λ b → get ⁻¹ f b)
                                                                                       (PT.truncation-is-proposition _ _)
                                                                                       (get⁻¹-const (get a′) (f ∣ get a′ ∣) (a′ , refl)) ≡
                                                                                     get⁻¹-const (get a) (f ∣ get a ∣) (a , refl))
                                                                                  (
             subst (λ _ → get ⁻¹ ∥B∥→B ∣ b ∣)
               (PT.truncation-is-proposition _ _)
               (get⁻¹-const (get a′) (∥B∥→B ∣ b ∣) (a′ , refl))                    ≡⟨ subst-const (PT.truncation-is-proposition _ _) ⟩

             get⁻¹-const (get a′) (∥B∥→B ∣ b ∣) (a′ , refl)                        ≡⟨ sym $ get⁻¹-const-∘ _ _ _ _ ⟩

             get⁻¹-const (get a) (∥B∥→B ∣ b ∣)
               (get⁻¹-const (get a′) (get a) (a′ , refl))                          ≡⟨ cong (get⁻¹-const (get a) (∥B∥→B ∣ b ∣)) $
                                                                                      elim¹
                                                                                        (λ {b} eq → get⁻¹-const (get a′) (get a) (a′ , refl) ≡
                                                                                                    get⁻¹-const b        (get a) (a′ , eq))
                                                                                        refl
                                                                                        (get-set a b) ⟩
             get⁻¹-const (get a) (∥B∥→B ∣ b ∣)
               (get⁻¹-const b (get a) (set a b , get-set a b))                     ≡⟨⟩

             get⁻¹-const (get a) (∥B∥→B ∣ b ∣)
               (get⁻¹-const b (get a)
                  (get⁻¹-const (get a) b (a , refl)))                              ≡⟨ cong (λ p → get⁻¹-const (get a) (∥B∥→B ∣ b ∣)
                                                                                                    (get⁻¹-const b (get a) p)) $
                                                                                      get⁻¹-const-inverse _ _ _ ⟩
             get⁻¹-const (get a) (∥B∥→B ∣ b ∣)
               (get⁻¹-const b (get a)
                  (get⁻¹-const⁻¹ b (get a) (a , refl)))                            ≡⟨ cong (get⁻¹-const (get a) (∥B∥→B ∣ b ∣)) $
                                                                                      _≃_.right-inverse-of (get⁻¹-constant _ _) _ ⟩∎
             get⁻¹-const (get a) (∥B∥→B ∣ b ∣) (a , refl)                          ∎)
                                                                                  (⟨ext⟩ λ _ → cong ∥B∥→B $ PT.truncation-is-proposition _ _) ⟩∎
         get⁻¹-const (get a) (∥B∥→B ∣ get a ∣) (a , refl)                    ∎) ⟩∎

     ∣ get a ∣ , get⁻¹-const (get a) (∥B∥→B ∣ get a ∣) (a , refl)      ∎)
    (get (set a b)  ≡⟨ get-set a b ⟩∎
     b              ∎)
  where
  open Lens l

  a′ : A
  a′ = set a b

-- There is a split surjection from Lens A B to Higher.Lens A B if B
-- is inhabited when it is merely inhabited (assuming univalence).

↠higher :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (∥ B ∥ → B) →
  Lens A B ↠ Higher.Lens A B
↠higher {A = A} {B = B} univ ∥B∥→B = record
  { logical-equivalence = record
    { to   = →higher ∥B∥→B
    ; from = higher→
    }
  ; right-inverse-of = λ l →
      Higher.lenses-equal-if-setters-equal
        univ _ _
        (λ _ → ∥B∥→B)
        (set (→higher ∥B∥→B (higher→ l))  ≡⟨ (⟨ext⟩ λ _ → ⟨ext⟩ λ _ → set-→higher≡set ∥B∥→B (higher→ l)) ⟩
         Lens.set (higher→ l)             ≡⟨ (⟨ext⟩ λ _ → ⟨ext⟩ λ _ → set-higher→≡set l) ⟩∎
         set l                            ∎)
  }
  where
  open Higher.Lens

-- If B is inhabited when it is merely inhabited and A has positive
-- h-level n, then Higher.Lens A B also has h-level n (assuming
-- univalence).

higher-lens-preserves-h-level-of-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (∥ B ∥ → B) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Higher.Lens A B)
higher-lens-preserves-h-level-of-domain {A = A} {B = B} univ ∥B∥→B n =
  H-level (1 + n) A                  ↝⟨ lens-preserves-h-level-of-domain n ⟩
  H-level (1 + n) (Lens A B)         ↝⟨ H-level.respects-surjection (↠higher univ ∥B∥→B) (1 + n) ⟩□
  H-level (1 + n) (Higher.Lens A B)  □

-- Traditional lenses that satisfy some coherence properties can be
-- translated to lenses of the kind defined above.

traditional→ :
  (l : Traditional.Lens A B) →
  let open Traditional.Lens l in
  (∀ a → cong get (set-get a) ≡ get-set a (get a)) →
  (∀ a b₁ b₂ →
   cong get (set-set a b₁ b₂) ≡
   trans (get-set (set a b₁) b₂) (sym (get-set a b₂))) →
  Lens A B
traditional→ l get-set-get get-set-set = _≃_.from Lens-as-Σ′
  ( get
  , (λ b₁ b₂ →
       Eq.↔→≃ (gg b₁ b₂) (gg b₂ b₁) (gg∘gg b₁ b₂) (gg∘gg b₂ b₁))
  , (λ b₁ b₂ b₃ (a , _) →
       Σ-≡,≡→≡
         (set (set a b₂) b₃  ≡⟨ set-set a b₂ b₃ ⟩∎
          set a b₃           ∎)
         (subst (λ a → get a ≡ b₃) (set-set a b₂ b₃)
            (get-set (set a b₂) b₃)                   ≡⟨ subst-∘ _ _ (set-set a b₂ b₃) ⟩

          subst (_≡ b₃) (cong get (set-set a b₂ b₃))
            (get-set (set a b₂) b₃)                   ≡⟨ subst-trans-sym {y≡x = cong get (set-set a b₂ b₃)} ⟩

          trans (sym (cong get (set-set a b₂ b₃)))
            (get-set (set a b₂) b₃)                   ≡⟨ get-set-set′ _ _ _ ⟩∎

          get-set a b₃                                ∎))
  )
  where
  open Traditional.Lens l

  get-set-set′ :
    ∀ a b₁ b₂ →
    trans (sym (cong get (set-set a b₁ b₂))) (get-set (set a b₁) b₂) ≡
    get-set a b₂
  get-set-set′ a b₁ b₂ =
    trans (sym (cong get (set-set a b₁ b₂))) (get-set (set a b₁) b₂)  ≡⟨ cong (λ eq → trans (sym eq) (get-set _ _)) $
                                                                         get-set-set _ _ _ ⟩
    trans (sym (trans (get-set (set a b₁) b₂) (sym (get-set a b₂))))
      (get-set (set a b₁) b₂)                                         ≡⟨ cong (flip trans (get-set _ _)) $
                                                                         sym-trans _ (sym (get-set _ _)) ⟩
    trans (trans (sym (sym (get-set a b₂)))
             (sym (get-set (set a b₁) b₂)))
      (get-set (set a b₁) b₂)                                         ≡⟨ trans-[trans-sym]- _ (get-set _ _) ⟩

    sym (sym (get-set a b₂))                                          ≡⟨ sym-sym (get-set _ _) ⟩∎

    get-set a b₂                                                      ∎

  gg : ∀ b₁ b₂ → get ⁻¹ b₁ → get ⁻¹ b₂
  gg b₁ b₂ (a , _) = set a b₂ , get-set a b₂

  gg∘gg : ∀ b₁ b₂ p → gg b₁ b₂ (gg b₂ b₁ p) ≡ p
  gg∘gg b₁ b₂ (a , get-a≡b₂) =
    Σ-≡,≡→≡ eq₁
      (subst (λ a → get a ≡ b₂) eq₁ (get-set (set a b₁) b₂)   ≡⟨ subst-∘ _ _ eq₁ ⟩

       subst (_≡ b₂) (cong get eq₁) (get-set (set a b₁) b₂)   ≡⟨ subst-trans-sym {y≡x = cong get eq₁} ⟩

       trans (sym (cong get eq₁)) (get-set (set a b₁) b₂)     ≡⟨ cong (flip trans (get-set (set a b₁) b₂))
                                                                 lemma₂ ⟩
       trans (trans (trans (sym (cong get (set-get a)))
                       (cong (get ⊚ set a) get-a≡b₂))
                (sym (cong get (set-set a b₁ b₂))))
         (get-set (set a b₁) b₂)                              ≡⟨ trans-assoc _ _ (get-set (set a b₁) b₂) ⟩

       trans (trans (sym (cong get (set-get a)))
                (cong (get ⊚ set a) get-a≡b₂))
         (trans (sym (cong get (set-set a b₁ b₂)))
            (get-set (set a b₁) b₂))                          ≡⟨ trans-assoc _ _ (trans (sym (cong get (set-set a b₁ b₂)))
                                                                                    (get-set (set a b₁) b₂)) ⟩
       trans (sym (cong get (set-get a)))
         (trans (cong (get ⊚ set a) get-a≡b₂)
            (trans (sym (cong get (set-set a b₁ b₂)))
               (get-set (set a b₁) b₂)))                      ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong (get ⊚ set a) get-a≡b₂) q))
                                                                   (get-set-get _)
                                                                   (get-set-set′ _ _ _) ⟩
       trans (sym (get-set a (get a)))
         (trans (cong (get ⊚ set a) get-a≡b₂)
            (get-set a b₂))                                   ≡⟨ cong (λ eq → trans (sym (eq (get a)))
                                                                                (trans (cong (get ⊚ set a) get-a≡b₂) (eq b₂))) $ sym $
                                                                 _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) _ ⟩
       trans (sym (ext⁻¹ (⟨ext⟩ (get-set a)) (get a)))
         (trans (cong (get ⊚ set a) get-a≡b₂)
            (ext⁻¹ (⟨ext⟩ (get-set a)) b₂))                   ≡⟨ elim₁
                                                                   (λ {f} gs →
                                                                      trans (sym (ext⁻¹ gs (get a))) (trans (cong f get-a≡b₂) (ext⁻¹ gs b₂)) ≡
                                                                      get-a≡b₂)
                                                                   (
          trans (sym (ext⁻¹ (refl {x = id}) (get a)))
             (trans (cong id get-a≡b₂)
                (ext⁻¹ (refl {x = id}) b₂))                         ≡⟨⟩

          trans refl (cong id get-a≡b₂)                             ≡⟨ trans-reflˡ (cong id get-a≡b₂) ⟩

          cong id get-a≡b₂                                          ≡⟨ sym $ cong-id get-a≡b₂ ⟩∎

          get-a≡b₂                                                  ∎)
                                                                 (⟨ext⟩ (get-set a)) ⟩
       get-a≡b₂                                               ∎)
    where
    eq₁ =
      set (set a b₁) b₂  ≡⟨ set-set a b₁ b₂ ⟩
      set a b₂           ≡⟨ cong (set a) (sym get-a≡b₂) ⟩
      set a (get a)      ≡⟨ set-get a ⟩∎
      a                  ∎

    lemma₁ =
      sym (cong get (cong (set a) (sym get-a≡b₂)))  ≡⟨ cong sym $ cong-∘ _ _ (sym get-a≡b₂) ⟩
      sym (cong (get ⊚ set a) (sym get-a≡b₂))       ≡⟨ sym $ cong-sym _ (sym get-a≡b₂) ⟩
      cong (get ⊚ set a) (sym (sym get-a≡b₂))       ≡⟨ cong (cong (get ⊚ set a)) $ sym-sym get-a≡b₂ ⟩∎
      cong (get ⊚ set a) get-a≡b₂                   ∎

    lemma₂ =
      sym (cong get eq₁)                                          ≡⟨⟩

      sym (cong get
             (trans (set-set a b₁ b₂)
                (trans (cong (set a) (sym get-a≡b₂))
                   (set-get a))))                                 ≡⟨ cong sym $
                                                                     cong-trans _ _ (trans (cong (set a) (sym get-a≡b₂)) (set-get a)) ⟩
      sym (trans (cong get (set-set a b₁ b₂))
             (cong get (trans (cong (set a) (sym get-a≡b₂))
                          (set-get a))))                          ≡⟨ cong (λ eq → sym (trans _ eq)) $
                                                                     cong-trans _ _ (set-get a) ⟩
      sym (trans (cong get (set-set a b₁ b₂))
             (trans (cong get (cong (set a) (sym get-a≡b₂)))
                (cong get (set-get a))))                          ≡⟨ sym-trans _ (trans (cong get (cong (set a) (sym get-a≡b₂)))
                                                                                    (cong get (set-get a))) ⟩
      trans (sym (trans (cong get (cong (set a) (sym get-a≡b₂)))
                    (cong get (set-get a))))
        (sym (cong get (set-set a b₁ b₂)))                        ≡⟨ cong (flip trans (sym (cong get (set-set a b₁ b₂)))) $
                                                                     sym-trans _ (cong get (set-get a)) ⟩
      trans (trans (sym (cong get (set-get a)))
               (sym (cong get (cong (set a) (sym get-a≡b₂)))))
        (sym (cong get (set-set a b₁ b₂)))                        ≡⟨ cong (λ eq → trans (trans _ eq) (sym (cong get (set-set a b₁ b₂))))
                                                                     lemma₁ ⟩∎
      trans (trans (sym (cong get (set-get a)))
               (cong (get ⊚ set a) get-a≡b₂))
        (sym (cong get (set-set a b₁ b₂)))                        ∎

-- If A is a set, then Traditional.Lens A B is equivalent to Lens A B.

traditional≃ :
  Is-set A → Traditional.Lens A B ≃ Lens A B
traditional≃ {A = A} {B = B} A-set = Eq.↔→≃
  (λ l →
     traditional→ l (λ a → B-set l a _ _) (λ a _ _ → B-set l a _ _))
  Lens.traditional-lens
  (λ l → _≃_.from (equality-characterisation-for-sets A-set)
     ( (λ _ → refl)
     , (λ b₁ b₂ p@(a , _) →
          let l′ = traditional-lens l
              l″ = traditional→ l′
                     (λ a → B-set l′ a _ _)
                     (λ a _ _ → B-set l′ a _ _)
          in
          proj₁ (get⁻¹-const l″ b₁ b₂
                   (subst (_⁻¹ b₁) (sym $ ⟨ext⟩ λ _ → refl) p))       ≡⟨ cong (λ eq → proj₁ (get⁻¹-const l″ b₁ b₂ (subst (_⁻¹ b₁) (sym eq) p)))
                                                                         ext-refl ⟩

          proj₁ (get⁻¹-const l″ b₁ b₂ (subst (_⁻¹ b₁) (sym refl) p))  ≡⟨⟩

          proj₁ (get⁻¹-const l″ b₁ b₂ p)                              ≡⟨⟩

          set l (proj₁ p) b₂                                          ≡⟨⟩

          proj₁ (get⁻¹-const l (get l a) b₂ (a , refl))               ≡⟨ elim¹
                                                                           (λ {b} eq →
                                                                              proj₁ (get⁻¹-const l (get l a) b₂ (a , refl)) ≡
                                                                              proj₁ (get⁻¹-const l b b₂ (a , eq)))
                                                                           refl
                                                                           (proj₂ p) ⟩∎
          proj₁ (get⁻¹-const l b₁ b₂ p)                               ∎)
     ))
  (λ _ →
     _↔_.from (Traditional.equality-characterisation-for-sets A-set)
       refl)
  where
  open Lens

  B-set : Traditional.Lens A B → A → Is-set B
  B-set l a =
    Traditional.h-level-respects-lens-from-inhabited 2 l a A-set

------------------------------------------------------------------------
-- Composition

-- A lemma used to define composition.

∘⁻¹≃ :
  Block "∘⁻¹≃" →
  (f : B → C) (g : A → B) →
  f ⊚ g ⁻¹ z ≃ ∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y
∘⁻¹≃ {z = z} ⊠ f g =
  f ⊚ g ⁻¹ z                                  ↔⟨⟩
  (∃ λ a → f (g a) ≡ z)                       ↔⟨ (∃-cong λ _ → ∃-intro _ _) ⟩
  (∃ λ a → ∃ λ y → f y ≡ z × y ≡ g a)         ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩
  (∃ λ a → ∃ λ ((y , _) : f ⁻¹ z) → y ≡ g a)  ↔⟨ ∃-comm ⟩
  (∃ λ ((y , _) : f ⁻¹ z) → ∃ λ a → y ≡ g a)  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ≡-comm) ⟩
  (∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y)           □

-- Composition.

infixr 9 _∘_

_∘_ : Lens B C → Lens A B → Lens A C
l₁@(lens _ _ _ _) ∘ l₂@(lens _ _ _ _) = block λ b → _≃_.from Lens-as-Σ′
  ( get l₁ ⊚ get l₂
  , (λ c₁ c₂ →
       get l₁ ⊚ get l₂ ⁻¹ c₁                         ↝⟨ ∘⁻¹≃ b _ _ ⟩
       (∃ λ ((b , _) : get l₁ ⁻¹ c₁) → get l₂ ⁻¹ b)  ↝⟨ (Σ-cong (get⁻¹-constant l₁ c₁ c₂) λ p@(b , _) →
                                                         get⁻¹-constant l₂ b (proj₁ (get⁻¹-const l₁ c₁ c₂ p))) ⟩
       (∃ λ ((b , _) : get l₁ ⁻¹ c₂) → get l₂ ⁻¹ b)  ↝⟨ inverse $ ∘⁻¹≃ b _ _ ⟩□
       get l₁ ⊚ get l₂ ⁻¹ c₂                         □)
  , (λ c₁ c₂ c₃ p →
       _≃_.from (∘⁻¹≃ b _ _)
         (Σ-map (get⁻¹-const l₁ c₂ c₃)
            (λ {p@(b , _)} →
               get⁻¹-const l₂ b (proj₁ (get⁻¹-const l₁ c₂ c₃ p)))
            (_≃_.to (∘⁻¹≃ b _ _)
               (_≃_.from (∘⁻¹≃ b _ _)
                  (Σ-map (get⁻¹-const l₁ c₁ c₂)
                     (λ {p@(b , _)} →
                        get⁻¹-const l₂ b
                          (proj₁ (get⁻¹-const l₁ c₁ c₂ p)))
                     (_≃_.to (∘⁻¹≃ b _ _) p)))))                      ≡⟨ cong (λ x → _≃_.from (∘⁻¹≃ b _ _)
                                                                                       (Σ-map (get⁻¹-const l₁ c₂ c₃)
                                                                                          (λ {p@(b , _)} →
                                                                                             get⁻¹-const l₂ b
                                                                                               (proj₁ (get⁻¹-const l₁ c₂ c₃ p))) x)) $
                                                                         _≃_.right-inverse-of (∘⁻¹≃ b _ _) _ ⟩
       _≃_.from (∘⁻¹≃ b _ _)
         (Σ-map (get⁻¹-const l₁ c₂ c₃)
            (λ {p@(b , _)} →
               get⁻¹-const l₂ b (proj₁ (get⁻¹-const l₁ c₂ c₃ p)))
            (Σ-map (get⁻¹-const l₁ c₁ c₂)
               (λ {p@(b , _)} →
                  get⁻¹-const l₂ b (proj₁ (get⁻¹-const l₁ c₁ c₂ p)))
               (_≃_.to (∘⁻¹≃ b _ _) p)))                              ≡⟨⟩

       _≃_.from (∘⁻¹≃ b _ _)
         (Σ-map (get⁻¹-const l₁ c₂ c₃ ⊚ get⁻¹-const l₁ c₁ c₂)
            (λ {p@(b , _)} →
               get⁻¹-const l₂ (proj₁ (get⁻¹-const l₁ c₁ c₂ p))
                 (proj₁ (get⁻¹-const l₁ c₂ c₃
                           (get⁻¹-const l₁ c₁ c₂ p))) ⊚
               get⁻¹-const l₂ b (proj₁ (get⁻¹-const l₁ c₁ c₂ p)))
            (_≃_.to (∘⁻¹≃ b _ _) p))                                  ≡⟨ cong (λ f → _≃_.from (∘⁻¹≃ b _ _)
                                                                                       (Σ-map (get⁻¹-const l₁ c₂ c₃ ⊚ get⁻¹-const l₁ c₁ c₂)
                                                                                          (λ {p} → f {p})
                                                                                          (_≃_.to (∘⁻¹≃ b _ _) p))) $
                                                                         (implicit-extensionality ext λ p →
                                                                          ⟨ext⟩ (get⁻¹-const-∘ l₂ _ (proj₁ (get⁻¹-const l₁ c₁ c₂ p)) _)) ⟩
       _≃_.from (∘⁻¹≃ b _ _)
         (Σ-map (get⁻¹-const l₁ c₂ c₃ ⊚ get⁻¹-const l₁ c₁ c₂)
            (λ {p@(b , _)} →
               get⁻¹-const l₂ b
                 (proj₁ (get⁻¹-const l₁ c₂ c₃
                           (get⁻¹-const l₁ c₁ c₂ p))))
            (_≃_.to (∘⁻¹≃ b _ _) p))                                  ≡⟨ cong (λ f → _≃_.from (∘⁻¹≃ b _ _)
                                                                                       (Σ-map f (λ {p@(b , _)} → get⁻¹-const l₂ b (proj₁ (f p)))
                                                                                          (_≃_.to (∘⁻¹≃ b _ _) p))) $
                                                                         ⟨ext⟩ (get⁻¹-const-∘ l₁ _ _ _) ⟩∎
       _≃_.from (∘⁻¹≃ b _ _)
         (Σ-map (get⁻¹-const l₁ c₁ c₃)
            (λ {p@(b , _)} →
               get⁻¹-const l₂ b (proj₁ (get⁻¹-const l₁ c₁ c₃ p)))
            (_≃_.to (∘⁻¹≃ b _ _) p))                                  ∎)
  )
  where
  open Lens

-- The setter of the resulting lens is defined in the "right" way.

set-∘≡ :
  (l₁ : Lens B C) (l₂ : Lens A B) →
  Lens.set (l₁ ∘ l₂) a c ≡
  Lens.set l₂ a (Lens.set l₁ (Lens.get l₂ a) c)
set-∘≡ (lens _ _ _ _) (lens _ _ _ _) = refl

-- Composition for higher lenses, defined under the assumption that
-- the resulting codomain is inhabited if it is merely inhabited.

infix 9 ⟨_⟩_⊚_

⟨_⟩_⊚_ :
  (∥ C ∥ → C) →
  Higher.Lens B C → Higher.Lens A B → Higher.Lens A C
⟨_⟩_⊚_ {C = C} {B = B} {A = A} ∥C∥→C = curry (
  Higher.Lens B C × Higher.Lens A B  ↝⟨ Σ-map higher→ higher→ ⟩
  Lens B C × Lens A B                ↝⟨ uncurry _∘_ ⟩
  Lens A C                           ↝⟨ →higher ∥C∥→C ⟩□
  Higher.Lens A C                    □)

-- The setter of the resulting lens is defined in the "right" way.

set-⊚≡ :
  ∀ ∥C∥→C (l₁ : Higher.Lens B C) (l₂ : Higher.Lens A B) →
  Higher.Lens.set (⟨ ∥C∥→C ⟩ l₁ ⊚ l₂) a c ≡
  Higher.Lens.set l₂ a (Higher.Lens.set l₁ (Higher.Lens.get l₂ a) c)
set-⊚≡ {a = a} {c = c} ∥C∥→C l₁ l₂ =
  set (⟨ ∥C∥→C ⟩ l₁ ⊚ l₂) a c                                   ≡⟨ set-→higher≡set ∥C∥→C (higher→ l₁ ∘ higher→ l₂) ⟩

  Lens.set (higher→ l₁ ∘ higher→ l₂) a c                        ≡⟨ set-∘≡ (higher→ l₁) (higher→ l₂) ⟩

  Lens.set (higher→ l₂) a
    (Lens.set (higher→ l₁) (Lens.get (higher→ l₂) a) c)         ≡⟨ set-higher→≡set l₂ ⟩

  set l₂ a (Lens.set (higher→ l₁) (Lens.get (higher→ l₂) a) c)  ≡⟨ cong (set l₂ a) $ set-higher→≡set l₁ ⟩

  set l₂ a (set l₁ (Lens.get (higher→ l₂) a) c)                 ≡⟨ cong (λ a′ → set l₂ a (set l₁ a′ c)) $ get-higher→≡get l₂ ⟩∎

  set l₂ a (set l₁ (get l₂ a) c)                                ∎
  where
  open Higher.Lens

-- The implementation of composition for higher lenses given above
-- matches the one in Higher when both are defined (assuming
-- univalence).

⊚≡∘ :
  ∀ a b {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
  Univalence (a ⊔ b ⊔ c) →
  (∥C∥→C : ∥ C ∥ → C) →
  ⟨_⟩_⊚_ {B = B} {A = A} ∥C∥→C ≡
  Higher.Lens-combinators.⟨ a , b ⟩_∘_
⊚≡∘ a b {A = A} {B = B} {C = C} univ ∥C∥→C =
  Higher.Lens-combinators.composition≡∘
    a b univ ∥C∥→C ⟨ ∥C∥→C ⟩_⊚_
    (λ l₁ l₂ _ _ → set-⊚≡ ∥C∥→C l₁ l₂)
