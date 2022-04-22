------------------------------------------------------------------------
-- Small coinductive higher lenses with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Small.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id)

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages.Cubical eq as ECP
  using (_⁻¹ᴱ_)
open import Erased.Cubical eq
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq using (∥_∥)
open import Preimage equality-with-J using (_⁻¹_)
open import Tactic.Sigma-cong equality-with-J
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant eq
  as V
open import Lens.Non-dependent.Higher.Coherently.Coinductive eq
import Lens.Non-dependent.Higher.Coinductive eq as C
import Lens.Non-dependent.Higher.Coinductive.Erased eq as CE
import Lens.Non-dependent.Higher.Coinductive.Small eq as S
import Lens.Non-dependent.Higher.Erased eq as E

private
  variable
    a b c d : Level
    A B     : Type a
    l g p s : A
    P       : A → Type p
    f       : (x : A) → P x
    univ    : Univalence a

------------------------------------------------------------------------
-- Weakly constant functions

-- Weakly constant type-valued functions.
--
-- Note that the definition does not use _≃ᴱ_: the right-to-left
-- directions of the equivalences are erased.

Constantᴱ :
  {A : Type a} →
  (A → Type p) → Type (a ⊔ p)
Constantᴱ P = ∀ x y → ∃ λ (f : P x → P y) → Erased (Is-equivalence f)

-- In erased contexts Constantᴱ is pointwise equivalent to Constant
-- (assuming univalence).

@0 Constantᴱ≃Constant :
  {P : A → Type p} →
  Univalence p →
  Constantᴱ P ≃ Constant P
Constantᴱ≃Constant {P = P} univ =
  Constantᴱ P                                                ↔⟨⟩
  (∀ x y → ∃ λ (f : P x → P y) → Erased (Is-equivalence f))  ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ _ → erased Erased↔) ⟩
  (∀ x y → ∃ λ (f : P x → P y) → Is-equivalence f)           ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse Eq.≃-as-Σ) ⟩
  (∀ x y → P x ≃ P y)                                        ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse $ ≡≃≃ univ) ⟩
  (∀ x y → P x ≡ P y)                                        ↔⟨⟩
  Constant P                                                 □

-- In erased contexts Constantᴱ is pointwise equivalent to
-- S.Constant-≃.

@0 Constantᴱ≃Constant-≃ : Constantᴱ P ≃ S.Constant-≃ P
Constantᴱ≃Constant-≃ {P = P} =
  Constantᴱ P                                                ↔⟨⟩
  (∀ x y → ∃ λ (f : P x → P y) → Erased (Is-equivalence f))  ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ _ → erased Erased↔) ⟩
  (∀ x y → ∃ λ (f : P x → P y) → Is-equivalence f)           ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse Eq.≃-as-Σ) ⟩
  (∀ x y → P x ≃ P y)                                        ↔⟨⟩
  S.Constant-≃ P                                             □

-- In erased contexts Constantᴱ (f ⁻¹ᴱ_) is pointwise equivalent to
-- S.Constant-≃ (f ⁻¹_).

@0 Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ :
  Constantᴱ (f ⁻¹ᴱ_) ≃ S.Constant-≃ (f ⁻¹_)
Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ {f = f} =
  Constantᴱ (f ⁻¹ᴱ_)               ↝⟨ Constantᴱ≃Constant-≃ ⟩
  S.Constant-≃ (f ⁻¹ᴱ_)            ↔⟨⟩
  (∀ b₁ b₂ → f ⁻¹ᴱ b₁ ≃ f ⁻¹ᴱ b₂)  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                       Eq.≃-preserves ext (inverse ECP.⁻¹≃⁻¹ᴱ) (inverse ECP.⁻¹≃⁻¹ᴱ)) ⟩
  (∀ b₁ b₂ → f ⁻¹ b₁ ≃ f ⁻¹ b₂)    ↔⟨⟩
  S.Constant-≃ (f ⁻¹_)             □

-- In erased contexts Constantᴱ (f ⁻¹ᴱ_) is pointwise equivalent to
-- Constant (f ⁻¹_) (assuming univalence).

@0 Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ :
  Block "Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹" →
  {A : Type a} {B : Type b} {f : A → B} →
  Univalence (a ⊔ b) →
  Constantᴱ (f ⁻¹ᴱ_) ≃ Constant (f ⁻¹_)
Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ ⊠ {f = f} univ =
  Constantᴱ (f ⁻¹ᴱ_)    ↝⟨ Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ ⟩
  S.Constant-≃ (f ⁻¹_)  ↝⟨ inverse $ S.Constant≃Constant-≃ univ ⟩□
  Constant (f ⁻¹_)      □

-- A "computation" rule for Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹.

@0 proj₁-from-Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ :
  (bl : Block "Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹") →
  ∀ {A : Type a} {B : Type b} {f : A → B} {univ : Univalence (a ⊔ b)}
    {c : Constant (f ⁻¹_)} {b₁ b₂} →
  proj₁ (_≃_.from (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c b₁ b₂) ≡
  ECP.⁻¹→⁻¹ᴱ ∘ subst P.id (c b₁ b₂) ∘ ECP.⁻¹ᴱ→⁻¹
proj₁-from-Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ ⊠ {c = c} {b₁ = b₁} {b₂ = b₂} =
  ⟨ext⟩ λ (a , [ eq ]) →

  ECP.⁻¹→⁻¹ᴱ (≡⇒→ (c b₁ b₂) (a , eq))         ≡⟨ cong ECP.⁻¹→⁻¹ᴱ $ sym $
                                                 subst-id-in-terms-of-≡⇒↝ equivalence ⟩∎
  ECP.⁻¹→⁻¹ᴱ (subst P.id (c b₁ b₂) (a , eq))  ∎

-- Constantᴱ (get ⁻¹ᴱ_) can be expressed (up to _≃ᴱ_) in terms of a
-- "setter" and an erased "get-set" law that, in a certain way, form
-- an erased family of equivalences.
--
-- This lemma is based on a lemma suggested by Andrea Vezzosi, see
-- S.Constant-≃-get-⁻¹-≃.

Constantᴱ-⁻¹ᴱ-≃ᴱ :
  {A : Type a} {B : Type b} {get : A → B} →
  Block "Constantᴱ-⁻¹ᴱ-≃ᴱ" →
  Constantᴱ (get ⁻¹ᴱ_) ≃ᴱ
  (∃ λ (set : A → B → A) →
   Erased (∃ λ (get-set : ∀ a b → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f))
Constantᴱ-⁻¹ᴱ-≃ᴱ {A = A} {B = B} {get = get} ⊠ =
  Constantᴱ (get ⁻¹ᴱ_)                                                    ↔⟨⟩

  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence f))                                             ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ f → Erased-cong (
                                                                              Is-equivalence≃Is-equivalence-∘ˡ
                                                                                (_≃_.is-equivalence $ from-bijection $
                                                                                 ∃-cong λ _ → erased Erased↔)
                                                                                {k = equivalence} ext)) ⟩
  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map P.id erased ∘ f)))                       ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ f → Erased-cong (
                                                                              Is-equivalence≃Is-equivalence-∘ʳ
                                                                                (_≃_.is-equivalence $ from-bijection $
                                                                                 ∃-cong λ _ → inverse $ erased Erased↔)
                                                                                {k = equivalence} ext)) ⟩
  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map P.id erased ∘ f ∘ Σ-map P.id [_]→)))     ↔⟨ Π-comm ⟩

  (∀ b₂ b₁ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map P.id erased ∘ f ∘ Σ-map P.id [_]→)))     ↔⟨ (∀-cong ext λ _ → ΠΣ-comm) ⟩

  (∀ b₂ →
   ∃ λ (f : ∀ b₁ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   ∀ b₁ →
   Erased (Is-equivalence (Σ-map P.id erased ∘ f b₁ ∘ Σ-map P.id [_]→)))  ↔⟨ (∀-cong ext λ _ → ∃-cong λ _ → inverse Erased-Π↔Π) ⟩

  (∀ b₂ →
   ∃ λ (f : ∀ b₁ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           Is-equivalence (Σ-map P.id erased ∘ f b₁ ∘ Σ-map P.id [_]→)))  ↔⟨ (∀-cong ext λ _ →
                                                                              Σ-cong {k₂ = equivalence}
                                                                                (inverse (∀-cong ext λ _ → currying) F.∘
                                                                                 Π-comm F.∘
                                                                                 (∀-cong ext λ _ → currying))
                                                                                (λ _ → Eq.id)) ⟩
  (∀ b₂ →
   ∃ λ (f : ∀ a → (∃ λ b₁ → Erased (get a ≡ b₁)) → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , eq) → Σ-map P.id erased (f a (b₁ , [ eq ]))
           in
           Is-equivalence g))                                             ↝⟨ (∀-cong [ ext ] λ _ →
                                                                              EEq.Σ-cong-≃ᴱ-Erased
                                                                                (∀-cong [ ext ] λ _ →
                                                                                 EEq.drop-⊤-left-Π-≃ᴱ ext
                                                                                   Erased-other-singleton≃ᴱ⊤
                                                                                   (λ _ _ → F.id)) λ f →
                                                                              Erased-cong (
                                                                              ∀-cong [ ext ] λ b₁ →
                                                                              Is-equivalence-cong [ ext ] λ (a , eq) →
      Σ-map P.id erased (f a (b₁ , [ eq ]))                                     ≡⟨ cong (Σ-map P.id erased ∘ f a) $ sym $
                                                                                   erased (proj₂ Contractibleᴱ-Erased-other-singleton) _ ⟩

      Σ-map P.id erased (f a (get a , [ refl _ ]))                              ≡⟨ cong (Σ-map P.id erased) $ sym $ subst-refl _ _ ⟩∎

      Σ-map P.id erased
        (subst (const _) (refl _) (f a (get a , [ refl _ ])))                   ∎)) ⟩

  (∀ b₂ →
   ∃ λ (f : A → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map P.id erased (f a)
           in
           Is-equivalence g))                                             ↔⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∀ b → A → get ⁻¹ᴱ b) →
   ∀ b₂ →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map P.id erased (f b₂ a)
           in
           Is-equivalence g))                                             ↔⟨ (∃-cong λ _ → inverse Erased-Π↔Π) ⟩

  (∃ λ (f : ∀ b → A → get ⁻¹ᴱ b) →
   Erased (∀ b₂ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map P.id erased (f b₂ a)
           in
           Is-equivalence g))                                             ↔⟨ Σ-cong Π-comm (λ _ → Erased-cong Π-comm) ⟩

  (∃ λ (f : A → ∀ b → get ⁻¹ᴱ b) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map P.id erased (f a b₂)
           in
           Is-equivalence g))                                             ↔⟨ Σ-cong (∀-cong ext λ _ → ΠΣ-comm) (λ _ → Eq.id) ⟩

  (∃ λ (f : A → ∃ λ (set : B → A) →
                ∀ b → Erased (get (set b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → proj₁ (f a) b₂ , erased (proj₂ (f a) b₂)
           in
           Is-equivalence g))                                             ↔⟨ Σ-cong
                                                                               (∀-cong ext λ _ → ∃-cong λ _ → inverse Erased-Π↔Π)
                                                                               (λ _ → Eq.id) ⟩
  (∃ λ (f : A → ∃ λ (set : B → A) →
                Erased (∀ b → get (set b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → proj₁ (f a) b₂ , erased (proj₂ (f a)) b₂
           in
           Is-equivalence g))                                             ↔⟨ Σ-cong-id {k₂ = equivalence} ΠΣ-comm ⟩

  (∃ λ ((set , get-set) :
        ∃ λ (set : A → B → A) →
        ∀ a → Erased (∀ b → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , erased (get-set a) b₂
           in
           Is-equivalence f))                                             ↔⟨ Σ-cong (∃-cong λ _ → inverse Erased-Π↔Π) (λ _ → Eq.id) ⟩

  (∃ λ ((set , [ get-set ]) :
        ∃ λ (set : A → B → A) →
        Erased (∀ a b → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f))                                             ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (set : A → B → A) →
   ∃ λ (([ get-set ]) : Erased (∀ a b → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           Is-equivalence λ (a , _) → set a b₂ , get-set a b₂))           ↔⟨ (∃-cong λ _ → inverse
                                                                              Erased-Σ↔Σ) ⟩□
  (∃ λ (set : A → B → A) →
   Erased (∃ λ (get-set : ∀ a b → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           Is-equivalence λ (a , _) → set a b₂ , get-set a b₂))           □

-- A lemma relating S.Constant-≃-get-⁻¹-≃,
-- Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ and Constantᴱ-⁻¹ᴱ-≃ᴱ.

@0 to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡ :
  (bl : Block "Constant-≃-get-⁻¹-≃")
  {A : Type a} {B : Type b} {get : A → B} →
  (c : Constantᴱ (get ⁻¹ᴱ_)) →
  _≃_.to (S.Constant-≃-get-⁻¹-≃ bl)
    (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c) ≡
  Σ-map P.id erased
    (_≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c)
to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡
  bl {get = get} c =
  _≃_.from (Eq.≃-≡ $ Eq.↔⇒≃ $ inverse Σ-assoc) $
  Σ-≡,≡→≡
    (lemma bl)
    ((Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Is-equivalence-propositional ext)
       _ _)
  where
  lemma :
    (bl : Block "Constant-≃-get-⁻¹-≃") →
    (proj₁ $ _↔_.to Σ-assoc $
     _≃_.to (S.Constant-≃-get-⁻¹-≃ bl)
       (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c)) ≡
    (proj₁ $ _↔_.to Σ-assoc $
     Σ-map P.id erased (_≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c))
  lemma ⊠ =
    Σ-≡,≡→≡
      (⟨ext⟩ λ a → ⟨ext⟩ λ b →

       proj₁ (proj₁ (c (get a) b) (a , [ refl _ ]))      ≡⟨ cong proj₁ $ sym $ subst-refl _ _ ⟩∎
       proj₁ (subst (λ _ → get ⁻¹ᴱ b) (refl _)
                (proj₁ (c (get a) b) (a , [ refl _ ])))  ∎)
      (⟨ext⟩ λ a → ⟨ext⟩ λ b →

       subst (λ set → ∀ a b → get (set a b) ≡ b)
         (⟨ext⟩ λ a → ⟨ext⟩ λ b →
          cong {x = proj₁ (c (get a) b) (a , [ refl _ ])} proj₁ $ sym $
          subst-refl _ _)
         (λ a b → erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ]))))
         a b                                                              ≡⟨ sym $
                                                                             trans (push-subst-application _ _) $
                                                                             cong (_$ b) $ push-subst-application _ _ ⟩
       subst (λ set → get (set a b) ≡ b)
         (⟨ext⟩ λ _ → ⟨ext⟩ λ _ → cong proj₁ $ sym $ subst-refl _ _)
         (erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ]))))          ≡⟨ trans (subst-ext ext) $
                                                                             subst-ext ext ⟩
       subst (λ s → get s ≡ b)
         (cong proj₁ $ sym $ subst-refl _ _)
         (erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ]))))          ≡⟨ sym $ subst-∘ _ _ _ ⟩

       subst (λ (s , _) → get s ≡ b)
         (sym $ subst-refl _ _)
         (erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ]))))          ≡⟨ elim¹
                                                                               (λ {p} eq →
                                                                                  subst (λ (s , _) → get s ≡ b) eq
                                                                                    (erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ])))) ≡
                                                                                  erased (proj₂ p))
                                                                               (subst-refl _ _)
                                                                               _ ⟩∎
       erased
         (proj₂ (subst (λ _ → get ⁻¹ᴱ b) (refl _)
                   (proj₁ (c (get a) b) (a , [ refl _ ]))))               ∎)

------------------------------------------------------------------------
-- Coherently constant families of fibres

-- Coherently constant families of fibres (with erased proofs),
-- defined using univalence.

Coherently-constant-fibres :
  {A : Type a} {B : Type b} →
  @0 Univalence (a ⊔ b) →
  (A → B) → Type (a ⊔ b)
Coherently-constant-fibres {A = A} {B = B} univ get =
  ∃ λ (set : A → B → A) →
    Erased
      (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
       set ≡
       S.Lens.set {univ = univ}
         (record { get⁻¹-coherently-constant = c }))

-- Coherently-constant-fibres univ get is equivalent (with erased
-- proofs) to CE.Coherently-constant (get ⁻¹ᴱ_) (assuming univalence).

Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ :
  {A : Type a} {B : Type b} {get : A → B} →
  @0 Univalence (lsuc (a ⊔ b)) →
  (@0 univ : Univalence (a ⊔ b)) →
  Coherently-constant-fibres univ get ≃ᴱ
  CE.Coherently-constant (get ⁻¹ᴱ_)
Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ
  {a = a} {b = b} {A = A} {B = B} {get = get} univ′ univ =
  block λ bl →

  Coherently-constant-fibres univ get                                     ↔⟨⟩

  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      set ≡
      S.Lens.set {univ = univ}
        (record { get⁻¹-coherently-constant = c })))                      ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ c →
                                                                              ≡⇒≃ $ cong (_ ≡_) $
                                                                              S.Lens.set≡ {univ = univ}
                                                                                (record { get⁻¹-coherently-constant = c })
                                                                                bl)) ⟩
  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      set ≡ proj₁ (_≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property))))     ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → inverse $
                                                                              ≡-comm F.∘
                                                                              drop-⊤-right λ _ →
                                                                              _⇔_.to contractible⇔↔⊤ $
                                                                              other-singleton-contractible _)) ⟩
  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      ∃ λ (p : proj₁ (_≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property)) ≡
               set) →
      ∃ λ (q : ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
               ∀ b₁ b₂ →
               let f : get ⁻¹ b₁ → get ⁻¹ b₂
                   f = λ (a , _) → set a b₂ , get-set a b₂
               in Is-equivalence f) →
      subst
        (λ set →
           ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f)
        p
        (proj₂ (_≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property))) ≡
        q))                                                               ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                              (∃-cong λ _ → ∃-comm) F.∘
                                                                              ∃-comm F.∘
                                                                              (∃-cong λ _ → inverse Σ-assoc))) ⟩
  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
      ∃ λ (eq : ∀ b₁ b₂ →
                let f : get ⁻¹ b₁ → get ⁻¹ b₂
                    f = λ (a , _) → set a b₂ , get-set a b₂
                in Is-equivalence f) →
      ∃ λ (p : proj₁ (_≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property)) ≡
               set) →
      subst
        (λ set →
           ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f)
        p
        (proj₂ (_≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property))) ≡
        (get-set , eq)))                                                  ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                              B.Σ-≡,≡↔≡)) ⟩
  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
      ∃ λ (eq : ∀ b₁ b₂ →
                let f : get ⁻¹ b₁ → get ⁻¹ b₂
                    f = λ (a , _) → set a b₂ , get-set a b₂
                in Is-equivalence f) →
      _≃_.to (S.Constant-≃-get-⁻¹-≃ bl) (c .property) ≡
      (set , get-set , eq)))                                              ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                              ≡⇒≃ (cong (_≡ _) $ _≃_.left-inverse-of (S.Constant-≃-get-⁻¹-≃ bl) _) F.∘
                                                                              inverse (Eq.≃-≡ $ inverse $ S.Constant-≃-get-⁻¹-≃ bl))) ⟩
  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      ∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
      ∃ λ (eq : ∀ b₁ b₂ →
                let f : get ⁻¹ b₁ → get ⁻¹ b₂
                    f = λ (a , _) → set a b₂ , get-set a b₂
                in Is-equivalence f) →
      c .property ≡ S.Constant-≃-get-⁻¹-≃⁻¹ (set , get-set , eq)))        ↔⟨ (Σ-assoc F.∘
                                                                              (∃-cong λ _ →
                                                                               Erased-Σ↔Σ F.∘
                                                                               Erased-cong
                                                                                 (Σ-assoc F.∘
                                                                                  (∃-cong λ _ → ∃-comm) F.∘
                                                                                  ∃-comm))) ⟩
  (∃ λ ((set , [ get-set , eq ]) :
        ∃ λ (set : A → B → A) →
        Erased
          (∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f)) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      c .property ≡ S.Constant-≃-get-⁻¹-≃⁻¹ (set , get-set , eq)))        ↝⟨ (inverse $
                                                                              EEq.Σ-cong-≃ᴱ-Erased (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) λ c →
                                                                              Erased-cong (∃-cong λ c′ →
                                                                              ≡⇒↝ _ (cong (c′ .property ≡_) (
       _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c                                   ≡⟨ sym $ _≃_.to-from (S.Constant-≃-get-⁻¹-≃ bl) $
                                                                                   to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡
                                                                                     bl c ⟩∎
       S.Constant-≃-get-⁻¹-≃⁻¹
         (Σ-map P.id erased $ _≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c)                  ∎)))) ⟩

  (∃ λ (c : Constantᴱ (get ⁻¹ᴱ_)) →
   Erased
     (∃ λ (c′ : S.Coherently-constant univ (get ⁻¹_)) →
      c′ .property ≡ _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))             ↔⟨ (∃-cong λ c → Erased-cong (inverse $
                                                                              Σ-cong (S.Coinductive-coherently-constant≃Coherently-constant
                                                                                        univ′ univ) λ c′ →
                                                                              lemma₁ bl c (c′ .property))) ⟩
  (∃ λ (c : Constantᴱ (get ⁻¹ᴱ_)) →
   Erased
     (∃ λ (c′ : C.Coherently-constant (get ⁻¹_)) →
      c′ .property ≡ _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c))     ↔⟨ (∃-cong λ c → Erased-cong (lemma₃ bl c)) ⟩

  (∃ λ (c : Constantᴱ (get ⁻¹ᴱ_)) →
   Erased (
   ∃ λ (c′ : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ → proj₁ (c b₁ b₂) ≡ subst P.id (c′ .property b₁ b₂)))          ↔⟨ inverse Σ-assoc F.∘
                                                                             (Σ-cong (ΠΣ-comm F.∘ ∀-cong ext λ _ → ΠΣ-comm) λ _ → F.id) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   (∀ b₁ b₂ → Erased (Is-equivalence (get⁻¹ᴱ-const b₁ b₂))) ×
   Erased (
   ∃ λ (c′ : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ → get⁻¹ᴱ-const b₁ b₂ ≡ subst P.id (c′ .property b₁ b₂)))       ↔⟨ (∃-cong {k = bijection} λ _ →
                                                                              drop-⊤-left-× λ ([ _ , eq ]) →
                                                                              _⇔_.to contractible⇔↔⊤ $
                                                                              propositional⇒inhabited⇒contractible
                                                                                (Π-closure ext 1 λ _ →
                                                                                 Π-closure ext 1 λ _ →
                                                                                 H-level-Erased 1 (Is-equivalence-propositional ext))
                                                                                (λ x y →
                                                                                   [ Eq.respects-extensional-equality
                                                                                       (ext⁻¹ (sym (eq x y)))
                                                                                       (_≃_.is-equivalence $ Eq.subst-as-equivalence _ _)
                                                                                   ])) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c′ : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ → get⁻¹ᴱ-const b₁ b₂ ≡ subst P.id (c′ .property b₁ b₂)))       ↔⟨⟩

  CE.Coherently-constant (get ⁻¹ᴱ_)                                       □
  where
  @0 lemma₁ : ∀ _ _ _ → _ ≃ _
  lemma₁ bl c c′ =
    c′ ≡ _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c  ↝⟨ ≡⇒≃ $ cong (c′ ≡_) $
                                                            unblock bl
                                                              (λ bl → _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c ≡
                                                                      _≃_.from (S.Constant≃Constant-≃ univ)
                                                                        (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))
                                                              (refl _) ⟩
    c′ ≡
    _≃_.from (S.Constant≃Constant-≃ univ)
      (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c)           ↝⟨ inverse $ Eq.≃-≡ (S.Constant≃Constant-≃ univ) ⟩

    _≃_.to (S.Constant≃Constant-≃ univ) c′ ≡
    _≃_.to (S.Constant≃Constant-≃ univ)
      (_≃_.from (S.Constant≃Constant-≃ univ)
         (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))       ↝⟨ ≡⇒≃ $
                                                            cong (_≃_.to (S.Constant≃Constant-≃ univ) c′ ≡_) $
                                                            _≃_.right-inverse-of (S.Constant≃Constant-≃ univ) _ ⟩□
    _≃_.to (S.Constant≃Constant-≃ univ) c′ ≡
    _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c               □

  @0 lemma₂ : ∀ _ _ _ _ → _
  lemma₂ bl c′ b₁ b₂ =
    proj₁ (_≃_.from (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)
             (c′ .property) b₁ b₂)                                      ≡⟨ proj₁-from-Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl ⟩

    ECP.⁻¹→⁻¹ᴱ ∘ subst P.id (c′ .property b₁ b₂) ∘ ECP.⁻¹ᴱ→⁻¹           ≡⟨ sym $
                                                                           cong₂ (λ f g → f ∘ subst P.id (c′ .property b₁ b₂) ∘ g)
                                                                             (trans (⟨ext⟩ λ _ →
                                                                                     subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                              cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ) _)
                                                                             (trans (⟨ext⟩ λ _ →
                                                                                     subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                              cong _≃_.from $ _≃_.right-inverse-of (≡≃≃ univ) _) ⟩
    subst P.id (≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ) ∘
    subst P.id (c′ .property b₁ b₂) ∘
    subst P.id (sym (≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ))                              ≡⟨ (⟨ext⟩ λ _ →
                                                                            trans (subst-subst _ _ _ _) $
                                                                            subst-subst _ _ _ _) ⟩
    subst P.id
      (trans (sym (≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₁})))
         (trans (c′ .property b₁ b₂)
           (≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₂}))))                           ≡⟨ sym $
                                                                           cong (λ f → subst P.id
                                                                                         (trans (sym (f b₁))
                                                                                            (trans (c′ .property b₁ b₂) (f b₂)))) $
                                                                           _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩
    subst P.id
      (trans (sym (cong (_$ b₁) $ ⟨ext⟩ λ _ → ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ))
         (trans (c′ .property b₁ b₂)
           (cong (_$ b₂) $ ⟨ext⟩ λ b₂ →
            ≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₂}))))                           ≡⟨ cong (subst P.id) $
                                                                           elim¹
                                                                             (λ eq →
                                                                                trans (sym (cong (_$ b₁) eq))
                                                                                  (trans (c′ .property b₁ b₂) (cong (_$ b₂) eq)) ≡
                                                                                ≡⇒→ (cong C.Coherently-constant eq) c′ .property b₁ b₂)
                                                                             (
        trans (sym (cong (_$ b₁) (refl _)))
          (trans (c′ .property b₁ b₂) (cong (_$ b₂) (refl (get ⁻¹_))))        ≡⟨ trans (cong (flip trans _) $
                                                                                        trans (cong sym $ cong-refl _) $
                                                                                        sym-refl) $
                                                                                 trans (trans-reflˡ _) $
                                                                                 trans (cong (trans _) $ cong-refl _) $
                                                                                 trans-reflʳ _ ⟩

        c′ .property b₁ b₂                                                    ≡⟨ cong (λ eq → _≃_.to eq c′ .property b₁ b₂) $ sym $
                                                                                 trans (cong ≡⇒≃ $ cong-refl C.Coherently-constant)
                                                                                 ≡⇒↝-refl ⟩∎
        ≡⇒→ (cong C.Coherently-constant (refl _)) c′ .property b₁ b₂          ∎)
                                                                             _ ⟩∎
    subst P.id (≡⇒→ (cong C.Coherently-constant $
                     ⟨ext⟩ λ _ → ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ)
                c′ .property b₁ b₂)                                     ∎

  @0 lemma₃ : ∀ _ _ → _ ≃ _
  lemma₃ bl c =
    (∃ λ (c′ : C.Coherently-constant (get ⁻¹_)) →
     c′ .property ≡ _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c)  ↝⟨ (∃-cong λ _ →
                                                                         (∀-cong ext λ _ → ∀-cong ext λ _ → from-bijection $ inverse $
                                                                          ≡-comm F.∘
                                                                          ignore-propositional-component
                                                                            (H-level-Erased 1 (Is-equivalence-propositional ext))) F.∘
                                                                         inverse
                                                                           (Eq.extensionality-isomorphism ext F.∘
                                                                            (∀-cong ext λ _ → Eq.extensionality-isomorphism ext)) F.∘
                                                                         (≡⇒≃ $ cong (_ ≡_) $
                                                                          _≃_.left-inverse-of (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) _) F.∘
                                                                         (inverse $
                                                                          Eq.≃-≡ $ inverse $ Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)) ⟩
    (∃ λ (c′ : C.Coherently-constant (get ⁻¹_)) →
     ∀ b₁ b₂ →
     proj₁ (c b₁ b₂) ≡
     proj₁ (_≃_.from (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)
              (c′ .property) b₁ b₂))                                 ↝⟨ (Σ-cong (≡⇒≃ $ cong C.Coherently-constant $ ⟨ext⟩ λ _ →
                                                                                 ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ) λ c′ →
                                                                         ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                         ≡⇒≃ $ cong (proj₁ (c b₁ b₂) ≡_) (lemma₂ bl c′ b₁ b₂)) ⟩□
    (∃ λ (c′ : C.Coherently-constant (get ⁻¹ᴱ_)) →
     ∀ b₁ b₂ → proj₁ (c b₁ b₂) ≡ subst P.id (c′ .property b₁ b₂))    □

-- In erased contexts Coherently-constant-fibres univ get is
-- equivalent to S.Coherently-constant univ (get ⁻¹_).

@0 Coherently-constant-fibres≃Coherently-constant-⁻¹ :
  (bl : Block "Constant-≃-get-⁻¹-≃")
  {A : Type a} {B : Type b} {get : A → B} →
  (univ : Univalence (a ⊔ b)) →
  Coherently-constant-fibres univ get ≃
  S.Coherently-constant univ (get ⁻¹_)
Coherently-constant-fibres≃Coherently-constant-⁻¹
  bl {A = A} {B = B} {get = get} univ =
  Coherently-constant-fibres univ get                               ↔⟨⟩

  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      set ≡
      S.Lens.set {univ = univ}
        (record { get⁻¹-coherently-constant = c })))                ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩

  (∃ λ (set : A → B → A) →
   ∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
   set ≡
   S.Lens.set {univ = univ}
     (record { get⁻¹-coherently-constant = c }))                    ↔⟨ ∃-comm ⟩

  (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
   ∃ λ (set : A → B → A) →
   set ≡
   S.Lens.set {univ = univ}
     (record { get⁻¹-coherently-constant = c }))                    ↔⟨ (drop-⊤-right λ _ →
                                                                        _⇔_.to contractible⇔↔⊤ $
                                                                        singleton-contractible _) ⟩□
  S.Coherently-constant univ (get ⁻¹_)                              □

------------------------------------------------------------------------
-- The lens type family

-- Small coinductive lenses.
--
-- The lens type is defined using (erased) univalence. The use of a
-- record type makes it easier for Agda to infer the argument univ
-- from a value of type Lens univ A B.
--
-- Note that everything is erased, except for the getter and the
-- setter.

record Lens (@0 univ : Univalence (a ⊔ b))
            (A : Type a) (B : Type b) : Type (a ⊔ b) where
  field

    -- A getter.

    get : A → B

    -- A setter.

    set : A → B → A

    -- The family get ⁻¹_ is coherently constant (in erased contexts).

    @0 get⁻¹-coherently-constant : S.Coherently-constant univ (get ⁻¹_)

  -- Using get and get⁻¹-coherently-constant we can construct an
  -- erased lens.

  @0 erased-lens : S.Lens univ A B
  erased-lens = record
    { get                       = get
    ; get⁻¹-coherently-constant = get⁻¹-coherently-constant
    }

  field

    -- The setter that we get from this lens is equal to set.

    @0 set≡set : set ≡ S.Lens.set erased-lens

  -- The family of fibres of the getter is coherently constant.

  coherently-constant-fibres-get : Coherently-constant-fibres univ get
  coherently-constant-fibres-get =
    set , [ (get⁻¹-coherently-constant , set≡set) ]

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    {@0 univ : Univalence (a ⊔ b)} →
    Has-getter-and-setter (Lens {a = a} {b = b} univ)
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens can be expressed as a Σ-type.

Lens-as-Σ :
  {A : Type a} {B : Type b} {@0 univ : Univalence (a ⊔ b)} →
  Lens univ A B ≃
  ∃ λ (get : A → B) → Coherently-constant-fibres univ get
Lens-as-Σ =
  Eq.↔→≃
    (λ l → Lens.get l , Lens.coherently-constant-fibres-get l)
    _ refl refl

-- Lens univ A B is equivalent to CE.Lens A B (with erased proofs,
-- assuming univalence).

Lens≃ᴱLens :
  Block "Lens≃ᴱLens" →
  {A : Type a} {B : Type b} →
  @0 Univalence (lsuc (a ⊔ b)) →
  (@0 univ : Univalence (a ⊔ b)) →
  Lens univ A B ≃ᴱ CE.Lens A B
Lens≃ᴱLens ⊠ {A = A} {B = B} univ′ univ =
  Lens univ A B                                              ↔⟨ Lens-as-Σ ⟩
  (∃ λ (get : A → B) → Coherently-constant-fibres univ get)  ↝⟨ (∃-cong λ _ →
                                                                 Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ univ′ univ) ⟩□
  (∃ λ (get : A → B) → CE.Coherently-constant (get ⁻¹ᴱ_))    □

-- The equivalence preserves getters and setters.

Lens≃ᴱLens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱLens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱLens bl univ′ univ))
Lens≃ᴱLens-preserves-getters-and-setters ⊠ univ′ univ =
    (λ _ → refl _ , refl _)
  , (λ l →
       let open CE.Lens l in
         refl _
       , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
         proj₁
           (subst (λ _ → get ⁻¹ᴱ b) (refl tt)
              (get⁻¹ᴱ-const (get a) b (a , [ refl (get a) ])))  ≡⟨ cong proj₁ $ subst-refl _ _ ⟩∎

         proj₁ (get⁻¹ᴱ-const (get a) b (a , [ refl (get a) ]))  ∎)

-- Lens univ A B is equivalent to E.Lens A B (with erased proofs,
-- assuming univalence).

Lens≃ᴱLensᴱ :
  Block "Lens≃ᴱLensᴱ" →
  {A : Type a} {B : Type b}
  {@0 univ : Univalence (a ⊔ b)} →
  @0 Univalence (lsuc (a ⊔ b)) →
  Lens univ A B ≃ᴱ E.Lens A B
Lens≃ᴱLensᴱ bl {A = A} {B = B} {univ = univ} univ′ =
  Lens univ A B  ↝⟨ Lens≃ᴱLens bl univ′ univ ⟩
  CE.Lens A B    ↝⟨ CE.Lens≃ᴱLens bl univ′ univ ⟩
  V.Lens A B     ↝⟨ V.Lens≃ᴱHigher-lens bl univ ⟩□
  E.Lens A B     □

-- The equivalence preserves getters and setters (in erased contexts).

@0 Lens≃ᴱLensᴱ-preserves-getters-and-setters :
  (bl : Block "Lens→Lens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱLensᴱ bl {univ = univ} univ′))
Lens≃ᴱLensᴱ-preserves-getters-and-setters bl univ′ univ =
  Preserves-getters-and-setters-⇔-∘
    {f = _≃ᴱ_.logical-equivalence (V.Lens≃ᴱHigher-lens bl univ) F.∘
         _≃ᴱ_.logical-equivalence (CE.Lens≃ᴱLens bl univ′ univ)}
    {g = _≃ᴱ_.logical-equivalence (Lens≃ᴱLens bl univ′ univ)}
    (Preserves-getters-and-setters-⇔-∘
       {f = _≃ᴱ_.logical-equivalence (V.Lens≃ᴱHigher-lens bl univ)}
       {g = _≃ᴱ_.logical-equivalence (CE.Lens≃ᴱLens bl univ′ univ)}
       (V.Lens≃ᴱHigher-lens-preserves-getters-and-setters bl univ)
       (CE.Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ))
    (Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ)

-- In erased contexts Lens univ A B is equivalent to S.Lens univ A B.

@0 Lens≃Lens :
  (bl : Block "Constant-≃-get-⁻¹-≃") →
  Lens univ A B ≃ S.Lens univ A B
Lens≃Lens {univ = univ} {A = A} {B = B} bl =
  Lens univ A B                                               ↝⟨ Lens-as-Σ ⟩
  (∃ λ (get : A → B) → Coherently-constant-fibres univ get)   ↝⟨ (∃-cong λ _ → Coherently-constant-fibres≃Coherently-constant-⁻¹ bl univ) ⟩
  (∃ λ (get : A → B) → S.Coherently-constant univ (get ⁻¹_))  ↝⟨ inverse S.Lens-as-Σ ⟩□
  S.Lens univ A B                                             □

-- Lens≃Lens preserves getters and setters.

@0 Lens≃Lens-preserves-getters-and-setters :
  (bl : Block "Lens≃Lens")
  {A : Type a} {B : Type b}
  {univ : Univalence (a ⊔ b)} →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Lens≃Lens {univ = univ} bl))
Lens≃Lens-preserves-getters-and-setters ⊠ =
    (λ l →
       let open Lens l in
         refl _
       , (S.Lens.set erased-lens  ≡⟨ sym set≡set ⟩∎
          set                     ∎))
  , (λ _ → refl _ , refl _)

-- Lenses with stable view types are equal if their setters are equal
-- (in erased contexts, assuming univalence).

@0 lenses-equal-if-setters-equal :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  (univ : Univalence (a ⊔ b)) →
  (l₁ l₂ : Lens univ A B) →
  (∥ B ∥ → B) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal univ′ univ l₁ l₂ stable =
  block λ bl →

  Lens.set l₁ ≡ Lens.set l₂                            ↔⟨ ≡⇒≃ $ sym $ cong₂ _≡_
                                                            (proj₂ $ proj₁ (Lens≃Lens-preserves-getters-and-setters bl) l₁)
                                                            (proj₂ $ proj₁ (Lens≃Lens-preserves-getters-and-setters bl) l₂) ⟩
  S.Lens.set (_≃_.to (Lens≃Lens bl) l₁) ≡
  S.Lens.set (_≃_.to (Lens≃Lens bl) l₂)                ↝⟨ S.lenses-equal-if-setters-equal univ′ _ _ _ stable ⟩

  _≃_.to (Lens≃Lens bl) l₁ ≡ _≃_.to (Lens≃Lens bl) l₂  ↔⟨ Eq.≃-≡ $ Lens≃Lens bl ⟩□

  l₁ ≡ l₂                                              □

------------------------------------------------------------------------
-- Changing the implementation of the getter and the setter

-- One can change the getter of a lens, provided that the new
-- implementation is extensionally equal to the old one.

with-other-getter :
  {A : Type a} {B : Type b}
  (@0 univ : Univalence (a ⊔ b))
  (l : Lens univ A B)
  (get : A → B) →
  @0 get ≡ Lens.get l →
  Lens univ A B
with-other-getter {A = A} {B = B} univ l get p = record l
  { get                       = get
  ; get⁻¹-coherently-constant =
      subst (S.Coherently-constant univ ∘ _⁻¹_)
        (sym p) L.get⁻¹-coherently-constant
  ; set≡set =
      L.set          ≡⟨ L.set≡set ⟩
      S.Lens.set l₁  ≡⟨ cong S.Lens.set $ sym l₂≡l₁ ⟩∎
      S.Lens.set l₂  ∎
  }
  where
  module L = Lens l

  @0 l₁ l₂ : S.Lens univ A B

  l₁ = record
    { get                       = L.get
    ; get⁻¹-coherently-constant = L.get⁻¹-coherently-constant
    }

  l₂ = record
    { get                       = get
    ; get⁻¹-coherently-constant =
        subst (S.Coherently-constant univ ∘ _⁻¹_) (sym p)
          L.get⁻¹-coherently-constant
    }

  @0 l₂≡l₁ : l₂ ≡ l₁
  l₂≡l₁ =
    _≃_.to (Eq.≃-≡ S.Lens-as-Σ) $ Σ-≡,≡→≡ p
      (subst (S.Coherently-constant univ ∘ _⁻¹_) p
         (subst (S.Coherently-constant univ ∘ _⁻¹_) (sym p)
            L.get⁻¹-coherently-constant)                     ≡⟨ subst-subst-sym _ _ _ ⟩∎

       L.get⁻¹-coherently-constant                           ∎)

_ : Lens.get (with-other-getter univ l g p) ≡ g
_ = refl _

_ : Lens.set (with-other-getter univ l g p) ≡ Lens.set l
_ = refl _

-- The resulting lens is equal to the old one (if the equality proof
-- is not erased).

with-other-getter≡ :
  {A : Type a} {B : Type b}
  (@0 univ : Univalence (a ⊔ b))
  (l : Lens univ A B)
  (get : A → B)
  (p : get ≡ Lens.get l) →
  with-other-getter univ l get p ≡ l
with-other-getter≡ {A = A} {B = B} univ l get p =
  _≃_.to (Eq.≃-≡ Lens-as-Σ) $ Σ-≡,≡→≡ p
    (subst (Coherently-constant-fibres univ) p
       L′.coherently-constant-fibres-get                             ≡⟨ push-subst-pair-× _ _ ⟩

     L.set ,
     subst
       (λ get →
          Erased
            (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
             L.set ≡
             S.Lens.set {univ = univ}
               (record { get⁻¹-coherently-constant = c })))
       p
       [ (L′.get⁻¹-coherently-constant , L′.set≡set) ]               ≡⟨ cong (L.set ,_) push-subst-[] ⟩

     L.set ,
     [ subst
         (λ get →
            ∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
            L.set ≡
            S.Lens.set {univ = univ}
              (record { get⁻¹-coherently-constant = c }))
         p
         (L′.get⁻¹-coherently-constant , L′.set≡set)
     ]                                                               ≡⟨ cong (L.set ,_) $ []-cong [ push-subst-pair′ _ _ _ ] ⟩

     L.set ,
     [ ( L.get⁻¹-coherently-constant
       , subst
           (λ ((get , c) : ∃ (S.Coherently-constant univ ∘ _⁻¹_)) →
              L.set ≡
              S.Lens.set {univ = univ}
                (record { get⁻¹-coherently-constant = c }))
           (Σ-≡,≡→≡ p (subst-subst-sym _ _ _))
           L′.set≡set
       )
     ]                                                               ≡⟨⟩

     L.set ,
     [ ( L.get⁻¹-coherently-constant
       , let q = Σ-≡,≡→≡ {p₂ = _ , L.get⁻¹-coherently-constant}
                   p
                   (subst-subst-sym _ _ _)
         in
         subst
           (λ ((get , c) : ∃ (S.Coherently-constant univ ∘ _⁻¹_)) →
              L.set ≡
              S.Lens.set {univ = univ}
                (record { get⁻¹-coherently-constant = c }))
           q
           (trans L.set≡set
              (cong (S.Lens.set {univ = univ}) $ sym $
               _≃_.to (Eq.≃-≡ S.Lens-as-Σ) q))
       )
     ]                                                               ≡⟨ cong (L.set ,_) $ []-cong
                                                                        [ cong (L.get⁻¹-coherently-constant ,_) $
                                                                          elim₁
                                                                            (λ q →
                                                                               subst
                                                                                 (λ ((get , c) : ∃ (S.Coherently-constant univ ∘ _⁻¹_)) →
                                                                                    L.set ≡
                                                                                    S.Lens.set {univ = univ}
                                                                                      (record { get⁻¹-coherently-constant = c }))
                                                                                 q
                                                                                 (trans L.set≡set
                                                                                    (cong (S.Lens.set {univ = univ}) $ sym $
                                                                                     _≃_.to (Eq.≃-≡ S.Lens-as-Σ) q)) ≡
                                                                               L.set≡set)
                                                                            (trans (subst-refl _ _) $
                                                                             trans (cong (trans _) $
                                                                                    trans (cong (cong _) $
                                                                                           trans (cong sym (Eq.to-≃-≡-refl S.Lens-as-Σ))
                                                                                           sym-refl) $
                                                                                    cong-refl _) $
                                                                             trans-reflʳ _)
                                                                            _
                                                                        ] ⟩
     L.set , [ (L.get⁻¹-coherently-constant , L.set≡set) ]           ≡⟨⟩

     L.coherently-constant-fibres-get                                ∎)
  where
  module L = Lens l

  l′ : Lens univ A B
  l′ = record
    { get                       = get
    ; get⁻¹-coherently-constant =
        subst (S.Coherently-constant univ ∘ _⁻¹_) (sym p)
          L.get⁻¹-coherently-constant
    }

  module L′ = Lens l′

-- One can change the setter of a lens, provided that the new
-- implementation is extensionally equal to the old one.

with-other-setter :
  {A : Type a} {B : Type b}
  {@0 univ : Univalence (a ⊔ b)}
  (l : Lens univ A B)
  (set : A → B → A) →
  @0 set ≡ Lens.set l →
  Lens univ A B
with-other-setter l set p = record l
  { set     = set
  ; set≡set = trans p (Lens.set≡set l)
  }

_ : Lens.get (with-other-setter l s p) ≡ Lens.get l
_ = refl _

_ : Lens.set (with-other-setter l s p) ≡ s
_ = refl _

-- The resulting lens is equal to the old one (if the equality proof
-- is not erased).

with-other-setter≡ :
  {A : Type a} {B : Type b}
  {@0 univ : Univalence (a ⊔ b)}
  (l : Lens univ A B)
  (set : A → B → A)
  (p : set ≡ Lens.set l) →
  with-other-setter l set p ≡ l
with-other-setter≡ {univ = univ} l set p =
  _≃_.to (Eq.≃-≡ Lens-as-Σ) $ cong (get ,_) $ Σ-≡,≡→≡ p
    (subst
       (λ set → Erased
                  (∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
                   set ≡
                   S.Lens.set {univ = univ}
                     (record { get⁻¹-coherently-constant = c })))
       p
       [ (get⁻¹-coherently-constant , trans p set≡set) ]             ≡⟨ push-subst-[] ⟩

     [ subst
         (λ set → ∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
                  set ≡
                  S.Lens.set {univ = univ}
                    (record { get⁻¹-coherently-constant = c }))
         p
         (get⁻¹-coherently-constant , trans p set≡set)
     ]                                                               ≡⟨ []-cong [ push-subst-pair-× _ _ ] ⟩

     [ ( get⁻¹-coherently-constant
       , subst (_≡ S.Lens.set {univ = univ}
                     (record { get⁻¹-coherently-constant =
                                 get⁻¹-coherently-constant }))
           p
           (trans p set≡set)
       )
     ]                                                               ≡⟨ []-cong [ cong (_ ,_) subst-trans-sym ] ⟩

     [ ( get⁻¹-coherently-constant
       , trans (sym p) (trans p set≡set)
       )
     ]                                                               ≡⟨ []-cong [ cong (_ ,_) $ trans-sym-[trans] _ _ ] ⟩∎

     [ (get⁻¹-coherently-constant , set≡set) ]                       ∎)
  where
  open Lens l

------------------------------------------------------------------------
-- Code for converting from S.Lens to Lens

-- Data corresponding to the erased proofs of a lens.

record Erased-proofs
         {A : Type a} {B : Type b}
         (univ : Univalence (a ⊔ b))
         (get : A → B) (set : A → B → A) : Type (a ⊔ b) where
  field
    @0 get⁻¹-coherently-constant : S.Coherently-constant univ (get ⁻¹_)

  @0 erased-lens : S.Lens univ A B
  erased-lens = record
    { get                       = get
    ; get⁻¹-coherently-constant = get⁻¹-coherently-constant
    }

  field
    @0 set≡set : set ≡ S.Lens.set erased-lens

-- Extracts "erased proofs" from a lens (in erased contexts).

@0 Lens→Erased-proofs :
  (l : S.Lens univ A B) →
  Erased-proofs univ (S.Lens.get l) (S.Lens.set l)
Lens→Erased-proofs {univ = univ} l = proofs ⊠
  where
  module _ (bl : Unit) where

    open Erased-proofs

    l′ = _≃_.from (Lens≃Lens bl) l

    proofs : Erased-proofs univ (Lens.get l′) (Lens.set l′)
    proofs .get⁻¹-coherently-constant =
      Lens.get⁻¹-coherently-constant l′
    proofs .set≡set = Lens.set≡set l′

-- Converts two functions and some erased proofs to a lens.
--
-- Note that Agda can in many cases infer "get" and "set" from the
-- first explicit argument, see (for instance) id below.

Erased-proofs→Lens :
  {A : Type a} {B : Type b} {get : A → B} {set : A → B → A}
  {@0 univ : Univalence (a ⊔ b)} →
  @0 Erased-proofs univ get set →
  Lens univ A B
Erased-proofs→Lens {get = get} {set = set} ep = λ where
  .Lens.get                       → get
  .Lens.set                       → set
  .Lens.get⁻¹-coherently-constant →
    Erased-proofs.get⁻¹-coherently-constant ep
  .Lens.set≡set → Erased-proofs.set≡set ep

------------------------------------------------------------------------
-- Identity and composition

-- An identity lens.

id :
  {A : Type a}
  (@0 univ : Univalence a) →
  Lens univ A A
id univ = Erased-proofs→Lens (Lens→Erased-proofs (S.id univ))

-- Composition.

infix 9 ⟨_,_⟩_∘_

⟨_,_⟩_∘_ :
  {A : Type a} {B : Type b} {C : Type c}
  {@0 univ₁ : Univalence (b ⊔ c)}
  {@0 univ₂ : Univalence (a ⊔ b)}
  (@0 univ₃ : Univalence (a ⊔ c)) →
  @0 Univalence (a ⊔ b ⊔ c) →
  Lens univ₁ B C → Lens univ₂ A B → Lens univ₃ A C
⟨ univ₃ , univ ⟩ l₁ ∘ l₂ =
  Erased-proofs→Lens
    (subst (Erased-proofs _ _)
       (⟨ext⟩ λ a → ⟨ext⟩ λ c →
        S.Lens.set l₂′ a (S.Lens.set l₁′ (get l₂ a) c)  ≡⟨ cong (λ s → s a (S.Lens.set l₁′ (get l₂ a) c)) $
                                                           proj₂ $ proj₁ (Lens≃Lens-preserves-getters-and-setters ⊠) l₂ ⟩
        set l₂ a (S.Lens.set l₁′ (get l₂ a) c)          ≡⟨ cong (λ s → set l₂ a (s (get l₂ a) c)) $
                                                           proj₂ $ proj₁ (Lens≃Lens-preserves-getters-and-setters ⊠) l₁ ⟩∎
        set l₂ a (set l₁ (get l₂ a) c)                  ∎) $
     Lens→Erased-proofs (S.⟨ univ₃ , univ ⟩ l₁′ ∘ l₂′))
  where
  open Lens

  @0 l₁′ : _
  l₁′ = _≃_.to (Lens≃Lens ⊠) l₁

  @0 l₂′ : _
  l₂′ = _≃_.to (Lens≃Lens ⊠) l₂

-- The setter of a lens formed using composition is defined in the
-- "right" way.

set-∘ :
  ∀ {A : Type a} {B : Type b} {C : Type c}
    {@0 univ₁ : Univalence (b ⊔ c)}
    {@0 univ₂ : Univalence (a ⊔ b)}
  (@0 univ₃ : Univalence (a ⊔ c))
  (@0 univ₄ : Univalence (a ⊔ b ⊔ c))
  (l₁ : Lens univ₁ B C) (l₂ : Lens univ₂ A B) {a c} →
  Lens.set (⟨ univ₃ , univ₄ ⟩ l₁ ∘ l₂) a c ≡
  Lens.set l₂ a (Lens.set l₁ (Lens.get l₂ a) c)
set-∘ _ _ _ _ = refl _

-- Composition is associative if the view type of the resulting lens
-- is stable (in erased contexts, assuming univalence).

@0 associativity :
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

@0 left-identity :
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

@0 right-identity :
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
