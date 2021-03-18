------------------------------------------------------------------------
-- Small coinductive higher lenses with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Small.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Colimit.Sequential.Very-erased eq as CS
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages.Cubical eq as ECP
  using (_⁻¹ᴱ_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Erased eq as T
  using (∥_∥ᴱ; ∣_∣)
import H-level.Truncation.Propositional.Non-recursive.Erased eq as N
open import H-level.Truncation.Propositional.One-step eq as O
  using (∣_∣; ∥_∥¹-out-^; ∥_∥¹-in-^; ∣_,_∣-in-^)
open import Preimage equality-with-J using (_⁻¹_)
open import Tactic.Sigma-cong equality-with-J
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant eq
  as V
open import Lens.Non-dependent.Higher.Coherently.Coinductive eq
import Lens.Non-dependent.Higher.Coinductive eq as C
import Lens.Non-dependent.Higher.Coinductive.Small eq as S

private
  variable
    a b p : Level
    A B   : Type a
    P     : A → Type p
    f     : (x : A) → P x

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
  ECP.⁻¹→⁻¹ᴱ ∘ subst id (c b₁ b₂) ∘ ECP.⁻¹ᴱ→⁻¹
proj₁-from-Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ ⊠ {c = c} {b₁ = b₁} {b₂ = b₂} =
  ⟨ext⟩ λ (a , [ eq ]) →

  ECP.⁻¹→⁻¹ᴱ (≡⇒→ (c b₁ b₂) (a , eq))       ≡⟨ cong ECP.⁻¹→⁻¹ᴱ $ sym $
                                               subst-id-in-terms-of-≡⇒↝ equivalence ⟩∎
  ECP.⁻¹→⁻¹ᴱ (subst id (c b₁ b₂) (a , eq))  ∎

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
   Erased (∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f))
Constantᴱ-⁻¹ᴱ-≃ᴱ {A = A} {B = B} {get = get} ⊠ =
  Constantᴱ (get ⁻¹ᴱ_)                                                   ↔⟨⟩

  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence f))                                            ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ f → Erased-cong (
                                                                             Is-equivalence≃Is-equivalence-∘ˡ {k = equivalence} ext $
                                                                             _≃_.is-equivalence $ from-bijection $
                                                                             ∃-cong λ _ → erased Erased↔)) ⟩
  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map id erased ∘ f)))                        ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∃-cong λ f → Erased-cong (
                                                                             Is-equivalence≃Is-equivalence-∘ʳ {k = equivalence} ext $
                                                                             _≃_.is-equivalence $ from-bijection $
                                                                             ∃-cong λ _ → inverse $ erased Erased↔)) ⟩
  (∀ b₁ b₂ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map id erased ∘ f ∘ Σ-map id [_]→)))        ↔⟨ Π-comm ⟩

  (∀ b₂ b₁ →
   ∃ λ (f : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (Is-equivalence (Σ-map id erased ∘ f ∘ Σ-map id [_]→)))        ↔⟨ (∀-cong ext λ _ → ΠΣ-comm) ⟩

  (∀ b₂ →
   ∃ λ (f : ∀ b₁ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   ∀ b₁ →
   Erased (Is-equivalence (Σ-map id erased ∘ f b₁ ∘ Σ-map id [_]→)))     ↔⟨ (∀-cong ext λ _ → ∃-cong λ _ → inverse Erased-Π↔Π) ⟩

  (∀ b₂ →
   ∃ λ (f : ∀ b₁ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           Is-equivalence (Σ-map id erased ∘ f b₁ ∘ Σ-map id [_]→)))     ↔⟨ (∀-cong ext λ _ →
                                                                             Σ-cong {k₂ = equivalence}
                                                                               (inverse (∀-cong ext λ _ → currying) F.∘
                                                                                Π-comm F.∘
                                                                                (∀-cong ext λ _ → currying))
                                                                               (λ _ → Eq.id)) ⟩
  (∀ b₂ →
   ∃ λ (f : ∀ a → (∃ λ b₁ → Erased (get a ≡ b₁)) → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , eq) → Σ-map id erased (f a (b₁ , [ eq ]))
           in
           Is-equivalence g))                                            ↝⟨ (∀-cong ext λ _ →
                                                                             EEq.Σ-cong-≃ᴱ-Erased
                                                                               (∀-cong ext λ _ →
                                                                                EEq.drop-⊤-left-Π-≃ᴱ ext
                                                                                  (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤
                                                                                   Contractibleᴱ-Erased-other-singleton)
                                                                                  (λ _ _ → F.id)) λ f →
                                                                             Erased-cong (
                                                                             ∀-cong ext λ b₁ →
                                                                             Is-equivalence-cong ext λ (a , eq) →
      Σ-map id erased (f a (b₁ , [ eq ]))                                      ≡⟨ cong (Σ-map id erased ∘ f a) $ sym $
                                                                                  erased (proj₂ Contractibleᴱ-Erased-other-singleton) _ ⟩

      Σ-map id erased (f a (get a , [ refl _ ]))                               ≡⟨ cong (Σ-map id erased) $ sym $ subst-refl _ _ ⟩∎

      Σ-map id erased
        (subst (const _) (refl _) (f a (get a , [ refl _ ])))                  ∎)) ⟩

  (∀ b₂ →
   ∃ λ (f : A → get ⁻¹ᴱ b₂) →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map id erased (f a)
           in
           Is-equivalence g))                                            ↔⟨ ΠΣ-comm ⟩

  (∃ λ (f : (b : B) → A → get ⁻¹ᴱ b) →
   ∀ b₂ →
   Erased (∀ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map id erased (f b₂ a)
           in
           Is-equivalence g))                                            ↔⟨ (∃-cong λ _ → inverse Erased-Π↔Π) ⟩

  (∃ λ (f : (b : B) → A → get ⁻¹ᴱ b) →
   Erased (∀ b₂ b₁ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map id erased (f b₂ a)
           in
           Is-equivalence g))                                            ↔⟨ Σ-cong Π-comm (λ _ → Erased-cong Π-comm) ⟩

  (∃ λ (f : A → (b : B) → get ⁻¹ᴱ b) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → Σ-map id erased (f a b₂)
           in
           Is-equivalence g))                                            ↔⟨ Σ-cong (∀-cong ext λ _ → ΠΣ-comm) (λ _ → Eq.id) ⟩

  (∃ λ (f : A → ∃ λ (set : B → A) →
                (b : B) → Erased (get (set b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → proj₁ (f a) b₂ , erased (proj₂ (f a) b₂)
           in
           Is-equivalence g))                                            ↔⟨ Σ-cong
                                                                              (∀-cong ext λ _ → ∃-cong λ _ → inverse Erased-Π↔Π)
                                                                              (λ _ → Eq.id) ⟩
  (∃ λ (f : A → ∃ λ (set : B → A) →
                Erased ((b : B) → get (set b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let g : get ⁻¹ b₁ → get ⁻¹ b₂
               g = λ (a , _) → proj₁ (f a) b₂ , erased (proj₂ (f a)) b₂
           in
           Is-equivalence g))                                            ↔⟨ Σ-cong-id {k₂ = equivalence} ΠΣ-comm ⟩

  (∃ λ ((set , get-set) :
        ∃ λ (set : A → B → A) →
        (a : A) → Erased ((b : B) → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , erased (get-set a) b₂
           in
           Is-equivalence f))                                            ↔⟨ Σ-cong (∃-cong λ _ → inverse Erased-Π↔Π) (λ _ → Eq.id) ⟩

  (∃ λ ((set , [ get-set ]) :
        ∃ λ (set : A → B → A) →
        Erased ((a : A) (b : B) → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           let f : get ⁻¹ b₁ → get ⁻¹ b₂
               f = λ (a , _) → set a b₂ , get-set a b₂
           in
           Is-equivalence f))                                            ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (set : A → B → A) →
   ∃ λ (([ get-set ]) : Erased ((a : A) (b : B) → get (set a b) ≡ b)) →
   Erased (∀ b₁ b₂ →
           Is-equivalence λ (a , _) → set a b₂ , get-set a b₂))          ↔⟨ (∃-cong λ _ → inverse
                                                                             Erased-Σ↔Σ) ⟩□
  (∃ λ (set : A → B → A) →
   Erased (∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
           ∀ b₁ b₂ →
           Is-equivalence λ (a , _) → set a b₂ , get-set a b₂))          □

-- A lemma relating S.Constant-≃-get-⁻¹-≃,
-- Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ and Constantᴱ-⁻¹ᴱ-≃ᴱ.

@0 to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡ :
  (bl : Block "Constant-≃-get-⁻¹-≃")
  {A : Type a} {B : Type b} {get : A → B} →
  (c : Constantᴱ (get ⁻¹ᴱ_)) →
  _≃_.to (S.Constant-≃-get-⁻¹-≃ bl)
    (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c) ≡
  Σ-map id erased
    (_≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c)
to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡
  bl {get = get} c =
  _≃_.from (Eq.≃-≡ $ Eq.↔⇒≃ $ inverse Σ-assoc) $
  Σ-≡,≡→≡
    (lemma bl)
    ((Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Eq.propositional ext _)
       _ _)
  where
  lemma :
    (bl : Block "Constant-≃-get-⁻¹-≃") →
    (proj₁ $ _↔_.to Σ-assoc $
     _≃_.to (S.Constant-≃-get-⁻¹-≃ bl)
       (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c)) ≡
    (proj₁ $ _↔_.to Σ-assoc $
     Σ-map id erased (_≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c))
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
         (erased (proj₂ (proj₁ (c (get a) b) (a , [ refl _ ]))))          ≡⟨ trans (subst-ext _ _) $
                                                                             subst-ext _ _ ⟩
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
      (∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
       ∃ λ (eq : ∀ b₁ b₂ →
                 let f : get ⁻¹ b₁ → get ⁻¹ b₂
                     f = λ (a , _) → set a b₂ , get-set a b₂
                 in
                 Is-equivalence f) →
       ∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
       ∃ λ b →
       c .property ≡
       _≃_.from (S.Constant-≃-get-⁻¹-≃ b) (set , get-set , eq))

private

  -- A lemma used in the implementation of ∥∥ᴱ→≃.

  ∥∥ᴱ→≃-lemma :
    Block "∥∥ᴱ→≃-lemma" →
    (f₀ : A → B) →
    (∃ λ (f₊ : ∀ n → ∥ A ∥¹-out-^ (1 + n) → B) →
       (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
       (∀ n x → f₊ (suc n) ∣ x ∣ ≡ f₊ n x)) ≃
    (∃ λ (f₊ : ∀ n → ∥ A ∥¹-in-^ (1 + n) → B) →
       (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
       (∀ n x → f₊ (suc n) ∣ n , x ∣-in-^ ≡ f₊ n x))
  ∥∥ᴱ→≃-lemma ⊠ _ =
    inverse $
    Σ-cong {k₁ = equivalence}
      (∀-cong ext λ n →
       →-cong₁ ext (inverse $ O.∥∥¹-out-^≃∥∥¹-in-^ (suc n))) λ f →
    ∃-cong λ _ → ∀-cong ext λ n →
    Π-cong-contra ext (O.∥∥¹-out-^≃∥∥¹-in-^ (suc n)) λ x →
    ≡⇒≃ $ cong (λ y → f (suc n) y ≡
                      f n (_≃_.to (O.∥∥¹-out-^≃∥∥¹-in-^ (suc n)) x)) $
    sym $ O.∣∣≡∣,∣-in-^ (1 + n)

-- Functions from ∥ A ∥ᴱ can be expressed as coherently constant
-- functions from A with erased "proofs" (assuming univalence).

∥∥ᴱ→≃ :
  Block "∥∥ᴱ→≃" →
  {A : Type a} {B : Type b} →
  @0 Univalence (a ⊔ b) →
  (∥ A ∥ᴱ → B)
    ≃
  (∃ λ (f : A → B) → Erased (C.Coherently-constant f))
∥∥ᴱ→≃ bl {A = A} {B = B} univ =
  (∥ A ∥ᴱ → B)                                                 ↝⟨ →-cong ext T.∥∥ᴱ≃∥∥ᴱ F.id ⟩

  (N.∥ A ∥ᴱ → B)                                               ↝⟨ CS.universal-property ⟩

  (∃ λ (f₀ : A → B) →
     Erased (∃ λ (f₊ : ∀ n → ∥ A ∥¹-out-^ (1 + n) → B) →
               (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
               (∀ n x → f₊ (suc n) ∣ x ∣ ≡ f₊ n x)))           ↝⟨ ∃-cong (λ f → Erased-cong (∥∥ᴱ→≃-lemma bl f)) ⟩

  (∃ λ (f₀ : A → B) →
     Erased (∃ λ (f₊ : ∀ n → ∥ A ∥¹-in-^ (1 + n) → B) →
               (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
               (∀ n x → f₊ (suc n) ∣ n , x ∣-in-^ ≡ f₊ n x)))  ↝⟨ ∃-cong (λ f → Erased-cong (inverse $
                                                                  C.Coherently-constant′≃ bl)) ⟩

  (∃ λ (f : A → B) → Erased (C.Coherently-constant′ f))        ↝⟨ ∃-cong (λ f → Erased-cong (inverse $
                                                                  C.Coherently-constant≃Coherently-constant′ bl univ)) ⟩□
  (∃ λ (f : A → B) → Erased (C.Coherently-constant f))         □

-- A "computation" rule for ∥∥ᴱ→≃.

@0 cong-from-∥∥ᴱ→≃-truncation-is-proposition :
  (bl : Block "∥∥ᴱ→≃")
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b)) →
  {f : A → B} {c : C.Coherently-constant f}
  {x y : A} {p : ∣ x ∣ ≡ ∣ y ∣} →
  cong (_≃_.from (∥∥ᴱ→≃ bl univ) (f , [ c ])) p ≡
  c .property x y
cong-from-∥∥ᴱ→≃-truncation-is-proposition
  bl {A = A} univ {f = f} {c = c} {x = x} {y = y} {p = p} =
  cong (_≃_.from (∥∥ᴱ→≃ bl univ) (f , [ c ])) p                         ≡⟨⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]) ∘
        _≃_.to T.∥∥ᴱ≃∥∥ᴱ)
    p                                                                   ≡⟨ sym $ cong-∘ _ _ _ ⟩

  (cong (_≃_.from CS.universal-property (f , [ g bl ])) $
   cong (_≃_.to T.∥∥ᴱ≃∥∥ᴱ) p)                                           ≡⟨ cong (cong _) $ mono₁ 1 N.∥∥ᴱ-proposition _ _ ⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]))
    (N.∥∥ᴱ-proposition N.∣ x ∣ N.∣ y ∣)                                 ≡⟨⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]))
    (trans (sym (CS.∣∣₊≡∣∣₀ x))
       (trans (cong CS.∣_∣₊ (O.∣∣-constant x y))
          (CS.∣∣₊≡∣∣₀ y)))                                              ≡⟨ trans (cong-trans _ _ _) $
                                                                           cong₂ trans
                                                                             (cong-sym _ _)
                                                                             (trans (cong-trans _ _ _) $
                                                                              cong (flip trans _) $
                                                                              cong-∘ _ _ _) ⟩
  trans
    (sym $ cong (_≃_.from CS.universal-property (f , [ g bl ]))
             (CS.∣∣₊≡∣∣₀ x))
    (trans
       (cong (_≃_.from CS.universal-property (f , [ g bl ]) ∘ CS.∣_∣₊)
          (O.∣∣-constant x y))
       (cong (_≃_.from CS.universal-property (f , [ g bl ]))
          (CS.∣∣₊≡∣∣₀ y)))                                              ≡⟨ cong₂ trans
                                                                             (cong sym CS.rec-∣∣₊≡∣∣₀)
                                                                             (cong (trans _) CS.rec-∣∣₊≡∣∣₀) ⟩
  trans (sym $ proj₁ (proj₂ (g bl)) x)
    (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
       (proj₁ (proj₂ (g bl)) y))                                        ≡⟨ lemma bl ⟩∎

  c .property x y                                                       ∎
  where
  g : ∀ _ → _
  g bl =
    _≃_.from (∥∥ᴱ→≃-lemma bl _) $
    _≃_.to (C.Coherently-constant′≃ bl) $
    _≃_.to (C.Coherently-constant≃Coherently-constant′ bl univ) c

  lemma :
    ∀ bl →
    trans (sym $ proj₁ (proj₂ (g bl)) x)
      (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
         (proj₁ (proj₂ (g bl)) y)) ≡
    c .property x y
  lemma bl@⊠ =
    trans (sym $ proj₁ (proj₂ (g bl)) x)
      (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
         (proj₁ (proj₂ (g bl)) y))                                ≡⟨⟩

    trans (sym $ refl _)
      (trans (cong (O.rec′ f (c .property)) (O.∣∣-constant x y))
         (refl _))                                                ≡⟨ trans (cong₂ trans sym-refl (trans-reflʳ _)) $
                                                                     trans-reflˡ _ ⟩

    cong (O.rec′ f (c .property)) (O.∣∣-constant x y)             ≡⟨ O.rec-∣∣-constant ⟩∎

    c .property x y                                               ∎

-- Coherently-constant-fibres univ get is equivalent (with erased
-- proofs) to V.Coherently-constant (get ⁻¹ᴱ_) (assuming univalence).

Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ :
  {A : Type a} {B : Type b} {get : A → B} →
  @0 Univalence (lsuc (a ⊔ b)) →
  (@0 univ : Univalence (a ⊔ b)) →
  Coherently-constant-fibres univ get ≃ᴱ
  V.Coherently-constant (get ⁻¹ᴱ_)
Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ
  {a = a} {b = b} {A = A} {B = B} {get = get} univ′ univ =
  block λ bl →

  (∃ λ (set : A → B → A) →
   Erased
     (∃ λ (get-set : (a : A) (b : B) → get (set a b) ≡ b) →
      ∃ λ (eq : ∀ b₁ b₂ →
                let f : get ⁻¹ b₁ → get ⁻¹ b₂
                    f = λ (a , _) → set a b₂ , get-set a b₂
                in Is-equivalence f) →
      ∃ λ (c : S.Coherently-constant univ (get ⁻¹_)) →
      ∃ λ b →
      c .property ≡
      _≃_.from (S.Constant-≃-get-⁻¹-≃ b) (set , get-set , eq)))           ↔⟨ (Σ-assoc F.∘
                                                                              (∃-cong λ _ →
                                                                               Erased-Σ↔Σ F.∘
                                                                               Erased-cong Σ-assoc)) ⟩
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
      ∃ λ b →
      c .property ≡
      _≃_.from (S.Constant-≃-get-⁻¹-≃ b) (set , get-set , eq)))           ↝⟨ (inverse $
                                                                              EEq.Σ-cong-≃ᴱ-Erased (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) λ c →
                                                                              Erased-cong (∃-cong λ c′ →
                                                                              (from-bijection $ inverse $ drop-⊤-left-Σ $ _≃_.bijection $
                                                                               Eq.↔→≃ _ (λ _ → bl) refl λ { ⊠ → unblock bl (_≡ ⊠) (refl _) }) F.∘
                                                                              ≡⇒↝ _ (cong (_ ≡_) (
       _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c                                   ≡⟨ sym $ _≃_.to-from (S.Constant-≃-get-⁻¹-≃ bl) $
                                                                                   to-Constant-≃-get-⁻¹-≃-to-Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹-≡
                                                                                     bl c ⟩∎
       _≃_.from (S.Constant-≃-get-⁻¹-≃ bl)
         (Σ-map id erased $ _≃ᴱ_.to (Constantᴱ-⁻¹ᴱ-≃ᴱ bl) c)                    ∎)))) ⟩

  (∃ λ (c : Constantᴱ (get ⁻¹ᴱ_)) →
   Erased
     (∃ λ (c′ : S.Coherently-constant univ (get ⁻¹_)) →
      c′ .property ≡ _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))             ↔⟨ (∃-cong λ c → Erased-cong (inverse $
                                                                              Σ-cong (S.Coinductive-coherently-constant≃Coherently-constant
                                                                                        univ′ univ) λ c′ →
      c′ .property ≡ _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c             ↝⟨ ≡⇒≃ $ cong (c′ .property ≡_) $
                                                                                   unblock bl
                                                                                     (λ bl → _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c ≡
                                                                                             _≃_.from (S.Constant≃Constant-≃ univ)
                                                                                               (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))
                                                                                     (refl _) ⟩
      c′ .property ≡
      _≃_.from (S.Constant≃Constant-≃ univ)
        (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c)                                ↝⟨ inverse $ Eq.≃-≡ (S.Constant≃Constant-≃ univ) ⟩

      _≃_.to (S.Constant≃Constant-≃ univ) (c′ .property) ≡
      _≃_.to (S.Constant≃Constant-≃ univ)
        (_≃_.from (S.Constant≃Constant-≃ univ)
           (_≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c))                            ↝⟨ ≡⇒≃ $
                                                                                   cong (_≃_.to (S.Constant≃Constant-≃ univ) (c′ .property) ≡_) $
                                                                                   _≃_.right-inverse-of (S.Constant≃Constant-≃ univ) _ ⟩□
      _≃_.to (S.Constant≃Constant-≃ univ) (c′ .property) ≡
      _≃_.to Constantᴱ-⁻¹ᴱ-≃-Constant-≃-⁻¹ c                                    □)) ⟩

  (∃ λ (c : Constantᴱ (get ⁻¹ᴱ_)) →
   Erased
     (∃ λ (c′ : C.Coherently-constant (get ⁻¹_)) →
      c′ .property ≡ _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) c))     ↔⟨ (∃-cong λ _ →
                                                                              Erased-cong ∃-comm F.∘
                                                                              inverse Erased-Σ↔Σ F.∘
                                                                              Σ-cong (inverse $
                                                                                      (∀-cong ext λ _ → Erased-Π↔Π) F.∘
                                                                                      Erased-Π↔Π)
                                                                                     (λ _ → F.id)) F.∘
                                                                             inverse Σ-assoc F.∘
                                                                             Σ-cong (ΠΣ-comm F.∘
                                                                                     (∀-cong ext λ _ → ΠΣ-comm))
                                                                                    (λ _ → F.id) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased
     (∃ λ (c : C.Coherently-constant (get ⁻¹_)) →
      ∃ λ (eq : ∀ b₁ b₂ → Is-equivalence (get⁻¹ᴱ-const b₁ b₂)) →
      c .property ≡
      _≃_.to (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)
        (λ b₁ b₂ → get⁻¹ᴱ-const b₁ b₂ , [ eq b₁ b₂ ])))                   ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                              (from-bijection $ inverse $
                                                                               ΠΣ-comm F.∘
                                                                               ∀-cong ext λ _ →
                                                                               ΠΣ-comm F.∘
                                                                               ∀-cong ext λ _ →
                                                                               ×-comm) F.∘
                                                                              (∃-cong λ _ →
                                                                               (∀-cong ext λ _ → ∀-cong ext λ _ → from-bijection $ inverse $
                                                                                ≡-comm F.∘
                                                                                ignore-propositional-component
                                                                                  (H-level-Erased 1 (Eq.propositional ext _))) F.∘
                                                                               inverse
                                                                                 (Eq.extensionality-isomorphism bad-ext F.∘
                                                                                  (∀-cong ext λ _ → Eq.extensionality-isomorphism bad-ext)) F.∘
                                                                               (≡⇒≃ $ cong (_ ≡_) $
                                                                                _≃_.left-inverse-of (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ) _) F.∘
                                                                               (inverse $
                                                                                Eq.≃-≡ $ inverse $ Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)))) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹_)) →
   ∀ b₁ b₂ →
   get⁻¹ᴱ-const b₁ b₂ ≡
   proj₁ (_≃_.from (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)
            (c .property) b₁ b₂) ×
   Is-equivalence (get⁻¹ᴱ-const b₁ b₂)))                                  ↔⟨ (∃-cong λ get⁻¹ᴱ-const → Erased-cong (
                                                                              Σ-cong (≡⇒≃ $ cong C.Coherently-constant $ ⟨ext⟩ λ _ →
                                                                                      ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ) λ c →
                                                                              ∀-cong ext λ b₁ → ∀-cong ext λ b₂ → ×-cong₁ λ _ →
                                                                              ≡⇒≃ $ cong (get⁻¹ᴱ-const b₁ b₂ ≡_) (
      proj₁ (_≃_.from (Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl univ)
               (c .property) b₁ b₂)                                             ≡⟨ proj₁-from-Constantᴱ-⁻¹ᴱ-≃-Constant-⁻¹ bl ⟩

      ECP.⁻¹→⁻¹ᴱ ∘ subst id (c .property b₁ b₂) ∘ ECP.⁻¹ᴱ→⁻¹                    ≡⟨ sym $
                                                                                   cong₂ (λ f g → f ∘ subst id (c .property b₁ b₂) ∘ g)
                                                                                     (trans (⟨ext⟩ λ _ →
                                                                                             subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                                      cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ) _)
                                                                                     (trans (⟨ext⟩ λ _ →
                                                                                             subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                                      cong _≃_.from $ _≃_.right-inverse-of (≡≃≃ univ) _) ⟩
      subst id (≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ) ∘
      subst id (c .property b₁ b₂) ∘
      subst id (sym (≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ))                                      ≡⟨ (⟨ext⟩ λ _ →
                                                                                    trans (subst-subst _ _ _ _) $
                                                                                    subst-subst _ _ _ _) ⟩
      subst id
        (trans (sym (≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₁})))
           (trans (c .property b₁ b₂)
             (≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₂}))))                                 ≡⟨ sym $
                                                                                   cong (λ f → subst id
                                                                                                 (trans (sym (f b₁))
                                                                                                    (trans (c .property b₁ b₂) (f b₂)))) $
                                                                                   _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) _ ⟩
      subst id
        (trans (sym (cong (_$ b₁) $ ⟨ext⟩ λ _ → ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ))
           (trans (c .property b₁ b₂)
             (cong (_$ b₂) $ ⟨ext⟩ λ b₂ →
              ≃⇒≡ univ (ECP.⁻¹≃⁻¹ᴱ {y = b₂}))))                                 ≡⟨ cong (subst id) $
                                                                                   elim¹
                                                                                     (λ eq →
                                                                                        trans (sym (cong (_$ b₁) eq))
                                                                                          (trans (c .property b₁ b₂) (cong (_$ b₂) eq)) ≡
                                                                                        ≡⇒→ (cong C.Coherently-constant eq) c .property b₁ b₂)
                                                                                     (
          trans (sym (cong (_$ b₁) (refl _)))
            (trans (c .property b₁ b₂) (cong (_$ b₂) (refl (get ⁻¹_))))               ≡⟨ trans (cong (flip trans _) $
                                                                                                trans (cong sym $ cong-refl _) $
                                                                                                sym-refl) $
                                                                                         trans (trans-reflˡ _) $
                                                                                         trans (cong (trans _) $ cong-refl _) $
                                                                                         trans-reflʳ _ ⟩

          c .property b₁ b₂                                                           ≡⟨ cong (λ eq → _≃_.to eq c .property b₁ b₂) $ sym $
                                                                                         trans (cong ≡⇒≃ $ cong-refl C.Coherently-constant)
                                                                                         ≡⇒↝-refl ⟩∎
          ≡⇒→ (cong C.Coherently-constant (refl _)) c .property b₁ b₂                 ∎)
                                                                                     _ ⟩
      subst id (≡⇒→ (cong C.Coherently-constant $
                     ⟨ext⟩ λ _ → ≃⇒≡ univ ECP.⁻¹≃⁻¹ᴱ)
                  c .property b₁ b₂)                                            ∎))) ⟩

  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ →
   get⁻¹ᴱ-const b₁ b₂ ≡ subst id (c .property b₁ b₂) ×
   Is-equivalence (get⁻¹ᴱ-const b₁ b₂)))                                  ↔⟨ (∃-cong λ _ → Erased-cong (
                                                                              ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              drop-⊤-right λ eq →
                                                                              _⇔_.to contractible⇔↔⊤ $
                                                                              propositional⇒inhabited⇒contractible
                                                                                (Eq.propositional ext _)
                                                                                (Eq.respects-extensional-equality
                                                                                   (ext⁻¹ (sym eq))
                                                                                   (_≃_.is-equivalence $ Eq.subst-as-equivalence _ _)))) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ →
   get⁻¹ᴱ-const b₁ b₂ ≡ subst id (c .property b₁ b₂)))                    ↔⟨ (∃-cong λ get⁻¹ᴱ-const → Erased-cong (
                                                                              ∃-cong λ c → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                              ≡⇒≃ $ cong (get⁻¹ᴱ-const b₁ b₂ ≡_) (
      subst id (c .property b₁ b₂)                                              ≡⟨ cong (subst id) $ sym $
                                                                                   cong-from-∥∥ᴱ→≃-truncation-is-proposition bl univ′ ⟩
      subst id
        (cong (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
           (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣))                         ≡⟨ (⟨ext⟩ λ _ → sym $
                                                                                    subst-∘ _ _ _) ⟩∎
      subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
        (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣)                             ∎))) ⟩

  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹ᴱ_)) →
   ∀ b₁ b₂ →
   get⁻¹ᴱ-const b₁ b₂ ≡
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
     (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣)))                        ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                              Eq.extensionality-isomorphism bad-ext F.∘
                                                                              (∀-cong ext λ _ → Eq.extensionality-isomorphism bad-ext))) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹ᴱ_)) →
   get⁻¹ᴱ-const ≡
   λ b₁ b₂ →
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
     (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣)))                        ↔⟨ (∃-cong λ get⁻¹ᴱ-const → Erased-cong (
                                                                              ∃-cong λ c → ≡⇒≃ $ cong (get⁻¹ᴱ-const ≡_) $ sym $
                                                                              ⟨ext⟩ λ b₁ → ⟨ext⟩ λ b₂ →
                                                                              cong₂ (λ (f : get ⁻¹ᴱ b₂ → get ⁻¹ᴱ b₂)
                                                                                       (g : get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₁) →
                                                                                       f ∘
                                                                                       subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
                                                                                         (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣) ∘
                                                                                       g)
                                                                                (cong _≃_.to $
                                                                                 trans (cong ≡⇒≃ $ cong-refl (_$ b₂)) $
                                                                                 ≡⇒↝-refl)
                                                                                (cong _≃_.from $
                                                                                 trans (cong ≡⇒≃ $ cong-refl (_$ b₁)) $
                                                                                 ≡⇒↝-refl))) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   Erased (
   ∃ λ (c : C.Coherently-constant (get ⁻¹ᴱ_)) →
   get⁻¹ᴱ-const ≡
   λ b₁ b₂ →
   ≡⇒→ (cong (_$ b₂) (refl (get ⁻¹ᴱ_))) ∘
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (get ⁻¹ᴱ_ , [ c ]))
     (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣) ∘
   _≃_.from (≡⇒≃ (cong (_$ b₁) (refl (get ⁻¹ᴱ_))))))                      ↝⟨ (∃-cong λ get⁻¹ᴱ-const → inverse $
                                                                              EEq.drop-⊤-left-Σ-≃ᴱ-Erased
                                                                                (EEq.other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ ext univ)) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   ∃ λ ((P , get⁻¹ᴱ≃) :
        ∃ λ (P : B → Type (a ⊔ b)) → ∀ b₁ → get ⁻¹ᴱ b₁ ≃ᴱ P b₁) →
   Erased (
   ∃ λ (c : C.Coherently-constant P) →
   get⁻¹ᴱ-const ≡
   λ b₁ b₂ →
   _≃ᴱ_.from (get⁻¹ᴱ≃ b₂) ∘
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
     (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣) ∘
   _≃ᴱ_.to (get⁻¹ᴱ≃ b₁)))                                                 ↔⟨ (∃-cong λ _ →
                                                                              Σ-assoc F.∘
                                                                              (∃-cong λ _ → ∃-comm) F.∘
                                                                              inverse Σ-assoc F.∘
                                                                              (∃-cong λ _ → Erased-Σ↔Σ)) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   ∃ λ ((P , c) : ∃ λ (P : B → Type (a ⊔ b)) →
                  Erased (C.Coherently-constant P)) →
   ∃ λ (get⁻¹ᴱ≃ : ∀ b₁ → get ⁻¹ᴱ b₁ ≃ᴱ P b₁) →
   Erased (get⁻¹ᴱ-const ≡
           λ b₁ b₂ →
           _≃ᴱ_.from (get⁻¹ᴱ≃ b₂) ∘
           subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , c))
             (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣) ∘
           _≃ᴱ_.to (get⁻¹ᴱ≃ b₁)))                                         ↔⟨ (∃-cong λ _ →
                                                                              Σ-cong (inverse $ ∥∥ᴱ→≃ bl univ′) λ _ → Eq.id) ⟩
  (∃ λ (get⁻¹ᴱ-const : ∀ b₁ b₂ → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂) →
   ∃ λ (P : ∥ B ∥ᴱ → Type (a ⊔ b)) →
   ∃ λ (get⁻¹ᴱ≃ : ∀ b₁ → get ⁻¹ᴱ b₁ ≃ᴱ P ∣ b₁ ∣) →
   Erased (get⁻¹ᴱ-const ≡
           λ b₁ b₂ →
           _≃ᴱ_.from (get⁻¹ᴱ≃ b₂) ∘
           subst P (T.truncation-is-proposition ∣ b₁ ∣ ∣ b₂ ∣) ∘
           _≃ᴱ_.to (get⁻¹ᴱ≃ b₁)))                                         ↔⟨⟩

  V.Coherently-constant′ (get ⁻¹ᴱ_)                                       ↝⟨ inverse V.Coherently-constant≃ᴱCoherently-constant′ ⟩□

  V.Coherently-constant (get ⁻¹ᴱ_)                                        □

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

    -- The get-set law.

    @0 get-set : (a : A) (b : B) → get (set a b) ≡ b

  -- In erased contexts one can convert from any "preimage" of the
  -- getter to any other.

  @0 get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂
  get⁻¹-const = λ b₁ b₂ (a , _) → set a b₂ , get-set a b₂

  field

    -- The function get⁻¹-const b₁ b₂ is an equivalence (in erased
    -- contexts).

    @0 get⁻¹-const-equivalence :
      (b₁ b₂ : B) → Is-equivalence (get⁻¹-const b₁ b₂)

  -- The family get ⁻¹_ is constant (in erased contexts).

  @0 get⁻¹-constant : S.Constant-≃ (get ⁻¹_)
  get⁻¹-constant =
    _≃_.from (S.Constant-≃-get-⁻¹-≃ ⊠)
      (set , get-set , get⁻¹-const-equivalence)

  field

    -- The family get ⁻¹_ is coherently constant (in erased contexts).

    @0 get⁻¹-coherently-constant : S.Coherently-constant univ (get ⁻¹_)

    -- The first "level" of get⁻¹-coherently-constant is equal to
    -- get⁻¹-constant (in erased contexts).

    @0 get⁻¹-coherently-constant-property≡get⁻¹-constant :
      get⁻¹-coherently-constant .property ≡ get⁻¹-constant

  -- The family of fibres of the getter is coherently constant.

  coherently-constant-fibres-get : Coherently-constant-fibres univ get
  coherently-constant-fibres-get =
      set
    , [ ( get-set
        , get⁻¹-const-equivalence
        , get⁻¹-coherently-constant
        , ⊠
        , get⁻¹-coherently-constant-property≡get⁻¹-constant
        )
      ]

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
    (λ { (_ , _ , [ (_ , _ , _ , ⊠ , _)]) → _ })
    (λ { (_ , _ , [ (_ , _ , _ , ⊠ , _)]) → refl _ })
    refl

-- Lens univ A B is equivalent to V.Lens A B (with erased proofs,
-- assuming univalence).

Lens≃ᴱLens :
  Block "Lens≃ᴱLens" →
  {A : Type a} {B : Type b} →
  @0 Univalence (lsuc (a ⊔ b)) →
  (@0 univ : Univalence (a ⊔ b)) →
  Lens univ A B ≃ᴱ V.Lens A B
Lens≃ᴱLens ⊠ {A = A} {B = B} univ′ univ =
  Lens univ A B                                              ↔⟨ Lens-as-Σ ⟩
  (∃ λ (get : A → B) → Coherently-constant-fibres univ get)  ↝⟨ (∃-cong λ _ →
                                                                 Coherently-constant-fibres≃ᴱCoherently-constant-⁻¹ᴱ univ′ univ) ⟩□
  (∃ λ (get : A → B) → V.Coherently-constant (get ⁻¹ᴱ_))     □

-- The right-to-left direction of the equivalence preserves getters
-- and setters.

from-Lens≃ᴱLens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱLens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-→ A B
    (_≃ᴱ_.from (Lens≃ᴱLens bl univ′ univ))
from-Lens≃ᴱLens-preserves-getters-and-setters ⊠ univ′ univ l =
    refl _
  , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
    proj₁
      (subst (λ _ → get ⁻¹ᴱ b) (refl tt)
         (get⁻¹ᴱ-const (get a) b (a , [ refl (get a) ])))  ≡⟨ cong proj₁ $ subst-refl _ _ ⟩∎

    proj₁ (get⁻¹ᴱ-const (get a) b (a , [ refl (get a) ]))  ∎
  where
  open V.Lens l

-- In erased contexts the equivalence preserves getters and setters.
--
-- I do not know if this result can be proved in non-erased contexts
-- (with erased proofs of univalence).

@0 Lens≃ᴱLens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱLens")
  {A : Type a} {B : Type b}
  (univ′ : Univalence (lsuc (a ⊔ b)))
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱLens bl univ′ univ))
Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ =
  Preserves-getters-and-setters-⇔-inverse
    {f = _≃ᴱ_.logical-equivalence
           (inverse $ Lens≃ᴱLens bl univ′ univ)} $
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (EEq.≃ᴱ→≃ $ inverse $ Lens≃ᴱLens bl univ′ univ))
    (from-Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ)
