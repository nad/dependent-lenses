------------------------------------------------------------------------
-- Some alternative formulations of non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lens.Non-dependent.Alternative where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_; module _≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
import Nat equality-with-J as Nat
open import Preimage equality-with-J
open import Surjection equality-with-J using (_↠_; module _↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent
import Lens.Non-dependent.Traditional as Traditional

------------------------------------------------------------------------
-- Alternative formulations of lenses

-- Paolo Capriotti has described higher lenses
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Higher-lens : ∀ {a b} → Set a → Set b → Set (lsuc (a ⊔ b))
Higher-lens {a} {b} A B =
  ∃ λ (g : A → B) →
  ∃ λ (H : Pow a ∥ B ∥) →
    (g ⁻¹_) ≡ H ⊚ ∣_∣

-- A more traditional (?) alternative definition that uses a
-- bijection.

Bijection-lens : ∀ {a b} → Set a → Set b → Set (lsuc (a ⊔ b))
Bijection-lens {a} {b} A B =
  ∃ λ (R : Set (a ⊔ b)) → A ↔ (R × B)

-- However, the definition above is not in general isomorphic to
-- Higher-lens A B or Traditional.Lens A B, not even if A and B are
-- sets (consider the case in which A and B are empty; see
-- ¬Iso-lens↠Bijection-lens below). The following variant of the
-- definition solves this problem.
--
-- (I had previously considered some other variants, when Andrea
-- Vezzosi suggested that I should look at higher lenses, and that I
-- could perhaps use R → ∥ B ∥. This worked out nicely.)

Iso-lens : ∀ {a b} → Set a → Set b → Set (lsuc (a ⊔ b))
Iso-lens {a} {b} A B =
  ∃ λ (R : Set (a ⊔ b)) →
    (A ≃ (R × B)) ×
    (R → ∥ B ∥)

-- Yet another alternative definition of lenses. This one replaces the
-- R → ∥ B ∥ function with a requirement that the remainder function
-- should be surjective.

Iso-lens′ : ∀ {a b} → Set a → Set b → Set (lsuc (a ⊔ b))
Iso-lens′ {a} {b} A B =
  ∃ λ (get       : A → B) →
  ∃ λ (R         : Set (a ⊔ b)) →
  ∃ λ (remainder : A → R) →
    Eq.Is-equivalence (λ a → remainder a , get a) ×
    Surjective remainder

------------------------------------------------------------------------
-- Simple definitions related to Iso-lenses

-- Some derived definitions.

module Iso-lens {a b} {A : Set a} {B : Set b} (l : Iso-lens A B) where

  -- Remainder type.

  R : Set (a ⊔ b)
  R = proj₁ l

  -- Equivalence.

  equiv : A ≃ (R × B)
  equiv = proj₁ (proj₂ l)

  -- The proof of (mere) inhabitance.

  inhabited : R → ∥ B ∥
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

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

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

  -- Another law.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b =
    proj₁ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of equiv _ ⟩∎
    remainder a                                              ∎

  -- Traditional lens.

  traditional-lens : Traditional.Lens A B
  traditional-lens = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }

-- Isomorphisms can be converted into lenses.

isomorphism-to-lens :
  ∀ {a b} {A : Set a} {B : Set b} {R : Set (a ⊔ b)} →
  A ↔ R × B → Iso-lens A B
isomorphism-to-lens {A = A} {B} {R} iso =

  (R × ∥ B ∥) ,

  (A                ↔⟨ iso ⟩
   R × B            ↔⟨ F.id ×-cong inverse ∥∥×↔ ⟩
   R × ∥ B ∥ × B    ↔⟨ ×-assoc ⟩□
   (R × ∥ B ∥) × B  □) ,

  proj₂

------------------------------------------------------------------------
-- Equality characterisations for Iso-lenses

-- Equality of Iso-lenses is isomorphic to certain pairs.

equality-characterisation₀ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B} {l₁} {l₂} =
  l₁ ≡ l₂                                                    ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B) × (R → ∥ B ∥)) p (proj₂ l₁) ≡
     proj₂ l₂)                                               ↝⟨ (∃-cong λ _ → inverse $
                                                                   ignore-propositional-component
                                                                     (Π-closure ext 1 λ _ →
                                                                      truncation-is-proposition)) ⟩
  (∃ λ (p : R l₁ ≡ R l₂) →
     proj₁ (subst (λ R → A ≃ (R × B) × (R → ∥ B ∥))
                  p
                  (proj₂ l₁)) ≡
     equiv l₂)                                               ↝⟨ (∃-cong λ p → ≡⇒↝ _ $
                                                                   cong (λ x → proj₁ x ≡ _) (push-subst-, {y≡z = p} _ _)) ⟩□
  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)      □
  where
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₁ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂
equality-characterisation₁ {A = A} {B} {l₁} {l₂} univ =
  l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₀ ⟩

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
-- univalence).

equality-characterisation₂ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
          _≃_.to (equiv l₂) x
equality-characterisation₂ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                             ↝⟨ equality-characterisation₁ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)        ↝⟨ (∃-cong λ _ → inverse $ ≃-to-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                       □
  where
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain triples (assuming
-- univalence).

equality-characterisation₃ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₃ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                                 ↝⟨ equality-characterisation₂ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                           ↔⟨ (∃-cong λ _ → Eq.∀-preserves ext λ _ → Eq.↔⇒≃ $ inverse ≡×≡↔≡) ⟩

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
-- univalence).

equality-characterisation₄ :
  ∀ {a b} {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃_.from (equiv l₂) p
equality-characterisation₄ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)                      ↝⟨ (∃-cong λ _ → inverse $ ≃-from-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃_.from (equiv l₂) p)                                   □
  where
  open Iso-lens

------------------------------------------------------------------------
-- More lens equalities

-- If two lenses have equal setters, then they also have equal
-- getters.

getters-equal-if-setters-equal :
  let open Iso-lens in
  ∀ {a b} {A : Set a} {B : Set b} →
  (l₁ l₂ : Iso-lens A B) →
  (∀ a b → set l₁ a b ≡ set l₂ a b) →
  (∀ a   → get l₁ a   ≡ get l₂ a)
getters-equal-if-setters-equal l₁ l₂ setters-equal a =
  get l₁ a                           ≡⟨⟩
  proj₂ (to (equiv l₁) a)            ≡⟨ cong proj₂ $ from-to (equiv l₁) lemma ⟩
  proj₂ (remainder l₁ a , get l₂ a)  ≡⟨ refl ⟩∎
  get l₂ a                           ∎
  where
  open Iso-lens
  open _≃_

  lemma =
    from (equiv l₁) (remainder l₁ a , get l₂ a)  ≡⟨⟩
    set l₁ a (get l₂ a)                          ≡⟨ setters-equal _ _ ⟩
    set l₂ a (get l₂ a)                          ≡⟨ set-get l₂ _ ⟩∎
    a                                            ∎

-- Let us assume that two lenses have a codomain type that is
-- inhabited whenever it is merely inhabited. In that case the lenses
-- are equal if their setters are equal (assuming univalence).

lenses-equal-if-setters-equal :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (∥ B ∥ → B) →
  (l₁ l₂ : Iso-lens A B) →
  (∀ a b → Iso-lens.set l₁ a b ≡ Iso-lens.set l₂ a b) →
  l₁ ≡ l₂
lenses-equal-if-setters-equal {A = A} {B = B}
                              univ ∥B∥→B l₁ l₂ setters-equal =
  _↔_.from (equality-characterisation₃ univ)
    ( R≃R
    , (λ a →
         remainder l₂ (set l₁ a _)  ≡⟨ cong (remainder l₂) $ setters-equal _ _ ⟩
         remainder l₂ (set l₂ a _)  ≡⟨ remainder-set l₂ _ _ ⟩∎
         remainder l₂ a             ∎)
    , getters-equal-if-setters-equal l₁ l₂ setters-equal
    )
  where
  open Iso-lens
  open _≃_

  BR≃BR =
    B × R l₁  ↔⟨ ×-comm ⟩
    R l₁ × B  ↝⟨ inverse (equiv l₁) ⟩
    A         ↝⟨ equiv l₂ ⟩
    R l₂ × B  ↔⟨ ×-comm ⟩□
    B × R l₂  □

  f : R l₁ → R l₂
  f r = remainder l₂ (from (equiv l₁) (r , ∥B∥→B (inhabited l₁ r)))

  id-f≃ : Eq.Is-equivalence (Σ-map P.id f)
  id-f≃ = Eq.respects-extensional-equality
    (λ { (b , r) → cong (uncurry λ x y → (y , x)) (
         let b′ = ∥B∥→B (inhabited l₁ r) in

         to (equiv l₂) (from (equiv l₁) (r , b))                    ≡⟨ cong (λ p → to (equiv l₂) (from (equiv l₁) (proj₁ p , b))) $
                                                                         sym $ right-inverse-of (equiv l₁) _ ⟩
         to (equiv l₂) (from (equiv l₁)
           (proj₁ (to (equiv l₁) (from (equiv l₁) (r , b′))) , b))  ≡⟨⟩

         to (equiv l₂) (set l₁ (from (equiv l₁) (r , b′)) b)        ≡⟨ cong (to (equiv l₂)) $ setters-equal _ _ ⟩

         to (equiv l₂) (set l₂ (from (equiv l₁) (r , b′)) b)        ≡⟨⟩

         to (equiv l₂)
            (from (equiv l₂)
                  (remainder l₂ (from (equiv l₁) (r , b′)) , b))    ≡⟨ right-inverse-of (equiv l₂) _ ⟩∎

         (remainder l₂ (from (equiv l₁) (r , b′)) , b)              ∎) })
    (is-equivalence BR≃BR)

  f≃ : Eq.Is-equivalence f
  f≃ r = Eq.drop-Σ-map-id _ id-f≃ (∥B∥→B (inhabited l₂ r)) r

  R≃R : R l₁ ≃ R l₂
  R≃R = Eq.⟨ f , f≃ ⟩

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Iso-lens preserves bijections.

Iso-lens′-cong :
  ∀ {r}
    {a₁ b₁} {A₁ : Set a₁} {B₁ : Set b₁}
    {a₂ b₂} {A₂ : Set a₂} {B₂ : Set b₂} →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  (∃ λ (R : Set r) → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥)) ↔
  (∃ λ (R : Set r) → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))
Iso-lens′-cong A₁↔A₂ B₁↔B₂ =
  ∃-cong λ _ →
  Eq.≃-preserves-bijections ext A₁↔A₂ (F.id ×-cong B₁↔B₂)
    ×-cong
  →-cong ext F.id (∥∥-cong B₁↔B₂)

-- Iso-lens preserves level-preserving bijections.

Iso-lens-cong :
  ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  Iso-lens A₁ B₁ ↔ Iso-lens A₂ B₂
Iso-lens-cong = Iso-lens′-cong

-- If B is a proposition, then Iso-lens A B is isomorphic to A → B
-- (assuming univalence).

lens-to-proposition↔get :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Iso-lens A B ↔ (A → B)
lens-to-proposition↔get {b = b} {A} {B} univ B-prop =
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥))  ↔⟨ (∃-cong λ _ →
                                           ∃-cong λ _ →
                                           Eq.∀-preserves ext λ _ →
                                             Eq.↔⇒≃ $ ∥∥↔ B-prop) ⟩
  (∃ λ R → A ≃ (R × B) × (R → B))      ↝⟨ (∃-cong λ _ →
                                           ×-cong₁ λ R→B →
                                           Eq.≃-preserves-bijections ext F.id $
                                             drop-⊤-right λ r →
                                               inverse $ _⇔_.to contractible⇔⊤↔ $
                                                 propositional⇒inhabited⇒contractible B-prop (R→B r)) ⟩
  (∃ λ R → A ≃ R × (R → B))            ↔⟨ (∃-cong λ _ →
                                           ∃-cong λ A≃R →
                                           →-cong ext {k = equivalence} (inverse A≃R) F.id) ⟩
  (∃ λ R → A ≃ R × (A → B))            ↝⟨ Σ-assoc ⟩
  (∃ λ R → A ≃ R) × (A → B)            ↝⟨ (drop-⊤-left-× λ _ → other-singleton-with-≃-↔-⊤ {b = b} ext univ) ⟩□
  (A → B)                              □

-- If B is contractible, then Iso-lens A B is isomorphic to ⊤
-- (assuming univalence).

lens-to-contractible↔⊤ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B →
  Iso-lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} univ cB =
  Iso-lens A B  ↝⟨ lens-to-proposition↔get univ (mono₁ 0 cB) ⟩
  (A → B)       ↝⟨ →-cong ext F.id $ inverse $ _⇔_.to contractible⇔⊤↔ cB ⟩
  (A → ⊤)       ↝⟨ →-right-zero ⟩□
  ⊤             □

-- Iso-lens A ⊥ is isomorphic to ¬ A (assuming univalence).

lens-to-⊥↔¬ :
  ∀ {a b} {A : Set a} →
  Univalence (a ⊔ b) →
  Iso-lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔¬ {A = A} univ =
  Iso-lens A ⊥  ↝⟨ lens-to-proposition↔get univ ⊥-propositional ⟩
  (A → ⊥)       ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A           □

-- If A is contractible, then Iso-lens A B is isomorphic to
-- Contractible B (assuming univalence).

lens-from-contractible↔codomain-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible A →
  Iso-lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible {A = A} {B} univ cA =
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥))                        ↝⟨ inverse $
                                                                ∃-cong (λ _ →
                                                                  Eq.≃-preserves-bijections ext (_⇔_.to contractible⇔⊤↔ cA) F.id
                                                                    ×-cong
                                                                  F.id) ⟩
  (∃ λ R → ⊤ ≃ (R × B) × (R → ∥ B ∥))                        ↝⟨ ∃-cong (λ _ → inverse (contractible↔⊤≃ ext) ×-cong F.id) ⟩
  (∃ λ R → Contractible (R × B) × (R → ∥ B ∥))               ↔⟨ ∃-cong (λ _ → Contractible-commutes-with-× ext ×-cong F.id) ⟩
  (∃ λ R → (Contractible R × Contractible B) × (R → ∥ B ∥))  ↝⟨ ∃-cong (λ _ → inverse ×-assoc) ⟩
  (∃ λ R → Contractible R × Contractible B × (R → ∥ B ∥))    ↝⟨ inverse $
                                                                ∃-cong (λ _ → ∃-cong λ cR →
                                                                  F.id
                                                                    ×-cong
                                                                  →-cong ext (_⇔_.to contractible⇔⊤↔ cR) F.id) ⟩
  (∃ λ R → Contractible R × Contractible B × (⊤ → ∥ B ∥))    ↝⟨ ∃-cong (λ _ → F.id ×-cong F.id ×-cong Π-left-identity) ⟩
  (∃ λ R → Contractible R × Contractible B × ∥ B ∥)          ↝⟨ ∃-cong (λ _ → ×-comm) ⟩
  (∃ λ R → (Contractible B × ∥ B ∥) × Contractible R)        ↝⟨ ∃-comm ⟩
  (Contractible B × ∥ B ∥) × (∃ λ R → Contractible R)        ↝⟨ drop-⊤-right (λ _ → ∃Contractible↔⊤ ext univ) ⟩
  Contractible B × ∥ B ∥                                     ↝⟨ drop-⊤-right (λ cB → inhabited⇒∥∥↔⊤ ∣ proj₁ cB ∣) ⟩□
  Contractible B                                             □

-- Iso-lens ⊥ B is isomorphic to the unit type (assuming univalence).

lens-from-⊥↔⊤ :
  ∀ {a b} {B : Set b} →
  Univalence (a ⊔ b) →
  Iso-lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ {B = B} univ =
  inverse $ _⇔_.to contractible⇔⊤↔ $
    isomorphism-to-lens
      (⊥      ↝⟨ inverse ×-left-zero ⟩□
       ⊥ × B  □) ,
    λ l → _↔_.from (equality-characterisation₂ univ)
            ( (⊥ × ∥ B ∥  ↔⟨ ×-left-zero ⟩
               ⊥₀         ↔⟨ lemma l ⟩□
               R l        □)
            , λ x → ⊥-elim x
            )
  where
  open Iso-lens

  lemma : (l : Iso-lens ⊥ B) → ⊥₀ ↔ R l
  lemma l = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⊥-elim
        ; from = whatever
        }
      ; right-inverse-of = whatever
      }
    ; left-inverse-of = λ x → ⊥-elim x
    }
    where
    whatever : ∀ {ℓ} {Whatever : R l → Set ℓ} → (r : R l) → Whatever r
    whatever r = ⊥-elim {ℓ = lzero} $
      rec ⊥-propositional
          (λ b → ⊥-elim (_≃_.from (equiv l) (r , b)))
          (inhabited l r)

-- Bijection-lens ⊥ ⊥ is isomorphic to Set something.

Bijection-lens-⊥-⊥↔Set :
  ∀ {a b} →
  Bijection-lens (⊥ {ℓ = a}) (⊥ {ℓ = b}) ↔ Set (a ⊔ b)
Bijection-lens-⊥-⊥↔Set =
  Bijection-lens ⊥ ⊥     ↔⟨ (∃-cong λ _ → Eq.↔↔≃ ext (mono₁ 1 ⊥-propositional)) ⟩
  (∃ λ R → ⊥ ≃ (R × ⊥))  ↔⟨ (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id ×-right-zero) ⟩
  (∃ λ R → ⊥ ≃ ⊥₀)       ↔⟨ (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ R → ¬ ⊥)          ↔⟨ drop-⊤-right (λ _ → ¬⊥↔⊤ ext) ⟩□
  Set _                  □

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- Higher-lens A B is isomorphic to Iso-lens A B (assuming
-- univalence).
--
-- (This proof was simplified following a suggestion by Paolo
-- Capriotti.)

Higher-lens↔Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Higher-lens A B ↔ Iso-lens A B
Higher-lens↔Iso-lens {a} {b} {A} {B} univ =

  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) →
     (g ⁻¹_) ≡ H ⊚ ∣_∣)                                            ↔⟨ Σ-cong lemma₂ (λ _ → ∃-cong (lemma₃ _)) ⟩

  (∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
   ∃ λ (H : Pow a ∥ B ∥) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ ∃-comm ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      A ≃ ∃ P × P ≡ H ⊚ ∣_∣)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ P)                                       ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq →
                                                                       Eq.≃-preserves ext F.id (∃-cong λ x → ≡⇒↝ _ (cong (_$ x) eq))) ⟩
  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ (H ⊚ ∣_∣))                               ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   (∃ λ (P : Pow a B) → P ≡ H ⊚ ∣_∣) ×
   A ≃ ∃ (H ⊚ ∣_∣))                                                ↝⟨ (∃-cong λ _ →
                                                                       drop-⊤-left-× λ _ →
                                                                       inverse (_⇔_.to contractible⇔⊤↔ (singleton-contractible _))) ⟩

  (∃ λ (H : Pow a ∥ B ∥) → A ≃ ∃ (H ⊚ ∣_∣))                        ↔⟨ inverse $
                                                                      Σ-cong (inverse $ Pow↔Fam a ext univ) (λ _ →
                                                                      Eq.≃-preserves ext F.id F.id) ⟩

  (∃ λ (H : Fam a ∥ B ∥) → A ≃ ∃ ((proj₂ H ⁻¹_) ⊚ ∣_∣))            ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set ℓ) →
   ∃ λ (f : R → ∥ B ∥) → A ≃ ∃ ((f ⁻¹_) ⊚ ∣_∣))                    ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                                       Eq.≃-preserves ext F.id
                            (∃ ((f ⁻¹_) ⊚ ∣_∣)                           ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                               inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                                 truncation-is-proposition _ _) ⟩
                             B × R                                       ↔⟨ ×-comm ⟩□
                             R × B                                       □)) ⟩

  (∃ λ (R : Set ℓ) → (R → ∥ B ∥) × (A ≃ (R × B)))                  ↝⟨ (∃-cong λ _ → ×-comm) ⟩□

  (∃ λ (R : Set ℓ) → (A ≃ (R × B)) × (R → ∥ B ∥))                  □

  where
  ℓ = a ⊔ b

  lemma₁ : ∀ (g : A → B) b →
           g ⁻¹ b ↔ (g ⊚ lower {ℓ = ℓ}) ⁻¹ b
  lemma₁ g b = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ { (a , ga≡b) → lift a , ga≡b }
        ; from = λ { (lift a , ga≡b) → a , ga≡b }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  abstract

    lemma₂ : (A → B) ↔ ∃ λ (P : Pow a B) → A ≃ ∃ P
    lemma₂ = →↔Σ≃Σ ℓ ext univ

    lemma₃ :
      (g : A → B) (H : Pow a ∥ B ∥) →
      ((g ⁻¹_) ≡ H ⊚ ∣_∣)
        ≃
      (proj₁ (_↔_.to lemma₂ g) ≡ H ⊚ ∣_∣)
    lemma₃ g H =
      (g ⁻¹_) ≡ H ⊚ ∣_∣                   ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (∀ b → g ⁻¹ b ≡ H ∣ b ∣)            ↝⟨ Eq.∀-preserves ext (λ _ →
                                               ≡-preserves-≃ ext univ univ
                                                 (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ⊚ lower) ⁻¹ b ≡ H ∣ b ∣)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
      ((g ⊚ lower) ⁻¹_) ≡ H ⊚ ∣_∣         □

-- Iso-lens A B is isomorphic to Iso-lens′ A B.

Iso-lens↔Iso-lens′ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Iso-lens A B ↔ Iso-lens′ A B
Iso-lens↔Iso-lens′ {A = A} {B} =

  (∃ λ (R : Set _) →
     (A ≃ (R × B)) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Eq.≃-as-Σ ×-cong F.id) ⟩

  (∃ λ (R : Set _) →
     (∃ λ (f : A → R × B) → Eq.Is-equivalence f) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (f : A → R × B) →
     Eq.Is-equivalence f ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ → F.id) ⟩

  (∃ λ (R  : Set _) →
   ∃ λ (rg : (A → R) × (A → B)) →
     Eq.Is-equivalence (λ a → proj₁ rg a , proj₂ rg a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
   ∃ λ (get       : A → B) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (get       : A → B) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ ∃-comm ⟩

  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↔⟨ (∃-cong λ get → ∃-cong λ R → ∃-cong λ rem → ∃-cong λ eq →
                                                              Eq.∀-preserves ext λ _ → Eq.↔⇒≃ $ ∥∥-cong $
                                                              lemma get R rem eq _) ⟩□
  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     Surjective remainder)                                □

  where
  lemma = λ _ _ remainder eq r →
    B                            ↝⟨ (inverse $ drop-⊤-right λ _ →
                                     inverse $ _⇔_.to contractible⇔⊤↔ $
                                     singleton-contractible _) ⟩
    B × Singleton r              ↝⟨ Σ-assoc ⟩
    (∃ λ { (_ , r′) → r′ ≡ r })  ↝⟨ (Σ-cong ×-comm λ _ → F.id) ⟩
    (∃ λ { (r′ , _) → r′ ≡ r })  ↝⟨ (inverse $ Σ-cong Eq.⟨ _ , eq ⟩ λ _ → F.id) ⟩□
    (∃ λ a → remainder a ≡ r)    □

-- There is a split surjection from Bijections-lens A B to
-- Iso-lens A B (assuming univalence).

Bijection-lens↠Iso-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Bijection-lens A B ↠ Iso-lens A B
Bijection-lens↠Iso-lens {A = A} {B} univ = record
  { logical-equivalence = record
    { to   = λ { (R , A↔R×B) → isomorphism-to-lens A↔R×B }
    ; from = λ { (R , A≃R×B , _) → R , _≃_.bijection A≃R×B }
    }
  ; right-inverse-of = λ { (R , A≃R×B , inh) →
      _↔_.from (equality-characterisation₂ univ)
        ( (R × ∥ B ∥  ↔⟨ drop-⊤-right (λ r → inhabited⇒∥∥↔⊤ (inh r)) ⟩□
           R          □)
        , λ _ → refl
        ) }
  }

-- However, there is in general no split surjection in the other
-- direction, not even for sets (assuming univalence).

¬Iso-lens↠Bijection-lens :
  ∀ {a b} →
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Is-set A → Is-set B →
     Iso-lens A B ↠ Bijection-lens A B)
¬Iso-lens↠Bijection-lens univ surj =
  ⊥-elim (subst F.id ⊤≡⊥ _)
  where
  ⊥-is-set : ∀ {ℓ} → Is-set (⊥ {ℓ = ℓ})
  ⊥-is-set = mono₁ 1 ⊥-propositional

  ⊤↠Set =
    ⊤                   ↔⟨ inverse $ lens-from-⊥↔⊤ univ ⟩
    Iso-lens ⊥ ⊥        ↝⟨ surj ⊥-is-set ⊥-is-set ⟩
    Bijection-lens ⊥ ⊥  ↔⟨ Bijection-lens-⊥-⊥↔Set ⟩□
    Set _               □

  ⊤≡⊥ : ↑ _ ⊤ ≡ ⊥
  ⊤≡⊥ =
    ↑ _ ⊤              ≡⟨ sym $ right-inverse-of _ ⟩
    to (from (↑ _ ⊤))  ≡⟨⟩
    to (from ⊥)        ≡⟨ right-inverse-of _ ⟩∎
    ⊥                  ∎
    where
    open _↠_ ⊤↠Set

-- In general there is no split surjection from Iso-lens A B to
-- Traditional.Lens A B (assuming univalence).

¬Iso-lens↠Traditional-lens :
  Univalence (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set₁) →
    ¬ (Iso-lens A ⊤ ↠ Traditional.Lens A ⊤)
¬Iso-lens↠Traditional-lens univ₁ univ₀ =
  let A = _ in

  A ,
  (λ surj →                               $⟨ _⇔_.from contractible⇔⊤↔ (inverse $ lens-to-contractible↔⊤ univ₁ ⊤-contractible) ⟩
     Contractible (Iso-lens A ⊤)          ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (Traditional.Lens A ⊤)  ↝⟨ H-level.respects-surjection (_↔_.surjection $ Traditional.lens-to-⊤↔) 0 ⟩
     Contractible ((a : A) → a ≡ a)       ↝⟨ mono₁ 0 ⟩
     Is-proposition ((a : A) → a ≡ a)     ↝⟨ proj₂ $ ¬-type-of-refl-propositional ext univ₀ ⟩□
     ⊥                                    □)

-- If the domain A is a set, then there is a split surjection from
-- Iso-lens A B to Traditional.Lens A B.

Iso-lens↠Traditional-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Is-set A →
  Iso-lens A B ↠ Traditional.Lens A B
Iso-lens↠Traditional-lens {A = A} {B} A-set = record
  { logical-equivalence = record
    { to   = Iso-lens.traditional-lens
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  from : Traditional.Lens A B → Iso-lens A B
  from l = isomorphism-to-lens
    {R = ∃ λ (f : B → A) → ∀ b b′ → set (f b) b′ ≡ f b′}
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
                  (Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   A-set _ _)
                  _ _

              lemma =
                get (f b)          ≡⟨ cong get (sym (h b b)) ⟩
                get (set (f b) b)  ≡⟨ get-set (f b) b ⟩∎
                b                  ∎
            in
            (set (f b) , set-set (f b)) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ (ext (h b)) irr) lemma ⟩∎
            (f         , h            ) , b          ∎ }
         }
       ; left-inverse-of = λ a →
           set a (get a)  ≡⟨ set-get a ⟩∎
           a              ∎
       })
    where
    open Traditional.Lens l

  to∘from : ∀ l → Iso-lens.traditional-lens (from l) ≡ l
  to∘from l = _↔_.from Traditional.equality-characterisation
    ( refl
    , refl
    , (λ a _ →
         _⇔_.to propositional⇔irrelevant
           (B-set a _ _)
           _ _)
    , (λ _ →
         _⇔_.to propositional⇔irrelevant
           (A-set _ _)
           _ _)
    , (λ _ _ _ →
         _⇔_.to propositional⇔irrelevant
           (A-set _ _)
              _ _)
    )
    where
    open Traditional.Lens l

    B-set : A → Is-set B
    B-set a =
      Traditional.h-level-respects-lens-from-inhabited l a A-set

-- If the domain A is a set, then Traditional.Lens A B and
-- Iso-lens A B are isomorphic (assuming univalence).

Iso-lens↔Traditional-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-set A →
  Iso-lens A B ↔ Traditional.Lens A B
Iso-lens↔Traditional-lens {A = A} {B} univ A-set = record
  { surjection      = surj
  ; left-inverse-of = from∘to
  }
  where
  surj = Iso-lens↠Traditional-lens A-set

  open Traditional.Lens
  open _↠_ surj

  from∘to : ∀ l → from (Iso-lens.traditional-lens l) ≡ l
  from∘to (R , l , inh) =
    _↔_.from (equality-characterisation₄ univ)
             (lemma , λ _ → refl)
    where
    B-set : (B → R) → ∥ B ∥ → Is-set B
    B-set f =
      rec (H-level-propositional ext 2)
          (λ b → proj₂-closure (f b) 2 $
                 H-level.respects-surjection (_≃_.surjection l) 2 A-set)

    R-set : ∥ B ∥ → Is-set R
    R-set =
      rec (H-level-propositional ext 2)
          (λ b → proj₁-closure (const b) 2 $
                 H-level.respects-surjection (_≃_.surjection l) 2 A-set)

    lemma′ : (∥ B ∥ × (∥ B ∥ → R)) ↔ R
    lemma′ = record
      { surjection = record
        { logical-equivalence = record
          { to   = λ { (∥b∥ , f) → f ∥b∥ }
          ; from = λ r → inh r , λ _ → r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (∥b∥ , f) →
          curry (_↔_.to ≡×≡↔≡)
            (_⇔_.to propositional⇔irrelevant
               truncation-is-proposition _ _)
            (ext λ ∥b∥′ →
               f ∥b∥           ≡⟨ cong f (_⇔_.to propositional⇔irrelevant
                                            truncation-is-proposition _ _) ⟩∎
               f ∥b∥′          ∎) }
      }

    lemma =
      (∃ λ (f : B → A) → ∀ b b′ →
           _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′) ×
      ∥ B ∥                                                       ↔⟨ ×-comm ⟩

      (∥ B ∥ ×
       ∃ λ (f : B → A) → ∀ b b′ →
           _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′)       ↝⟨ (∃-cong λ _ →
                                                                      Σ-cong (→-cong ext F.id l) λ f →
                                                                             Eq.∀-preserves ext λ b →
                                                                             Eq.∀-preserves ext λ b′ →
                                                                             ≡⇒↝ _ (cong (_≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡_)
                                                                                         (sym $ _≃_.left-inverse-of l _))) ⟩
      (∥ B ∥ ×
       ∃ λ (f : B → R × B) → ∀ b b′ →
           _≃_.from l (proj₁ (f b) , b′) ≡ _≃_.from l (f b′))     ↝⟨ ∃-cong (λ _ → ∃-cong λ _ →
                                                                       Eq.Π-preserves ext F.id λ _ →
                                                                       Eq.Π-preserves ext F.id λ _ →
                                                                       Eq.≃-≡ (inverse l)) ⟩
      (∥ B ∥ ×
       ∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)  ↝⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ →
                                                                        Eq.Π-preserves ext F.id λ _ →
                                                                        Eq.Π-preserves ext F.id λ _ →
                                                                        inverse $ Eq.↔⇒≃ ≡×≡↔≡) ⟩
      (∥ B ∥ ×
       ∃ λ (p : (B → R) × (B → B)) →
         ∀ b b′ → proj₁ p b ≡ proj₁ p b′ × b′ ≡ proj₂ p b′)       ↔⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

      (∥ B ∥ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         ∀ b b′ → f b ≡ f b′ × b′ ≡ g b′)                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                        Eq.Π-preserves ext F.id λ _ →
                                                                        Eq.↔⇒≃ ΠΣ-comm) ⟩
      (∥ B ∥ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         ∀ b → (∀ b′ → f b ≡ f b′) × (∀ b′ → b′ ≡ g b′))          ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ΠΣ-comm) ⟩

      (∥ B ∥ ×
       ∃ λ (f : B → R) → ∃ λ (g : B → B) →
         Constant f × (B → ∀ b → b ≡ g b))                        ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

      (∥ B ∥ ×
       ∃ λ (f : B → R) → Constant f ×
       ∃ λ (g : B → B) → B → ∀ b → b ≡ g b)                       ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

      (∥ B ∥ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → B → ∀ b → b ≡ g b))                     ↔⟨ (∃-cong λ ∥b∥ → ∃-cong λ { (f , _) → ∃-cong λ _ → inverse $
                                                                        →-intro ext (λ _ → B-set f ∥b∥ _ _) }) ⟩
      (∥ B ∥ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → ∀ b → b ≡ g b))                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                        Eq.extensionality-isomorphism ext) ⟩
      (∥ B ∥ ×
       (∃ λ (f : B → R) → Constant f) ×
       (∃ λ (g : B → B) → F.id ≡ g))                              ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                                        inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                        other-singleton-contractible _) ⟩
      (∥ B ∥ × ∃ λ (f : B → R) → Constant f)                      ↝⟨ (∃-cong λ ∥b∥ → constant-function≃∥inhabited∥⇒inhabited (R-set ∥b∥)) ⟩

      (∥ B ∥ × (∥ B ∥ → R))                                       ↔⟨ lemma′ ⟩

      R                                                           □

-- If the codomain B is an inhabited set, then Iso-lens A B and
-- Traditional.Lens A B are logically equivalent.
--
-- This definition is inspired by the statement of Corollary 13 from
-- "Algebras and Update Strategies" by Johnson, Rosebrugh and Wood.

Iso-lens⇔Traditional-lens :
  ∀ {a b} {A : Set a} {B : Set b} →
  Is-set B →
  B →
  Iso-lens A B ⇔ Traditional.Lens A B
Iso-lens⇔Traditional-lens {A = A} {B} B-set b₀ = record
  { to   = Iso-lens.traditional-lens
  ; from = from
  }
  where
  from : Traditional.Lens A B → Iso-lens A B
  from l = isomorphism-to-lens
    {R = ∃ λ (a : A) → get a ≡ b₀}
    (record
       { surjection = record
         { logical-equivalence = record
           { to   = λ a → (set a b₀ , get-set a b₀) , get a
           ; from = λ { ((a , _) , b) → set a b }
           }
         ; right-inverse-of = λ { ((a , h) , b) →
             let
               lemma =
                 set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
                 set a b₀          ≡⟨ cong (set a) (sym h) ⟩
                 set a (get a)     ≡⟨ set-get a ⟩∎
                 a                 ∎
             in
             ((set (set a b) b₀ , get-set (set a b) b₀) , get (set a b))  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma (_⇔_.to set⇔UIP B-set _ _)) (get-set a b) ⟩∎
             ((a                , h                   ) , b            )  ∎
           }
         }
       ; left-inverse-of = λ a →
           set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
           set a (get a)           ≡⟨ set-get a ⟩∎
           a                       ∎
       })
    where
    open Traditional.Lens l

------------------------------------------------------------------------
-- Some Iso-lens results related to h-levels

-- If the domain of an Iso-lens is inhabited and has h-level n, then
-- the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ {n a b} {A : Set a} {B : Set b} →
  Iso-lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {n} {A = A} {B} l a =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ proj₂-closure (remainder a) n ⟩□
  H-level n B        □
  where
  open Iso-lens l

-- This is not necessarily true for arbitrary domains (assuming
-- univalence).

¬-h-level-respects-lens :
  ∀ {a b} →
  Univalence (a ⊔ b) →
  ¬ (∀ {n} {A : Set a} {B : Set b} →
     Iso-lens A B → H-level n A → H-level n B)
¬-h-level-respects-lens univ resp =
                             $⟨ ⊥-propositional ⟩
  Is-proposition ⊥           ↝⟨ resp (_↔_.from (lens-from-⊥↔⊤ univ) _) ⟩
  Is-proposition (↑ _ Bool)  ↝⟨ ↑⁻¹-closure 1 ⟩
  Is-proposition Bool        ↝⟨ ¬-Bool-propositional ⟩□
  ⊥₀                         □

-- In fact, there is an Iso-lens with a proposition as its domain and
-- a non-set as its codomain (assuming univalence).

lens-from-proposition-to-non-set :
  Univalence (# 0) →
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

-- Iso-lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  Iso-lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited l (proj₁ c) c

-- If the domain type of an Iso-lens is contractible, then the
-- remainder type is also contractible.

domain-contractible⇒remainder-contractible :
  ∀ {a b} {A : Set a} {B : Set b} →
  (l : Iso-lens A B) → Contractible A → Contractible (Iso-lens.R l)
domain-contractible⇒remainder-contractible {A = A} {B} l =
  Contractible A                   ↔⟨ H-level-cong ext 0 equiv ⟩
  Contractible (R × B)             ↔⟨ Contractible-commutes-with-× ext ⟩
  Contractible R × Contractible B  ↝⟨ proj₁ ⟩□
  Contractible R                   □
  where
  open Iso-lens l

-- If the domain type of an Iso-lens has h-level n, then the remainder
-- type also has h-level n.

remainder-has-same-h-level-as-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  (l : Iso-lens A B) → ∀ n → H-level n A → H-level n (Iso-lens.R l)
remainder-has-same-h-level-as-domain l zero =
  domain-contractible⇒remainder-contractible l
remainder-has-same-h-level-as-domain {A = A} {B} l (suc n) h =
  [inhabited⇒+]⇒+ n λ r →
                             $⟨ h ⟩
    H-level (1 + n) A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) (1 + n) ⟩
    H-level (1 + n) (R × B)  ↝⟨ rec (Π-closure ext 1 λ _ → H-level-propositional ext (1 + n))
                                    (λ b → proj₁-closure (λ _ → b) (1 + n))
                                    (inhabited r) ⟩□
    H-level (1 + n) R        □
  where
  open Iso-lens l

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Iso-lens A B (assuming univalence).

¬-Contractible-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Contractible A → Contractible (Iso-lens A B))
¬-Contractible-closed-domain univ closure =
                                     $⟨ ↑⊤-contractible ⟩
  Contractible (↑ _ ⊤)               ↝⟨ closure ⟩
  Contractible (Iso-lens (↑ _ ⊤) ⊥)  ↝⟨ H-level.respects-surjection
                                          (_↔_.surjection $ lens-from-contractible↔codomain-contractible univ ↑⊤-contractible)
                                          0 ⟩
  Contractible (Contractible ⊥)      ↝⟨ proj₁ ⟩
  Contractible ⊥                     ↝⟨ proj₁ ⟩
  ⊥                                  ↝⟨ ⊥-elim ⟩□
  ⊥₀                                 □
  where
  ↑⊤-contractible = ↑-closure 0 ⊤-contractible

-- Contractible is closed under Iso-lens A (assuming univalence).

Contractible-closed-codomain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B → Contractible (Iso-lens A B)
Contractible-closed-codomain {A = A} {B} univ cB =
                               $⟨ lens-to-contractible↔⊤ univ cB ⟩
  Iso-lens A B ↔ ⊤             ↝⟨ _⇔_.from contractible⇔⊤↔ ⊚ inverse ⟩□
  Contractible (Iso-lens A B)  □

-- If B is a proposition, then Iso-lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-codomain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B → Is-proposition (Iso-lens A B)
Is-proposition-closed-codomain {A = A} {B} univ B-prop =
                                 $⟨ Π-closure ext 1 (λ _ → B-prop) ⟩
  Is-proposition (A → B)         ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ lens-to-proposition↔get univ B-prop)
                                      1 ⟩□
  Is-proposition (Iso-lens A B)  □

private

  -- If A has h-level 1 + n and equivalence between certain remainder
  -- types has h-level n, then Iso-lens A B has h-level 1 + n
  -- (assuming univalence).

  domain-1+-remainder-equivalence-0+⇒lens-1+ :
    ∀ {a b} {A : Set a} {B : Set b} →
    Univalence (a ⊔ b) →
    ∀ n →
    H-level (1 + n) A →
    ((l₁ l₂ : Iso-lens A B) →
       H-level n (Iso-lens.R l₁ ≃ Iso-lens.R l₂)) →
    H-level (1 + n) (Iso-lens A B)
  domain-1+-remainder-equivalence-0+⇒lens-1+
    {A = A} univ n hA hR l₁ l₂ =                                $⟨ Σ-closure n (hR l₁ l₂) (λ _ →
                                                                   Π-closure ext n λ _ →
                                                                   hA _ _) ⟩
    H-level n (∃ λ (eq : R l₁ ≃ R l₂) → ∀ p → _≡_ {A = A} _ _)  ↝⟨ H-level.respects-surjection
                                                                     (_↔_.surjection $ inverse $ equality-characterisation₄ univ)
                                                                     n ⟩□
    H-level n (l₁ ≡ l₂)                                         □
    where
    open Iso-lens

-- If A is a proposition, then Iso-lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Iso-lens A B)
Is-proposition-closed-domain {b = b} {A} {B} univ A-prop =
                                          $⟨ R₁≃R₂ ⟩
  (∀ l₁ l₂ → R l₁ ≃ R l₂)                 ↝⟨ (λ hyp l₁ l₂ → propositional⇒inhabited⇒contractible
                                                              (Eq.left-closure ext 0 (R-prop l₁))
                                                              (hyp l₁ l₂)) ⟩
  (∀ l₁ l₂ → Contractible (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ 0 A-prop ⟩□
  Is-proposition (Iso-lens A B)           □
  where
  open Iso-lens

  R-prop : (l : Iso-lens A B) → Is-proposition (R l)
  R-prop l =
    remainder-has-same-h-level-as-domain l 1 A-prop

  remainder⁻¹ : (l : Iso-lens A B) → R l → A
  remainder⁻¹ l r =
    rec A-prop
        (λ b → _≃_.from (equiv l) (r , b))
        (inhabited l r)

  R-to-R : (l₁ l₂ : Iso-lens A B) → R l₁ → R l₂
  R-to-R l₁ l₂ = remainder l₂ ⊚ remainder⁻¹ l₁

  involutive : (l : Iso-lens A B) {f : R l → R l} → ∀ r → f r ≡ r
  involutive l _ = _⇔_.to propositional⇔irrelevant (R-prop l) _ _

  R₁≃R₂ : (l₁ l₂ : Iso-lens A B) → R l₁ ≃ R l₂
  R₁≃R₂ l₁ l₂ = Eq.↔⇒≃ $
    Bij.bijection-from-involutive-family
      R-to-R (λ l _ → involutive l) l₁ l₂

-- An alternative proof.

Is-proposition-closed-domain′ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Iso-lens A B)
Is-proposition-closed-domain′ {A = A} {B} univ A-prop =
                                         $⟨ Traditional.lens-preserves-h-level-of-domain 0 A-prop ⟩
  Is-proposition (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                              (_↔_.surjection $ inverse $ Iso-lens↔Traditional-lens univ (mono₁ 1 A-prop))
                                              1 ⟩□
  Is-proposition (Iso-lens A B)          □

-- If A is a set, then Iso-lens A B is also a set (assuming
-- univalence).
--
-- TODO: Can one prove that the corresponding result does not hold for
-- codomains? Are there types A and B such that B is a set, but
-- Iso-lens A B is not?

Is-set-closed-domain :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-set A → Is-set (Iso-lens A B)
Is-set-closed-domain {A = A} {B} univ A-set =
                                 $⟨ Traditional.lens-preserves-h-level-of-domain 1 A-set ⟩
  Is-set (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ Iso-lens↔Traditional-lens univ A-set)
                                      2 ⟩□
  Is-set (Iso-lens A B)          □

-- If A has h-level n, then Iso-lens A B has h-level 1 + n (assuming
-- univalence).
--
-- TODO: Can this be improved? The corresponding result for
-- Traditional.Lens (Traditional.lens-preserves-h-level-of-domain) is
-- stronger.

domain-0+⇒lens-1+ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
domain-0+⇒lens-1+ {A = A} {B} univ n hA =
                                                      $⟨ (λ l₁ l₂ → Eq.h-level-closure ext n (hR l₁) (hR l₂)) ⟩
  ((l₁ l₂ : Iso-lens A B) → H-level n (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ n (mono₁ n hA) ⟩□
  H-level (1 + n) (Iso-lens A B)                      □
  where
  open Iso-lens

  hR : ∀ l → H-level n (R l)
  hR l = remainder-has-same-h-level-as-domain l n hA

-- An alternative proof.

domain-0+⇒lens-1+′ :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
domain-0+⇒lens-1+′ {A = A} {B} univ n hA =
                                               $⟨ Σ-closure (1 + n)
                                                    (∃-H-level-H-level-1+ ext univ n)
                                                    (λ _ → ×-closure (1 + n)
                                                             (Eq.left-closure ext n (mono₁ n hA))
                                                             (Π-closure ext (1 + n) λ _ →
                                                              mono (Nat.suc≤suc (Nat.zero≤ n)) $
                                                              truncation-is-proposition)) ⟩
  H-level (1 + n)
    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥))  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse iso) (1 + n) ⟩□

  H-level (1 + n) (Iso-lens A B)               □
  where
  open Iso-lens

  iso =
    Iso-lens A B                                         ↝⟨ inverse $ drop-⊤-right (λ l →
                                                              inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                propositional⇒inhabited⇒contractible
                                                                  (H-level-propositional ext n)
                                                                  (remainder-has-same-h-level-as-domain l n hA)) ⟩
    (∃ λ (l : Iso-lens A B) → H-level n (R l))           ↝⟨ inverse Σ-assoc ⟩

    (∃ λ R → (A ≃ (R × B) × (R → ∥ B ∥)) × H-level n R)  ↝⟨ (∃-cong λ _ → ×-comm) ⟩

    (∃ λ R → H-level n R × A ≃ (R × B) × (R → ∥ B ∥))    ↝⟨ Σ-assoc ⟩□

    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥))            □

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no Iso-lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∀ {a b} →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Iso-lens (Σ A B) A
no-first-projection-lens =
  Lens.Non-dependent.no-first-projection-lens
    Iso-lens contractible-to-contractible

------------------------------------------------------------------------
-- Iso-lens combinators

module Iso-lens-combinators where

  -- The definition of the identity lens is unique, if the get
  -- function is required to be the identity (assuming univalence).

  id-unique :
    ∀ {a} {A : Set a} →
    Univalence a →
    (l₁ l₂ : ∃ λ (l : Iso-lens A A) →
                 ∀ a → Iso-lens.get l a ≡ a) →
    proj₁ l₁ ≡ proj₁ l₂
  id-unique {A = A} univ l₁ l₂ =
    _↔_.from (equality-characterisation₃ univ)
      ( R₁≃R₂
      , (λ _ → _⇔_.to propositional⇔irrelevant
                 (remainder-propositional l₂)
                 _ _)
      , λ a →
          get (proj₁ l₁) a  ≡⟨ proj₂ l₁ a ⟩
          a                 ≡⟨ sym $ proj₂ l₂ a ⟩∎
          get (proj₁ l₂) a  ∎
      )
    where
    remainder-propositional :
      (l : ∃ λ (l : Iso-lens A A) → ∀ a → Iso-lens.get l a ≡ a) →
      Is-proposition (Iso-lens.R (proj₁ l))
    remainder-propositional (l , get≡id) =
      [inhabited⇒+]⇒+ 0 λ r →
        Trunc.rec
          (H-level-propositional ext 1)
          (λ a → _⇔_.from propositional⇔irrelevant λ r₁ r₂ →
                   cong proj₁ (
                     (r₁ , a)        ≡⟨ sym $ to-lemma a r₁ ⟩
                     _≃_.to equiv a  ≡⟨ to-lemma a r₂ ⟩∎
                     (r₂ , a)        ∎))
          (inhabited r)
      where
      open Iso-lens l

      from-lemma : ∀ r a → _≃_.from equiv (r , a) ≡ a
      from-lemma r a =
        _≃_.from equiv (r , a)                                 ≡⟨ cong (λ a′ → _≃_.from equiv (proj₁ a′ , a)) $ sym $
                                                                    _≃_.right-inverse-of equiv _ ⟩
        _≃_.from equiv
          (proj₁ (_≃_.to equiv (_≃_.from equiv (r , a))) , a)  ≡⟨⟩

        set (_≃_.from equiv (r , a)) a                         ≡⟨ sym $ get≡id _ ⟩

        get (set (_≃_.from equiv (r , a)) a)                   ≡⟨ get-set _ _ ⟩∎

        a                                                      ∎

      to-lemma : ∀ a r → _≃_.to equiv a ≡ (r , a)
      to-lemma a r =
        _≃_.to equiv a                         ≡⟨ cong (_≃_.to equiv) $ sym $ from-lemma r a ⟩
        _≃_.to equiv (_≃_.from equiv (r , a))  ≡⟨ _≃_.right-inverse-of equiv (r , a) ⟩∎
        (r , a)                                ∎

    open Iso-lens

    R→R :
      (l₁ l₂ : ∃ λ (l : Iso-lens A A) → ∀ a → get l a ≡ a) →
      R (proj₁ l₁) → R (proj₁ l₂)
    R→R (l₁ , l₁-id) (l₂ , l₂-id) r =
      Trunc.rec
        (remainder-propositional (l₂ , l₂-id))
        (A         ↔⟨ equiv l₂ ⟩
         R l₂ × A  ↝⟨ proj₁ ⟩□
         R l₂      □)
        (inhabited l₁ r)

    R₁≃R₂ : R (proj₁ l₁) ≃ R (proj₁ l₂)
    R₁≃R₂ =
      _↠_.from (Eq.≃↠⇔ (remainder-propositional l₁)
                       (remainder-propositional l₂))
               (record { to   = R→R l₁ l₂
                       ; from = R→R l₂ l₁
                       })

  -- The result of composing two lenses is unique if the codomain type
  -- is inhabited whenever it is merely inhabited, and we require that
  -- the resulting setter function is defined in a certain way
  -- (assuming univalence).

  ∘-unique :
    let open Iso-lens in
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    Univalence (a ⊔ c) →
    (∥ C ∥ → C) →
    (comp₁ comp₂ :
       ∃ λ (comp : Iso-lens B C → Iso-lens A B → Iso-lens A C) →
         ∀ l₁ l₂ a c →
           set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    proj₁ comp₁ ≡ proj₁ comp₂
  ∘-unique {A = A} {C = C} univ ∥C∥→C
           (comp₁ , set₁) (comp₂ , set₂) =
    ext λ l₁ → ext λ l₂ →
      lenses-equal-if-setters-equal univ
        ∥C∥→C (comp₁ l₁ l₂) (comp₂ l₁ l₂) λ a c →
          set (comp₁ l₁ l₂) a c           ≡⟨ set₁ _ _ _ _ ⟩
          set l₂ a (set l₁ (get l₂ a) c)  ≡⟨ sym $ set₂ _ _ _ _ ⟩∎
          set (comp₂ l₁ l₂) a c           ∎
    where
    open Iso-lens

  -- Identity lens.

  id : ∀ {a} {A : Set a} →
       Iso-lens A A
  id {A = A} =
    isomorphism-to-lens
      (A          ↝⟨ inverse $ drop-⊤-left-× (λ _ → Bij.↑↔) ⟩□
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

  -- Other definitions of composition match ⟨_,_⟩_∘_, if the codomain
  -- type is inhabited whenever it is merely inhabited, and the
  -- resulting setter function is defined in a certain way (assuming
  -- univalence).

  composition≡∘ :
    let open Iso-lens in
    ∀ {a b c} {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Univalence (a ⊔ b ⊔ c) →
    (∥ C ∥ → C) →
    (comp : Iso-lens B C → Iso-lens A B → Iso-lens A C) →
    (∀ l₁ l₂ a c →
       set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp ≡ ⟨ a , b ⟩_∘_
  composition≡∘ univ ∥C∥→C comp set-comp =
    ∘-unique univ ∥C∥→C (comp , set-comp) (_ , λ _ _ _ _ → refl)

  -- Identity and composition form a kind of monoid (assuming
  -- univalence).

  associativity :
    ∀ a b c {d}
      {A : Set (a ⊔ b ⊔ c ⊔ d)} {B : Set (b ⊔ c ⊔ d)}
      {C : Set (c ⊔ d)} {D : Set d} →
    Univalence (a ⊔ b ⊔ c ⊔ d) →
    (l₁ : Iso-lens C D)
    (l₂ : Iso-lens B C)
    (l₃ : Iso-lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ univ _ _ _ =
    _↔_.from (equality-characterisation₂ univ)
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl)

  left-identity :
    ∀ a {b} {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Iso-lens A B) →
    ⟨ a , lzero ⟩ id ∘ l ≡ l
  left-identity _ {B = B} univ l =
    _↔_.from (equality-characterisation₂ univ)
      ( (R × ↑ _ ⊤ × ∥ B ∥  ↔⟨ F.id ×-cong drop-⊤-left-× (λ _ → Bij.↑↔) ⟩
         R × ∥ B ∥          ↔⟨ lemma ⟩□
         R                  □)
      , λ _ → refl
      )
    where
    open Iso-lens l

    lemma : R × ∥ B ∥ ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₁
          ; from = λ r → r , inhabited r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (r , _) →
          cong (λ x → r , x) $
            _⇔_.to propositional⇔irrelevant
              truncation-is-proposition _ _ }
      }

  right-identity :
    ∀ a {b} {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Iso-lens A B) →
    ⟨ lzero , a ⟩ l ∘ id ≡ l
  right-identity a {b} {A} univ l =
    _↔_.from (equality-characterisation₂ univ)
      ( ((↑ _ ⊤ × ∥ A ∥) × R  ↔⟨ drop-⊤-left-× (λ _ → Bij.↑↔) ×-cong F.id ⟩
         ∥ A ∥ × R            ↔⟨ lemma ⟩□
         R                    □)
      , λ _ → refl
      )
    where
    open Iso-lens l

    lemma : ∥ A ∥ × R ↔ R
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
              truncation-is-proposition _ _ }
      }
