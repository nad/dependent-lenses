------------------------------------------------------------------------
-- A variant of Paolo Capriotti's variant of higher lenses
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti.Variant
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id)

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Preimage equality-with-J as Preimage
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher

private
  variable
    a b p : Level
    A B   : Type a
    P Q   : A → Type p

------------------------------------------------------------------------
-- Coherently-constant

-- Coherently constant type-valued functions.
--
-- This definition is based on Paolo Capriotti's definition of higher
-- lenses, but uses a family of equivalences instead of an equality.

Coherently-constant :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant {p = p} {A = A} P =
  ∃ λ (Q : ∥ A ∥ → Type p) → ∀ x → P x ≃ Q ∣ x ∣

-- A preservation lemma for Coherently-constant.
--
-- Note that P and Q must target the same universe.

Coherently-constant-map :
  {P : A → Type p} {Q : B → Type p}
  (f : B → A) →
  (∀ x → P (f x) ≃ Q x) →
  Coherently-constant P → Coherently-constant Q
Coherently-constant-map {P = P} {Q = Q} f P≃Q (R , P≃R) =
    R ∘ T.∥∥-map f
  , λ x →
      Q x        ↝⟨ inverse $ P≃Q x ⟩
      P (f x)    ↝⟨ P≃R (f x) ⟩□
      R ∣ f x ∣  □

-- Coherently-constant is, in a certain sense, closed under Σ.
--
-- This lemma is due to Paolo Capriotti.

Coherently-constant-Σ :
  Coherently-constant P →
  Coherently-constant Q →
  Coherently-constant (λ x → ∃ λ (y : P x) → Q (x , y))
Coherently-constant-Σ {P = P} {Q = Q} (P′ , p) (Q′ , q) =
    (λ x → ∃ λ (y : P′ x) →
               Q′ (T.elim
                     (λ x → P′ x → ∥ ∃ P ∥)
                     (λ _ → Π-closure ext 1 λ _ →
                            T.truncation-is-proposition)
                     (λ x y → ∣ x , _≃_.from (p x) y ∣)
                     x y))
  , (λ x →

       (∃ λ (y : P x) → Q (x , y))                         ↝⟨ (Σ-cong (p x) λ y →

          Q (x , y)                                              ↝⟨ q (x , y) ⟩
          Q′ ∣ x , y ∣                                           ↝⟨ ≡⇒≃ $ cong Q′ $ T.truncation-is-proposition _ _ ⟩□
          Q′ ∣ x , _≃_.from (p x) (_≃_.to (p x) y) ∣             □) ⟩□

       (∃ λ (y : P′ ∣ x ∣) → Q′ ∣ x , _≃_.from (p x) y ∣)  □)

------------------------------------------------------------------------
-- The lens type family

-- Paolo Capriotti's variant of higher lenses, but with a family of
-- equivalences instead of an equality.

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹_)

-- Some derived definitions (based on Capriotti's).

module Lens {A : Type a} {B : Type b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- A predicate.

  H : Pow a ∥ B ∥
  H = proj₁ (proj₂ l)

  -- An equivalence.

  get⁻¹-≃ : ∀ b → get ⁻¹ b ≃ H ∣ b ∣
  get⁻¹-≃ = proj₂ (proj₂ l)

  -- All the getter's "preimages" are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant b₁ b₂ =
    get ⁻¹ b₁  ↝⟨ get⁻¹-≃ b₁ ⟩
    H ∣ b₁ ∣   ↝⟨ ≡⇒≃ $ cong H $ T.truncation-is-proposition _ _ ⟩
    H ∣ b₂ ∣   ↝⟨ inverse $ get⁻¹-≃ b₂ ⟩□
    get ⁻¹ b₂  □

  -- The two directions of get⁻¹-constant.

  get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂
  get⁻¹-const b₁ b₂ = _≃_.to (get⁻¹-constant b₁ b₂)

  get⁻¹-const⁻¹ : (b₁ b₂ : B) → get ⁻¹ b₂ → get ⁻¹ b₁
  get⁻¹-const⁻¹ b₁ b₂ = _≃_.from (get⁻¹-constant b₁ b₂)

  -- Some coherence properties.

  get⁻¹-const-∘ :
    (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
    get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p
  get⁻¹-const-∘ b₁ b₂ b₃ p =
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃_.to (get⁻¹-≃ b₂)
            (_≃_.from (get⁻¹-≃ b₂)
               (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
                  (_≃_.to (get⁻¹-≃ b₁) p)))))                   ≡⟨ cong (_≃_.from (get⁻¹-≃ _) ∘ ≡⇒→ _) $
                                                                   _≃_.right-inverse-of (get⁻¹-≃ _) _ ⟩
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
            (_≃_.to (get⁻¹-≃ b₁) p)))                           ≡⟨ cong (λ eq → _≃_.from (get⁻¹-≃ _) (_≃_.to eq (_≃_.to (get⁻¹-≃ _) _))) $ sym $
                                                                   ≡⇒≃-trans ext _ _ ⟩
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (trans (cong H $ T.truncation-is-proposition _ _)
              (cong H $ T.truncation-is-proposition _ _))
            (_≃_.to (get⁻¹-≃ b₁) p))                            ≡⟨ cong (λ eq → _≃_.from (get⁻¹-≃ b₃) (≡⇒→ eq _)) $
                                                                   trans (sym $ cong-trans _ _ _) $
                                                                   cong (cong H) $ mono₁ 1 T.truncation-is-proposition _ _ ⟩∎
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃_.to (get⁻¹-≃ b₁) p))                               ∎

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
  set a b =                    $⟨ get⁻¹-const _ _ ⟩
    (get ⁻¹ get a → get ⁻¹ b)  ↝⟨ _$ (a , refl _) ⟩
    get ⁻¹ b                   ↝⟨ proj₁ ⟩□
    A                          □

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    get (proj₁ (get⁻¹-const (get a) b (a , refl _)))  ≡⟨ proj₂ (get⁻¹-const (get a) b (a , refl _)) ⟩∎
    b                                                 ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    proj₁ (get⁻¹-const (get a) (get a) (a , refl _))  ≡⟨ cong proj₁ $ get⁻¹-const-id _ _ ⟩∎
    a                                                 ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl _))  ≡⟨ elim¹
                                                                      (λ {b} eq →
                                                                         proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl _)) ≡
                                                                         proj₁ (get⁻¹-const b b₂ (set a b₁ , eq)))
                                                                      (refl _)
                                                                      (get-set a b₁) ⟩
    proj₁ (get⁻¹-const b₁ b₂ (set a b₁ , get-set a b₁))          ≡⟨⟩

    proj₁ (get⁻¹-const b₁ b₂
             (get⁻¹-const (get a) b₁ (a , refl _)))              ≡⟨ cong proj₁ $ get⁻¹-const-∘ _ _ _ _ ⟩∎

    proj₁ (get⁻¹-const (get a) b₂ (a , refl _))                  ∎

  -- TODO: Can get-set-get and get-set-set be proved for the lens laws
  -- given above?

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Equality characterisation lemmas

-- An equality characterisation lemma.

equality-characterisation₁ :
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)
equality-characterisation₁ {a = a} {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                          ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Σ-assoc ⟩

  ((get l₁ , H l₁) , get⁻¹-≃ l₁) ≡ ((get l₂ , H l₂) , get⁻¹-≃ l₂)  ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

  (∃ λ (eq : (get l₁ , H l₁) ≡ (get l₂ , H l₂)) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣) eq (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↝⟨ (Σ-cong-contra ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ ((g , h) : get l₁ ≡ get l₂ × H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                       Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹-≃ l₁) b ≡
           get⁻¹-≃ l₂ b)                                           ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                       push-subst-application _ _) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹-≃ l₁ b) ≡
           get⁻¹-≃ l₂ b)                                           ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                       ≃-to-≡↔≡ ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     _≃_.to (subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
               (cong₂ _,_ g h) (get⁻¹-≃ l₁ b)) p ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                       ≡⇒↝ _ $ cong (_≡ _) $ lemma _ _ _ _) ⟩□
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                      □
  where
  open Lens

  lemma : ∀ _ _ _ _ → _ ≡ _
  lemma g h b p =
    _≃_.to (subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
              (cong₂ _,_ g h) (get⁻¹-≃ l₁ b)) p                 ≡⟨ cong (_$ p) Eq.to-subst ⟩

    subst (λ (g , H) → g ⁻¹ b → H ∣ b ∣)
      (cong₂ _,_ g h) (_≃_.to (get⁻¹-≃ l₁ b)) p                 ≡⟨ subst-→ ⟩

    subst (λ (g , H) → H ∣ b ∣) (cong₂ _,_ g h)
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (λ (g , H) → g ⁻¹ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ subst-∘ _ _ _ ⟩

    subst (_$ ∣ b ∣) (cong proj₂ $ cong₂ _,_ g h)
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (λ (g , H) → g ⁻¹ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ cong₂ (λ p q → subst (λ (H : Pow a _) → H ∣ b ∣)
                                                                                    p (_≃_.to (get⁻¹-≃ l₁ b) q))
                                                                     (cong-proj₂-cong₂-, _ _)
                                                                     (subst-∘ _ _ _) ⟩
    subst (_$ ∣ b ∣) h
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (_⁻¹ b) (cong proj₁ $ sym $ cong₂ _,_ g h) p))  ≡⟨ cong (λ eq → subst (_$ ∣ b ∣) h
                                                                                  (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) eq p))) $
                                                                   trans (cong-sym _ _) $
                                                                   cong sym $ cong-proj₁-cong₂-, _ _ ⟩∎
    subst (_$ ∣ b ∣) h
      (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p))         ∎

-- Another equality characterisation lemma.

equality-characterisation₂ :
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst P.id (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)
equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ ⊠ ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                        Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                        F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst (_$ ∣ b ∣) (⟨ext⟩ h)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        ≡⇒↝ _ $ cong (_≡ _) $
                                                                        subst-ext ext) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst P.id (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       □
  where
  open Lens

-- Yet another equality characterisation lemma.

equality-characterisation₃ :
  {A : Type a} {B : Type b}
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  Univalence (a ⊔ b) →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     ∀ b p →
     _≃_.to (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)
equality-characterisation₃ {l₁ = l₁} {l₂ = l₂} ⊠ univ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₂ ⊠ ⟩

  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst P.id (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (∃-cong λ _ →
                                                                        Σ-cong-contra (∀-cong ext λ _ → inverse $ ≡≃≃ univ) λ _ → F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     ∀ b p →
     subst P.id (≃⇒≡ univ (h ∣ b ∣))
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        ≡⇒↝ _ $ cong (_≡ _) $
                                                                        trans (subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                        cong (λ eq → _≃_.to eq _) $
                                                                        _≃_.right-inverse-of (≡≃≃ univ) _) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     ∀ b p →
     _≃_.to (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       □
  where
  open Lens

------------------------------------------------------------------------
-- Conversion functions

-- The lenses defined above can be converted to and from the lenses
-- defined in Higher.

Lens⇔Higher-lens : Lens A B ⇔ Higher.Lens A B
Lens⇔Higher-lens {A = A} {B = B} = record
  { to = λ (g , H , eq) → record
           { R = Σ ∥ B ∥ H

           ; equiv =
               A                                      ↔⟨ (inverse $ drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                          other-singleton-contractible _) ⟩
               (∃ λ (a : A) → ∃ λ (b : B) → g a ≡ b)  ↔⟨ ∃-comm ⟩
               (∃ λ (b : B) → g ⁻¹ b)                 ↝⟨ ∃-cong eq ⟩
               (∃ λ (b : B) → H ∣ b ∣)                ↝⟨ (Σ-cong (inverse T.∥∥×≃) λ _ → ≡⇒↝ _ $ cong H $ T.truncation-is-proposition _ _) ⟩
               (∃ λ ((b , _) : ∥ B ∥ × B) → H b)      ↔⟨ Σ-assoc F.∘
                                                         (∃-cong λ _ → ×-comm) F.∘
                                                         inverse Σ-assoc ⟩□
               Σ ∥ B ∥ H × B                          □

           ; inhabited = proj₁
           }
  ; from = λ l →
               Higher.Lens.get l
             , (λ _ → Higher.Lens.R l)
             , (λ b → inverse (Higher.remainder≃get⁻¹ l b))
  }

-- The conversion preserves getters and setters.

Lens⇔Higher-lens-preserves-getters-and-setters :
  Preserves-getters-and-setters-⇔ A B Lens⇔Higher-lens
Lens⇔Higher-lens-preserves-getters-and-setters =
    (λ l@(g , H , eq) →
         refl _
       , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
         let h₁ = _≃_.to (eq (g a)) (a , refl _)

             h₂ =
               _≃_.from (≡⇒≃ (cong H _))
                 (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                    (≡⇒→ (cong H _) h₁))

             h₃ = ≡⇒→ (cong H _) h₁

             lemma =
               h₂                                                         ≡⟨ sym $ subst-in-terms-of-inverse∘≡⇒↝ equivalence _ _ _ ⟩

               subst H _
                 (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                    (≡⇒→ (cong H _) h₁))                                  ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _)
                                                                                           (subst (H ∘ proj₁)
                                                                                              (sym (_≃_.left-inverse-of T.∥∥×≃ (∣ g a ∣ , b)))
                                                                                              x)) $ sym $
                                                                             subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
               subst H _
                 (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                    (subst H _ h₁))                                       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                                             subst-∘ _ _ _ ⟩

               subst H _ (subst H _ (subst H _ h₁))                       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                                             subst-subst _ _ _ _ ⟩

               subst H _ (subst H _ h₁)                                   ≡⟨ subst-subst _ _ _ _ ⟩

               subst H _ h₁                                               ≡⟨ cong (λ eq → subst H eq h₁) $
                                                                             mono₁ 1 T.truncation-is-proposition _ _ ⟩

               subst H _ h₁                                               ≡⟨ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩∎

               ≡⇒→ (cong H _) h₁                                          ∎
         in
         Higher.Lens.set (_⇔_.to Lens⇔Higher-lens l) a b  ≡⟨⟩
         proj₁ (_≃_.from (eq b) h₂)                       ≡⟨ cong (λ h → proj₁ (_≃_.from (eq b) h)) lemma ⟩
         proj₁ (_≃_.from (eq b) h₃)                       ≡⟨⟩
         Lens.set l a b                                   ∎)
  , (λ l →
         refl _
       , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
         Lens.set (_⇔_.from Lens⇔Higher-lens l) a b        ≡⟨⟩

         _≃_.from (Higher.Lens.equiv l)
           ( ≡⇒→ (cong (λ _ → Higher.Lens.R l) _)
               (Higher.Lens.remainder l a)
           , b
           )                                               ≡⟨ cong (λ eq → _≃_.from (Higher.Lens.equiv l) (≡⇒→ eq _ , b)) $
                                                              cong-const _ ⟩
         _≃_.from (Higher.Lens.equiv l)
           (≡⇒→ (refl _) (Higher.Lens.remainder l a) , b)  ≡⟨ cong (λ f → _≃_.from (Higher.Lens.equiv l) (f _ , b)) $
                                                              ≡⇒→-refl ⟩
         _≃_.from (Higher.Lens.equiv l)
           (Higher.Lens.remainder l a , b)                 ≡⟨⟩

         Higher.Lens.set l a b                             ∎)

-- Lens A B is equivalent to Higher.Lens A B (assuming univalence).

Lens≃Higher-lens :
  {A : Type a} {B : Type b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Lens A B ≃ Higher.Lens A B
Lens≃Higher-lens {A = A} {B = B} ⊠ univ =
  Eq.↔→≃ to from to∘from from∘to
  where
  to = _⇔_.to Lens⇔Higher-lens

  from = _⇔_.from Lens⇔Higher-lens

  to∘from : ∀ l → to (from l) ≡ l
  to∘from l = _↔_.from (Higher.equality-characterisation₂ ⊠ univ)
    ( (∥ B ∥ × R  ↔⟨ (drop-⊤-left-× λ r → _⇔_.to contractible⇔↔⊤ $
                      propositional⇒inhabited⇒contractible
                        T.truncation-is-proposition
                        (inhabited r)) ⟩□
       R          □)
    , (λ a →
         ≡⇒→ (cong (λ _ → R) (T.truncation-is-proposition _ _))
           (remainder a)                                         ≡⟨ cong (λ eq → ≡⇒→ eq _) $ cong-const _ ⟩

         ≡⇒→ (refl _) (remainder a)                              ≡⟨ cong (_$ _) ≡⇒→-refl ⟩∎

         remainder a                                             ∎)
    , (λ _ → refl _)
    )
    where
    open Higher.Lens l

  from∘to : ∀ l → from (to l) ≡ l
  from∘to l = _≃_.from (equality-characterisation₃ ⊠ univ)
    ( (λ _ → refl _)
    , Σ∥B∥H≃H
    , (λ b p@(a , get-a≡b) →
         _≃_.to (Σ∥B∥H≃H ∣ b ∣)
           (_≃_.from (Higher.remainder≃get⁻¹ (to l) b)
              (subst (_⁻¹ b) (sym (⟨ext⟩ λ _ → refl _)) p))             ≡⟨ cong (_≃_.to (Σ∥B∥H≃H ∣ b ∣) ∘
                                                                                 _≃_.from (Higher.remainder≃get⁻¹ (to l) b)) $
                                                                           trans (cong (flip (subst (_⁻¹ b)) p) $
                                                                                  trans (cong sym $ ext-refl ext) $
                                                                                  sym-refl) $
                                                                           subst-refl _ _ ⟩
         _≃_.to (Σ∥B∥H≃H ∣ b ∣)
           (_≃_.from (Higher.remainder≃get⁻¹ (to l) b) p)               ≡⟨⟩

         _≃_.to (Σ∥B∥H≃H ∣ b ∣) (Higher.Lens.remainder (to l) a)        ≡⟨⟩

         subst H _
           (≡⇒→ (cong H _) (_≃_.to (get⁻¹-≃ (get a)) (a , refl _)))     ≡⟨ cong (subst H _) $ sym $
                                                                           subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩

         subst H _ (subst H _ (_≃_.to (get⁻¹-≃ (get a)) (a , refl _)))  ≡⟨ subst-subst _ _ _ _ ⟩

         subst H _ (_≃_.to (get⁻¹-≃ (get a)) (a , refl _))              ≡⟨ cong (λ eq → subst H eq (_≃_.to (get⁻¹-≃ (get a)) (a , refl _))) $
                                                                           mono₁ 1 T.truncation-is-proposition _ _ ⟩
         subst H (cong ∣_∣ get-a≡b)
           (_≃_.to (get⁻¹-≃ (get a)) (a , refl _))                      ≡⟨ elim¹
                                                                             (λ {b} eq →
                                                                                subst H (cong ∣_∣ eq)
                                                                                  (_≃_.to (get⁻¹-≃ (get a)) (a , refl _)) ≡
                                                                                _≃_.to (get⁻¹-≃ b) (a , eq))
                                                                             (
           subst H (cong ∣_∣ (refl _))
             (_≃_.to (get⁻¹-≃ (get a)) (a , refl _))                          ≡⟨ trans (cong (flip (subst H) _) $ cong-refl _) $
                                                                                 subst-refl _ _ ⟩
           _≃_.to (get⁻¹-≃ (get a)) (a , refl _)                              ∎)
                                                                             _ ⟩∎
         _≃_.to (get⁻¹-≃ b) p                                           ∎)
    )
    where
    open Lens l

    Σ∥B∥H≃H = λ b →
      Σ ∥ B ∥ H  ↔⟨ (drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                     propositional⇒inhabited⇒contractible
                       T.truncation-is-proposition b) ⟩□
      H b        □

-- The equivalence preserves getters and setters.

Lens≃Higher-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bl : Block "conversion")
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Lens≃Higher-lens bl univ))
Lens≃Higher-lens-preserves-getters-and-setters ⊠ _ =
  Lens⇔Higher-lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- Identity

-- An identity lens.

id : {A : Type a} → Lens A A
id =
    P.id
  , (λ _ → ↑ _ ⊤)
  , (λ a →
       P.id ⁻¹ a  ↔⟨ _⇔_.to contractible⇔↔⊤ $ Preimage.id⁻¹-contractible _ ⟩
       ⊤          ↔⟨ inverse B.↑↔ ⟩□
       ↑ _ ⊤      □)

------------------------------------------------------------------------
-- Some results related to fibres of Lens.set

-- When proving that Lens.set ⁻¹ s is a proposition, for
-- s : A → B → A, one can assume that B is inhabited.
--
-- This result is due to Andrea Vezzosi.

[codomain-inhabited→proposition]→proposition :
  {s : A → B → A} →
  (B → Is-proposition (Lens.set ⁻¹ s)) ≃
  Is-proposition (Lens.set ⁻¹ s)
[codomain-inhabited→proposition]→proposition {B = B} {s = s} =
  block λ b →

  (B → Is-proposition (Lens.set ⁻¹ s))      ↝⟨ inverse $ T.universal-property (H-level-propositional ext 1) ⟩
  (∥ B ∥ → Is-proposition (Lens.set ⁻¹ s))  ↔⟨⟩
  (∥ B ∥ → (p q : Lens.set ⁻¹ s) → p ≡ q)   ↔⟨ (∀-cong ext λ _ → Π-comm) F.∘ Π-comm ⟩
  ((p q : Lens.set ⁻¹ s) → ∥ B ∥ → p ≡ q)   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → lemma b _ _) ⟩
  ((p q : Lens.set ⁻¹ s) → p ≡ q)           ↔⟨⟩
  Is-proposition (Lens.set ⁻¹ s)            □
  where
  open Lens

  lemma :
    (b : Block "equality-characterisation") →
    (p₁ p₂ : Lens.set ⁻¹ s) →
    (∥ B ∥ → p₁ ≡ p₂) ≃ (p₁ ≡ p₂)
  lemma b p₁@(l₁ , eq₁) p₂@(l₂ , eq₂) =
    (∥ B ∥ → p₁ ≡ p₂)                                           ↝⟨ (∀-cong ext λ _ → ec) ⟩

    (∥ B ∥ →
     ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst P.id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ T.push-∥∥ (∣_∣ ∘ get l₁) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∥ B ∥ →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst P.id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → T.push-∥∥ P.id) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∥ B ∥ →
     ∃ λ (f : ∀ b p →
              subst P.id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → T.push-∥∥ ∣_∣) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst P.id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∥ B ∥ →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → T.drop-∥∥ (∣_∣ ∘ get l₁)) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst P.id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ inverse ec ⟩□

    p₁ ≡ p₂                                                     □
    where
    ec =
      p₁ ≡ p₂                                                     ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

      (∃ λ (l : l₁ ≡ l₂) →
         subst (λ l → Lens.set l ≡ s) l eq₁ ≡ eq₂)                ↝⟨ (∃-cong λ _ → inverse $
                                                                      Eq.≃-≡ $ inverse $ Eq.extensionality-isomorphism ext) ⟩
      (∃ λ (l : l₁ ≡ l₂) →
         ext⁻¹ (subst (λ l → Lens.set l ≡ s) l eq₁) ≡ ext⁻¹ eq₂)  ↝⟨ (∃-cong λ _ → inverse $
                                                                      Eq.extensionality-isomorphism ext) ⟩
      (∃ λ (l : l₁ ≡ l₂) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s) l eq₁) a ≡
               ext⁻¹ eq₂ a)                                       ↝⟨ (Σ-cong-contra (inverse $ equality-characterisation₂ b) λ _ → F.id) ⟩

      (∃ λ (l : ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
                ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
                  ∀ b p →
                  subst P.id (h ∣ b ∣)
                    (_≃_.to (get⁻¹-≃ l₁ b)
                       (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
                  _≃_.to (get⁻¹-≃ l₂ b) p) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                        (_≃_.from (equality-characterisation₂ b)
                           l) eq₁) a ≡
               ext⁻¹ eq₂ a)                                       ↔⟨ (∃-cong λ _ → inverse Σ-assoc) F.∘ inverse Σ-assoc ⟩□

      (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
       ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∃ λ (f : ∀ b p →
                subst P.id (h ∣ b ∣)
                  (_≃_.to (get⁻¹-≃ l₁ b)
                     (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
                _≃_.to (get⁻¹-≃ l₂ b) p) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                        (_≃_.from (equality-characterisation₂ b)
                           (g , h , f)) eq₁) a ≡
               ext⁻¹ eq₂ a)                                       □

-- The previous result holds also for the lenses in Higher (assuming
-- univalence).

[codomain-inhabited→proposition]→proposition-for-higher :
  {A : Type a} {B : Type b} {s : A → B → A} →
  Univalence (a ⊔ b) →
  (B → Is-proposition (Higher.Lens.set ⁻¹ s)) ≃
  Is-proposition (Higher.Lens.set ⁻¹ s)
[codomain-inhabited→proposition]→proposition-for-higher
  {A = A} {B = B} {s = s} univ =

  (B → Is-proposition (Higher.Lens.set ⁻¹ s))  ↝⟨ (∀-cong ext λ _ → H-level-cong ext 1 lemma) ⟩
  (B → Is-proposition (Lens.set ⁻¹ s))         ↝⟨ [codomain-inhabited→proposition]→proposition ⟩
  Is-proposition (Lens.set ⁻¹ s)               ↝⟨ inverse $ H-level-cong ext 1 lemma ⟩□
  Is-proposition (Higher.Lens.set ⁻¹ s)        □
  where
  lemma : Higher.Lens.set ⁻¹ s ≃ Lens.set ⁻¹ s
  lemma = block λ b →
    (∃ λ (l : Higher.Lens A B) → Higher.Lens.set l ≡ s)  ↝⟨ (Σ-cong (inverse $ Lens≃Higher-lens b univ) λ l →
                                                             ≡⇒↝ _ $ cong (_≡ s) $ sym $ proj₂ $
                                                             proj₂ (Lens≃Higher-lens-preserves-getters-and-setters b univ) l) ⟩□
    (∃ λ (l : Lens A B) → Lens.set l ≡ s)                □

-- If a certain variant of Higher.lenses-equal-if-setters-equal can be
-- proved, then Higher.Lens.set ⁻¹ s is a proposition (assuming
-- univalence).

lenses-equal-if-setters-equal→set⁻¹-proposition :
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b)) →
  ((l₁ l₂ : Higher.Lens A B) →
   B →
   (s : Higher.Lens.set l₁ ≡ Higher.Lens.set l₂) →
   ∃ λ (l : l₁ ≡ l₂) → cong Higher.Lens.set l ≡ s) →
  (s : A → B → A) →
  Is-proposition (Higher.Lens.set ⁻¹ s)
lenses-equal-if-setters-equal→set⁻¹-proposition
  {B = B} univ lenses-equal-if-setters-equal s =
                                               $⟨ lemma ⟩
  (B → Is-proposition (Higher.Lens.set ⁻¹ s))  ↝⟨ [codomain-inhabited→proposition]→proposition-for-higher univ ⟩□
  Is-proposition (Higher.Lens.set ⁻¹ s)        □
  where
  lemma : B → Is-proposition (Higher.Lens.set ⁻¹ s)
  lemma b (l₁ , set-l₁≡s) (l₂ , set-l₂≡s) = Σ-≡,≡→≡
    lemma₁
    (subst (λ l → set l ≡ s) lemma₁ set-l₁≡s                     ≡⟨ subst-∘ _ _ _ ⟩
     subst (_≡ s) (cong set lemma₁) set-l₁≡s                     ≡⟨ subst-trans-sym ⟩
     trans (sym (cong set lemma₁)) set-l₁≡s                      ≡⟨ cong (λ eq → trans (sym eq) set-l₁≡s) lemma₂ ⟩
     trans (sym (trans set-l₁≡s (sym set-l₂≡s))) set-l₁≡s        ≡⟨ cong (λ eq → trans eq set-l₁≡s) $ sym-trans _ _ ⟩
     trans (trans (sym (sym set-l₂≡s)) (sym set-l₁≡s)) set-l₁≡s  ≡⟨ trans-[trans-sym]- _ _ ⟩
     sym (sym set-l₂≡s)                                          ≡⟨ sym-sym _ ⟩∎
     set-l₂≡s                                                    ∎)
    where
    open Higher.Lens

    lemma′ =
      lenses-equal-if-setters-equal l₁ l₂ b
        (set l₁  ≡⟨ set-l₁≡s ⟩
         s       ≡⟨ sym set-l₂≡s ⟩∎
         set l₂  ∎)

    lemma₁ = proj₁ lemma′
    lemma₂ = proj₂ lemma′

-- If a certain variant of Higher.lenses-equal-if-setters-equal can be
-- proved, then lenses with equal setters are equal (assuming
-- univalence).

lenses-equal-if-setters-equal→lenses-equal-if-setters-equal :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  ((l₁ l₂ : Higher.Lens A B) →
   B →
   (s : Higher.Lens.set l₁ ≡ Higher.Lens.set l₂) →
   ∃ λ (l : l₁ ≡ l₂) → cong Higher.Lens.set l ≡ s) →
  (l₁ l₂ : Higher.Lens A B) →
  Higher.Lens.set l₁ ≡ Higher.Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal→lenses-equal-if-setters-equal
  univ lenses-equal-if-setters-equal l₁ l₂ s =
  cong proj₁ (
    (l₁ , s)       ≡⟨ lenses-equal-if-setters-equal→set⁻¹-proposition
                        univ lenses-equal-if-setters-equal (Higher.Lens.set l₂) _ _ ⟩∎
    (l₂ , refl _)  ∎)
