------------------------------------------------------------------------
-- Some code suggesting that types used in "programs" might not
-- necessarily be sets
------------------------------------------------------------------------

-- If lenses are only used in programs, and types used in programs are
-- always sets, then higher lenses might be pointless.

-- This module uses univalence without tracking such uses in the types
-- of functions.

{-# OPTIONS --cubical #-}

open import Equality.Path as P hiding (Is-proposition; Is-set)

module README.Not-a-set
  {e⁺} (eq : ∀ {a p} → Equality-with-paths a p e⁺) where

private
  open module D = Derived-definitions-and-properties eq
    using (Is-proposition; Is-set)

open import Equality.Path.Univalence
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
import Bijection D.equality-with-J as DB
import Bool equality-with-J as B
open import Equality.Decision-procedures equality-with-J
import Equality.Path.Isomorphisms eq as I
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
import H-level D.equality-with-J as H-level
open import H-level.Closure D.equality-with-J
open import Surjection D.equality-with-J using (_↠_)

private
  variable
    A B C : Type

------------------------------------------------------------------------
-- Dynamic types

-- Values of arbitrary type that can be turned into strings.

Printable : Type₁
Printable = ∃ λ (A : Type) → A × (A → String)

-- Printable is not a set.

¬-Printable-set : ¬ Is-set Printable
¬-Printable-set =
  Is-set Printable        ↝⟨ DB._↔_.to (I.H-level↔H-level 2) ⟩
  P.Is-set Printable      ↝⟨ (λ h → h _ _) ⟩
  refl ≡ q                ↝⟨ cong (cong proj₁) ⟩
  refl ≡ cong proj₁ q     ↝⟨ flip trans (proj₁-Σ-≡,≡→≡ {B = λ A → A × (A → String)} {y₁ = proj₂ x} _ refl) ⟩
  refl ≡ q′               ↝⟨ cong (λ eq → subst id eq (just true)) ⟩
  just true ≡ just false  ↝⟨ Bool.true≢false ∘ ⊎.cancel-inj₂ ⟩□
  ⊥                       □
  where
  x : Printable
  x = Maybe Bool , nothing , λ _ → ""

  q′ : Maybe Bool ≡ Maybe Bool
  q′ = ≃⇒≡ (F.id ⊎-cong Eq.↔⇒≃ B.swap)

  q : x ≡ x
  q = Σ-≡,≡→≡ q′ refl

------------------------------------------------------------------------
-- Streams

-- Streams, based on the definition given by Coutts et al. in "Stream
-- Fusion: From Lists to Streams to Nothing at All".

data Step (A S : Type) : Type where
  done  : Step A S
  yield : A → S → Step A S
  skip  : S → Step A S

Stream : Type → Type₁
Stream A = ∃ λ (S : Type) → (S → Step A S) × S

-- Stream A is not a set.

¬-Stream-set : ¬ Is-set (Stream A)
¬-Stream-set {A = A} =
  Is-set (Stream A)       ↝⟨ DB._↔_.to (I.H-level↔H-level 2) ⟩
  P.Is-set (Stream A)     ↝⟨ (λ h → h _ _) ⟩
  refl ≡ p                ↝⟨ cong (cong proj₁) ⟩
  refl ≡ cong proj₁ p     ↝⟨ flip trans (proj₁-Σ-≡,≡→≡ {B = F} {y₁ = proj₂ t} _ refl) ⟩
  refl ≡ q                ↝⟨ cong (λ eq → subst id eq (just true)) ⟩
  just true ≡ just false  ↝⟨ Bool.true≢false ∘ ⊎.cancel-inj₂ ⟩□
  ⊥                       □
  where
  F : Type → Type
  F S = (S → Step A S) × S

  t : Stream A
  t = Maybe Bool
    , const done
    , nothing

  q : Maybe Bool ≡ Maybe Bool
  q = ≃⇒≡ (F.id ⊎-cong Eq.↔⇒≃ B.swap)

  p : t ≡ t
  p = Σ-≡,≡→≡ q refl

-- Streams, with the added requirement that the state type must be a
-- set.

Streamˢ : Type → Type₁
Streamˢ A = ∃ λ (S : Type) → Is-set S × (S → Step A S) × S

-- Streamˢ A is not a set.

¬-Streamˢ-set : ¬ Is-set (Streamˢ A)
¬-Streamˢ-set {A = A} =
  Is-set (Streamˢ A)      ↝⟨ DB._↔_.to (I.H-level↔H-level 2) ⟩
  P.Is-set (Streamˢ A)    ↝⟨ (λ h → h _ _) ⟩
  refl ≡ p                ↝⟨ cong (cong proj₁) ⟩
  refl ≡ cong proj₁ p     ↝⟨ flip trans (proj₁-Σ-≡,≡→≡ {B = F} {y₁ = proj₂ t} _ refl) ⟩
  refl ≡ q                ↝⟨ cong (λ eq → subst id eq (inj₂ true)) ⟩
  just true ≡ just false  ↝⟨ Bool.true≢false ∘ ⊎.cancel-inj₂ ⟩□
  ⊥                       □
  where
  F : Type → Type
  F S = Is-set S × (S → Step A S) × S

  t : Streamˢ A
  t = Maybe Bool
    , Maybe-closure 0 Bool-set
    , const done
    , nothing

  q : Maybe Bool ≡ Maybe Bool
  q = ≃⇒≡ (F.id ⊎-cong Eq.↔⇒≃ B.swap)

  p : t ≡ t
  p =
    Σ-≡,≡→≡ q $
    cong₂ _,_
      (DB._↔_.to D.≡↔≡ (H-level-propositional I.ext 2 _ _))
      refl

------------------------------------------------------------------------
-- Some deep embeddings

-- The module is parametrised by a predicate P that satisfies some
-- properties.

module Tm-with-predicate
  (P : Type → Type)
  (P-Maybe-Bool : P (Maybe Bool))
  (P-Maybe-Bool-propositional : Is-proposition (P (Maybe Bool)))
  where

  -- A deep embedding of a simple programming language. Note the
  -- requirement that P B must hold.

  data Tm (A : Type) : Type₁ where
    literal : A → Tm A
    map     : {B : Type} → P B → Tm (B → A) → Tm B → Tm A

  -- An unfolding lemma.

  Tm≃ : Tm A ≃ (A ⊎ ∃ λ (B : Type) → P B × Tm (B → A) × Tm B)
  Tm≃ = Eq.↔→≃
    (λ where
       (literal x) → inj₁ x
       (map p f t) → inj₂ (_ , p , f , t))
    [ literal , (λ (_ , p , f , t) → map p f t) ]
    [ (λ _ → refl) , (λ _ → refl) ]
    (λ where
       (literal _) → refl
       (map _ _ _) → refl)

  -- If A is inhabited, then Tm A is not a set.

  ¬-Tm-set : A → ¬ Is-set (Tm A)
  ¬-Tm-set {A = A} a =
    Is-set (Tm A)           ↝⟨ DB._↔_.to (I.H-level↔H-level 2) ⟩
    P.Is-set (Tm A)         ↝⟨ (λ h → h _ _) ⟩
    refl ≡ p                ↝⟨ cong map-injective ⟩
    refl ≡ map-injective p  ↝⟨ flip trans lemma ⟩
    refl ≡ p₁               ↝⟨ cong (λ eq → subst id eq (just true)) ⟩
    just true ≡ just false  ↝⟨ Bool.true≢false ∘ ⊎.cancel-inj₂ ⟩□
    ⊥                       □
    where
    F : Type → Type₁
    F B = P B × Tm (B → A) × Tm B

    t : Tm A
    t = map P-Maybe-Bool (literal λ _ → a) (literal nothing)

    t′ : F (Maybe Bool)
    t′ = P-Maybe-Bool
       , literal (const a)
       , literal nothing

    p₁ : Maybe Bool ≡ Maybe Bool
    p₁ = ≃⇒≡ (F.id ⊎-cong Eq.↔⇒≃ B.swap)

    p₂ : subst F p₁ t′ ≡ t′
    p₂ =
      cong₂ _,_
        (DB._↔_.to (I.H-level↔H-level 1) P-Maybe-Bool-propositional _ _)
        (cong (_, literal nothing)
           (subst (λ B → Tm (B → A)) p₁ (literal (const a))  ≡⟨⟩
            literal (subst (λ B → B → A) p₁ (const a))       ≡⟨ (cong literal $ ⟨ext⟩ λ b → subst-→-domain id p₁ {u = b}) ⟩∎
            literal (const a)                                ∎))

    p : t ≡ t
    p = _≃_.to (Eq.≃-≡ Tm≃) $ cong inj₂ $ Σ-≡,≡→≡ p₁ p₂

    map-injective :
      {p : P B} {f : Tm (B → C)} {t : Tm B} →
      map p f t ≡ map p f t → B ≡ B
    map-injective {B = B} {p = p} {f = f} {t = t} =
      map p f t ≡ map p f t                            ↔⟨ inverse $ Eq.≃-≡ Tm≃ ⟩
      _≃_.to Tm≃ (map p f t) ≡ _≃_.to Tm≃ (map p f t)  ↔⟨⟩
      inj₂ (B , p , f , t) ≡ inj₂ (B , p , f , t)      ↔⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
      (B , p , f , t) ≡ (B , p , f , t)                ↝⟨ cong proj₁ ⟩□
      B ≡ B                                            □

    lemma : map-injective p ≡ p₁
    lemma =
      map-injective p                                ≡⟨⟩

      cong proj₁ (⊎.cancel-inj₂
        (_≃_.from (Eq.≃-≡ Tm≃) (_≃_.to (Eq.≃-≡ Tm≃)
           (cong inj₂ (Σ-≡,≡→≡ p₁ p₂)))))            ≡⟨ cong (cong proj₁ ∘ ⊎.cancel-inj₂) $
                                                        _≃_.left-inverse-of (Eq.≃-≡ Tm≃) (cong inj₂ (Σ-≡,≡→≡ p₁ p₂)) ⟩
      cong (proj₁ {B = F})
        (⊎.cancel-inj₂ {A = ⊤ ⊎ ⊤} (cong inj₂
           (Σ-≡,≡→≡ {p₁ = _ , t′} p₁ p₂)))           ≡⟨ cong (cong (proj₁ {B = F})) $
                                                        _↔_.left-inverse-of (Bijection.≡↔inj₂≡inj₂ {A = ⊤ ⊎ ⊤}) (Σ-≡,≡→≡ {p₁ = _ , t′} _ refl) ⟩
      cong (proj₁ {B = F})
        (Σ-≡,≡→≡ {p₁ = _ , t′} p₁ p₂)                ≡⟨ proj₁-Σ-≡,≡→≡ {B = F} {y₁ = t′} _ refl ⟩∎

      p₁                                             ∎

-- A deep embedding of a simple programming language.

data Tm (A : Type) : Type₁ where
  literal : A → Tm A
  map     : {B : Type} → Tm (B → A) → Tm B → Tm A

-- If A is inhabited, then Tm A is not a set.

¬-Tm-set : A → ¬ Is-set (Tm A)
¬-Tm-set {A = A} a =
  Is-set (Tm A)    ↝⟨ H-level.respects-surjection Tm↠Tm 2 ⟩
  Is-set (T.Tm A)  ↝⟨ T.¬-Tm-set a ⟩□
  ⊥                □
  where
  module T = Tm-with-predicate (λ _ → ⊤) _ (λ _ _ → D.refl _)

  to : Tm B → T.Tm B
  to (literal x) = T.literal x
  to (map f t)   = T.map _ (to f) (to t)

  from : T.Tm B → Tm B
  from (T.literal x) = literal x
  from (T.map _ f t) = map (from f) (from t)

  to-from : (t : T.Tm B) → to (from t) D.≡ t
  to-from (T.literal x) = D.refl _
  to-from (T.map _ f t) = D.cong₂ (T.map _) (to-from f) (to-from t)

  Tm↠Tm : Tm B ↠ T.Tm B
  Tm↠Tm = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to-from
    }

-- A deep embedding of a simple programming language. Note the
-- requirement that "B" must be a set.

data Tmˢ (A : Type) : Type₁ where
  literal : A → Tmˢ A
  map     : {B : Type} → Is-set B → Tmˢ (B → A) → Tmˢ B → Tmˢ A

-- If A is inhabited, then Tmˢ A is not a set.

¬-Tmˢ-set : A → ¬ Is-set (Tmˢ A)
¬-Tmˢ-set {A = A} a =
  Is-set (Tmˢ A)   ↝⟨ H-level.respects-surjection Tmˢ↠Tm 2 ⟩
  Is-set (T.Tm A)  ↝⟨ T.¬-Tm-set a ⟩□
  ⊥                □
  where
  module T = Tm-with-predicate
    Is-set
    (Maybe-closure 0 Bool-set)
    (H-level-propositional I.ext 2)

  to : Tmˢ B → T.Tm B
  to (literal x) = T.literal x
  to (map s f t) = T.map s (to f) (to t)

  from : T.Tm B → Tmˢ B
  from (T.literal x) = literal x
  from (T.map s f t) = map s (from f) (from t)

  to-from : (t : T.Tm B) → to (from t) D.≡ t
  to-from (T.literal x) = D.refl _
  to-from (T.map s f t) = D.cong₂ (T.map s) (to-from f) (to-from t)

  Tmˢ↠Tm : Tmˢ B ↠ T.Tm B
  Tmˢ↠Tm = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to-from
    }
