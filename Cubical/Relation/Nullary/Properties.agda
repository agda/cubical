{-

Properties of nullary relations, i.e. structures on types.

Includes several results from [Notions of Anonymous Existence in Martin-Löf Type Theory](https://lmcs.episciences.org/3217)
by Altenkirch, Coquand, Escardo, Kraus.

-}
module Cubical.Relation.Nullary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Fixpoint

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sum.Base

open import Cubical.Relation.Nullary.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    P : A -> Type ℓ

-- Functions with a section preserve discreteness.
sectionDiscrete
  : (f : A → B) (g : B → A) → section f g → Discrete A → Discrete B
sectionDiscrete f g sect dA x y with dA (g x) (g y)
... | yes p = yes (sym (sect x) ∙∙ cong f p ∙∙ sect y)
... | no ¬p = no (λ p → ¬p (cong g p))

isoPresDiscrete : Iso A B → Discrete A → Discrete B
isoPresDiscrete e = sectionDiscrete fun inv rightInv
  where open Iso e

EquivPresDiscrete : ∀ {ℓ ℓ'}{A : Type ℓ} {B : Type ℓ'} → A ≃ B
               → Discrete A → Discrete B
EquivPresDiscrete e = isoPresDiscrete (equivToIso e)

isProp¬ : (A : Type ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

Stable¬ : Stable (¬ A)
Stable¬ ¬¬¬a a = ¬¬¬a ¬¬a
  where
  ¬¬a = λ ¬a → ¬a a

StableΠ : (∀ x → Stable (P x)) -> Stable (∀ x → P x)
StableΠ Ps e x = Ps x λ k → e λ f → k (f x)

Stable→ : Stable B → Stable (A → B)
Stable→ Bs = StableΠ (λ _ → Bs)

Stable× : Stable A -> Stable B -> Stable (A × B)
Stable× As Bs e = λ where
  .fst → As λ k → e (k ∘ fst)
  .snd → Bs λ k → e (k ∘ snd)

StableΣ : ∀ {A : Type ℓ} {P : A → Type ℓ'} →
  Stable A → isProp A → ((a : A) → Stable (P a)) → Stable (Σ A P)
StableΣ {P = P} As Aprop Ps e =
  let a = (As (λ notA → e (λ (a , _) → notA a))) in
  a ,
  Ps a λ notPa → e (λ (a' , p) → notPa (subst P (Aprop a' a) p))

fromYes : A → Dec A → A
fromYes _ (yes a) = a
fromYes a (no _) = a

discreteDec : (Adis : Discrete A) → Discrete (Dec A)
discreteDec Adis (yes p) (yes p') = decideYes (Adis p p') -- TODO: monad would simply stuff
  where
    decideYes : Dec (p ≡ p') → Dec (yes p ≡ yes p')
    decideYes (yes eq) = yes (cong yes eq)
    decideYes (no ¬eq) = no λ eq → ¬eq (cong (fromYes p) eq)
discreteDec Adis (yes p) (no ¬p) = ⊥.rec (¬p p)
discreteDec Adis (no ¬p) (yes p) = ⊥.rec (¬p p)
discreteDec {A = A} Adis (no ¬p) (no ¬p') = yes (cong no (isProp¬ A ¬p ¬p'))

isPropDec : (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') = cong yes (Aprop a a')
isPropDec Aprop (yes a) (no ¬a) = ⊥.rec (¬a a)
isPropDec Aprop (no ¬a) (yes a) = ⊥.rec (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') = cong no (isProp¬ A ¬a ¬a')

mapDec : ∀ {B : Type ℓ} → (A → B) → (¬ A → ¬ B) → Dec A → Dec B
mapDec f _ (yes p) = yes (f p)
mapDec _ f (no ¬p) = no (f ¬p)

EquivPresDec : ∀ {ℓ ℓ'}{A : Type ℓ} {B : Type ℓ'} → A ≃ B
          → Dec A → Dec B
EquivPresDec p = mapDec (p .fst) (λ f → f ∘ invEq p)

¬→¬∥∥ : ¬ A → ¬ ∥ A ∥₁
¬→¬∥∥ ¬p ∣ a ∣₁ = ¬p a
¬→¬∥∥ ¬p (squash₁ x y i) = isProp⊥ (¬→¬∥∥ ¬p x) (¬→¬∥∥ ¬p y) i

Dec∥∥ : Dec A → Dec ∥ A ∥₁
Dec∥∥ = mapDec ∣_∣₁ ¬→¬∥∥

-- we have the following implications
-- X ── ∣_∣ ─→ ∥ X ∥
-- ∥ X ∥ ── populatedBy ─→ ⟪ X ⟫
-- ⟪ X ⟫ ── notEmptyPopulated ─→ NonEmpty X

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base

populatedBy : ∥ A ∥₁ → ⟪ A ⟫
populatedBy {A = A} a (f , fIsConst) = h a where
  h : ∥ A ∥₁ → Fixpoint f
  h ∣ a ∣₁ = f a , fIsConst (f a) a
  h (squash₁ a b i) = 2-Constant→isPropFixpoint f fIsConst (h a) (h b) i

notEmptyPopulated : ⟪ A ⟫ → NonEmpty A
notEmptyPopulated {A = A} pop u = u (fixpoint (pop (h , hIsConst))) where
  h : A → A
  h a = ⊥.elim (u a)
  hIsConst : ∀ x y → h x ≡ h y
  hIsConst x y i = ⊥.elim (isProp⊥ (u x) (u y) i)

-- these implications induce the following for different kinds of stability, gradually weakening the assumption
Dec→Stable : Dec A → Stable A
Dec→Stable (yes x) = λ _ → x
Dec→Stable (no x) = λ f → ⊥.elim (f x)

Stable→PStable : Stable A → PStable A
Stable→PStable st = st ∘ notEmptyPopulated

PStable→SplitSupport : PStable A → SplitSupport A
PStable→SplitSupport pst = pst ∘ populatedBy

-- Although SplitSupport and Collapsible are not properties, their path versions, HSeparated and Collapsible≡, are.
-- Nevertheless they are logically equivalent
SplitSupport→Collapsible : SplitSupport A → Collapsible A
SplitSupport→Collapsible {A = A} hst = h , hIsConst where
  h : A → A
  h p = hst ∣ p ∣₁
  hIsConst : 2-Constant h
  hIsConst p q i = hst (squash₁ ∣ p ∣₁ ∣ q ∣₁ i)

Collapsible→SplitSupport : Collapsible A → SplitSupport A
Collapsible→SplitSupport f x = fixpoint (populatedBy x f)

HSeparated→Collapsible≡ : HSeparated A → Collapsible≡ A
HSeparated→Collapsible≡ hst x y = SplitSupport→Collapsible (hst x y)

Collapsible≡→HSeparated : Collapsible≡ A → HSeparated A
Collapsible≡→HSeparated col x y = Collapsible→SplitSupport (col x y)

-- stability of path space under truncation or path collapsability are necessary and sufficient properties
-- for a a type to be a set.
Collapsible≡→isSet : Collapsible≡ A → isSet A
Collapsible≡→isSet {A = A} col a b p q = p≡q where
  f : (x : A) → a ≡ x → a ≡ x
  f x = col a x .fst
  fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
  fIsConst x = col a x .snd
  rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
  rem p j = f (p j) (λ i → p (i ∧ j))
  p≡q : p ≡ q
  p≡q j i = hcomp (λ k → λ { (i = i0) → f a refl k
                           ; (i = i1) → fIsConst b p q j k
                           ; (j = i0) → rem p i k
                           ; (j = i1) → rem q i k }) a

HSeparated→isSet : HSeparated A → isSet A
HSeparated→isSet = Collapsible≡→isSet ∘ HSeparated→Collapsible≡

isSet→HSeparated : isSet A → HSeparated A
isSet→HSeparated setA x y = extract where
  extract : ∥ x ≡ y ∥₁ → x ≡ y
  extract ∣ p ∣₁ = p
  extract (squash₁ p q i) = setA x y (extract p) (extract q) i

-- by the above more sufficient conditions to inhibit isSet A are given
PStable≡→HSeparated : PStable≡ A → HSeparated A
PStable≡→HSeparated pst x y = PStable→SplitSupport (pst x y)

PStable≡→isSet : PStable≡ A → isSet A
PStable≡→isSet = HSeparated→isSet ∘ PStable≡→HSeparated

Separated→PStable≡ : Separated A → PStable≡ A
Separated→PStable≡ st x y = Stable→PStable (st x y)

Separated→isSet : Separated A → isSet A
Separated→isSet = PStable≡→isSet ∘ Separated→PStable≡

SeparatedΠ : (∀ x → Separated (P x)) -> Separated ((x : A) -> P x)
SeparatedΠ Ps f g e i x = Ps x (f x) (g x) (λ k → e (k ∘ cong (λ f → f x))) i

Separated→ : Separated B -> Separated (A → B)
Separated→ Bs = SeparatedΠ (λ _ → Bs)

Separated× : Separated A -> Separated B -> Separated (A × B)
Separated× As Bs p q e i = λ where
  .fst → As (fst p) (fst q) (λ k → e λ r → k (cong fst r)) i
  .snd → Bs (snd p) (snd q) (λ k → e λ r → k (cong snd r)) i

-- Proof of Hedberg's theorem: a type with decidable equality is an h-set
Discrete→Separated : Discrete A → Separated A
Discrete→Separated d x y = Dec→Stable (d x y)

Discrete→isSet : Discrete A → isSet A
Discrete→isSet = Separated→isSet ∘ Discrete→Separated

≡no : ∀ {A : Type ℓ} x y → Path (Dec A) x (no y)
≡no (yes p) y = ⊥.rec (y p)
≡no (no ¬p) y i = no (isProp¬ _ ¬p y i)

inhabitedFibres? : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) → Type (ℓ-max ℓ ℓ')
inhabitedFibres? {A = A} {B = B} f =
  (y : B) → (Σ[ x ∈ A ] f x ≡ y) ⊎ ((x : A) → ¬ f x ≡ y)
