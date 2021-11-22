{-# OPTIONS --safe #-}
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

open import Cubical.Relation.Nullary.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

IsoPresDiscrete : ∀ {ℓ ℓ'}{A : Type ℓ} {B : Type ℓ'} → Iso A B
               → Discrete A → Discrete B
IsoPresDiscrete e dA x y with dA (Iso.inv e x) (Iso.inv e y)
... | yes p = subst Dec (λ i → Iso.rightInv e x i ≡ Iso.rightInv e y i)
                        (yes (cong (Iso.fun e) p))
... | no p = subst Dec (λ i → Iso.rightInv e x i ≡ Iso.rightInv e y i)
                   (no λ q → p (sym (Iso.leftInv e (Iso.inv e x))
                     ∙∙ cong (Iso.inv e) q
                     ∙∙ Iso.leftInv e (Iso.inv e y)))

EquivPresDiscrete : ∀ {ℓ ℓ'}{A : Type ℓ} {B : Type ℓ'} → A ≃ B
               → Discrete A → Discrete B
EquivPresDiscrete e = IsoPresDiscrete (equivToIso e)

isProp¬ : (A : Type ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

Stable¬ : Stable (¬ A)
Stable¬ ¬¬¬a a = ¬¬¬a ¬¬a
  where
  ¬¬a = λ ¬a → ¬a a

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

-- we have the following implications
-- X ── ∣_∣ ─→ ∥ X ∥
-- ∥ X ∥ ── populatedBy ─→ ⟪ X ⟫
-- ⟪ X ⟫ ── notEmptyPopulated ─→ NonEmpty X

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∣_∣) public

populatedBy : ∥ A ∥ → ⟪ A ⟫
populatedBy {A = A} a (f , fIsConst) = h a where
  h : ∥ A ∥ → Fixpoint f
  h ∣ a ∣ = f a , fIsConst (f a) a
  h (squash a b i) = 2-Constant→isPropFixpoint f fIsConst (h a) (h b) i

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
  h p = hst ∣ p ∣
  hIsConst : 2-Constant h
  hIsConst p q i = hst (squash ∣ p ∣ ∣ q ∣ i)

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
  extract : ∥ x ≡ y ∥ → x ≡ y
  extract ∣ p ∣ = p
  extract (squash p q i) = setA x y (extract p) (extract q) i

-- by the above more sufficient conditions to inhibit isSet A are given
PStable≡→HSeparated : PStable≡ A → HSeparated A
PStable≡→HSeparated pst x y = PStable→SplitSupport (pst x y)

PStable≡→isSet : PStable≡ A → isSet A
PStable≡→isSet = HSeparated→isSet ∘ PStable≡→HSeparated

Separated→PStable≡ : Separated A → PStable≡ A
Separated→PStable≡ st x y = Stable→PStable (st x y)

Separated→isSet : Separated A → isSet A
Separated→isSet = PStable≡→isSet ∘ Separated→PStable≡

-- Proof of Hedberg's theorem: a type with decidable equality is an h-set
Discrete→Separated : Discrete A → Separated A
Discrete→Separated d x y = Dec→Stable (d x y)

Discrete→isSet : Discrete A → isSet A
Discrete→isSet = Separated→isSet ∘ Discrete→Separated
