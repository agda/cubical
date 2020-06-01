{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

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
-- ∥ X ∥ ── populatedBy ─→ Populated X
-- Populated X ── notEmptyPopulated ─→ NonEmpty X

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∣_∣) public

populatedBy : ∥ A ∥ → Populated A
populatedBy {A = A} a (f , fIsConst) = h a where
  h : ∥ A ∥ → Fixpoint f
  h ∣ a ∣ = f a , fIsConst (f a) a
  h (squash a b i) = 2-Constant→isPropFixpoint f fIsConst (h a) (h b) i

notEmptyPopulated : Populated A → NonEmpty A
notEmptyPopulated {A = A} pop u = u (fixpoint (pop (h , hIsConst))) where
  h : A → A
  h a = ⊥.elim (u a)
  hIsConst : ∀ x y → h x ≡ h y
  hIsConst x y i = ⊥.elim (isProp⊥ (u x) (u y) i)

-- these implications induce the following for different kinds of stability
Stable→PStable : Stable A → PStable A
Stable→PStable st = st ∘ notEmptyPopulated

PStable→HStable : PStable A → HStable A
PStable→HStable pst = pst ∘ populatedBy

-- Although HStable and Collapsible are not properties, their path versions, HStable≡ and Collapsible≡, are.
-- Nevertheless they are logically equivalent
HStable→Collapsible : HStable A → Collapsible A
HStable→Collapsible {A = A} hst = h , hIsConst where
  h : A → A
  h p = hst ∣ p ∣
  hIsConst : 2-Constant h
  hIsConst p q i = hst (squash ∣ p ∣ ∣ q ∣ i)

Collapsible→HStable : Collapsible A → HStable A
Collapsible→HStable f x = fixpoint (populatedBy x f)

HStable≡→Collapsible≡ : HStable≡ A → Collapsible≡ A
HStable≡→Collapsible≡ st x y = HStable→Collapsible (st x y)

Collapsible≡→HStable≡ : Collapsible≡ A → HStable≡ A
Collapsible≡→HStable≡ col x y = Collapsible→HStable (col x y)

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

HStable≡→isSet : HStable≡ A → isSet A
HStable≡→isSet = Collapsible≡→isSet ∘ HStable≡→Collapsible≡

isSet→HStable≡ : isSet A → HStable≡ A
isSet→HStable≡ setA x y = extract where
  extract : ∥ x ≡ y ∥ → x ≡ y
  extract ∣ p ∣ = p
  extract (squash p q i) = setA x y (extract p) (extract q) i

-- by the above two more sufficient conditions to inhibit isSet A are given
PStable≡→isSet : PStable≡ A → isSet A
PStable≡→isSet st = HStable≡→isSet (λ x y → PStable→HStable (st x y))

Stable≡→isSet : Stable≡ A → isSet A
Stable≡→isSet st = PStable≡→isSet (λ x y → Stable→PStable (st x y))
