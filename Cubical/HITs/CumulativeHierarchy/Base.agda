{-# OPTIONS --cubical --no-import-sorts --safe #-}
{-
This file models "ZF - powerset" in cubical agda, via a cumulative hierarchy, in the sense given
in the HoTT book §10.5 "The cumulative hierarchy".

A great amount of inspiration is taken from the Coq implementations found in
Jérémy Ledent, Modeling set theory in homotopy type theory, code of which can be found online at
https://github.com/jledent/vset
-}

module Cubical.HITs.CumulativeHierarchy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic as L hiding (_∈_; _⊆_; ⊆-refl)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E hiding (elim)
open import Cubical.HITs.PropositionalTruncation as P hiding (elim; elim2)
open import Cubical.HITs.Pushout as Pu
open import Cubical.HITs.SetQuotients as Q using (_/_; setQuotUniversal; eq/; squash/)

import Cubical.HITs.PropositionalTruncation.Monad as PropMonad

private
  variable
    ℓ ℓ' : Level

------------
-- Start implementation of V
------------

-- set up the basic hierarchy definition and _∈_ as recursive, higher inductive types
data V (ℓ : Level) : Type (ℓ-suc ℓ)
_∈_ : (S T : V ℓ) → hProp (ℓ-suc ℓ)

eqImage : {X Y : Type ℓ} (ix : X → V ℓ) (iy : Y → V ℓ) → Type (ℓ-suc ℓ)
eqImage {X = X} {Y = Y} ix iy = (∀ (a : X) → ∃[ b ∈ Y ] iy b ≡ ix a) ⊓′ (∀ (b : Y) → ∃[ a ∈ X ] ix a ≡ iy b)

data V ℓ where
  sett : (X : Type ℓ) → (X → V ℓ) → V ℓ
  seteq : (X Y : Type ℓ) (ix : X → V ℓ) (iy : Y → V ℓ) (eq : eqImage ix iy) → sett X ix ≡ sett Y iy
  setIsSet : isSet (V ℓ)

A ∈ sett X ix = ∥ Σ[ i ∈ X ] (ix i ≡ A) ∥ₚ
A ∈ seteq X Y ix iy (f , g) i =
  ⇔toPath {P = A ∈ sett X ix} {Q = A ∈ sett Y iy}
    (λ ax → do (x , xa) ← ax ; (y , ya) ← f x ; ∣ y , ya ∙ xa ∣)
    (λ ay → do (y , ya) ← ay ; (x , xa) ← g y ; ∣ x , xa ∙ ya ∣) i
  where open PropMonad
A ∈ setIsSet a b p q i j = isSetHProp (A ∈ a) (A ∈ b) (λ j → A ∈ p j) (λ j → A ∈ q j) i j
{-# INLINE _∈_ #-}

-- a provisional definition of equality, we will show that this is actually equivalent to an hProp in universe ℓ
infix 4 _≡ₛ_
_≡ₛ_ : (a b : V ℓ) → hProp (ℓ-suc ℓ)
_≡ₛ_ a b = (a ≡ b) , setIsSet a b

-- setup a general eliminator into h-sets
record ElimSet {Z : (s : V ℓ) → Type ℓ'} (isSetZ : ∀ s → isSet (Z s)) : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    ElimSett : (X : Type ℓ) (ix : X → V ℓ)
             -- ^ the structural parts of the set
             → (rec : ∀ x → Z (ix x))
             -- ^ a recursor into the elements
             → Z (sett X ix)
    ElimEq   : (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) (eq : eqImage ix₁ ix₂)
             -- ^ the structural parts of the seteq path
             → (rec₁ : ∀ x₁ → Z (ix₁ x₁)) (rec₂ : ∀ x₂ → Z (ix₂ x₂))
             -- ^ recursors into the elements
             → ((x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → Z (p i)) (rec₂ x₂) (rec₁ x₁))
             → ((x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → Z (p i)) (rec₁ x₁) (rec₂ x₂))
             -- ^ proofs that the recursors have equal images
             → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i)) (ElimSett X₁ ix₁ rec₁) (ElimSett X₂ ix₂ rec₂)

module _ {Z : (s : V ℓ) → Type ℓ'} {isSetZ : ∀ s → isSet (Z s)} (E : ElimSet isSetZ) where
  open ElimSet E
  elim : (s : V ℓ) → Z s
  elim (sett X ix) = ElimSett X ix (elim ∘ ix)
  elim (seteq X₁ X₂ ix₁ ix₂ eq i) = ElimEq X₁ X₂ ix₁ ix₂ eq (elim ∘ ix₁) (elim ∘ ix₂) rec₁→₂ rec₂→₁ i where
    rec₁→₂ : (x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → Z (p i)) (elim (ix₂ x₂)) (elim (ix₁ x₁))
    rec₂→₁ : (x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → Z (p i)) (elim (ix₁ x₁)) (elim (ix₂ x₂))

    rec₁→₂ x₁ = localRec₁ (eq .fst x₁) where
      localRec₁ : ∃[ x₂ ∈ X₂ ] (ix₂ x₂ ≡ ix₁ x₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → Z (p i)) (elim (ix₂ x₂)) (elim (ix₁ x₁))
      localRec₁ ∣ x₂ , xx ∣ = ∣ x₂ , xx , (λ i → elim (xx i)) ∣
      localRec₁ (squash x y i) = squash (localRec₁ x) (localRec₁ y) i
    rec₂→₁ x₂ = localRec₂ (eq .snd x₂) where
      localRec₂ : ∃[ x₁ ∈ X₁ ] (ix₁ x₁ ≡ ix₂ x₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → Z (p i)) (elim (ix₁ x₁)) (elim (ix₂ x₂))
      localRec₂ ∣ x₁ , xx ∣ = ∣ x₁ , xx , (λ i → elim (xx i)) ∣
      localRec₂ (squash x y i) = squash (localRec₂ x) (localRec₂ y) i
  elim (setIsSet S T x y i j) = isProp→PathP propPathP (cong elim x) (cong elim y) i j where
    propPathP : (i : I) → isProp (PathP (λ j → Z (setIsSet S T x y i j)) (elim S) (elim T))
    propPathP _ = subst isProp (sym (PathP≡Path _ _ _)) (isSetZ _ _ _)

-- eliminator into propositions
elimProp : {Z : (s : V ℓ) → Type ℓ'} (isPropZ : ∀ s → isProp (Z s))
         → ((X : Type ℓ) → (ix : X → V ℓ) → (∀ x → Z (ix x)) → Z (sett X ix))
         → (s : V ℓ) → Z s
elimProp isPropZ algz (sett X ix) = algz X ix (λ x → elimProp isPropZ algz (ix x))
elimProp isPropZ algz (seteq X Y ix iy eq i) =
  isProp→PathP (λ i → isPropZ (seteq X Y ix iy eq i))
               (algz X ix (elimProp isPropZ algz ∘ ix))
               (algz Y iy (elimProp isPropZ algz ∘ iy)) i
elimProp isPropZ algz (setIsSet S T x y i j) =
  isProp→SquareP (λ i j → isPropZ (setIsSet S T x y i j))
                 (λ _ → elimProp isPropZ algz S)
                 (λ _ → elimProp isPropZ algz T)
                 (cong (elimProp isPropZ algz) x)
                 (cong (elimProp isPropZ algz) y) i j

-- eliminator for two sets at once
record Elim2Set {Z : (s t : V ℓ) → Type ℓ'} (isSetZ : ∀ s t → isSet (Z s t)) : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    ElimSett2 : (X : Type ℓ) (ix : X → V ℓ) (Y : Type ℓ) (iy : Y → V ℓ)
              -- ^ the structural parts of the set
              → (rec : ∀ x y → Z (ix x) (iy y))
              -- ^ a recursor into the elements
              → Z (sett X ix) (sett Y iy)
    -- path when the the first argument deforms along seteq and the second argument is held constant
    ElimEqFst : (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) → (eq : eqImage ix₁ ix₂) → (Y : Type ℓ) (iy : Y → V ℓ)
              -- ^ the structural parts of the seteq path
              → (rec₁ : ∀ x₁ y → Z (ix₁ x₁) (iy y)) (rec₂ : ∀ x₂ y → Z (ix₂ x₂) (iy y))
              -- ^ recursors into the elements
              → (rec₁→₂ : (x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₂ x₂ y) (λ y → rec₁ x₁ y))
              → (rec₂→₁ : (x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₁ x₁ y) (λ y → rec₂ x₂ y))
              -- ^ proofs that the recursors have equal images
              → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) (sett Y iy)) (ElimSett2 X₁ ix₁ Y iy rec₁) (ElimSett2 X₂ ix₂ Y iy rec₂)
    -- path when the the second argument deforms along seteq and the first argument is held constant
    ElimEqSnd : (X : Type ℓ) (ix : X → V ℓ) → (Y₁ Y₂ : Type ℓ) (iy₁ : Y₁ → V ℓ) (iy₂ : Y₂ → V ℓ) → (eq : eqImage iy₁ iy₂)
              -- ^ the structural parts of the seteq path
              → (rec₁ : ∀ x y₁ → Z (ix x) (iy₁ y₁)) (rec₂ : ∀ x y₂ → Z (ix x) (iy₂ y₂))
              -- ^ recursors into the elements
              → (rec₁→₂ : (y₁ : Y₁) → ∃[ y₂ ∈ Y₂ ] Σ[ p ∈ (iy₂ y₂ ≡ iy₁ y₁) ] PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec₂ x y₂) (λ x → rec₁ x y₁))
              → (rec₂→₁ : (y₂ : Y₂) → ∃[ y₁ ∈ Y₁ ] Σ[ p ∈ (iy₁ y₁ ≡ iy₂ y₂) ] PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec₁ x y₁) (λ x → rec₂ x y₂))
              -- ^ proofs that the recursors have equal images
              → PathP (λ i → Z (sett X ix) (seteq Y₁ Y₂ iy₁ iy₂ eq i)) (ElimSett2 X ix Y₁ iy₁ rec₁) (ElimSett2 X ix Y₂ iy₂ rec₂)

module _ {Z : (s t : V ℓ) → Type ℓ'} {isSetZ : ∀ s t → isSet (Z s t)} (E : Elim2Set isSetZ) where
  open Elim2Set E
  open ElimSet

  elim2 : (s t : V ℓ) → Z s t
  elim2 = elim pElim where
    open PropMonad

    isSetPElim : ∀ s → isSet (∀ t → Z s t)
    isSetPElim s = isSetΠ (isSetZ s)

    eliminatorImplX : (X : Type ℓ) (ix : X → V ℓ)
                    → (rec : ∀ x y → Z (ix x) y)
                    → ElimSet (λ t → isSetZ (sett X ix) t)
    ElimSett (eliminatorImplX X ix rec) Y iy _ =
      ElimSett2 X ix Y iy (λ x → rec x ∘ iy)
    ElimEq (eliminatorImplX X ix rec) Y₁ Y₂ iy₁ iy₂ eq _ _ _ _ =
      ElimEqSnd X ix Y₁ Y₂ iy₁ iy₂ eq (λ x → rec x ∘ iy₁) (λ x → rec x ∘ iy₂) rec₁→₂ rec₂→₁
      where
      rec₁→₂ : (y₁ : Y₁) → ∃[ y₂ ∈ Y₂ ] Σ[ p ∈ (iy₂ y₂ ≡ iy₁ y₁) ] PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec x (iy₂ y₂)) (λ x → rec x (iy₁ y₁))
      rec₂→₁ : (y₂ : Y₂) → ∃[ y₁ ∈ Y₁ ] Σ[ p ∈ (iy₁ y₁ ≡ iy₂ y₂) ] PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec x (iy₁ y₁)) (λ x → rec x (iy₂ y₂))
      rec₁→₂ y₁ = do (y₂ , yy) ← fst eq y₁ ; ∣ y₂ , yy , (λ i x → rec x (yy i)) ∣
      rec₂→₁ y₂ = do (y₁ , yy) ← snd eq y₂ ; ∣ y₁ , yy , (λ i x → rec x (yy i)) ∣

    elimImplS : (X : Type ℓ) (ix : X → V ℓ)
              → (∀ x t₂ → Z (ix x) t₂)
              → (t : V ℓ) → Z (sett X ix) t
    elimImplS X ix rec = elim (eliminatorImplX X ix rec)

    elimImplSExt : (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) → (eq : eqImage ix₁ ix₂)
                 → (rec₁ : ∀ x₁ t₂ → Z (ix₁ x₁) t₂) (rec₂ : ∀ x₂ t₂ → Z (ix₂ x₂) t₂)
                 → ((x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → ∀ t → Z (p i) t) (rec₂ x₂) (rec₁ x₁))
                 → ((x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → ∀ t → Z (p i) t) (rec₁ x₁) (rec₂ x₂))
                 → (t : V ℓ) → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) t) (elimImplS X₁ ix₁ rec₁ t) (elimImplS X₂ ix₂ rec₂ t)
    elimImplSExt X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ =
      elimProp propPathP (λ Y iy _ → elimImplSExtT Y iy)
      where
      propPathP : (t : V ℓ) → isProp (PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) t) (elimImplS X₁ ix₁ rec₁ t) (elimImplS X₂ ix₂ rec₂ t))
      propPathP _ = subst isProp (sym (PathP≡Path _ _ _)) (isSetZ _ _ _ _)

      elimImplSExtT : (Y : Type ℓ) (iy : Y → V ℓ) → _ {- the appropriate path type -}
      elimImplSExtT Y iy =
        ElimEqFst X₁ X₂ ix₁ ix₂ eq Y iy (λ x₁ y → rec₁ x₁ (iy y)) (λ x₂ y → rec₂ x₂ (iy y)) rec₁→₂Impl rec₂→₁Impl
        where
        rec₁→₂Impl : (x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₂ x₂ (iy y)) (λ y → rec₁ x₁ (iy y))
        rec₂→₁Impl : (x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₁ x₁ (iy y)) (λ y → rec₂ x₂ (iy y))
        rec₁→₂Impl x₁ = do (x₂ , xx , rx) ← rec₁→₂ x₁ ; ∣ x₂ , xx , (λ i y → rx i (iy y)) ∣
        rec₂→₁Impl x₂ = do (x₁ , xx , rx) ← rec₂→₁ x₂ ; ∣ x₁ , xx , (λ i y → rx i (iy y)) ∣

    pElim : ElimSet isSetPElim
    ElimSett pElim = elimImplS
    ElimEq pElim X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ i t = elimImplSExt X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ t i

------------
-- "bisimulation"
-----------

-- bisimulation is needed to define a quotient in the correct universe when
-- implementing the map : V ℓ → Σ[ X : Type ℓ ] (X → V ℓ)
-- Quotienting by Path (V ℓ) or via eqImage would lead to X : Type (ℓ-suc ℓ)

_∼_ : (s t : V ℓ) → hProp ℓ
_∼_ = elim2 eliminator where
  goalProp : (X : Type ℓ) (ix : X → V ℓ) (Y : Type ℓ) (iy : Y → V ℓ) (rec : X → Y → hProp ℓ) → hProp ℓ
  goalProp X ix Y iy rec = (∀[ a ∶ X ] ∃[ b ∶ Y ] rec a b) ⊓ (∀[ b ∶ Y ] ∃[ a ∶ X ] rec a b)

  ⇔-swap : ∀ {P Q : Type ℓ} → P ⊓′ Q → Q ⊓′ P
  ⇔-swap (p , q) = (q , p)

  open PropMonad
  lemma : {X₁ X₂ Y : Type ℓ} {ix₁ : X₁ → V ℓ} {ix₂ : X₂ → V ℓ} (iy : Y → V ℓ) {rec₁ : X₁ → Y → hProp ℓ} {rec₂ : X₂ → Y → hProp ℓ}
        → (rec₁→₂ : (x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] rec₂ x₂ ≡ rec₁ x₁)
        → (rec₂→₁ : (x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] rec₁ x₁ ≡ rec₂ x₂)
        → [ goalProp X₁ ix₁ Y iy rec₁ ⇒ goalProp X₂ ix₂ Y iy rec₂ ]
  lemma _ rec₁→₂ rec₂→₁ (X₁→Y , Y→X₁) =
    (λ x₂ → do (x₁ , _ , xr₁) ← rec₂→₁ x₂
               (y , yr) ← X₁→Y x₁
               ∣ y , subst fst (λ i → xr₁ i y) yr ∣
    ) ,
    (λ y → do (x₁ , xr₁) ← Y→X₁ y
              (x₂ , _ , xr₂) ← rec₁→₂ x₁
              ∣ x₂ , subst fst (λ i → xr₂ (~ i) y) xr₁ ∣
    )

  open Elim2Set
  eliminator : Elim2Set (λ _ _ → isSetHProp)
  ElimSett2 eliminator = goalProp
  ElimEqSnd eliminator X ix Y₁ Y₂ iy₁ iy₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ =
    ⇔toPath (⇔-swap ∘ lemma ix rec₁→₂ rec₂→₁ ∘ ⇔-swap) (⇔-swap ∘ lemma ix rec₂→₁ rec₁→₂ ∘ ⇔-swap)
  ElimEqFst eliminator X₁ X₂ ix₁ ix₂ eq Y iy rec₁ rec₂ rec₁→₂ rec₂→₁ =
    ⇔toPath (lemma iy rec₁→₂ rec₂→₁) (lemma iy rec₂→₁ rec₁→₂)

∼refl : (a : V ℓ) → [ a ∼ a ]
∼refl = elimProp (λ a → isProp[] (a ∼ a)) (λ X ix rec → (λ x → ∣ x , rec x ∣) , (λ x → ∣ x , rec x ∣))

-- keep in mind that the left and right side here live in different universes
V∼-≡ : ∀ {a b : V ℓ} → [ a ∼ b ] ≃ (a ≡ b)
V∼-≡ {ℓ = ℓ} {a = a} {b = b} = isoToEquiv (iso from into (λ _ → setIsSet _ _ _ _) (λ _ → isProp[] (a ∼ b) _ _)) where
  open PropMonad

  eqImageXY : {X Y : Type ℓ} {ix : X → V ℓ} {iy : Y → V ℓ} → (∀ x y → [ ix x ∼ iy y ] → ix x ≡ iy y)
            → [ sett X ix ∼ sett Y iy ] → eqImage ix iy
  eqImageXY rec rel = (λ x → do (y , y∼x) ← fst rel x ; ∣ y , sym (rec _ _ y∼x) ∣)
                    , (λ y → do (x , x∼y) ← snd rel y ; ∣ x ,      rec _ _ x∼y  ∣)

  from : [ a ∼ b ] → a ≡ b
  from = elimProp propB (λ X ix rec → elimProp prop∼ λ Y iy _ → seteq X Y ix iy ∘ eqImageXY (λ x y → rec x (iy y))) a b where
    prop∼ : {a : V ℓ} → ∀ b → isProp ([ a ∼ b ] → a ≡ b)
    prop∼ {a} b = isPropΠ λ a∼b → setIsSet a b
    propB : (a : V ℓ) → isProp (∀ b → [ a ∼ b ] → a ≡ b)
    propB a = isPropΠ prop∼

  into : a ≡ b → [ a ∼ b ]
  into ab = subst (λ b → [ a ∼ b ]) ab (∼refl a)

_≊_ : (s t : V ℓ) → Type ℓ
s ≊ t = [ s ∼ t ]

------------
-- Monic presentation of sets
-----------

-- like fiber, but in a lower universe
repFiber : {A : Type ℓ} (f : A → V ℓ) (b : V ℓ) → Type ℓ
repFiber f b = Σ[ a ∈ _ ] f a ≊ b

repFiber≃fiber : {A : Type ℓ} (f : A → V ℓ) (b : V ℓ) → repFiber f b ≃ fiber f b
repFiber≃fiber f b = Σ-cong-equiv (idEquiv _) (λ a → V∼-≡ {a = f a} {b})

-- projecting out a representing type together with the embedding
MonicPresentation : (a : V ℓ) → Type (ℓ-suc ℓ)
MonicPresentation {ℓ} a =  Σ[ X ∈ Type ℓ ] Σ[ ix ∈ (X → V ℓ) ] (isEmbedding ix) × (a ≡ sett X ix)

isPropMonicPresentation : (a : V ℓ) → isProp (MonicPresentation a)
isPropMonicPresentation a (X₁ , ix₁ , isEmb₁ , p) (X₂ , ix₂ , isEmb₂ , q) = λ i → (X₁≡X₂ i , ix₁≡ix₂ i , isEmbix i , a≡sett i) where
  fib1 : (x₁ : X₁) → fiber ix₂ (ix₁ x₁)
  fib1 x₁ = Σx₂ where
    x₁∈X₂ : [ ix₁ x₁ ∈ sett X₂ ix₂ ]
    x₁∈X₂ = subst (λ A → [ ix₁ x₁ ∈ A ]) (sym p ∙ q) ∣ x₁ , refl ∣
    Σx₂ : fiber ix₂ (ix₁ x₁)
    Σx₂ = P.rec (isEmbedding→hasPropFibers isEmb₂ (ix₁ x₁)) (λ (x₂ , p) → (x₂ , p)) x₁∈X₂
  hom1 : X₁ → X₂
  hom1 x₁ = fst (fib1 x₁)

  fib2 : (x₂ : X₂) → fiber ix₁ (ix₂ x₂)
  fib2 x₂ = Σx₁ where
    x₂∈X₁ : [ ix₂ x₂ ∈ sett X₁ ix₁ ]
    x₂∈X₁ = subst (λ A → [ ix₂ x₂ ∈ A ]) (sym q ∙ p) ∣ x₂ , refl ∣
    Σx₁ : fiber ix₁ (ix₂ x₂)
    Σx₁ = P.rec (isEmbedding→hasPropFibers isEmb₁ (ix₂ x₂)) (λ (x₁ , p) → (x₁ , p)) x₂∈X₁
  hom2 : X₂ → X₁
  hom2 x₂ = fst (fib2 x₂)

  X₁≃X₂ : X₁ ≃ X₂
  X₁≃X₂ = isoToEquiv (iso hom1 hom2 sec1 sec2) where
    sec1 : section hom1 hom2
    sec1 x = isEmb₂ (hom1 (hom2 x)) x .equiv-proof h2x≡x .fst .fst where
      h2x≡x : ix₂ (hom1 (hom2 x)) ≡ ix₂ x
      h2x≡x = fib1 (hom2 x) .snd ∙ fib2 x .snd
    sec2 : section hom2 hom1
    sec2 x = isEmb₁ (hom2 (hom1 x)) x .equiv-proof h1x≡x .fst .fst where
      h1x≡x : ix₁ (hom2 (hom1 x)) ≡ ix₁ x
      h1x≡x = fib2 (hom1 x) .snd ∙ fib1 x .snd

  X₁≡X₂ : X₁ ≡ X₂
  X₁≡X₂ = ua X₁≃X₂

  ix₁≡ix₂ : PathP (λ i → X₁≡X₂ i → V _) ix₁ ix₂
  ix₁≡ix₂ = toPathP (
    transport refl ∘ ix₁ ∘ transport⁻ X₁≡X₂
      ≡[ i ]⟨ (λ x → transportRefl x i) ∘ ix₁ ∘ transportUaInv X₁≃X₂ (~ i) ⟩
    ix₁ ∘ transport (ua (invEquiv X₁≃X₂))
      ≡[ i ]⟨ ix₁ ∘ (λ x → uaβ (invEquiv X₁≃X₂) x i) ⟩
    ix₁ ∘ hom2
      ≡⟨ (λ i x → fib2 x .snd i) ⟩
    ix₂
      ∎ )

  isEmbix : PathP (λ i → isEmbedding (ix₁≡ix₂ i)) isEmb₁ isEmb₂
  isEmbix = isProp→PathP (λ i → isEmbeddingIsProp) isEmb₁ isEmb₂

  a≡sett : PathP (λ i → a ≡ sett (X₁≡X₂ i) (ix₁≡ix₂ i)) p q
  a≡sett = isProp→PathP (λ i → setIsSet a _) p q

sett-repr : (X : Type ℓ) (ix : X → V ℓ) → MonicPresentation (sett X ix)
sett-repr {ℓ} X ix = Rep , ixRep , isEmbIxRep , seteq X Rep ix ixRep eqImIxRep where
  Kernel : X → X → Type ℓ
  Kernel x y = ix x ≊ ix y
  Rep : Type ℓ
  Rep = X / Kernel
  ixRep : Rep → V ℓ
  ixRep = invEquiv (setQuotUniversal setIsSet) .fst (ix , λ _ _ → V∼-≡ .fst)
  isEmbIxRep : isEmbedding ixRep
  isEmbIxRep = hasPropFibers→isEmbedding propFibers where
    propFibers : ∀ y → (a b : Σ[ p ∈ Rep ] (ixRep p ≡ y)) → a ≡ b
    propFibers y (p₁ , m) (p₂ , n) = ΣPathP {B = λ _ p → ixRep p ≡ y} (base , isProp→PathP (λ _ → setIsSet _ _) _ _) where
      solution : ∀ p₁ p₂ → (p : ixRep Q.[ p₁ ] ≡ y) (q : ixRep Q.[ p₂ ] ≡ y) → Kernel p₁ p₂
      solution _ _ m n = invEquiv V∼-≡ .fst (m ∙ sym n)
      propP₁ : ∀ p₁ → isProp ((ixRep p₁ ≡ y) → p₁ ≡ p₂)
      propP₁ p₁ = isPropΠ λ eq → squash/ p₁ p₂
      propP₂ : ∀ {p₁} p₂ → isProp ((ixRep p₂ ≡ y) → Q.[ p₁ ] ≡ p₂)
      propP₂ {p₁} p₂ = isPropΠ λ eq → squash/ Q.[ p₁ ] p₂
      base : p₁ ≡ p₂
      base = Q.elimProp propP₁ (λ p₁ m → Q.elimProp propP₂ (λ p₂ n → eq/ p₁ p₂ (solution p₁ p₂ m n)) p₂ n) p₁ m

  eqImIxRep : eqImage ix ixRep
  eqImIxRep = (λ x → ∣ Q.[ x ] , refl ∣) , Q.elimProp (λ _ → P.squash) (λ b → ∣ b , refl ∣)

V-repr : (a : V ℓ) → MonicPresentation a
V-repr = elimProp isPropMonicPresentation λ X ix _ → sett-repr X ix

⟪_⟫ : (s : V ℓ) → Type ℓ
⟪ X ⟫ = V-repr X .fst

⟪_⟫↪ : (s : V ℓ) → ⟪ s ⟫ → V ℓ
⟪ X ⟫↪ = V-repr X .snd .fst

isEmb⟪_⟫↪ : (s : V ℓ) → isEmbedding ⟪ s ⟫↪
isEmb⟪ X ⟫↪ = V-repr X .snd .snd .fst

⟪_⟫-represents : (s : V ℓ) → s ≡ sett ⟪ s ⟫ ⟪ s ⟫↪
⟪ X ⟫-represents = V-repr X .snd .snd .snd

isPropRepFiber : (a b : V ℓ) → isProp (repFiber ⟪ a ⟫↪ b)
isPropRepFiber a b = embedIsProp (isEquiv→isEmbedding (repFiber≃fiber ⟪ a ⟫↪ b .snd))
                                 (isEmbedding→hasPropFibers isEmb⟪ a ⟫↪ b)

-- while ∈ is hProp (ℓ-suc ℓ), ∈ₛ is in ℓ
_∈ₛ_ : (a b : V ℓ) → hProp ℓ
a ∈ₛ b = repFiber ⟪ b ⟫↪ a , isPropRepFiber b a

∈-asFiber : {a b : V ℓ} → [ a ∈ b ] → fiber ⟪ b ⟫↪ a
∈-asFiber {a = a} {b = b} = subst (λ br → [ a ∈ br ] → fiber ⟪ b ⟫↪ a) (sym ⟪ b ⟫-represents) asRep where
  asRep : [ a ∈ sett ⟪ b ⟫ ⟪ b ⟫↪ ] → fiber ⟪ b ⟫↪ a
  asRep = P.propTruncIdempotent≃ (isEmbedding→hasPropFibers isEmb⟪ b ⟫↪ a) .fst
∈-fromFiber : {a b : V ℓ} → fiber ⟪ b ⟫↪ a → [ a ∈ b ]
∈-fromFiber {a = a} {b = b} = subst (λ br → [ a ∈ br ]) (sym ⟪ b ⟫-represents) ∘ ∣_∣

∈∈ₛ : {a b : V ℓ} → [ a ∈ b ⇔ a ∈ₛ b ]
∈∈ₛ {a = a} {b = b} = invEquiv (repFiber≃fiber ⟪ b ⟫↪ a) .fst ∘ ∈-asFiber {b = b} , ∈-fromFiber {b = b} ∘ repFiber≃fiber ⟪ b ⟫↪ a .fst

ix∈ₛ : {X : Type ℓ} {ix : X → V ℓ}
     → (x : X) → [ ix x ∈ₛ sett X ix ]
ix∈ₛ {X = X} {ix = ix} x = ∈∈ₛ {a = ix x} {b = sett X ix} .fst ∣ x , refl ∣

∈ₛ⟪_⟫↪_ : (a : V ℓ) (ix : ⟪ a ⟫) → [ ⟪ a ⟫↪ ix ∈ₛ a ]
∈ₛ⟪ a ⟫↪ ix = ix , ∼refl (⟪ a ⟫↪ ix)

-- also here, the left side is in level (ℓ-suc ℓ) while the right is in ℓ
presentation : (A : V ℓ) → (Σ[ v ∈ V ℓ ] [ v ∈ₛ A ]) ≃ ⟪ A ⟫
presentation A = isoToEquiv (iso into from (λ _ → refl) (λ s → Σ≡Prop (λ v → (v ∈ₛ A) .snd) (V∼-≡ .fst (s .snd .snd)))) where
  into : Σ[ v ∈ V _ ] [ v ∈ₛ A ] → ⟪ A ⟫
  into = fst ∘ snd
  from : ⟪ A ⟫ → Σ[ v ∈ V _ ] [ v ∈ₛ A ]
  from ⟪a⟫ = ⟪ A ⟫↪ ⟪a⟫ , ∈ₛ⟪ A ⟫↪ ⟪a⟫

-- subset relation, once in level (ℓ-suc ℓ) and once in ℓ
infixr 7 _∈_ _∈ₛ_ _⊆_ _⊆ₛ_

_⊆_ : (a b : V ℓ) → hProp (ℓ-suc ℓ)
a ⊆ b = ∀[ x ] x ∈ₛ a ⇒ x ∈ₛ b

⊆-refl : (a : V ℓ) → [ a ⊆ a ]
⊆-refl a = λ _ xa → xa

_⊆ₛ_ : (a b : V ℓ) → hProp ℓ
a ⊆ₛ b = ∀[ x ∶ ⟪ a ⟫ ] ⟪ a ⟫↪ x ∈ₛ b

⊆⊆ₛ : (a b : V ℓ) → [ a ⊆ b ⇔ a ⊆ₛ b ]
⊆⊆ₛ a b = (λ s → invEq curryEquiv s ∘ invEq (presentation a))
         , (λ s x xa → subst (λ x → [ x ∈ₛ b ]) (equivFun V∼-≡ (xa .snd)) (s (xa .fst)))

------------
-- Structures for building specific sets by giving encodings and decodings for their membership
-----------
record SetStructure ℓ : Type (ℓ-suc ℓ) where
  field
    X : Type ℓ
    ix : X → V ℓ
  resSet : V ℓ
  resSet = sett X ix

record SetPackage (S : SetStructure ℓ) ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  open SetStructure S hiding (resSet)
  open SetStructure S using (resSet) public
  field
    ∈-rep : V ℓ → hProp ℓ'
    unpack : (x : X) → [ ∈-rep (ix x) ]
    repack : {y : V ℓ} → [ ∈-rep y ] → ∥ fiber ix y ∥

  classification : [ ∀[ y ] (y ∈ₛ resSet ⇔ ∈-rep y) ]
  classification y = intoClassifier , fromClassifier where
    intoClassifier : [ y ∈ₛ resSet ] → [ ∈-rep y ]
    intoClassifier (yi , yr) = P.rec (∈-rep y .snd) (λ { (x , ix) → subst (fst ∘ ∈-rep) ix (unpack x) }) y∈ where
      y∈ : [ y ∈ resSet ]
      y∈ = ∈∈ₛ {a = y} {b = resSet} .snd (yi , yr)
    fromClassifier : [ ∈-rep y ] → [ y ∈ₛ resSet ]
    fromClassifier yr = ∈∈ₛ {a = y} {b = resSet} .fst (repack {y = y} yr)

-- extensionality
extensionality : [ ∀[ a ∶ V ℓ ] ∀[ b ] (a ⊆ b) ⊓ (b ⊆ a) ⇒ (a ≡ₛ b) ]
extensionality {ℓ = ℓ} a b imeq = ⟪ a ⟫-represents ∙∙ settab ∙∙ sym ⟪ b ⟫-represents where
  abpth : Path (Embedding _ _) (⟪ a ⟫ , ⟪ a ⟫↪ , isEmb⟪ a ⟫↪) (⟪ b ⟫ , ⟪ b ⟫↪ , isEmb⟪ b ⟫↪)
  abpth = equivFun (EmbeddingIP _ _)
    ( (λ p → equivFun (repFiber≃fiber ⟪ b ⟫↪ p) ∘ imeq .fst p ∘ invEq (repFiber≃fiber ⟪ a ⟫↪ p))
    , (λ p → equivFun (repFiber≃fiber ⟪ a ⟫↪ p) ∘ imeq .snd p ∘ invEq (repFiber≃fiber ⟪ b ⟫↪ p))
    )
  settab : sett ⟪ a ⟫ ⟪ a ⟫↪ ≡ sett ⟪ b ⟫ ⟪ b ⟫↪
  settab i = sett (abpth i .fst) (abpth i .snd .fst)

extInverse : [ ∀[ a ∶ V ℓ ] ∀[ b ] (a ≡ₛ b) ⇒ (a ⊆ b) ⊓ (b ⊆ a) ]
extInverse a b a≡b = subst (λ b → [ (a ⊆ b) ⊓ (b ⊆ a) ]) a≡b (⊆-refl a , ⊆-refl a)

set≡-characterization : {a b : V ℓ} → (a ≡ₛ b) ≡ (a ⊆ b) ⊓ (b ⊆ a)
set≡-characterization = ⇔toPath (extInverse _ _) (extensionality _ _)

------------
-- Specific constructions
-----------
module EmptySet where
  EmptyStructure : SetStructure ℓ
  SetStructure.X EmptyStructure = Lift E.⊥
  SetStructure.ix EmptyStructure ()

  EmptyPackage : SetPackage {ℓ = ℓ} EmptyStructure ℓ-zero
  SetPackage.∈-rep EmptyPackage _ = L.⊥
  SetPackage.unpack EmptyPackage ()
  SetPackage.repack EmptyPackage ()

  ∅ : V ℓ
  ∅ = SetStructure.resSet EmptyStructure

  ∅-empty : [ ∀[ b ∶ V ℓ ] ¬ (b ∈ₛ ∅) ]
  ∅-empty b = SetPackage.classification EmptyPackage b .fst
open EmptySet using (∅; ∅-empty)

module UnionSet (S : V ℓ) where
  UnionStructure : SetStructure ℓ
  SetStructure.X UnionStructure = Σ[ r ∈ ⟪ S ⟫ ] ⟪ ⟪ S ⟫↪ r ⟫
  SetStructure.ix UnionStructure (r , i) = ⟪ ⟪ S ⟫↪ r ⟫↪ i

  UNION : V ℓ
  UNION = SetStructure.resSet UnionStructure

  UnionPackage : SetPackage UnionStructure (ℓ-suc ℓ)
  SetPackage.∈-rep UnionPackage y = ∃[ v ] (v ∈ₛ S) ⊓ (y ∈ₛ v)
  SetPackage.unpack UnionPackage (vi , yi) = ∣ ⟪ S ⟫↪ vi , ∈ₛ⟪ S ⟫↪ vi , ∈ₛ⟪ ⟪ S ⟫↪ vi ⟫↪ yi ∣
  SetPackage.repack UnionPackage {y = y} = P.rec squash go where
    go : Σ[ v ∈ V _ ] [ v ∈ₛ S ] ⊓′ [ y ∈ₛ v ] → ∥ fiber _ y ∥
    go (v , (vi , vS) , xv) = ∣ repFiber≃fiber _ _ .fst ((vi , key .fst) , key .snd) ∣ where
      path : v ≡ ⟪ S ⟫↪ vi
      path = sym (V∼-≡ .fst vS)
      key : Σ[ i ∈ ⟪ ⟪ S ⟫↪ vi ⟫ ] ⟪ ⟪ S ⟫↪ vi ⟫↪ i ≊ y
      key = subst (λ v → Σ[ ix ∈ ⟪ v ⟫ ] ⟪ v ⟫↪ ix ≊ y) path xv

  union-ax : [ ∀[ u ] (u ∈ₛ UNION ⇔ (∃[ v ] (v ∈ₛ S) ⊓ (u ∈ₛ v))) ]
  union-ax u = classification u .fst , classification u .snd where
    open SetPackage UnionPackage using (classification)
open UnionSet renaming (UNION to infixr 9 ⋃_) using (union-ax)

module PairingSet (a b : V ℓ) where
  PairingStructure : SetStructure ℓ
  SetStructure.X PairingStructure = Lift Bool
  SetStructure.ix PairingStructure (lift false) = a
  SetStructure.ix PairingStructure (lift true) = b

  PairingPackage : SetPackage PairingStructure (ℓ-suc ℓ)
  SetPackage.∈-rep PairingPackage d = (d ≡ₛ a) ⊔ (d ≡ₛ b)
  SetPackage.unpack PairingPackage (lift false) = L.inl refl
  SetPackage.unpack PairingPackage (lift true) = L.inr refl
  SetPackage.repack PairingPackage {y = y} = P.rec squash λ { (_⊎_.inl ya) → ∣ lift false , sym ya ∣ ; (_⊎_.inr yb) → ∣ lift true , sym yb ∣ }

  PAIR : V ℓ
  PAIR = SetStructure.resSet PairingStructure

  pairing-ax : [ ∀[ d ] (d ∈ₛ PAIR ⇔ (d ≡ₛ a) ⊔ (d ≡ₛ b)) ]
  pairing-ax d = classification d .fst , classification d .snd where
    open SetPackage PairingPackage using (classification)
-- pairing TODO: notation?
open PairingSet renaming (PAIR to infix 12 ⁅_,_⁆) using (pairing-ax)

module SingletonSet (a : V ℓ) where
  SingletonStructure : SetStructure ℓ
  SetStructure.X SingletonStructure = Lift Unit
  SetStructure.ix SingletonStructure (lift tt) = a

  SingletonPackage : SetPackage SingletonStructure (ℓ-suc ℓ)
  SetPackage.∈-rep SingletonPackage d = d ≡ₛ a
  SetPackage.unpack SingletonPackage _ = refl
  SetPackage.repack SingletonPackage ya = ∣ lift tt , sym ya ∣

  SINGL : V ℓ
  SINGL = SetStructure.resSet SingletonStructure
open SingletonSet renaming (SINGL to infix 10 ⁅_⁆s)

-- small unions
_∪_ : (a b : V ℓ) → V ℓ
a ∪ b = ⋃ ⁅ a , b ⁆

module InfinitySet {ℓ} where
  #_ : ℕ → V ℓ
  # zero = ∅
  # suc n = (# n) ∪ ⁅ # n ⁆s

  ωStructure : SetStructure ℓ
  SetStructure.X ωStructure = Lift ℕ
  SetStructure.ix ωStructure = #_ ∘ lower

  ω : V ℓ
  ω = SetStructure.resSet ωStructure

  open PropMonad
  ωPackage : SetPackage ωStructure (ℓ-suc ℓ)
  SetPackage.∈-rep ωPackage d = (d ≡ₛ ∅) ⊔ (∃[ v ] (d ≡ₛ v ∪ ⁅ v ⁆s) ⊓ (v ∈ₛ ω))
  SetPackage.unpack ωPackage (lift zero) = L.inl refl
  SetPackage.unpack ωPackage (lift (suc n)) = L.inr ∣ # n , refl , ∈∈ₛ {b = ω} .fst ∣ lift n , refl ∣ ∣
  SetPackage.repack ωPackage {y = y} = ⊔-elim (y ≡ₛ ∅) ∥ _ ∥ₚ (λ _ → ∥ fiber _ y ∥ₚ)
    (λ e → ∣ lift zero , sym e ∣)
    (λ m → do (v , yv , vr) ← m
              (lift n , eq) ← ∈∈ₛ {b = ω} .snd vr
              ∣ lift (suc n) , sym (subst (λ v → y ≡ (v ∪ ⁅ v ⁆s)) (sym eq) yv) ∣
    )

  ω-empty : [ ∅ ∈ₛ ω ]
  ω-empty = SetPackage.classification ωPackage ∅ .snd (L.inl refl)

  ω-next : [ ∀[ x ∶ V ℓ ] x ∈ₛ ω ⇒ (x ∪ ⁅ x ⁆s) ∈ₛ ω ]
  ω-next x x∈ω = SetPackage.classification ωPackage (x ∪ ⁅ x ⁆s) .snd (L.inr ∣ x , refl , x∈ω ∣)
open InfinitySet using (ω; ω-empty; ω-next)

module ReplacementSet (r : V ℓ → V ℓ) (a : V ℓ) where
  ReplacementStructure : SetStructure ℓ
  SetStructure.X ReplacementStructure = ⟪ a ⟫
  SetStructure.ix ReplacementStructure = r ∘ ⟪ a ⟫↪

  REPLACED : V ℓ
  REPLACED = SetStructure.resSet ReplacementStructure

  open PropMonad
  ReplacementPackage : SetPackage ReplacementStructure (ℓ-suc ℓ)
  SetPackage.∈-rep ReplacementPackage y = ∃[ z ] (z ∈ₛ a) ⊓ (y ≡ₛ r z)
  SetPackage.unpack ReplacementPackage ⟪a⟫ = ∣ ⟪ a ⟫↪ ⟪a⟫ , (∈ₛ⟪ a ⟫↪ ⟪a⟫) , refl ∣
  SetPackage.repack ReplacementPackage {y = y} m = do
    (z , (a , za) , yr) ← m
    ∣ a , cong r (V∼-≡ .fst za) ∙ sym yr ∣

  replacement-ax : [ ∀[ y ] (y ∈ₛ REPLACED ⇔ (∃[ z ] (z ∈ₛ a) ⊓ (y ≡ₛ r z))) ]
  replacement-ax y = classification y .fst , classification y .snd where
    open SetPackage ReplacementPackage using (classification)
open ReplacementSet renaming (REPLACED to infix 12 ⁅_∣_⁆) using (replacement-ax)

module SeparationSet (a : V ℓ) (ϕ : V ℓ → hProp ℓ) where
  SeparationStructure : SetStructure ℓ
  SetStructure.X SeparationStructure = Σ[ x ∈ ⟪ a ⟫ ] [ ϕ (⟪ a ⟫↪ x) ]
  SetStructure.ix SeparationStructure = ⟪ a ⟫↪ ∘ fst

  SeparationPackage : SetPackage SeparationStructure ℓ
  SetPackage.∈-rep SeparationPackage y = (y ∈ₛ a) ⊓ ϕ y
  SetPackage.unpack SeparationPackage (⟪a⟫ , phi) = (∈ₛ⟪ a ⟫↪ ⟪a⟫) , phi
  SetPackage.repack SeparationPackage ((⟪a⟫ , ya) , phi) = ∣ (⟪a⟫ , subst (fst ∘ ϕ) (sym (V∼-≡ .fst ya)) phi) , V∼-≡ .fst ya ∣

  SEPAREE : V ℓ
  SEPAREE = SetStructure.resSet SeparationStructure

  separation-ax : [ ∀[ y ] (y ∈ₛ SEPAREE ⇔ (y ∈ₛ a) ⊓ ϕ y) ]
  separation-ax y = classification y .fst , classification y .snd where
    open SetPackage SeparationPackage using (classification)
open SeparationSet renaming (SEPAREE to infix 12 ⁅_∶_⁆) using (separation-ax)
