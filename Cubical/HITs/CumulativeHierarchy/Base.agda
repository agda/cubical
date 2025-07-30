{-
This file models "ZF - powerset" in cubical agda, via a cumulative hierarchy, in the sense given
in the HoTT book §10.5 "The cumulative hierarchy".

A great amount of inspiration is taken from the Coq implementations found in
Jérémy Ledent, Modeling set theory in homotopy type theory, code of which can be found online at
https://github.com/jledent/vset
-}

module Cubical.HITs.CumulativeHierarchy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Functions.Logic
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as P hiding (elim; elim2)

import Cubical.HITs.PropositionalTruncation.Monad as PropMonad

private
  variable
    ℓ ℓ' : Level

infix 5 _∈_

-- set up the basic hierarchy definition and _∈_ as recursive, higher inductive types
data V (ℓ : Level) : Type (ℓ-suc ℓ)
_∈_ : (S T : V ℓ) → hProp (ℓ-suc ℓ)

eqImage : {X Y : Type ℓ} (ix : X → V ℓ) (iy : Y → V ℓ) → Type (ℓ-suc ℓ)
eqImage {X = X} {Y = Y} ix iy = (∀ (a : X) → ∥ fiber iy (ix a) ∥₁) ⊓′
                                (∀ (b : Y) → ∥ fiber ix (iy b) ∥₁)

data V ℓ where
  sett : (X : Type ℓ) → (X → V ℓ) → V ℓ
  seteq : (X Y : Type ℓ) (ix : X → V ℓ) (iy : Y → V ℓ) (eq : eqImage ix iy) → sett X ix ≡ sett Y iy
  setIsSet : isSet (V ℓ)

A ∈ sett X ix = ∥ Σ[ i ∈ X ] (ix i ≡ A) ∥ₚ
A ∈ seteq X Y ix iy (f , g) i =
  ⇔toPath {P = A ∈ sett X ix} {Q = A ∈ sett Y iy}
    (λ ax → do (x , xa) ← ax ; (y , ya) ← f x ; ∣ y , ya ∙ xa ∣₁)
    (λ ay → do (y , ya) ← ay ; (x , xa) ← g y ; ∣ x , xa ∙ ya ∣₁) i
  where open PropMonad
A ∈ setIsSet a b p q i j = isSetHProp (A ∈ a) (A ∈ b) (λ j → A ∈ p j) (λ j → A ∈ q j) i j

-- setup a general eliminator into h-sets
record ElimSet {Z : (s : V ℓ) → Type ℓ'}
               (isSetZ : ∀ s → isSet (Z s)) : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    ElimSett :
      ∀ (X : Type ℓ) (ix : X → V ℓ)
      -- ^ the structural parts of the set
      → (rec : ∀ x → Z (ix x))
      -- ^ a recursor into the elements
      → Z (sett X ix)
    ElimEq :
      ∀ (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) (eq : eqImage ix₁ ix₂)
      -- ^ the structural parts of the seteq path
      → (rc₁ : ∀ x₁ → Z (ix₁ x₁)) (rc₂ : ∀ x₂ → Z (ix₂ x₂))
      -- ^ recursors into the elements
      → ((x₁ : X₁) → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ] PathP (λ i → Z (p i)) (rc₂ x₂) (rc₁ x₁))
      → ((x₂ : X₂) → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ] PathP (λ i → Z (p i)) (rc₁ x₁) (rc₂ x₂))
      -- ^ proofs that the recursors have equal images
      → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i)) (ElimSett X₁ ix₁ rc₁) (ElimSett X₂ ix₂ rc₂)

module _ {Z : (s : V ℓ) → Type ℓ'} {isSetZ : ∀ s → isSet (Z s)} (E : ElimSet isSetZ) where
  open ElimSet E
  elim : (s : V ℓ) → Z s
  elim (sett X ix) = ElimSett X ix (elim ∘ ix)
  elim (seteq X₁ X₂ ix₁ ix₂ eq i) =
    ElimEq X₁ X₂ ix₁ ix₂ eq (elim ∘ ix₁) (elim ∘ ix₂) rec₁→₂ rec₂→₁ i
    where
    rec₁→₂ :
      ∀ (x₁ : X₁)
      → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ] PathP (λ i → Z (p i)) (elim (ix₂ x₂)) (elim (ix₁ x₁))
    rec₂→₁ :
      ∀ (x₂ : X₂)
      → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ] PathP (λ i → Z (p i)) (elim (ix₁ x₁)) (elim (ix₂ x₂))
    -- using a local definition of Prop.rec satisfies the termination checker
    rec₁→₂ x₁ = localRec₁ (eq .fst x₁) where
      localRec₁ :
          ∥ fiber ix₂ (ix₁ x₁) ∥₁
        → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ] PathP (λ i → Z (p i)) (elim (ix₂ x₂)) (elim (ix₁ x₁))
      localRec₁ ∣ x₂ , xx ∣₁ = ∣ (x₂ , xx) , (λ i → elim (xx i)) ∣₁
      localRec₁ (squash₁ x y i) = squash₁ (localRec₁ x) (localRec₁ y) i
    rec₂→₁ x₂ = localRec₂ (eq .snd x₂) where
      localRec₂ :
          ∥ fiber ix₁ (ix₂ x₂) ∥₁
        → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ] PathP (λ i → Z (p i)) (elim (ix₁ x₁)) (elim (ix₂ x₂))
      localRec₂ ∣ x₁ , xx ∣₁ = ∣ (x₁ , xx) , (λ i → elim (xx i)) ∣₁
      localRec₂ (squash₁ x y i) = squash₁ (localRec₂ x) (localRec₂ y) i
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
record Elim2Set {Z : (s t : V ℓ) → Type ℓ'}
                (isSetZ : ∀ s t → isSet (Z s t)) : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    ElimSett2 :
      ∀ (X : Type ℓ) (ix : X → V ℓ) (Y : Type ℓ) (iy : Y → V ℓ)
      -- ^ the structural parts of the set
      → (rec : ∀ x y → Z (ix x) (iy y))
      -- ^ a recursor into the elements
      → Z (sett X ix) (sett Y iy)
    -- path when the the first argument deforms along seteq and the second argument is held constant
    ElimEqFst :
      ∀ (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) (eq : eqImage ix₁ ix₂)
      -- ^ the structural parts of the seteq path
      → (Y : Type ℓ) (iy : Y → V ℓ)
      -- ^ the second argument held constant
      → (rec₁ : ∀ x₁ y → Z (ix₁ x₁) (iy y)) (rec₂ : ∀ x₂ y → Z (ix₂ x₂) (iy y))
      -- ^ recursors into the elements
      → (rec₁→₂ : (x₁ : X₁)
                → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ]
                     PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₂ x₂ y) (λ y → rec₁ x₁ y))
      → (rec₂→₁ : (x₂ : X₂)
                → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ]
                     PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₁ x₁ y) (λ y → rec₂ x₂ y))
      -- ^ proofs that the recursors have equal images
      → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) (sett Y iy))
              (ElimSett2 X₁ ix₁ Y iy rec₁)
              (ElimSett2 X₂ ix₂ Y iy rec₂)
    -- path when the the second argument deforms along seteq and the first argument is held constant
    ElimEqSnd :
      ∀ (X : Type ℓ) (ix : X → V ℓ)
      -- ^ the first argument held constant
      → (Y₁ Y₂ : Type ℓ) (iy₁ : Y₁ → V ℓ) (iy₂ : Y₂ → V ℓ) → (eq : eqImage iy₁ iy₂)
      -- ^ the structural parts of the seteq path
      → (rec₁ : ∀ x y₁ → Z (ix x) (iy₁ y₁)) (rec₂ : ∀ x y₂ → Z (ix x) (iy₂ y₂))
      -- ^ recursors into the elements
      → (rec₁→₂ : (y₁ : Y₁)
                → ∃[ (y₂ , p) ∈ fiber iy₂ (iy₁ y₁) ]
                     PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec₂ x y₂) (λ x → rec₁ x y₁))
      → (rec₂→₁ : (y₂ : Y₂)
                → ∃[ (y₁ , p) ∈ fiber iy₁ (iy₂ y₂) ]
                     PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec₁ x y₁) (λ x → rec₂ x y₂))
      -- ^ proofs that the recursors have equal images
      → PathP (λ i → Z (sett X ix) (seteq Y₁ Y₂ iy₁ iy₂ eq i))
              (ElimSett2 X ix Y₁ iy₁ rec₁)
              (ElimSett2 X ix Y₂ iy₂ rec₂)

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
      rec₁→₂ :
        ∀ (y₁ : Y₁)
        → ∃[ (y₂ , p) ∈ fiber iy₂ (iy₁ y₁) ]
             PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec x (iy₂ y₂)) (λ x → rec x (iy₁ y₁))
      rec₂→₁ :
        ∀ (y₂ : Y₂)
        → ∃[ (y₁ , p) ∈ fiber iy₁ (iy₂ y₂) ]
             PathP (λ i → ∀ x → Z (ix x) (p i)) (λ x → rec x (iy₁ y₁)) (λ x → rec x (iy₂ y₂))
      rec₁→₂ y₁ = do (y₂ , yy) ← fst eq y₁ ; ∣ (y₂ , yy) , (λ i x → rec x (yy i)) ∣₁
      rec₂→₁ y₂ = do (y₁ , yy) ← snd eq y₂ ; ∣ (y₁ , yy) , (λ i x → rec x (yy i)) ∣₁

    elimImplS :
      ∀ (X : Type ℓ) (ix : X → V ℓ)
      → (∀ x t₂ → Z (ix x) t₂)
      → (t : V ℓ) → Z (sett X ix) t
    elimImplS X ix rec = elim (eliminatorImplX X ix rec)

    elimImplSExt :
      ∀ (X₁ X₂ : Type ℓ) (ix₁ : X₁ → V ℓ) (ix₂ : X₂ → V ℓ) → (eq : eqImage ix₁ ix₂)
      → (rec₁ : ∀ x₁ t₂ → Z (ix₁ x₁) t₂) (rec₂ : ∀ x₂ t₂ → Z (ix₂ x₂) t₂)
      → ((x₁ : X₁) → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ]
                        PathP (λ i → ∀ t → Z (p i) t) (rec₂ x₂) (rec₁ x₁))
      → ((x₂ : X₂) → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ]
                        PathP (λ i → ∀ t → Z (p i) t) (rec₁ x₁) (rec₂ x₂))
      → (t : V ℓ)
      → PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) t)
              (elimImplS X₁ ix₁ rec₁ t)
              (elimImplS X₂ ix₂ rec₂ t)
    elimImplSExt X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ =
      elimProp propPathP (λ Y iy _ → elimImplSExtT Y iy)
      where
      propPathP : (t : V ℓ)
                → isProp (PathP (λ i → Z (seteq X₁ X₂ ix₁ ix₂ eq i) t)
                                (elimImplS X₁ ix₁ rec₁ t)
                                (elimImplS X₂ ix₂ rec₂ t))
      propPathP _ = subst isProp (sym (PathP≡Path _ _ _)) (isSetZ _ _ _ _)

      elimImplSExtT : (Y : Type ℓ) (iy : Y → V ℓ) → _ {- the appropriate path type -}
      elimImplSExtT Y iy =
        ElimEqFst X₁ X₂ ix₁ ix₂ eq Y iy (λ x₁ y → rec₁ x₁ (iy y))
                                        (λ x₂ y → rec₂ x₂ (iy y)) rec₁→₂Impl rec₂→₁Impl
        where
        rec₁→₂Impl :
          ∀ (x₁ : X₁)
          → ∃[ (x₂ , p) ∈ fiber ix₂ (ix₁ x₁) ]
               PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₂ x₂ (iy y)) (λ y → rec₁ x₁ (iy y))
        rec₂→₁Impl :
          ∀ (x₂ : X₂)
          → ∃[ (x₁ , p) ∈ fiber ix₁ (ix₂ x₂) ]
               PathP (λ i → ∀ y → Z (p i) (iy y)) (λ y → rec₁ x₁ (iy y)) (λ y → rec₂ x₂ (iy y))
        rec₁→₂Impl x₁ = do ((x₂ , xx) , rx) ← rec₁→₂ x₁ ; ∣ (x₂ , xx) , (λ i y → rx i (iy y)) ∣₁
        rec₂→₁Impl x₂ = do ((x₁ , xx) , rx) ← rec₂→₁ x₂ ; ∣ (x₁ , xx) , (λ i y → rx i (iy y)) ∣₁

    pElim : ElimSet isSetPElim
    ElimSett pElim = elimImplS
    ElimEq pElim X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ i t =
      elimImplSExt X₁ X₂ ix₁ ix₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ t i
