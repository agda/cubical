{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contains:
1. The long exact sequence of loop spaces Ωⁿ (fib f) → Ωⁿ A → Ωⁿ B
2. The long exact sequence of homotopy groups πₙ(fib f) → πₙ A → πₙ B
3. Some lemmas relating the map in the sequence to maps
-}
module Cubical.Homotopy.Group.Pi4S3.HopfGen2 where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)
open import Cubical.HITs.S2

-- move to SetTruncation
∥_∥₂∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
fst ∥ A ∥₂∙ = ∥ fst A ∥₂
snd ∥ A ∥₂∙ = ∣ pt A ∣₂

map∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
       (f : A →∙ B) → ∥ A ∥₂∙ →∙ ∥ B ∥₂∙
fst (map∙ f) = sMap (fst f)
snd (map∙ f) = cong ∣_∣₂ (snd f)

-- move to pointed
module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  isInIm∙ : (x : typ B) → Type (ℓ-max ℓ ℓ')
  isInIm∙ x = Σ[ z ∈ typ A ] fst f z ≡ x

  ∥isInIm∙∥ : (x : typ B) → Type (ℓ-max ℓ ℓ')
  ∥isInIm∙∥ x = ∃[ z ∈ typ A ] fst f z ≡ x

  isInKer∙ : (x : fst A) → Type ℓ'
  isInKer∙ x = fst f x ≡ snd B

  ∥isInKer∙∥ : (x : fst A) → Type ℓ'
  ∥isInKer∙∥ x = ∥ fst f x ≡ snd B ∥

-- Move to pointed or Equiv
_≃∙_ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
A ≃∙ B = Σ[ e ∈ fst A ≃ fst B ] fst e (pt A) ≡ pt B

invEquiv∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ≃∙ B → B ≃∙ A
fst (invEquiv∙ x) = invEquiv (fst x)
snd (invEquiv∙ {A = A} x) =
  sym (cong (fst (invEquiv (fst x))) (snd x)) ∙ retEq (fst x) (pt A)

compEquiv∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → A ≃∙ B → B ≃∙ C → A ≃∙ C
fst (compEquiv∙ e1 e2) = compEquiv (fst e1) (fst e2)
snd (compEquiv∙ e1 e2) = cong (fst (fst e2)) (snd e1) ∙ snd e2

-- Move to Loopspace
ΩIso : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (Ω A) ≃∙ (Ω B)
fst (fst (ΩIso e)) = fst (Ω→ (fst (fst e) , snd e))
snd (fst (ΩIso e)) = isEquivΩ→ (fst (fst e) , snd e) (snd (fst e))
snd (ΩIso e) = snd (Ω→ (fst (fst e) , snd e))

ΩIsopres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (p q : typ (Ω A))
     → fst (fst (ΩIso e)) (p ∙ q)
     ≡ fst (fst (ΩIso e)) p
     ∙ fst (fst (ΩIso e)) q
ΩIsopres∙ e p q = Ω→pres∙ (fst (fst e) , snd e) p q

Ω^≃ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
     → (e : A ≃∙ B)
     → ((Ω^ n) A) ≃∙ ((Ω^ n) B)
Ω^≃ zero e = e
fst (fst (Ω^≃ (suc n) e)) =
  fst (Ω→ (fst (fst (Ω^≃ n e)) , snd (Ω^≃ n e)))
snd (fst (Ω^≃ (suc n) e)) =
  isEquivΩ→ (fst (fst (Ω^≃ n e)) , snd (Ω^≃ n e)) (snd (fst (Ω^≃ n e)))
snd (Ω^≃ (suc n) e) =
  snd (Ω→ (fst (fst (Ω^≃ n e)) , snd (Ω^≃ n e)))


-- We will need an explicitly defined equivalence
-- (PathP (λ i → p i ≡ y) q q) ≃ (sym q ∙∙ p ∙∙ q ≡ refl)
-- This is given by →∙∙lCancel below
module _ {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y) where
  →∙∙lCancel-fill : PathP (λ i → p i ≡ y) q q → I → I → I → A
  →∙∙lCancel-fill PP k i j =
    hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym q) p q k j
                 ; (i = i1) → y
                 ; (j = i0) → q (i ∨ k)
                 ; (j = i1) → q (i ∨ k)})
        (inS (PP j i))
        k

  ←∙∙lCancel-fill : sym q ∙∙ p ∙∙ q ≡ refl → I → I → I → A
  ←∙∙lCancel-fill PP k i j =
    hfill (λ k → λ {(i = i0) → q (j ∨ ~ k)
                   ; (i = i1) → q (j ∨ ~ k)
                   ; (j = i0) → doubleCompPath-filler (sym q) p q (~ k) i
                   ; (j = i1) → y})
          (inS (PP j i))
          k

  →∙∙lCancel : PathP (λ i → p i ≡ y) q q → sym q ∙∙ p ∙∙ q ≡ refl
  →∙∙lCancel PP i j = →∙∙lCancel-fill PP i1 i j

  ←∙∙lCancel : sym q ∙∙ p ∙∙ q ≡ refl → PathP (λ i → p i ≡ y) q q
  ←∙∙lCancel PP i j = ←∙∙lCancel-fill PP i1 i j

  ←∙∙lCancel→∙∙lCancel : (PP : PathP (λ i → p i ≡ y) q q)
    → ←∙∙lCancel (→∙∙lCancel PP) ≡ PP
  ←∙∙lCancel→∙∙lCancel PP r i j =
    hcomp (λ k → λ {(r = i0) → ←∙∙lCancel-fill (→∙∙lCancel PP) k i j
                   ; (r = i1) → PP i j
                   ; (j = i0) → doubleCompPath-filler (sym q) p q (~ k ∧ ~ r) i
                   ; (j = i1) → y
                   ; (i = i0) → q (j ∨ ~ k ∧ ~ r)
                   ; (i = i1) → q (j ∨ ~ k ∧ ~ r)})
     (hcomp (λ k → λ {(r = i0) → →∙∙lCancel-fill PP k j i
                   ; (r = i1) → PP i j
                   ; (j = i0) → doubleCompPath-filler (sym q) p q (k ∧ ~ r) i
                   ; (j = i1) → y
                   ; (i = i0) → q (j ∨ k ∧ ~ r)
                   ; (i = i1) → q (j ∨ k ∧ ~ r)})
            (PP i j))

  →∙∙lCancel←∙∙lCancel : (PP : sym q ∙∙ p ∙∙ q ≡ refl)
    → →∙∙lCancel (←∙∙lCancel PP) ≡ PP
  →∙∙lCancel←∙∙lCancel PP r i j =
    hcomp (λ k → λ {(r = i0) → →∙∙lCancel-fill (←∙∙lCancel PP) k i j
                   ; (r = i1) → PP i j
                   ; (j = i0) → q (i ∨ k ∨ r) 
                   ; (j = i1) → q (i ∨ k ∨ r)
                   ; (i = i0) → doubleCompPath-filler (sym q) p q (r ∨ k) j
                   ; (i = i1) → y})
     (hcomp (λ k → λ {(r = i0) → ←∙∙lCancel-fill PP k j i
                   ; (r = i1) → PP i j
                   ; (j = i0) → q (i ∨ r ∨ ~ k)
                   ; (j = i1) → q (i ∨ r ∨ ~ k)
                   ; (i = i0) → doubleCompPath-filler (sym q) p q (r ∨ ~ k) j
                   ; (i = i1) → y})
            (PP i j))

←∙∙lCancel-refl-refl :
  {ℓ : Level} {A : Type ℓ} {x : A} (p : refl {x = x} ≡ refl)
  → ←∙∙lCancel {x = x} {y = x} refl refl (sym (rUnit refl) ∙ p)
  ≡ flipSquare p
←∙∙lCancel-refl-refl p k i j =
  hcomp (λ r → λ { (i = i0) → p i0 i0
             ; (i = i1) → p i0 i0
             ; (j = i0) → rUnit (λ _ → p i0 i0) (~ r) i
             ; (j = i1) → p i0 i0
             ; (k = i0) → ←∙∙lCancel-fill refl refl (sym (rUnit refl) ∙ p) r i j
             ; (k = i1) → compPath-filler' (sym (rUnit refl)) p (~ r) j i})
         ((sym (rUnit refl) ∙ p) j i)

{- We need an iso Ω(fib f) ≅ fib(Ω f) -}
ΩFibreIso : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
            → Iso (typ (Ω (fiber (fst f) (pt B) , (pt A) , snd f)))
                   (fiber (Ω→ f .fst) refl)
fun (ΩFibreIso f) p = (cong fst p) ,
                   →∙∙lCancel (cong (fst f) (cong fst p)) (snd f)
                      (cong snd p)
fst (inv (ΩFibreIso f) (p , q) i) = p i
snd (inv (ΩFibreIso f) (p , q) i) = ←∙∙lCancel (cong (fst f) p) (snd f) q i
rightInv (ΩFibreIso f) (p , q) = ΣPathP (refl , →∙∙lCancel←∙∙lCancel _ _ q)
fst (leftInv (ΩFibreIso f) p i j) = fst (p j)
snd (leftInv (ΩFibreIso f) p i j) k = ←∙∙lCancel→∙∙lCancel _ _ (cong snd p) i j k

{- Some homomorphism properties of the above iso -}
ΩFibreIsopres∙fst : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                    → (p q : (typ (Ω (fiber (fst f) (pt B) , (pt A) , snd f))))
                    → fst (fun (ΩFibreIso f) (p ∙ q))
                    ≡ fst (fun (ΩFibreIso f) p) ∙ fst (fun (ΩFibreIso f) q)
ΩFibreIsopres∙fst f p q = cong-∙ fst p q

ΩFibreIso⁻pres∙snd : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
                    (f : A →∙ B) (p q : typ (Ω (Ω B))) 
                    → inv (ΩFibreIso f) (refl , (Ω→ f .snd ∙ p ∙ q))
                    ≡ inv (ΩFibreIso f) (refl , Ω→ f .snd ∙ p)
                    ∙ inv (ΩFibreIso f) (refl , Ω→ f .snd ∙ q)
ΩFibreIso⁻pres∙snd {A = A} {B = B}=
  →∙J (λ b₀ f → (p q : typ (Ω (Ω (fst B , b₀))))
               → inv (ΩFibreIso f) (refl , (Ω→ f .snd ∙ p ∙ q))
                 ≡ inv (ΩFibreIso f) (refl , Ω→ f .snd ∙ p)
                 ∙ inv (ΩFibreIso f) (refl , Ω→ f .snd ∙ q))
       ind
  where
  ind : (f : typ A → typ B) (p q : typ (Ω (Ω (fst B , f (pt A)))))
      → inv (ΩFibreIso (f , refl)) (refl , (sym (rUnit refl) ∙ p ∙ q))
       ≡ inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ p)
       ∙ inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q)
  fst (ind f p q i j) =
    (rUnit refl
     ∙ sym (cong-∙ fst
      (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ p))
      (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q)))) i j
  snd (ind f p q i j) k =
    hcomp (λ r → λ {(i = i0) → ←∙∙lCancel-refl-refl (p ∙ q) (~ r) j k -- 
                   ; (i = i1) →
                     snd (compPath-filler
                         (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ p))
                         (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q)) r j) k
                   ; (j = i0) → f (snd A)
                   ; (j = i1) → snd (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q) (r ∨ ~ i)) k
                   ; (k = i0) → main r i j
                   ; (k = i1) → f (snd A)})
       (hcomp (λ r → λ {(i = i0) → (p ∙ q) k j
                   ; (i = i1) → ←∙∙lCancel-refl-refl p (~ r) j k
                   ; (j = i0) → f (snd A)
                   ; (j = i1) → ←∙∙lCancel-refl-refl q (~ r) (~ i) k
                   ; (k = i0) → f (pt A)
                   ; (k = i1) → f (snd A)})
              (hcomp (λ r → λ {(i = i0) → (compPath-filler' p q r) k j
                   ; (i = i1) → p (k ∨ ~ r) j
                   ; (j = i0) → f (snd A)
                   ; (j = i1) → q k (~ i)
                   ; (k = i0) → p (k ∨ ~ r) j
                   ; (k = i1) → f (snd A)})
               (q k (~ i ∧ j))))
    where
    P = (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ p))
    Q = (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q))

    main : Cube refl
              (λ i j → f ((rUnit refl ∙ sym (cong-∙ fst P Q)) i j)) -- r i j
              (λ r j → f (snd A))
              (λ r j → f (fst (compPath-filler P Q r j)))
              (λ r i → f (snd A))
              λ r i → f (snd A)
    main r i j =
      hcomp (λ k → λ {(i = i0) → f (snd A)
                     ; (i = i1) → f (fst (compPath-filler P Q (r ∨ ~ k) j))
                     ; (j = i0) → f (snd A)
                     ; (j = i1) → f (snd A)
                     ; (r = i0) → f (fst (compPath-filler P Q (i ∧ ~ k) j))
                     ; (r = i1) → f ((rUnit refl ∙ sym (cong-∙ fst P Q)) i j)})
            (hcomp (λ k → λ {(i = i0) → f (rUnit (λ _ → pt A) (~ k ∧ r) j)
                     ; (i = i1) → f (fst ((P ∙ Q) j))
                     ; (j = i0) → f (snd A)
                     ; (j = i1) → f (snd A)
                     ; (r = i0) → f (fst (compPath-filler P Q i j))
                     ; (r = i1) → f ((compPath-filler' (rUnit refl) (sym (cong-∙ fst P Q)) k) i j)})
             (hcomp (λ k → λ {(i = i0) → f (rUnit (λ _ → pt A) (k ∧ r) j)
                     ; (i = i1) → f (fst (compPath-filler P Q k j))
                     ; (j = i0) → f (snd A)
                     ; (j = i1) → f (snd A)
                     ; (r = i0) → f (fst (compPath-filler P Q (i ∧ k) j))
                     ; (r = i1) → f ((cong-∙∙-filler fst refl P Q) k (~ i) j)})
                    (f (snd A))))

ΩFibreIso∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
            → Iso.fun (ΩFibreIso f) refl ≡ (refl , (∙∙lCancel (snd f)))
ΩFibreIso∙ {A = A} {B = B} =
  →∙J (λ b f → Iso.fun (ΩFibreIso f) refl ≡ (refl , (∙∙lCancel (snd f))))
    λ f → ΣPathP (refl , help f)
  where
  help : (f : fst A → fst B) → →∙∙lCancel (λ i → f (snd A)) refl (λ i → refl) ≡
       ∙∙lCancel refl
  help f i j r =
    hcomp (λ k → λ {(i = i0) → →∙∙lCancel-fill (λ i₁ → f (snd A)) refl refl k j r
                   ; (i = i1) → ∙∙lCancel-fill (λ i₁ → f (snd A))  j r k
                   ; (j = i0) → rUnit (λ i₁ → f (snd A)) k r
                   ; (j = i1) → f (snd A)
                   ; (r = i1) → f (snd A)
                   ; (r = i0) → f (snd A)})
          (f (snd A))

ΩFibreIso⁻∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
           → Iso.inv (ΩFibreIso f) (refl , (∙∙lCancel (snd f))) ≡ refl
ΩFibreIso⁻∙ f =
  cong (Iso.inv (ΩFibreIso f)) (sym (ΩFibreIso∙ f)) ∙ leftInv (ΩFibreIso f) refl 

{- Iso Ωⁿ (fib f) ≅ fib (Ωⁿ f) -}
Ω^Fibre≃∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
              ≃∙ ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
                , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd))
Ω^Fibre≃∙ zero f =  (idEquiv _) , refl
Ω^Fibre≃∙ (suc n) f = 
  compEquiv∙
    (ΩIso (Ω^Fibre≃∙ n f))
    ((isoToEquiv (ΩFibreIso (Ω^→ n f))) , ΩFibreIso∙ (Ω^→ n f))

{- Its inverse iso directly defined -}
Ω^Fibre≃∙⁻ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
                , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd))
             ≃∙ ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
Ω^Fibre≃∙⁻ zero f = (idEquiv _) , refl
Ω^Fibre≃∙⁻ (suc n) f =
  compEquiv∙
    ((isoToEquiv (invIso (ΩFibreIso (Ω^→ n f))))
    , (ΩFibreIso⁻∙ (Ω^→ n f)))
    (ΩIso (Ω^Fibre≃∙⁻ n f))

isHomogeneousΩ^→fib : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
  → isHomogeneous (((fiber (Ω^→ (suc n) f .fst) (snd ((Ω^ (suc n)) (fst B , snd B))))
                 , (snd ((Ω^ (suc n)) (fst A , snd A))) , (Ω^→ (suc n) f .snd)))
isHomogeneousΩ^→fib n f =
  subst isHomogeneous (ua∙ ((fst (Ω^Fibre≃∙ (suc n) f)))
                           (snd (Ω^Fibre≃∙ (suc n) f)))
                      (isHomogeneousPath _ _)

Ω^Fibre≃∙sect : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ((fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f)) ∘∙
            (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)))
          ≡ idfun∙ _
Ω^Fibre≃∙sect zero f = ΣPathP (refl , (sym (rUnit refl)))
Ω^Fibre≃∙sect (suc n) f =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt
      λ p → cong (fst (fst (ΩIso (Ω^Fibre≃∙⁻ n f))))
                   (leftInv (ΩFibreIso (Ω^→ n f))
                     ((fst (fst (ΩIso (Ω^Fibre≃∙ n f))) p)))
          ∙ sym (Ω→∘ (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
                 (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) p)
          ∙ (λ i → (Ω→ (Ω^Fibre≃∙sect n f i)) .fst p)
          ∙ sym (rUnit p))

Ω^Fibre≃∙retr : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ((fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) ∘∙
           (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f)))
          ≡ idfun∙ _
Ω^Fibre≃∙retr zero f = ΣPathP (refl , (sym (rUnit refl)))
Ω^Fibre≃∙retr (suc n) f =
    →∙Homogeneous≡ (isHomogeneousΩ^→fib n f)
      (funExt (λ p →
        cong (fun (ΩFibreIso (Ω^→ n f)))
          ((sym (Ω→∘ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))
                     (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
               (inv (ΩFibreIso (Ω^→ n f)) p)))
         ∙ (λ i → Ω→ (Ω^Fibre≃∙retr n f i) .fst (inv (ΩFibreIso (Ω^→ n f)) p))
         ∙ sym (rUnit (inv (ΩFibreIso (Ω^→ n f)) p)))
        ∙ rightInv (ΩFibreIso (Ω^→ n f)) p))

Ω^Fibre≃∙' : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
              ≃∙ ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
                , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd))
Ω^Fibre≃∙' zero f = idEquiv _ , refl
Ω^Fibre≃∙' (suc zero) f = ((isoToEquiv (ΩFibreIso (Ω^→ zero f))) , ΩFibreIso∙ (Ω^→ zero f))
Ω^Fibre≃∙' (suc (suc n)) f =
  compEquiv∙
    (ΩIso (Ω^Fibre≃∙ (suc n) f))
    ((isoToEquiv (ΩFibreIso (Ω^→ (suc n) f))) , ΩFibreIso∙ (Ω^→ (suc n) f))

-- The long exact sequence of loop spaces.
module ΩLES {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  {- Fibre of f -}
  fibf : Pointed _
  fibf = fiber (fst f) (pt B) , (pt A , snd f)

  {- Fibre of Ωⁿ f -}
  fibΩ^f : (n : ℕ) → Pointed _
  fibΩ^f n = (fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
         , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd)

  Ω^fibf : (n : ℕ) → Pointed _
  Ω^fibf n = (Ω^ n) fibf

  {- Helper function fib (Ωⁿ f) → Ωⁿ A -}
  fibΩ^f→A : (n : ℕ) → fibΩ^f n →∙ (Ω^ n) A
  fst (fibΩ^f→A n) = fst
  snd (fibΩ^f→A n) = refl

  {- The main function Ωⁿ(fib f) → Ωⁿ A, which is just the composition
  Ωⁿ(fib f) ≃ fib (Ωⁿ f) → Ωⁿ A, where the last function is
  fibΩ^f→A. Hence most proofs will concern fibΩ^f→A, since it is easier to
  work with. -}
  Ω^fibf→A : (n : ℕ) → Ω^fibf n →∙ (Ω^ n) A
  Ω^fibf→A n = fibΩ^f→A n ∘∙ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))

  {- The function preserves path composition -}
  Ω^fibf→A-pres∙ : (n : ℕ) → (p q : Ω^fibf (suc n) .fst)
    → Ω^fibf→A (suc n) .fst (p ∙ q)
     ≡ Ω^fibf→A (suc n) .fst p
     ∙ Ω^fibf→A (suc n) .fst q
  Ω^fibf→A-pres∙ n p q =
    cong (fst (fibΩ^f→A (suc n)))
      (cong (fun (ΩFibreIso (Ω^→ n f)))
        (Ω→pres∙ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f)))) p q))
    ∙ ΩFibreIsopres∙fst (Ω^→ n f)
        (fst (Ω→ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f))))) p)
        (fst (Ω→ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f))))) q)

  {- The function Ωⁿ A → Ωⁿ B -}
  A→B : (n : ℕ) → (Ω^ n) A →∙ (Ω^ n) B
  A→B n = Ω^→ n f

  {- It preserves path composition -}
  A→B-pres∙ : (n : ℕ) → (p q : typ ((Ω^ (suc n)) A))
            → fst (A→B (suc n)) (p ∙ q)
            ≡ fst (A→B (suc n)) p ∙ fst (A→B (suc n)) q
  A→B-pres∙ n p q = Ω^→pres∙ f n p q

  {- Helper function Ωⁿ⁺¹ B → fib (Ωⁿ f) -}
  ΩB→fibΩ^f : (n : ℕ) → ((Ω^ (suc n)) B) →∙ fibΩ^f n
  fst (ΩB→fibΩ^f n) x = (snd ((Ω^ n) A)) , (Ω^→ n f .snd ∙ x)
  snd (ΩB→fibΩ^f n) = ΣPathP (refl , (sym (rUnit _)))

  {- The main function Ωⁿ⁺¹ B → Ωⁿ (fib f),
     factoring through the above function -}
  ΩB→Ω^fibf : (n : ℕ) → (Ω^ (suc n)) B →∙ Ω^fibf n
  ΩB→Ω^fibf n =
       (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
    ∘∙ ΩB→fibΩ^f n

  {- It preserves path composition -}
  ΩB→Ω^fibf-pres∙ : (n : ℕ) → (p q : typ ((Ω^ (2 + n)) B))
    → fst (ΩB→Ω^fibf (suc n)) (p ∙ q)
     ≡ fst (ΩB→Ω^fibf (suc n)) p ∙ fst (ΩB→Ω^fibf (suc n)) q 
  ΩB→Ω^fibf-pres∙ n p q =
      cong (fst (fst (Ω^Fibre≃∙⁻ (suc n) f)))
        refl
    ∙ cong (fst (fst (ΩIso (Ω^Fibre≃∙⁻ n f))))
        (cong (fun (invIso (ΩFibreIso (Ω^→ n f))))
          (λ _ → snd ((Ω^ suc n) A) , Ω^→ (suc n) f .snd ∙ p ∙ q))
    ∙ cong (fst (fst (ΩIso (Ω^Fibre≃∙⁻ n f))))
           (ΩFibreIso⁻pres∙snd (Ω^→ n f) p q)
    ∙ ΩIsopres∙ (Ω^Fibre≃∙⁻ n f)
        (inv (ΩFibreIso (Ω^→ n f)) (refl , Ω→ (Ω^→ n f) .snd ∙ p))
        (inv (ΩFibreIso (Ω^→ n f)) (refl , Ω→ (Ω^→ n f) .snd ∙ q))

  {- Hence we have our sequence
     ... → Ωⁿ⁺¹B → Ωⁿ(fib f) → Ωⁿ A → Ωⁿ B → ...  (*)
     We first prove the exactness properties for the helper functions
     ΩB→fibΩ^f and fibΩ^f→A, and then deduce exactness of the whole sequence
     by noting that the functions in (*) are just ΩB→fibΩ^f, fibΩ^f→A but composed
     with equivalences
  -}
  private
    Im-fibΩ^f→A⊂Ker-A→B : (n : ℕ) (x : _)
                       → isInIm∙ (fibΩ^f→A n) x
                       → isInKer∙ (A→B n) x
    Im-fibΩ^f→A⊂Ker-A→B n x =
      uncurry λ p → J (λ x _ → isInKer∙ (A→B n) x)
        (snd p)

    Ker-fibΩ^f→A⊂Im-ΩB→fibΩ^f : (n : ℕ) (x : _)
                       → isInKer∙ (fibΩ^f→A n) x
                       → isInIm∙ (ΩB→fibΩ^f n) x
    Ker-fibΩ^f→A⊂Im-ΩB→fibΩ^f n x ker =
        (sym (Ω^→ n f .snd)
      ∙ cong (Ω^→ n f .fst) (sym ker) ∙ snd x) , ΣPathP ((sym ker) ,
      ((∙assoc (Ω^→ n f .snd) (sym (Ω^→ n f .snd)) (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)
      ∙∙ cong (_∙ (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)) (rCancel (Ω^→ n f .snd))
      ∙∙ sym (lUnit (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)))
      ◁ (λ i j → compPath-filler' (cong (Ω^→ n f .fst) (sym ker)) (snd x) (~ i) j)))

    Im-A→B⊂Ker-ΩB→fibΩ^f : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                       → isInIm∙ (A→B (suc n)) x
                       → isInKer∙ (ΩB→fibΩ^f n) x
    Im-A→B⊂Ker-ΩB→fibΩ^f n x =
      uncurry λ p
       → J (λ x _ → isInKer∙ (ΩB→fibΩ^f n) x)
         (ΣPathP (p , (((λ i → (λ j → Ω^→ n f .snd (j ∧ ~ i))
                             ∙ ((λ j → Ω^→ n f .snd (~ j ∧ ~ i))
                             ∙∙ cong (Ω^→ n f .fst) p
                             ∙∙ Ω^→ n f .snd))
                      ∙ sym (lUnit (cong (Ω^→ n f .fst) p ∙ Ω^→ n f .snd)))
                    ◁ λ i j → compPath-filler' (cong (Ω^→ n f .fst) p) (Ω^→ n f .snd) (~ i) j)))

    Ker-ΩB→fibΩ^f⊂Im-A→B : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                       → isInKer∙ (ΩB→fibΩ^f n) x
                       → isInIm∙ (A→B (suc n)) x
    fst (Ker-ΩB→fibΩ^f⊂Im-A→B n x inker) = cong fst inker
    snd (Ker-ΩB→fibΩ^f⊂Im-A→B n x inker) = pp
      where
      pp : fst (A→B (suc n)) (λ i → fst (inker i)) ≡ x
      pp i j =
        hcomp (λ k → λ { (i = i0) → doubleCompPath-filler
                                       (sym (snd (Ω^→ n f)))
                                       ((λ i → Ω^→ n f .fst (fst (inker i))))
                                       (snd (Ω^→ n f)) k j
                        ; (i = i1) → compPath-filler' (Ω^→ n f .snd) x (~ k) j
                        ; (j = i0) → snd (Ω^→ n f) k
                        ; (j = i1) → snd (Ω^→ n f) (k ∨ i)})
              (hcomp (λ k → λ { (i = i0) → (snd (inker j)) (~ k)
                               ; (i = i1) → ((Ω^→ n f .snd) ∙ x) (j ∨ ~ k)
                               ; (j = i0) → ((Ω^→ n f .snd) ∙ x) (~ k)
                               ; (j = i1) → snd (Ω^→ n f) (i ∨ ~ k)})
                      (snd ((Ω^ n) B)))

  {- Finally, we get exactness of the sequence
     we are interested in -}
  Im-Ω^fibf→A⊂Ker-A→B : (n : ℕ) (x : _)
                     → isInIm∙ (Ω^fibf→A n) x
                     → isInKer∙ (A→B n) x
  Im-Ω^fibf→A⊂Ker-A→B n x x₁ =
    Im-fibΩ^f→A⊂Ker-A→B n x
      (((fst (fst (Ω^Fibre≃∙ n f))) (fst x₁))
        , snd x₁)

  Ker-A→B⊂Im-Ω^fibf→A : (n : ℕ) (x : _)
                   → isInKer∙ (A→B n) x
                   → isInIm∙ (Ω^fibf→A n) x
  Ker-A→B⊂Im-Ω^fibf→A n x ker =
      invEq (fst (Ω^Fibre≃∙ n f)) (x , ker)
    , (cong fst (secEq (fst (Ω^Fibre≃∙ n f)) (x , ker)))

  Ker-Ω^fibf→A⊂Im-ΩB→Ω^fibf : (n : ℕ) (x : _)
                     → isInKer∙ (Ω^fibf→A n) x
                     → isInIm∙ (ΩB→Ω^fibf n) x
  Ker-Ω^fibf→A⊂Im-ΩB→Ω^fibf n x p =
      fst r
    , cong (fst ((fst (Ω^Fibre≃∙⁻ n f)))) (snd r)
    ∙ funExt⁻ (cong fst (Ω^Fibre≃∙sect n f)) x
    where
    r : isInIm∙ (ΩB→fibΩ^f n) (fst (fst (Ω^Fibre≃∙ n f)) x)
    r = Ker-fibΩ^f→A⊂Im-ΩB→fibΩ^f n (fst (fst (Ω^Fibre≃∙ n f)) x) p

  Im-ΩB→Ω^fibf⊂Ker-Ω^fibf→A : (n : ℕ) (x : _)
                     → isInIm∙ (ΩB→Ω^fibf n) x
                     → isInKer∙ (Ω^fibf→A n) x
  Im-ΩB→Ω^fibf⊂Ker-Ω^fibf→A n x =
    uncurry λ p →
      J (λ x _ → isInKer∙ (Ω^fibf→A n) x)
        (cong (fst (fibΩ^f→A n))
          (funExt⁻ (cong fst (Ω^Fibre≃∙retr n f)) _))

  Im-A→B⊂Ker-ΩB→Ω^fibf : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInIm∙ (A→B (suc n)) x
                     → isInKer∙ (ΩB→Ω^fibf n) x
  Im-A→B⊂Ker-ΩB→Ω^fibf n x p =
      cong (fst ((fst (Ω^Fibre≃∙⁻ n f))))
           (Im-A→B⊂Ker-ΩB→fibΩ^f n x p)
    ∙ snd (Ω^Fibre≃∙⁻ n f)

  Ker-ΩB→Ω^fibf⊂Im-A→B : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInKer∙ (ΩB→Ω^fibf n) x
                     → isInIm∙ (A→B (suc n)) x
  Ker-ΩB→Ω^fibf⊂Im-A→B n x p =
    Ker-ΩB→fibΩ^f⊂Im-A→B n x
         (funExt⁻ (cong fst (sym (Ω^Fibre≃∙retr n f))) (ΩB→fibΩ^f n .fst x)
        ∙ cong (fst (fst (Ω^Fibre≃∙ n f))) p
        ∙ snd (Ω^Fibre≃∙ n f))

{- Some useful lemmas for converting the above sequence to on for
   homotopy groups -}
module setTruncLemmas {ℓ ℓ' ℓ'' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (n m l : ℕ)
  (f : (Ω ((Ω^ n) A)) →∙ (Ω ((Ω^ m) B)))
  (g : (Ω ((Ω^ m) B)) →∙ (Ω ((Ω^ l) C)))
  (e₁ : IsGroupHom (snd (πGr n A)) (sMap (fst f)) (snd (πGr m B)))
  (e₂ : IsGroupHom (snd (πGr m B)) (sMap (fst g)) (snd (πGr l C))) where

  ker⊂im : ((x : typ (Ω ((Ω^ m) B))) → isInKer∙ g x → isInIm∙ f x)
         → (x : π (suc m) B) → isInKer (_ , e₂) x → isInIm (_  , e₁) x
  ker⊂im ind =
    sElim (λ _ → isSetΠ λ _ → isProp→isSet squash)
      λ p ker →
        pRec squash
        (λ ker∙ → ∣ ∣ ind p ker∙ .fst ∣₂ , cong ∣_∣₂ (ind p ker∙ .snd) ∣ )
        (fun PathIdTrunc₀Iso ker)

  im⊂ker : ((x : typ (Ω ((Ω^ m) B))) → isInIm∙ f x → isInKer∙ g x)
        → (x : π (suc m) B) → isInIm (_  , e₁) x → isInKer (_ , e₂) x
  im⊂ker ind =
    sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
      λ p →
       pRec (squash₂ _ _)
       (uncurry (sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
         λ a q → pRec (squash₂ _ _)
                       (λ q → cong ∣_∣₂ (ind p (a , q)))
                       (fun PathIdTrunc₀Iso q)))

{- The long exact sequence of homotopy groups -}
module πLES {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  module Ωs = ΩLES f 
  open Ωs renaming (A→B to A→B')

  fib = fibf

  fib→A : (n : ℕ) → GroupHom (πGr n fib) (πGr n A)
  fst (fib→A n) = sMap (fst (Ω^fibf→A (suc n)))
  snd (fib→A n) =
    makeIsGroupHom
      (sElim2 (λ _  _ → isSetPathImplicit)
        λ p q → cong ∣_∣₂ (Ω^fibf→A-pres∙ n p q))

  A→B : (n : ℕ) → GroupHom (πGr n A) (πGr n B)
  fst (A→B n) = sMap (fst (A→B' (suc n)))
  snd (A→B n) =
    makeIsGroupHom
      (sElim2 (λ _  _ → isSetPathImplicit)
        λ g h → cong ∣_∣₂ (Ω^→pres∙ f n g h))

  B→fib : (n : ℕ) → GroupHom (πGr (suc n) B) (πGr n fib)
  fst (B→fib n) = sMap (fst (ΩB→Ω^fibf (suc n)))
  snd (B→fib n) =
    makeIsGroupHom
      (sElim2
        (λ _  _ → isSetPathImplicit)
        λ p q → cong ∣_∣₂ (ΩB→Ω^fibf-pres∙ n p q))

  Ker-A→B⊂Im-fib→A : (n : ℕ) (x : π (suc n) A)
    → isInKer (A→B n) x
    → isInIm (fib→A n) x
  Ker-A→B⊂Im-fib→A n =
    setTruncLemmas.ker⊂im n n n
      (Ω^fibf→A (suc n)) (A→B' (suc n))
      (snd (fib→A n)) (snd (A→B n))
      (Ker-A→B⊂Im-Ω^fibf→A (suc n))

  Im-fib→A⊂Ker-A→B : (n : ℕ) (x : π (suc n) A)
    → isInIm (fib→A n) x
    → isInKer (A→B n) x
  Im-fib→A⊂Ker-A→B n =
    setTruncLemmas.im⊂ker n n n
      (Ω^fibf→A (suc n)) (A→B' (suc n))
      (snd (fib→A n)) (snd (A→B n))
      (Im-Ω^fibf→A⊂Ker-A→B (suc n))

  Ker-fib→A⊂Im-B→fib : (n : ℕ) (x : π (suc n) fib)
    → isInKer (fib→A n) x
    → isInIm (B→fib n) x
  Ker-fib→A⊂Im-B→fib n =
    setTruncLemmas.ker⊂im (suc n) n n
      (ΩB→Ω^fibf (suc n)) (Ω^fibf→A (suc n))
      (snd (B→fib n)) (snd (fib→A n))
      (Ker-Ω^fibf→A⊂Im-ΩB→Ω^fibf (suc n))

  Im-B→fib⊂Ker-fib→A : (n : ℕ) (x : π (suc n) fib)
    → isInIm (B→fib n) x
    → isInKer (fib→A n) x
  Im-B→fib⊂Ker-fib→A n =
    setTruncLemmas.im⊂ker (suc n) n n
      (ΩB→Ω^fibf (suc n)) (Ω^fibf→A (suc n))
      (snd (B→fib n)) (snd (fib→A n))
      (Im-ΩB→Ω^fibf⊂Ker-Ω^fibf→A (suc n))

  Im-A→B⊂Ker-B→fib : (n : ℕ) (x : π (suc (suc n)) B)
    → isInIm (A→B (suc n)) x
    → isInKer (B→fib n) x
  Im-A→B⊂Ker-B→fib n =
    setTruncLemmas.im⊂ker (suc n) (suc n) n
      (A→B' (suc (suc n))) (ΩB→Ω^fibf (suc n))
      (snd (A→B (suc n))) (snd (B→fib n))
      (Im-A→B⊂Ker-ΩB→Ω^fibf (suc n))

  Ker-B→fib⊂Im-A→B : (n : ℕ) (x : π (suc (suc n)) B)
    → isInKer (B→fib n) x
    → isInIm (A→B (suc n)) x
  Ker-B→fib⊂Im-A→B n =
    setTruncLemmas.ker⊂im (suc n) (suc n) n
      (A→B' (suc (suc n))) (ΩB→Ω^fibf (suc n))
      (snd (A→B (suc n))) (snd (B→fib n))
      (Ker-ΩB→Ω^fibf⊂Im-A→B (suc n))

-- Often, we prefer thinking of Ωⁿ A as (Sⁿ →∙ A).
-- The goal of the following lemmas is to show that the maps
-- Ωⁿ A → Ωⁿ B and Ωⁿ (fib f) →∙ Ωⁿ A get sent to post composition
-- under the equivalence Ωⁿ A as (Sⁿ →∙ A)

{- We first need to prove that the map Ωⁿ(fib f) → Ωⁿ A indeed is just the map
Ωⁿ fst -}
private
  Ω^fibf→A-ind : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ΩLES.Ω^fibf→A f (suc n) ≡ Ω→ (ΩLES.Ω^fibf→A f n)
  Ω^fibf→A-ind {A = A} {B = B} n f =
      (λ _ → πLES.Ωs.fibΩ^f→A f (suc n) ∘∙ (fst (fst (Ω^Fibre≃∙ (suc n) f)) , snd (Ω^Fibre≃∙ (suc n) f)))
    ∙ →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt λ p → (λ j → cong fst (Ω→ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) .fst p))
                  ∙ rUnit ((λ i →
           fst
           (Ω→ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) .fst p i)))
                  ∙ sym (Ω→∘ (πLES.Ωs.fibΩ^f→A f n) ((fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))) p))

Ω^fibf→A≡ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
      → ΩLES.Ω^fibf→A f n ≡ Ω^→ n (fst , refl)
Ω^fibf→A≡ zero f = ΣPathP (refl , (sym (lUnit refl)))
Ω^fibf→A≡ (suc n) f = Ω^fibf→A-ind n f ∙ cong Ω→ (Ω^fibf→A≡ n f)

-- The goal is not to show that Ωⁿ f : (Ωⁿ A → Ωⁿ B)
-- is taken to post composition : (Sⁿ →∙ A) → (Sⁿ →∙ B)
-- The following lemmas is not pretty but very helpful
private
  bigLemma : ∀ {ℓ ℓ'} {A₁ B₁ C₁ : Type ℓ} {A₂ B₂ C₂ : Type ℓ'}
             (A₁→B₁ : A₁ ≃ B₁) (B₁→C₁ : B₁ ≃ C₁)
             (A₂→B₂ : A₂ ≃ B₂) (B₂→C₂ : B₂ ≃ C₂)
             (A₁→A₂ : A₁ → A₂)
             (B₁→B₂ : B₁ → B₂)
             (C₁→C₂ : C₁ → C₂)
          → (B₁→B₂ ∘ (fst A₁→B₁)) ≡ (fst A₂→B₂ ∘ A₁→A₂)
          → C₁→C₂ ∘ fst B₁→C₁ ≡ fst B₂→C₂ ∘ B₁→B₂
          → C₁→C₂ ∘ fst B₁→C₁ ∘ fst A₁→B₁
          ≡ fst B₂→C₂ ∘ fst A₂→B₂ ∘ A₁→A₂
  bigLemma {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂} =
    EquivJ
      (λ A₁ A₁→B₁ → (B₁→C₁ : B₁ ≃ C₁) (A₂→B₂ : A₂ ≃ B₂)
        (B₂→C₂ : B₂ ≃ C₂) (A₁→A₂ : A₁ → A₂) (B₁→B₂ : B₁ → B₂)
        (C₁→C₂ : C₁ → C₂) →
        B₁→B₂ ∘ fst A₁→B₁ ≡ fst A₂→B₂ ∘ A₁→A₂ →
        C₁→C₂ ∘ fst B₁→C₁ ≡ fst B₂→C₂ ∘ B₁→B₂ →
        C₁→C₂ ∘ fst B₁→C₁ ∘ fst A₁→B₁ ≡ fst B₂→C₂ ∘ fst A₂→B₂ ∘ A₁→A₂)
      (EquivJ (λ B₁ B₁→C₁ → (A₂→B₂ : A₂ ≃ B₂) (B₂→C₂ : B₂ ≃ C₂)
        (A₁→A₂ : B₁ → A₂) (B₁→B₂ : B₁ → B₂) (C₁→C₂ : C₁ → C₂) →
        (B₁→B₂) ≡ (fst A₂→B₂ ∘ A₁→A₂) →
        (C₁→C₂ ∘ (fst B₁→C₁)) ≡ (fst B₂→C₂ ∘ (B₁→B₂)) →
        (C₁→C₂ ∘ (fst B₁→C₁)) ≡ (fst B₂→C₂ ∘ (fst A₂→B₂ ∘ A₁→A₂)))
        (EquivJ (λ A₂ A₂→B₂ → (B₂→C₂ : B₂ ≃ C₂) (A₁→A₂ : C₁ → A₂)
          (B₁→B₂ : C₁ → B₂) (C₁→C₂ : C₁ → C₂) →
          B₁→B₂ ≡ (fst A₂→B₂ ∘ A₁→A₂) →
          (C₁→C₂) ≡ (fst B₂→C₂ ∘ B₁→B₂) →
          (C₁→C₂) ≡ fst B₂→C₂ ∘ (fst A₂→B₂ ∘ A₁→A₂))
          (EquivJ (λ B₂ B₂→C₂ → (A₁→A₂ B₁→B₂ : C₁ → B₂) (C₁→C₂ : C₁ → C₂) →
        B₁→B₂ ≡ A₁→A₂ →
        C₁→C₂ ≡ (fst B₂→C₂ ∘ B₁→B₂) →
        C₁→C₂ ≡ (fst B₂→C₂ ∘ A₁→A₂))
          λ _ _ _ p q → q ∙ p)))

{-
We want to show that the following square
commutes.

       Ωⁿ f
Ωⁿ A ----------→ Ωⁿ B
|                  |
|                  |
v         f∘_      v
(Sⁿ→∙A) ------> (Sⁿ→∙B)
-}

Ω^→≈post∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
                → (f : A →∙ B)
                → Path ((Ω^ (suc n)) A →∙ (S₊∙ (suc n) →∙ B ∙))
                        (post∘∙ (S₊∙ (suc n)) f ∘∙ Ω→SphereMap∙ (suc n))
                        (Ω→SphereMap∙ (suc n) ∘∙ Ω^→ (suc n) f)
Ω^→≈post∘∙ {A = A} {B = B} zero f =
    →∙Homogeneous≡
       (subst isHomogeneous
        (ua∙ (Ω→SphereMap 1 , (isEquiv-Ω→SphereMap 1)) (Ω→SphereMap∙ 1 {A = B} .snd))
    (isHomogeneousPath _ _))
    (funExt λ p →
      ΣPathP ((funExt (λ { base → snd f
                        ; (loop i) j →
                          doubleCompPath-filler (sym (snd f)) (cong (fst f) p) (snd f) j i}))
            , (sym (lUnit (snd f)) ◁ λ i j → snd f (i ∨ j))))
Ω^→≈post∘∙ {A = A} {B = B} (suc n) f =
  →∙Homogeneous≡
    (subst isHomogeneous
      (ua∙ (Ω→SphereMap (2 + n) , (isEquiv-Ω→SphereMap (2 + n)))
           (Ω→SphereMap∙ (2 + n) {A = B} .snd))
           (isHomogeneousPath _ _))
    ((funExt λ p
        → (λ i → post∘∙ (S₊∙ (2 + n)) f .fst (Ω→SphereMap-split (suc n) p i))
        ∙∙ funExt⁻ (bigLemma
                     (Ω→SphereMapSplit₁ (suc n) , isEquivΩ→ _ (isEquiv-Ω→SphereMap (suc n)))
                     (ΩSphereMap (suc n) , isoToIsEquiv (invIso (SphereMapΩIso (suc n))))
                     (Ω→SphereMapSplit₁ (suc n) , isEquivΩ→ _ (isEquiv-Ω→SphereMap (suc n)))
                     (ΩSphereMap (suc n) , isoToIsEquiv (invIso (SphereMapΩIso (suc n))))
                     (Ω^→ (2 + n) f .fst) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst)
                     (post∘∙ (S₊∙ (2 + n)) f .fst)
                     (funExt topSquare)
                     (sym (funExt (bottomSquare f))))
                     p
        ∙∙ sym (Ω→SphereMap-split (suc n) (Ω^→ (2 + n) f .fst p))))
  where
  topSquare : (p : typ ((Ω^ (2 + n)) A))
           → Path (typ (Ω ((S₊∙ (suc n)) →∙ B ∙)))
                  ((Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst ∘ Ω→ (Ω→SphereMap∙ (suc n)) .fst) p)
                  (((Ω→ (Ω→SphereMap∙ (suc n))) .fst ∘ (Ω^→ (suc (suc n)) f .fst)) p)
  topSquare p = sym (Ω→∘ (post∘∙ (S₊∙ (suc n)) f) (Ω→SphereMap∙ (suc n)) p)
              ∙ (λ i → Ω→ (Ω^→≈post∘∙ {A = A} {B = B} n f i) .fst p)
              ∙ Ω→∘ (Ω→SphereMap∙ (suc n)) (Ω^→ (suc n) f) p

  bottomSquare : (f : A →∙ B) (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
    → Path (S₊∙ (2 + n) →∙ B)
            (ΩSphereMap (suc n) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst g))
            ((post∘∙ (S₊∙ (2 + n)) f .fst ∘ ΩSphereMap (suc n)) g)
  bottomSquare =
    →∙J (λ b₀ f → (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
            → Path (S₊∙ (suc (suc n)) →∙ (fst B , b₀))
            (ΩSphereMap (suc n) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst g))
            ((post∘∙ (S₊∙ (suc (suc n))) f .fst ∘ ΩSphereMap (suc n)) g))
           λ f g → ΣPathP ((funExt (λ { north → refl
                                       ; south → refl
                                       ; (merid a i) j → h f g a j i}))
                        , lUnit refl)
    where
    h : (f : typ A → typ B) (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
      → (a : S₊ (suc n))
      → cong (fst (ΩSphereMap (suc n) (Ω→ (post∘∙ (S₊∙ (suc n)) (f , refl)) .fst g))) (merid a)
        ≡ cong (fst ((f , refl) ∘∙ ΩSphereMap (suc n) g)) (merid a)
    h f g a =
      (λ i → funExt⁻ (cong-∙∙ fst (sym (snd (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))))
                                  (cong (fst (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))) g)
                                  (snd (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))) i) a)
              ∙ sym (rUnit (λ i → f (fst (g i) a)))

{- We can use this to define prove that post composition induces a homomorphism
πₙ A → πₙ B-}
π∘∙raw : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → π' (suc n) A → π' (suc n) B
π∘∙raw n f = sMap (f ∘∙_)

GroupHomπ≅π'PathP : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (n : ℕ)
                  → GroupHom (πGr n A) (πGr n B) ≡ GroupHom (π'Gr n A) (π'Gr n B)
GroupHomπ≅π'PathP A B n i = 
  GroupHom (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i))
           (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n B)) (~ i))

private
  π∘∙' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
          → GroupHom (π'Gr n A) (π'Gr n B)
  π∘∙' {A = A} {B = B} n f =
    transport (λ i → GroupHomπ≅π'PathP A B n i)
              (πLES.A→B f n)

  π∘∙'≡π∘∙raw : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
    (n : ℕ) (f : A →∙ B) → π∘∙' n f .fst ≡ π∘∙raw n f
  π∘∙'≡π∘∙raw n f =
    funExt (sElim (λ _ → isSetPathImplicit)
      λ g → cong ∣_∣₂
        ((λ i → inv (IsoSphereMapΩ (suc n))
            (transportRefl (fst (πLES.Ωs.A→B f (suc n))
              (transportRefl (fun (IsoSphereMapΩ (suc n)) g) i)) i))
       ∙ sym (funExt⁻ (cong fst (Ω^→≈post∘∙ n f)) (fun (IsoSphereMapΩ (suc n)) g))
       ∙ cong (f ∘∙_) (leftInv (IsoSphereMapΩ (suc n)) g)))

π∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
       → GroupHom (π'Gr n A) (π'Gr n B)
fst (π∘∙ n f) = sMap (f ∘∙_)
snd (π∘∙ {A = A} {B = B} n f) = isHom∘∙
  where
  abstract
    isHom∘∙ : IsGroupHom (π'Gr n A .snd) (fst (π∘∙ n f)) (π'Gr n B .snd)
    isHom∘∙ =
      transport (λ i → IsGroupHom (π'Gr n A .snd)
                                   (π∘∙'≡π∘∙raw n f i)
                                   (π'Gr n B .snd))
                (π∘∙' n f .snd)

π∘∙A→B-PathP : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP A B n i)
           (πLES.A→B f n)
           (π∘∙ n f)
π∘∙A→B-PathP n f = toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _) (π∘∙'≡π∘∙raw n f))

π∘∙fib→A-PathP : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP (ΩLES.fibf f) A n i)
           (πLES.fib→A f n)
           (π∘∙ n (fst , refl))
π∘∙fib→A-PathP {A = A} {B = B} n f =
  toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (cong (transport
      (λ i → (fst (GroupPath _ _)
               (GroupIso→GroupEquiv (π'Gr≅πGr n (ΩLES.fibf f))) (~ i)) .fst
           → (fst (GroupPath _ _)
               (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i)) .fst))
          lem
   ∙ π∘∙'≡π∘∙raw n (fst , refl)))
  where
  lem : πLES.fib→A f n .fst ≡ sMap (Ω^→ (suc n) (fst , refl) .fst)
  lem = cong sMap (cong fst (Ω^fibf→A≡ (suc n) f))

open import Cubical.Homotopy.Hopf
open import Cubical.Algebra.Group.Exact
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Algebra.Group.Instances.Unit renaming (Unit to UnitGr)

TotalHopf→∙S² : (Σ (S₊ 2) S¹Hopf , north , base) →∙ S₊∙ 2
fst TotalHopf→∙S² = fst
snd TotalHopf→∙S² = refl

IsoTotalSpaceJoin' : Iso (Σ (S₊ 2) S¹Hopf) (S₊ 3)
IsoTotalSpaceJoin' = compIso hopfS¹.IsoTotalSpaceJoin (IsoSphereJoin 1 1)

fiberTotalHopf : Iso (fiber (fst TotalHopf→∙S²) north) S¹
fun fiberTotalHopf ((x , y) , z) = subst S¹Hopf z y
inv fiberTotalHopf x = (north , x) , refl
rightInv fiberTotalHopf x = refl
leftInv fiberTotalHopf ((x , y) , z) =
  ΣPathP ((ΣPathP (sym z , (λ i → transp (λ j → S¹Hopf (z (~ i ∧ j))) i y)))
         , (λ j i → z (i ∨ ~ j)))

fiberTotalHopf∙≡ : (fiber (fst TotalHopf→∙S²) north , (north , base) , refl) ≡ S₊∙ 1
fiberTotalHopf∙≡ = ua∙ (isoToEquiv fiberTotalHopf) refl

-- IsoSphereMapΩ : ?



--- Hopf stuff


private
  transportGroupEquiv : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
    → isEquiv (fst (πLES.A→B f n))
    → isEquiv (fst (π∘∙ n f))
  transportGroupEquiv n f iseq = transport (λ i → isEquiv (fst (π∘∙A→B-PathP n f i))) iseq


π₃S²≅π₃TotalHopf : GroupEquiv (πGr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                              (πGr 2 (S₊∙ 2))
fst (fst π₃S²≅π₃TotalHopf) = fst (πLES.A→B TotalHopf→∙S² 2)
snd (fst π₃S²≅π₃TotalHopf) =
  SES→isEquiv
    (isContr→≡UnitGroup
      (subst isContr (cong (π 3) (sym fiberTotalHopf∙≡))
        (∣ refl ∣₂ , (sElim (λ _ → isSetPathImplicit)
          (λ p → cong ∣_∣₂ (isOfHLevelSuc 3 isGroupoidS¹ _ _ _ _ _ _ refl p))))))
    (isContr→≡UnitGroup
      (subst isContr (cong (π 2) (sym fiberTotalHopf∙≡))
        (∣ refl ∣₂ , (sElim (λ _ → isSetPathImplicit) (λ p
                    → cong ∣_∣₂ (isGroupoidS¹ _ _ _ _ refl p))))))
    (πLES.fib→A TotalHopf→∙S² 2)
    (πLES.A→B TotalHopf→∙S² 2)
    (πLES.B→fib TotalHopf→∙S² 1)
    (πLES.Ker-A→B⊂Im-fib→A TotalHopf→∙S² 2)
    (πLES.Ker-B→fib⊂Im-A→B TotalHopf→∙S² 1)
snd π₃S²≅π₃TotalHopf = snd (πLES.A→B TotalHopf→∙S² 2)

π'₃S²≅π'₃TotalHopf : GroupEquiv (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                                (π'Gr 2 (S₊∙ 2))
fst (fst π'₃S²≅π'₃TotalHopf) = fst (π∘∙ 2 TotalHopf→∙S²)
snd (fst π'₃S²≅π'₃TotalHopf) =
  transportGroupEquiv 2 TotalHopf→∙S² (π₃S²≅π₃TotalHopf .fst .snd)
snd π'₃S²≅π'₃TotalHopf = snd (π∘∙ 2 TotalHopf→∙S²)

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Properties
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)
open import Cubical.Algebra.Group.Instances.Int renaming (ℤ to ℤGroup)

open import Cubical.Homotopy.Group.SuspensionMap

susper : (n : ℕ) → GroupHom (π'Gr n (S₊∙ (suc n))) (π'Gr (suc n) (S₊∙ (suc (suc n))))
susper n = suspMapπ'Hom n

susper' : (n : ℕ) → (S₊∙ (suc n) →∙ S₊∙ (suc n)) → S₊∙ (2 + n) →∙ S₊∙ (2 + n)
susper' n = suspMap {A = S₊∙ (suc n)} n

lem : (n : ℕ) → isConnectedFun 2 (susper' (suc n))
lem n =
  isConnectedFunSubtr 2 n _
    (subst (λ x → isConnectedFun x (susper' (suc n)))
                   (subtrLem n (suc (suc n)) ∙ +-comm 2 n)
      (isConnectedSuspMap (suc n) (suc n)))
  where
  subtrLem : (n m : ℕ) → (n + m ∸ n) ≡ m 
  subtrLem zero m = refl
  subtrLem (suc n) m = subtrLem n m

suspIso : (n : ℕ) → Iso ∥ (S₊∙ (2 + n) →∙ S₊∙ (2 + n)) ∥₂ ∥ S₊∙ (3 + n) →∙ S₊∙ (3 + n) ∥₂
suspIso n =
  compIso setTruncTrunc2Iso
   (compIso (connectedTruncIso 2 (suspMap {A = S₊∙ (suc (suc n))} (suc n)) (lem n))
     (invIso (setTruncTrunc2Iso)))

suspGrIso : (n : ℕ) → GroupIso (π'Gr (suc n) (S₊∙ (2 + n))) (π'Gr (2 + n) (S₊∙ (3 + n)))
fst (suspGrIso n) = suspIso n
snd (suspGrIso n) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → IsGroupHom.pres· (suspMapπ'Hom (suc n) .snd) ∣ f ∣₂ ∣ g ∣₂)


open import Cubical.Foundations.Equiv.HalfAdjoint

stLoop₁ : π 2 (S₊∙ 2)
stLoop₁ = ∣ sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base) ∣₂

stLoop₁flip : π 2 (S₊∙ 2)
stLoop₁flip =
  ∣ flipSquare (sym (rCancel (merid base))
  ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
  ∙∙ rCancel (merid base)) ∣₂

flipLoopIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → GroupIso (πGr (suc n) A) (πGr (suc n) A)
fun (fst (flipLoopIso n)) = sMap flipSquare
inv (fst (flipLoopIso n)) = sMap flipSquare
rightInv (fst (flipLoopIso n)) =
  sElim (λ _ → isSetPathImplicit) λ _ → refl
leftInv (fst (flipLoopIso n)) =
  sElim (λ _ → isSetPathImplicit) λ _ → refl
snd (flipLoopIso n) =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂
        ((sym (sym≡flipSquare (f ∙ g))
      ∙∙ symDistr f g
      ∙∙ cong₂ _∙_ (sym≡flipSquare g) (sym≡flipSquare f)
       ∙ EH n (flipSquare g) (flipSquare f))))

setTruncTrunc2IsoFunct : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : hLevelTrunc 2 (x ≡ x))
  → inv setTruncTrunc2Iso
       (Cubical.HITs.Truncation.map2 _∙_ p q)
     ≡ ·π 0 (inv setTruncTrunc2Iso p) (inv setTruncTrunc2Iso q)
setTruncTrunc2IsoFunct =
  trElim2 (λ  _ _ → isSetPathImplicit) λ _ _ → refl

π'₂S²≅π₂S² : GroupIso (π'Gr 1 (S₊∙ 2)) (πGr 1 (S₊∙ 2))
π'₂S²≅π₂S² = π'Gr≅πGr 1 (S₊∙ 2)

π'₂S²≅π₂S²⁻-stLoop' : inv (fst (π'₂S²≅π₂S²)) stLoop₁flip ≡ ∣ idfun∙ _ ∣₂
π'₂S²≅π₂S²⁻-stLoop' =
  cong ∣_∣₂ (ΣPathP ((funExt
    (λ { north → refl
       ; south → merid base
       ; (merid base i) j →
         hcomp (λ k → λ {(i = i0) → north
                        ; (i = i1) → merid base (j ∧ k)
                        ; (j = i0) → rUnit (λ _ → north) k i
                        ; (j = i1) → merid base (i ∧ k)})
               north
       ; (merid (loop k) i) j
                → hcomp (λ r → λ {(i = i0) → north
                           ; (i = i1) → merid base (j ∧ r)
                           ; (j = i0) → rUnit (funExt⁻ (cong fst (cong (Ω→SphereMap 1)
                                                     (flipSquare ((λ i₁ → rCancel (merid base) (~ i₁)) ∙∙
                                                     (λ i₁ → merid (loop i₁) ∙ (λ i₂ → merid base (~ i₂))) ∙∙
                                                     rCancel (merid base))))) (loop k)) r i
                           ; (j = i1) → pp r i k})
                    ((((λ i₁ → rCancel (merid base) (~ i₁)) ∙∙
                       (λ i₁ → merid (loop i₁) ∙ (λ i₂ → merid base (~ i₂))) ∙∙
                       rCancel (merid base))) k i)})) , refl))
  where
  genBot+side : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
              → Cube {A = A} (λ j r → x) (λ j r → p (~ j ∨ r))
                              (λ i r → p i) (λ i r → p (i ∧ r))
                              (λ i j → p (i ∧ ~ j)) (λ i j → p i)
               × Cube {A = A} (λ j r → p (~ j ∨ r)) (λ j r → p (r ∧ j))
                              (λ k r → p (~ k)) (λ k r → p r)
                              (λ k j → p (~ k ∧ ~ j)) λ k j → p (j ∨ ~ k)
  genBot+side {A = A} {x = x} =
    J (λ y p → Cube {A = A} (λ j r → x) (λ j r → p (~ j ∨ r))
                              (λ i r → p i) (λ i r → p (i ∧ r))
                              (λ i j → p (i ∧ ~ j)) (λ i j → p i)
               × Cube {A = A} (λ j r → p (~ j ∨ r)) (λ j r → p (r ∧ j))
                              (λ k r → p (~ k)) (λ k r → p r)
                              (λ k j → p (~ k ∧ ~ j)) λ k j → p (j ∨ ~ k))
       (refl , refl)

  pp1 : Cube {A = S₊ 2} (λ i _ → (merid base ∙ sym (merid base)) i)
             (λ i r → merid base (i ∧ r))
             (λ j r → north)
             (λ j r → merid base (r ∧ j))
             (λ j i → rCancel (merid base) j i)
             λ j i → compPath-filler (merid base) (sym (merid base)) (~ j) i
  pp1 j i r =
    hcomp (λ k → λ {(i = i0) → north
                   ; (i = i1) → genBot+side (merid base) .snd k j r
                   ; (j = i0) → compPath-filler (merid base) (sym (merid base)) k i
                   ; (j = i1) → merid base (i ∧ r)
                   ; (r = i0) → rCancel-filler (merid base) k j i
                   ; (r = i1) → compPath-filler (merid base) (sym (merid base)) (~ j ∧ k) i})
          (genBot+side (merid base) .fst i j r)

  pp : Cube (λ i k → (((λ i₁ → rCancel (merid base) (~ i₁)) ∙∙
                       (λ i₁ → merid (loop i₁) ∙ (λ i₂ → merid base (~ i₂))) ∙∙
                       rCancel (merid base))) k i) -- r i k
            (λ i k → merid (loop k) i)
            (λ r k → north)
            (λ r k → merid base r)
            (λ i j → merid base (i ∧ j))
            λ i j → merid base (i ∧ j)
  pp r i k =
    hcomp (λ j → λ {(i = i0) → north
                   ; (i = i1) → merid base (r ∧ j)
                   ; (r = i0) → doubleCompPath-filler
                                  (sym (rCancel (merid base)))
                                  (λ i₁ → merid (loop i₁) ∙ sym (merid base))
                                  (rCancel (merid base)) j k i
                   ; (r = i1) → compPath-filler (merid (loop k)) (sym (merid base)) (~ j) i
                   ; (k = i0) → pp1 j i r
                   ; (k = i1) → pp1 j i r})
          ((merid (loop k) ∙ sym (merid base)) i)

π₂S²≅π₁S¹ : GroupIso (πGr 1 (S₊∙ 2)) (πGr 0 (S₊∙ 1))
fst π₂S²≅π₁S¹ =
  compIso setTruncTrunc2Iso
   (compIso
    (compIso (invIso (PathIdTruncIso 2))
     (compIso (congIso (invIso (PathIdTruncIso 3)))
      (compIso
        (congIso (invIso (Iso-Kn-ΩKn+1 1)))
        (PathIdTruncIso 2))))
    (invIso setTruncTrunc2Iso))
snd π₂S²≅π₁S¹ =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
            λ f g →
              cong (inv setTruncTrunc2Iso)
                (cong (fun (PathIdTruncIso 2))
                  (cong (cong (ΩKn+1→Kn 1))
                    (cong (cong (inv (PathIdTruncIso 3)))
                      (cong (inv (PathIdTruncIso 2))
                        (refl {x = ∣ f ∙ g ∣})
                     ∙ cong-∙ ∣_∣ₕ f g)
                   ∙ cong-∙ (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ f) (cong ∣_∣ₕ g))
                 ∙ cong-∙ (ΩKn+1→Kn 1) (cong (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ f))
                                        ((cong (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ g))))
               ∙ PathIdTruncIsoFunct 1 (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ f i ∣ₕ))
                                       (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ g i ∣ₕ)))
               ∙ setTruncTrunc2IsoFunct
                  ((fun (PathIdTruncIso 2)) (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ f i ∣ₕ)))
                  ((fun (PathIdTruncIso 2)) (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ g i ∣ₕ))))

π₂S²≅π₁S¹-stLoop : fun (fst π₂S²≅π₁S¹) stLoop₁ ≡ ∣ loop ∣₂
π₂S²≅π₁S¹-stLoop =
    sym (leftInv (compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)
        (fun (fst π₂S²≅π₁S¹) stLoop₁))
 ∙∙ cong (inv (compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ))
         compute
 ∙∙ leftInv (compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)
            ∣ loop ∣₂
  where
  compute : fun ((compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ))
                (fun (fst π₂S²≅π₁S¹) stLoop₁)
           ≡ fun ((compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ))
                ∣ loop ∣₂
  compute = refl

stLoop2 : GroupIso (π'Gr 1 (S₊∙ 2)) (π'Gr 0 (S₊∙ 1))
stLoop2 =
  compGroupIso (π'Gr≅πGr 1 (S₊∙ 2))
    (compGroupIso (flipLoopIso 0)
      (compGroupIso π₂S²≅π₁S¹
        (invGroupIso (π'Gr≅πGr 0 (S₊∙ 1)))))

stLoop2≡helper : (x : _) (y : π 2 (S₊∙ 2))
   → (x ≡ inv (fst π'₂S²≅π₂S²) (fun (fst (flipLoopIso 0)) y))
   → inv (fst (π'Gr≅πGr zero (S₊∙ 1))) (fun (fst π₂S²≅π₁S¹) y) ≡ ∣ idfun∙ _ ∣₂
   → fun (fst stLoop2) x ≡ ∣ idfun∙ _ ∣₂
stLoop2≡helper x y p q =
     cong (fun (fst stLoop2)) p
  ∙∙ (λ i → inv (fst (π'Gr≅πGr zero (S₊∙ (suc zero)))) (fun (fst π₂S²≅π₁S¹)
      (fun (fst (flipLoopIso zero))
        (rightInv
          (fst (π'Gr≅πGr (suc zero) (S₊∙ (suc (suc zero)))))
          (inv (fst (flipLoopIso zero)) y) i)
      )))
  ∙∙ cong (inv (fst (π'Gr≅πGr zero (S₊∙ (suc zero)))))
          (cong (fun (fst π₂S²≅π₁S¹))
            (rightInv (fst (flipLoopIso zero)) y))
   ∙ q

stLoop2≡ : fun (fst stLoop2) ∣ idfun∙ _ ∣₂ ≡ ∣ idfun∙ _ ∣₂
stLoop2≡ =
  stLoop2≡helper ∣ idfun∙ _ ∣₂ stLoop₁
    (sym π'₂S²≅π₂S²⁻-stLoop')
    (cong (inv (fst (π'Gr≅πGr zero (S₊∙ 1)))) π₂S²≅π₁S¹-stLoop
   ∙ lem₂)
  where
  lem₂ : inv (fst (π'Gr≅πGr zero (S₊∙ 1))) ∣ loop ∣₂ ≡ ∣ idfun∙ _ ∣₂
  lem₂ = cong ∣_∣₂ (ΣPathP (funExt (λ { base → refl ; (loop i) → refl}) , refl))


πS≅ℤ : (n : ℕ) → GroupIso (π'Gr n (S₊∙ (suc n))) ℤGroup
πS≅ℤ zero =
  compGroupIso (π'Gr≅πGr zero (S₊∙ 1))
    ((compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)
      , makeIsGroupHom (sElim2 (λ _ _ → isProp→isSet (isSetℤ _ _))
           winding-hom))
πS≅ℤ (suc zero) = compGroupIso stLoop2 (πS≅ℤ zero)
πS≅ℤ (suc (suc n)) = compGroupIso (invGroupIso (suspGrIso n)) (πS≅ℤ (suc n))

suspPresIdfun : (n : ℕ) → suspMap n (idfun∙ (S₊∙ (suc n))) ≡ idfun∙ _
suspPresIdfun n = ΣPathP ((funExt (λ { north → refl
                                     ; south → merid (ptSn (suc n))
                                     ; (merid a i) j → compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ j) i}))
                        , refl)
suspPresIdfun2 : (n : ℕ)
  → fun (fst (invGroupIso (suspGrIso n))) ∣ idfun∙ (S₊∙ (suc (suc (suc n)))) ∣₂
  ≡ ∣ idfun∙ _ ∣₂
suspPresIdfun2 n =
    sym (cong (fun (fst (invGroupIso (suspGrIso n))))
        (cong ∣_∣₂ (suspPresIdfun (suc n))))
  ∙ leftInv (suspIso n) ∣ idfun∙ _ ∣₂


πS≅ℤ-idfun∙ : (n : ℕ) → fun (fst (πS≅ℤ n)) ∣ idfun∙ _ ∣₂ ≡ (pos (suc zero))
πS≅ℤ-idfun∙ zero = refl
πS≅ℤ-idfun∙ (suc zero) = speedUp ∣ idfun∙ _ ∣₂ stLoop2≡
  where
  speedUp : (x : _)
           → fun (fst stLoop2) x ≡ ∣ idfun∙ _ ∣₂
           → fun (fst (πS≅ℤ (suc zero))) x ≡ pos (suc zero)
  speedUp x p = cong (fun (fst (πS≅ℤ zero))) p
πS≅ℤ-idfun∙ (suc (suc n)) =
  cong (fun (fst (πS≅ℤ (suc n)))) (suspPresIdfun2 n)
  ∙ πS≅ℤ-idfun∙ (suc n)

open import Cubical.Algebra.Group.ZAction

πS-gen-by-idfun : (n : ℕ) → gen₁-by (π'Gr n (S₊∙ (suc n))) ∣ idfun∙ _ ∣₂
πS-gen-by-idfun n =
  subst (gen₁-by (π'Gr n (S₊∙ (suc n))))
        (sym (cong (inv (fst (πS≅ℤ n))) (πS≅ℤ-idfun∙ n))
        ∙ leftInv (fst (πS≅ℤ n)) ∣ idfun∙ _ ∣₂)
        (Iso-pres-gen₁ ℤGroup (π'Gr n (S₊∙ (suc n)))
          (pos (suc zero))
          (λ h → h , (sym (·Comm h (pos 1)) ∙ ℤ·≡· h (pos 1)))
          (invGroupIso (πS≅ℤ n)))

Equiv∙J : ∀ {ℓ ℓ'} {B : Pointed ℓ} (C : (A : Pointed ℓ) → A ≃∙ B → Type ℓ')
          → C B (idEquiv (fst B) , refl)
          → {A : _} (e : A ≃∙ B) → C A e
Equiv∙J {ℓ} {ℓ'} {B = B} C ind {A = A} =
  uncurry λ e p → help e (pt A) (pt B) p C ind
  where
  help : ∀ {A : Type ℓ} (e : A ≃ typ B) (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p)
  help = EquivJ (λ A e → (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p))
        λ a b → J (λ b p
          → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
                → C (fst B , b)
      (idEquiv (fst B) , refl) →
      C (typ B , a) (idEquiv (typ B) , p))
         λ _ p → p

π'fun : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → (π' (suc n) A) → π' (suc n) B
π'fun n p = sMap ((fst (fst p) , snd p) ∘∙_)

π'fun-idEquiv : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
              → π'fun n (idEquiv (fst A) , (λ _ → pt A))
              ≡ idfun _
π'fun-idEquiv n =
  funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (∘∙-idʳ f))

π'funIsEquiv : 
  ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → isEquiv (π'fun n e)
π'funIsEquiv {B = B} n =
  Equiv∙J (λ A e → isEquiv (π'fun n e))
    (subst isEquiv (sym (π'fun-idEquiv n))
      (idIsEquiv (π' (suc n) B)))

π'funIsHom : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → IsGroupHom (π'Gr n A .snd) (π'fun n e)
                      (π'Gr n B .snd)
π'funIsHom {B = B} n =
  Equiv∙J (λ A e → IsGroupHom (π'Gr n A .snd) (π'fun n e) (π'Gr n B .snd))
    (subst (λ x → IsGroupHom (π'Gr n B .snd) x (π'Gr n B .snd))
      (sym (π'fun-idEquiv n))
      (makeIsGroupHom λ _ _ → refl))

π'Iso : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (π'Iso n e)) = π'fun n e
snd (fst (π'Iso n e)) = π'funIsEquiv n e
snd (π'Iso n e) = π'funIsHom n e

πS³≅πTotalHopf : (n : ℕ) → GroupEquiv (π'Gr n (S₊∙ 3)) (π'Gr n (Σ (S₊ 2) S¹Hopf , north , base))
πS³≅πTotalHopf n =
  π'Iso n ((isoToEquiv (invIso (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1))))
         , refl)

πS³≅πTotalHopf-gen : fst (fst (πS³≅πTotalHopf 2)) ∣ idfun∙ _ ∣₂
                   ≡ ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
πS³≅πTotalHopf-gen =
  cong ∣_∣₂ (∘∙-idʳ (inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl))

πTotalHopf-gen :
  gen₁-by (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
    ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
πTotalHopf-gen = 
  subst (gen₁-by (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base)))
        πS³≅πTotalHopf-gen
        (Iso-pres-gen₁ (π'Gr 2 (S₊∙ 3))
                       (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                       ∣ idfun∙ _ ∣₂
                       (πS-gen-by-idfun 2)
                       (GroupEquiv→GroupIso (πS³≅πTotalHopf 2)))

πTotalHopf≅πS²-gen :
    fst (fst π'₃S²≅π'₃TotalHopf) ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
  ≡ ∣ HopfMap' , refl ∣₂
πTotalHopf≅πS²-gen =
  cong ∣_∣₂ (ΣPathP (refl , (sym (rUnit refl))))

π₂S³-gen-by-HopfMap' : gen₁-by (π'Gr 2 (S₊∙ 2)) ∣ HopfMap' , refl ∣₂
π₂S³-gen-by-HopfMap' =
  subst (gen₁-by (π'Gr 2 (S₊∙ 2)))  πTotalHopf≅πS²-gen
    (Iso-pres-gen₁ (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base)) (π'Gr 2 (S₊∙ 2))
      ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
      πTotalHopf-gen
      (GroupEquiv→GroupIso π'₃S²≅π'₃TotalHopf))

π₂S³-gen-by-HopfMap : gen₁-by (π'Gr 2 (S₊∙ 2)) ∣ HopfMap ∣₂
π₂S³-gen-by-HopfMap =
  subst (gen₁-by (π'Gr 2 (S₊∙ 2)))
        (cong ∣_∣₂ (sym hopfMap≡HopfMap'))
        π₂S³-gen-by-HopfMap'
