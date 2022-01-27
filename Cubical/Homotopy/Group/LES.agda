{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contains:
1. The long exact sequence of loop spaces Ωⁿ (fib f) → Ωⁿ A → Ωⁿ B
2. The long exact sequence of homotopy groups πₙ(fib f) → πₙ A → πₙ B
3. Some lemmas relating the map in the sequence to maps using the
   other definition of πₙ (maps from Sⁿ)
-}
module Cubical.Homotopy.Group.LES where

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
open import Cubical.Foundations.Function

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec
          ; elim to sElim ; elim2 to sElim2
          ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group

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
snd (leftInv (ΩFibreIso f) p i j) k =
  ←∙∙lCancel→∙∙lCancel _ _ (cong snd p) i j k

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
    hcomp (λ r
      → λ {(i = i0) → ←∙∙lCancel-refl-refl (p ∙ q) (~ r) j k --
          ; (i = i1) →
            snd (compPath-filler
                (inv (ΩFibreIso (f , refl))
                     (refl , sym (rUnit refl) ∙ p))
                (inv (ΩFibreIso (f , refl))
                     (refl , sym (rUnit refl) ∙ q)) r j) k
          ; (j = i0) → f (snd A)
          ; (j = i1) → snd (inv (ΩFibreIso (f , refl))
                            (refl , sym (rUnit refl) ∙ q) (r ∨ ~ i)) k
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

    main : I → I → I → fst B
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
                     ; (r = i1) → f ((compPath-filler' (rUnit refl)
                                     (sym (cong-∙ fst P Q)) k) i j)})
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
  help : (f : fst A → fst B) →
       →∙∙lCancel (λ i → f (snd A)) refl (λ i → refl)
       ≡ ∙∙lCancel refl
  help f i j r =
    hcomp (λ k → λ {(i = i0) →
                    →∙∙lCancel-fill (λ _ → f (snd A)) refl refl k j r
                   ; (i = i1) → ∙∙lCancel-fill (λ _ → f (snd A))  j r k
                   ; (j = i0) → rUnit (λ _ → f (snd A)) k r
                   ; (j = i1) → f (snd A)
                   ; (r = i1) → f (snd A)
                   ; (r = i0) → f (snd A)})
          (f (snd A))

ΩFibreIso⁻∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
           → Iso.inv (ΩFibreIso f) (refl , (∙∙lCancel (snd f))) ≡ refl
ΩFibreIso⁻∙ f =
  cong (Iso.inv (ΩFibreIso f)) (sym (ΩFibreIso∙ f)) ∙ leftInv (ΩFibreIso f) refl

{- Ωⁿ (fib f) ≃∙ fib (Ωⁿ f) -}
Ω^Fibre≃∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
              ≃∙ ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) B)))
                , (snd ((Ω^ n) A)) , (Ω^→ n f .snd))
Ω^Fibre≃∙ zero f =  (idEquiv _) , refl
Ω^Fibre≃∙ (suc n) f =
  compEquiv∙
    (Ω≃∙ (Ω^Fibre≃∙ n f))
    ((isoToEquiv (ΩFibreIso (Ω^→ n f))) , ΩFibreIso∙ (Ω^→ n f))

{- Its inverse iso directly defined -}
Ω^Fibre≃∙⁻ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
     (n : ℕ) (f : A →∙ B)
  → ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) B)))
     , (snd ((Ω^ n) A)) , (Ω^→ n f .snd))
  ≃∙ ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
Ω^Fibre≃∙⁻ zero f = (idEquiv _) , refl
Ω^Fibre≃∙⁻ (suc n) f =
  compEquiv∙
    ((isoToEquiv (invIso (ΩFibreIso (Ω^→ n f))))
    , (ΩFibreIso⁻∙ (Ω^→ n f)))
    (Ω≃∙ (Ω^Fibre≃∙⁻ n f))

isHomogeneousΩ^→fib : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
    (n : ℕ) (f : A →∙ B)
  → isHomogeneous
    ((fiber (Ω^→ (suc n) f .fst) (snd ((Ω^ (suc n)) B)))
      , (snd ((Ω^ (suc n)) A)) , (Ω^→ (suc n) f .snd))
isHomogeneousΩ^→fib n f =
  subst isHomogeneous (ua∙ ((fst (Ω^Fibre≃∙ (suc n) f)))
                           (snd (Ω^Fibre≃∙ (suc n) f)))
                      (isHomogeneousPath _ _)

Ω^Fibre≃∙sect : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
     (n : ℕ) (f : A →∙ B)
  → (≃∙map (Ω^Fibre≃∙⁻ n f) ∘∙ ≃∙map (Ω^Fibre≃∙ n f))
    ≡ idfun∙ _
Ω^Fibre≃∙sect zero f = ΣPathP (refl , (sym (rUnit refl)))
Ω^Fibre≃∙sect (suc n) f =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt
      λ p → cong (fst (fst (Ω≃∙ (Ω^Fibre≃∙⁻ n f))))
                   (leftInv (ΩFibreIso (Ω^→ n f))
                     ((fst (fst (Ω≃∙ (Ω^Fibre≃∙ n f))) p)))
          ∙ sym (Ω→∘ (≃∙map (Ω^Fibre≃∙⁻ n f))
                      (≃∙map (Ω^Fibre≃∙ n f)) p)
          ∙ (λ i → (Ω→ (Ω^Fibre≃∙sect n f i)) .fst p)
          ∙ sym (rUnit p))

Ω^Fibre≃∙retr : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
     (n : ℕ) (f : A →∙ B)
  → (≃∙map (Ω^Fibre≃∙ n f) ∘∙ ≃∙map (Ω^Fibre≃∙⁻ n f))
    ≡ idfun∙ _
Ω^Fibre≃∙retr zero f = ΣPathP (refl , (sym (rUnit refl)))
Ω^Fibre≃∙retr (suc n) f =
    →∙Homogeneous≡ (isHomogeneousΩ^→fib n f)
      (funExt (λ p →
        cong (fun (ΩFibreIso (Ω^→ n f)))
          ((sym (Ω→∘ (≃∙map (Ω^Fibre≃∙ n f))
                     (≃∙map (Ω^Fibre≃∙⁻ n f))
               (inv (ΩFibreIso (Ω^→ n f)) p)))
         ∙ (λ i → Ω→ (Ω^Fibre≃∙retr n f i) .fst (inv (ΩFibreIso (Ω^→ n f)) p))
         ∙ sym (rUnit (inv (ΩFibreIso (Ω^→ n f)) p)))
        ∙ rightInv (ΩFibreIso (Ω^→ n f)) p))

Ω^Fibre≃∙' : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
     (n : ℕ) (f : A →∙ B)
  → ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
   ≃∙ ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) B)))
     , (snd ((Ω^ n) A)) , (Ω^→ n f .snd))
Ω^Fibre≃∙' zero f = idEquiv _ , refl
Ω^Fibre≃∙' (suc zero) f =
  (isoToEquiv (ΩFibreIso (Ω^→ zero f))) , ΩFibreIso∙ (Ω^→ zero f)
Ω^Fibre≃∙' (suc (suc n)) f =
  compEquiv∙
    (Ω≃∙ (Ω^Fibre≃∙ (suc n) f))
    ((isoToEquiv (ΩFibreIso (Ω^→ (suc n) f))) , ΩFibreIso∙ (Ω^→ (suc n) f))

-- The long exact sequence of loop spaces.
module ΩLES {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  {- Fibre of f -}
  fibf : Pointed _
  fibf = fiber (fst f) (pt B) , (pt A , snd f)

  {- Fibre of Ωⁿ f -}
  fibΩ^f : (n : ℕ) → Pointed _
  fst (fibΩ^f n) = fiber (Ω^→ n f .fst) (snd ((Ω^ n) B))
  snd (fibΩ^f n) = (snd ((Ω^ n) A)) , (Ω^→ n f .snd)

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
  Ω^fibf→A n = fibΩ^f→A n ∘∙ ≃∙map (Ω^Fibre≃∙ n f)

  {- The function preserves path composition -}
  Ω^fibf→A-pres∙ : (n : ℕ) → (p q : Ω^fibf (suc n) .fst)
    → Ω^fibf→A (suc n) .fst (p ∙ q)
     ≡ Ω^fibf→A (suc n) .fst p
     ∙ Ω^fibf→A (suc n) .fst q
  Ω^fibf→A-pres∙ n p q =
    cong (fst (fibΩ^f→A (suc n)))
      (cong (fun (ΩFibreIso (Ω^→ n f)))
        (Ω→pres∙ (≃∙map (Ω^Fibre≃∙ n f)) p q))
    ∙ ΩFibreIsopres∙fst (Ω^→ n f)
        (fst (Ω→ (≃∙map (Ω^Fibre≃∙ n f))) p)
        (fst (Ω→ (≃∙map (Ω^Fibre≃∙ n f))) q)

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
       (≃∙map (Ω^Fibre≃∙⁻ n f))
    ∘∙ ΩB→fibΩ^f n

  {- It preserves path composition -}
  ΩB→Ω^fibf-pres∙ : (n : ℕ) → (p q : typ ((Ω^ (2 + n)) B))
    → fst (ΩB→Ω^fibf (suc n)) (p ∙ q)
     ≡ fst (ΩB→Ω^fibf (suc n)) p ∙ fst (ΩB→Ω^fibf (suc n)) q
  ΩB→Ω^fibf-pres∙ n p q =
      cong (fst (fst (Ω^Fibre≃∙⁻ (suc n) f)))
        refl
    ∙ cong (fst (fst (Ω≃∙ (Ω^Fibre≃∙⁻ n f))))
        (cong (fun (invIso (ΩFibreIso (Ω^→ n f))))
          (λ _ → snd ((Ω^ suc n) A) , Ω^→ (suc n) f .snd ∙ p ∙ q))
    ∙ cong (fst (fst (Ω≃∙ (Ω^Fibre≃∙⁻ n f))))
           (ΩFibreIso⁻pres∙snd (Ω^→ n f) p q)
    ∙ Ω≃∙pres∙ (Ω^Fibre≃∙⁻ n f)
        (inv (ΩFibreIso (Ω^→ n f)) (refl , Ω→ (Ω^→ n f) .snd ∙ p))
        (inv (ΩFibreIso (Ω^→ n f)) (refl , Ω→ (Ω^→ n f) .snd ∙ q))

  {- Hence we have our sequence
     ... → Ωⁿ⁺¹B → Ωⁿ(fib f) → Ωⁿ A → Ωⁿ B → ...  (*)
     We first prove the exactness properties for the helper functions
     ΩB→fibΩ^f and fibΩ^f→A, and then deduce exactness of the whole sequence
     by noting that the functions in (*) are just ΩB→fibΩ^f, fibΩ^f→A but
     composed with equivalences
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
      ((∙assoc (Ω^→ n f .snd)
        (sym (Ω^→ n f .snd))
        (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)
      ∙∙ cong (_∙ (sym (cong (Ω^→ n f .fst) ker) ∙ snd x))
              (rCancel (Ω^→ n f .snd))
      ∙∙ sym (lUnit (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)))
      ◁ (λ i j → compPath-filler'
                  (cong (Ω^→ n f .fst) (sym ker)) (snd x) (~ i) j)))

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
                    ◁ λ i j → compPath-filler'
                       (cong (Ω^→ n f .fst) p) (Ω^→ n f .snd) (~ i) j)))

    Ker-ΩB→fibΩ^f⊂Im-A→B : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                       → isInKer∙ (ΩB→fibΩ^f n) x
                       → isInIm∙ (A→B (suc n)) x
    fst (Ker-ΩB→fibΩ^f⊂Im-A→B n x inker) = cong fst inker
    snd (Ker-ΩB→fibΩ^f⊂Im-A→B n x inker) = lem
      where
      lem : fst (A→B (suc n)) (λ i → fst (inker i)) ≡ x
      lem i j =
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

{- Some useful lemmas for converting the above sequence a
a sequence of homotopy groups -}
module setTruncLemmas {ℓ ℓ' ℓ'' : Level}
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
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

{- We prove that the map Ωⁿ(fib f) → Ωⁿ A indeed is just the map
Ωⁿ fst -}
private
  Ω^fibf→A-ind : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ΩLES.Ω^fibf→A f (suc n) ≡ Ω→ (ΩLES.Ω^fibf→A f n)
  Ω^fibf→A-ind {A = A} {B = B} n f =
      (λ _ → πLES.Ωs.fibΩ^f→A f (suc n)
     ∘∙ ≃∙map (Ω^Fibre≃∙ (suc n) f))
    ∙ →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt λ p →
        (λ j → cong fst (Ω→ (≃∙map (Ω^Fibre≃∙ n f)) .fst p))
       ∙ rUnit ((λ i → fst
           (Ω→ (≃∙map (Ω^Fibre≃∙ n f)) .fst p i)))
      ∙ sym (Ω→∘ (πLES.Ωs.fibΩ^f→A f n) (≃∙map (Ω^Fibre≃∙ n f)) p))

Ω^fibf→A≡ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
      → ΩLES.Ω^fibf→A f n ≡ Ω^→ n (fst , refl)
Ω^fibf→A≡ zero f = ΣPathP (refl , (sym (lUnit refl)))
Ω^fibf→A≡ (suc n) f = Ω^fibf→A-ind n f ∙ cong Ω→ (Ω^fibf→A≡ n f)

{- We now get a nice characterisation of the functions in the induced LES
of homotopy groups defined using (Sⁿ →∙ A) -}

π∘∙A→B-PathP : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP A B n i)
           (πLES.A→B f n)
           (π'∘∙Hom n f)
π∘∙A→B-PathP n f =
  toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _) (π'∘∙Hom'≡π'∘∙fun n f))

π∘∙fib→A-PathP : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP (ΩLES.fibf f) A n i)
           (πLES.fib→A f n)
           (π'∘∙Hom n (fst , refl))
π∘∙fib→A-PathP {A = A} {B = B} n f =
  toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (cong (transport
      (λ i → (fst (GroupPath _ _)
               (GroupIso→GroupEquiv (π'Gr≅πGr n (ΩLES.fibf f))) (~ i)) .fst
           → (fst (GroupPath _ _)
               (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i)) .fst))
          lem
   ∙ π'∘∙Hom'≡π'∘∙fun n (fst , refl)))
  where
  lem : πLES.fib→A f n .fst ≡ sMap (Ω^→ (suc n) (fst , refl) .fst)
  lem = cong sMap (cong fst (Ω^fibf→A≡ (suc n) f))
