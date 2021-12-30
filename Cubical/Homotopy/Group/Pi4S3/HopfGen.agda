module Cubical.Homotopy.Group.Pi4S3.HopfGen where

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

π≡-connected : ∀ {ℓ} {A : Pointed ℓ}
  → isConnected 3 (typ A)
  → (n : ℕ)
  → (f g : S₊∙ (suc (suc n)) →∙ A)
  → ∥ fst f ≡ fst g ∥
  → ∥ f ≡ g ∥
π≡-connected {A = A} con n f g =
  pRec squash
    λ p → pRec squash (λ q → ∣ ΣPathP (p , q) ∣) (lem p)
  where
  lem : (p : fst f ≡ fst g)
     → ∥ PathP (λ i → p i north ≡ pt A) (snd f) (snd g) ∥
  lem p =
    trRec squash ∣_∣
     (isConnectedPathP 1 {A = λ i → p i north ≡ pt A}
       (isConnectedPath 2 con _ _)
       (snd f) (snd g) .fst)

module _ {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y) where
  →∙∙lCancel-fill : PathP (λ i → p i ≡ y) q q → I → I → I → A
  →∙∙lCancel-fill PP k i j =
    hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym q) p q k j
                 ; (i = i1) → y
                 ; (j = i0) → q (i ∨ k)
                 ; (j = i1) → q (i ∨ k)})
        (inS (PP j i))
        k

  →∙∙lCancel'-fill : sym q ∙∙ p ∙∙ q ≡ refl → I → I → I → A
  →∙∙lCancel'-fill PP k i j =
    hfill (λ k → λ {(i = i0) → q (j ∨ ~ k)
                   ; (i = i1) → q (j ∨ ~ k)
                   ; (j = i0) → doubleCompPath-filler (sym q) p q (~ k) i
                   ; (j = i1) → y})
          (inS (PP j i))
          k

  →∙∙lCancel : PathP (λ i → p i ≡ y) q q → sym q ∙∙ p ∙∙ q ≡ refl
  →∙∙lCancel PP i j = →∙∙lCancel-fill PP i1 i j

  →∙∙lCancel' : sym q ∙∙ p ∙∙ q ≡ refl → PathP (λ i → p i ≡ y) q q
  →∙∙lCancel' PP i j = →∙∙lCancel'-fill PP i1 i j

  →∙∙lCancel'→∙∙lCancel : (PP : PathP (λ i → p i ≡ y) q q)
    → →∙∙lCancel' (→∙∙lCancel PP) ≡ PP
  →∙∙lCancel'→∙∙lCancel PP r i j = {!!}

  →∙∙lCancel→∙∙lCancel' : (PP : sym q ∙∙ p ∙∙ q ≡ refl)
    → →∙∙lCancel (→∙∙lCancel' PP) ≡ PP
  →∙∙lCancel→∙∙lCancel' PP r i j =
    hcomp (λ k → λ {(r = i0) → →∙∙lCancel-fill (→∙∙lCancel' PP) k i j
                   ; (r = i1) → PP i j
                   ; (j = i0) → q (i ∨ k ∨ r) 
                   ; (j = i1) → q (i ∨ k ∨ r)
                   ; (i = i0) → doubleCompPath-filler (sym q) p q (r ∨ k) j
                   ; (i = i1) → y})
     (hcomp (λ k → λ {(r = i0) → →∙∙lCancel'-fill PP k j i
                   ; (r = i1) → PP i j
                   ; (j = i0) → q (i ∨ r ∨ ~ k)
                   ; (j = i1) → q (i ∨ r ∨ ~ k)
                   ; (i = i0) → doubleCompPath-filler (sym q) p q (r ∨ ~ k) j
                   ; (i = i1) → y})
            (PP i j))

{-
r = i0 ⊢ →∙∙lCancel (→∙∙lCancel' PP) i j
r = i1 ⊢ PP i j
i = i0 ⊢ (sym q ∙∙ p ∙∙ q) j
i = i1 ⊢ refl j
j = i0 ⊢ y
j = i1 ⊢ y
-}


ΩFibreIso : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
            → Iso (typ (Ω (fiber (fst f) (pt B) , (pt A) , snd f)))
                   (fiber (Ω→ f .fst) refl)
fun (ΩFibreIso f) p = (cong fst p) ,
                   →∙∙lCancel (cong (fst f) (cong fst p)) (snd f)
                      (cong snd p)
fst (inv (ΩFibreIso f) (p , q) i) = p i
snd (inv (ΩFibreIso f) (p , q) i) = →∙∙lCancel' (cong (fst f) p) (snd f) q i
rightInv (ΩFibreIso f) (p , q) = ΣPathP (refl , →∙∙lCancel→∙∙lCancel' _ _ q)
fst (leftInv (ΩFibreIso f) p i j) = fst (p j)
snd (leftInv (ΩFibreIso f) p i j) k = →∙∙lCancel'→∙∙lCancel _ _ (cong snd p) i j k

ΩFibreIsopres∙fst : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                    → (p q : (typ (Ω (fiber (fst f) (pt B) , (pt A) , snd f))))
                    → fst (fun (ΩFibreIso f) (p ∙ q))
                    ≡ fst (fun (ΩFibreIso f) p) ∙ fst (fun (ΩFibreIso f) q)
ΩFibreIsopres∙fst f p q = cong-∙ fst p q

fibcomp : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → fiber (Ω→ f .fst) refl → fiber (Ω→ f .fst) refl → fiber (Ω→ f .fst) refl
fst (fibcomp f p q) = fst p ∙ fst q
snd (fibcomp f p q) = Ω→pres∙ f (fst p) (fst q)
                    ∙ cong₂ _∙_ (snd p) (snd q)
                    ∙ sym (rUnit refl)

Ω→pres∙-refl : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Type ℓ'} (f : typ A → B) (p q : _)
               → Ω→pres∙ {B = B , f (pt A)} (f , refl) p q
               ≡ sym (rUnit ((λ i → f ((p ∙ q) i))))
               ∙∙ cong-∙ f p q
               ∙∙ cong₂ _∙_ (rUnit (cong f p)) (rUnit (cong f q))
Ω→pres∙-refl {A = A} f p q k i j =
  hcomp (λ r → λ { (i = i0) → rUnit (λ i₁ → f ((p ∙ q) i₁)) r j
                  ; (i = i1) → ((rUnit (cong f p) r) ∙ (rUnit (cong f q) r)) j
                  ; (j = i0) → f (pt A)
                  ; (j = i1) → f (pt A)
                  ; (k = i0) → Ω→pres∙filler (f , refl) p q i j r
                  ; (k = i1) →
                    doubleCompPath-filler
                      (sym (rUnit (λ i₁ → f ((p ∙ q) i₁))))
                      (cong-∙ f p q)
                      (cong₂ _∙_ (rUnit (cong f p)) (rUnit (cong f q))) r i j})
        (cong-∙ f p q i j)

fibIsopres∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                  (p q : (typ (Ω (fiber (fst f) (pt B) , (pt A) , snd f))))
            → fun (ΩFibreIso f) (p ∙ q)
             ≡ fibcomp f (fun (ΩFibreIso f) p) (fun (ΩFibreIso f) q)
fibIsopres∙ {A = A} {B = B}=
  →∙J (λ b₀ f → (p q : (typ (Ω (fiber (fst f) b₀ , (pt A) , snd f))))
            → fun (ΩFibreIso f) (p ∙ q) ≡ fibcomp f (fun (ΩFibreIso f) p) (fun (ΩFibreIso f) q))
      λ f p q → ΣPathP ((cong-∙ fst p q)
                      , help f p q)
  where
  helpgen : (f : typ A → typ B) (p q : (typ (Ω (fiber f (f (pt A)) , (pt A) , refl))))
          → cong (_∙ refl) (cong (cong f) (sym (cong-∙ fst p q)))
          ∙ (→∙∙lCancel (cong f (cong fst (p ∙ q))) refl
                      (cong snd (p ∙ q)))
      ≡ (Ω→pres∙ (f , refl) (cong fst p) (cong fst q)
     ∙ cong₂ _∙_ (→∙∙lCancel (λ i → f (fst (p i))) refl (cong snd p))
                 (→∙∙lCancel (λ i → f (fst (q i))) refl (cong snd q))
     ∙ sym (rUnit refl))
  helpgen f p q =
       (cong (cong (_∙ refl) (cong (cong f) (sym (cong-∙ fst p q))) ∙_)
         (lem (p ∙ q))
      ∙ zz
      ∙ cong₂ _∙_
        ((compPath≡compPath'
          (sym (rUnit (cong f (cong fst p ∙ cong fst q))))
          (cong-∙ f (cong fst p) (cong fst q))))
          (cong (_∙ sym (rUnit (λ _ → f (pt A))))
                (λ _ → (cong (λ x → x ∙ (λ i₂ → f (fst (q i₂))))
          (flipSquare (λ i₂ → snd (p i₂)))
          ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂)))))
          ∙ cong (_∙ sym (rUnit (λ _ → f (pt A))))
                 (sym (cong₂Funct _∙_ (flipSquare (cong snd p)) (flipSquare (cong snd q))))
         ∙ λ _ → cong₂ _∙_ (flipSquare (cong snd p)) (flipSquare (cong snd q))
                ∙ sym (rUnit (λ _ → f (pt A)))))
    ∙∙ (λ i →
          ((sym (rUnit (λ i → f (((λ i₁ → fst (p i₁)) ∙ (λ i₁ → fst (q i₁))) i)))
       ∙∙ cong-∙ f (λ i → fst (p i)) (λ i → fst (q i))
       ∙∙ cong₂ _∙_ (λ j → rUnit (cong f (λ i → fst (p i))) (j ∧ i))
                    (λ j → rUnit (cong f (λ i → fst (q i))) (j ∧ i))))
             ∙ cong₂ _∙_
                 (compPath-filler'
                   (sym (rUnit (cong f (cong fst p))))
                   (flipSquare (cong snd p)) i)
                 (compPath-filler'
                   (sym (rUnit (cong f (cong fst q))))
                   (flipSquare (cong snd q)) i)
             ∙ sym (rUnit (λ _ → f (pt A))))
    ∙∙ cong₂ _∙_ (sym (Ω→pres∙-refl f (cong fst p) (cong fst q)))
                 (cong (_∙ sym (rUnit refl))
                   λ j → cong₂ _∙_ (lem p (~ j)) (lem q (~ j)))
    where
    zz : (λ i → (λ i₁ → f (cong-∙ fst p q (~ i) i₁)) ∙ (λ _ → f (pt A)))
      ∙ sym (rUnit (λ i → f (fst ((p ∙ q) i))))
      ∙ flipSquare (cong snd (p ∙ q))
      ≡
      ((sym (rUnit (λ i₁ → f (((λ i₂ → fst (p i₂)) ∙ (λ i₂ → fst (q i₂))) i₁))))
       ∙ cong-∙ f (cong fst p) (cong fst q))
      ∙ ((λ i → flipSquare (λ i₂ → snd (p i₂)) i ∙ (λ i₂ → f (fst (q i₂))))
      ∙ (cong ((λ i₂ → f (pt A)) ∙_) (flipSquare (λ i₂ → snd (q i₂)))))
      ∙ (sym (rUnit (λ _ → f (pt A))))
    zz k i j =
      hcomp (λ r → λ {(i = i0) → rUnit (λ i₁ → f ((cong fst p ∙ cong fst q) i₁)) r j
                     ; (i = i1) → f (pt A)
                     ; (j = i0) → f (pt A)
                     ; (j = i1) → f (pt A)
                     ; (k = i0) → ((λ i₁ → rUnit (λ i₂ → f (cong-∙ fst p q (~ i₁) i₂)) r)
                                 ∙ compPath-filler'
                                     (sym (rUnit (λ i₁ → f (fst ((p ∙ q) i₁)))))
                                     (flipSquare (cong snd (p ∙ q))) r) i j
                     ; (k = i1) →
                       (compPath-filler' (sym (rUnit (λ i₁ → f ((cong fst p ∙ cong fst q) i₁))))
                                         (cong-∙ f (cong fst p) (cong fst q)) r
                     ∙ ((λ i₁ → flipSquare (λ i₂ → snd (p i₂)) i₁ ∙ (λ i₂ → f (fst (q i₂))))
                     ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂))))
                     ∙ sym (rUnit (λ _ → f (pt A)))) i j})
        (hcomp (λ r → λ {(i = i0) → f (cong-∙ fst p q r j)
                     ; (i = i1) → f (pt A)
                     ; (j = i0) → f (pt A)
                     ; (j = i1) → f (pt A)
                     ; (k = i0) → (compPath-filler'
                                     (λ i₁ → (λ i₂ → f (cong-∙ fst p q (~ i₁) i₂)))
                                     (flipSquare (cong snd (p ∙ q)))) r i j
                     ; (k = i1) → (h r
                                 ∙ ((λ i₁ → flipSquare (cong snd p) i₁ ∙ (λ i₂ → f (fst (q i₂))))
                                 ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂))))
                                 ∙ sym (rUnit (λ _ → f (pt A)))) i j})
               (hcomp (λ r → λ {(i = i0) → flipSquare (cong snd (p ∙ q)) (~ r) j
                     ; (i = i1) → f (pt A)
                     ; (j = i0) → f (pt A)
                     ; (j = i1) → f (pt A)
                     ; (k = i0) → flipSquare (cong snd (p ∙ q)) (~ r ∨ i) j
                     ; (k = i1) → compPath-filler' (sym (flipSquare (cong snd (p ∙ q)))) ((cong-∙ (f ∘ fst) p q)
                                 ∙ ((λ i₁ → flipSquare (cong snd p) i₁ ∙ (λ i₂ → f (fst (q i₂))))
                                 ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂))))
                                 ∙ sym (rUnit (λ _ → f (pt A)))) (~ r) i j} )
                    (main (~ k) i j)))
      where
      genlem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} {p q : x ≡ x} (f : A → B)
               (r : f x ≡ f x)
        → (P : cong f p ≡ refl)
        → (Q : cong f q ≡ refl)
        → {!cong f (p ∙ q)!} ∙ {!!}
        ≡ rUnit refl ∙ cong₂ _∙_ (sym P) (sym Q)
      genlem = {!!}

      id1 : sym (flipSquare (cong snd (p ∙ q)))
           ∙ cong-∙ (f ∘ fst) p q
           ≡ rUnit refl
           ∙ cong₂ _∙_ (sym (flipSquare (cong snd p))) (sym (flipSquare (cong snd q)))
      id1  k i j =
        hcomp (λ r → λ {(i = i0) → snd (compPath-filler p q (~ k) j) r
                       ; (i = i1) → (cong (f ∘ fst) p ∙ flipSquare (cong snd q) (~ r ∧ k)) j
                       ; (j = i0) → f (snd A)
                       ; (j = i1) → snd (q (~ k)) (r ∨ i)
                       ; (k = i0) → compPath-filler'
                                      (sym (flipSquare (cong snd (p ∙ q))))
                                      (cong-∙ (f ∘ fst) p q) r i j
                       ; (k = i1) →
                         (rUnit ((flipSquare (cong snd p)) r)
                        ∙ cong₂ _∙_ (λ j → flipSquare (λ i₃ → snd (p i₃)) (r ∧ ~ j))
                         (λ i → (flipSquare (cong snd q)) (~ i ∨ ~ r))) i j })
              (hcomp (λ r → λ {(i = i0) → f (fst (compPath-filler p q (~ k) j))
                       ; (i = i1) → (cong (f ∘ fst) p ∙ flipSquare (cong snd q) k) j
                       ; (j = i0) → f (snd A)
                       ; (j = i1) → snd (q (~ k)) i
                       ; (k = i0) → (cong-∙ (f ∘ fst) p q i j)
                       ; (k = i1) → (rUnit (rUnit (cong (f ∘ fst) p)) r) i j })
               (hcomp (λ r → λ {(i = i0) → {!!}
                       ; (i = i1) → compPath-filler' (cong (f ∘ fst) p) (flipSquare (cong snd q) k) r j
                       ; (j = i0) → {!!}
                       ; (j = i1) → {!snd (q (~ k)) i!}
                       ; (k = i0) → {!!}
                       ; (k = i1) → {!compPath-filler (cong (f ∘ fst) p) refl (~ r ∧ i) j!} })
                      {!!}))
{-
k = i0 ⊢ (sym (flipSquare (cong snd (p ∙ q))) ∙
          cong-∙ (f ∘ fst) p q)
         i j
k = i1 ⊢ (rUnit refl ∙
          sym (cong (_∙_ (λ i₃ → f (pt A))) (flipSquare (λ i₃ → snd (q i₃))))
          ∙
          (λ i₁ → flipSquare (cong snd p) (~ i₁) ∙ (λ i₃ → f (fst (q i₃)))))
         i j
i = i0 ⊢ f (pt A)
i = i1 ⊢ (cong (f ∘ fst) p ∙ cong (f ∘ fst) q) j
j = i0 ⊢ f (snd A)
j = i1 ⊢ f (snd A)
-}

      main : sym (flipSquare (cong snd (p ∙ q)))
           ∙ cong-∙ (f ∘ fst) p q
           ∙ (((λ i₁ → flipSquare (cong snd p) i₁ ∙ (λ i₂ → f (fst (q i₂)))))
           ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂))))
           ∙ sym (rUnit (λ _ → f (pt A)))
           ≡ refl
      main = {!sym (flipSquare (cong snd (p ∙ q)))
           ∙ cong-∙ (f ∘ fst) p q!}

      h : PathP (λ i → cong f (cong-∙ fst p q i)
                      ≡ cong f (cong fst p) ∙ cong f (cong fst q))
                (cong-∙ (f ∘ fst) p q)
                (cong-∙ f (cong fst p) (cong fst q))
      h = {!!}

{-
k = i0 ⊢ ((λ i₁ →
             (λ i₂ → f (cong-∙ fst p q (~ i₁) i₂)))
          ∙
          flipSquare (cong snd (p ∙ q)))
         i j
k = i1 ⊢ (cong-∙ f (cong fst p) (cong fst q)
          ∙
          ((λ i₁ →
              flipSquare (λ i₂ → snd (p i₂)) i₁ ∙ (λ i₂ → f (fst (q i₂))))
           ∙ cong (_∙_ (λ i₂ → f (pt A))) (flipSquare (λ i₂ → snd (q i₂))))
          ∙ sym (rUnit (λ _ → f (pt A))))
         i j
i = i0 ⊢ f ((cong fst p ∙ cong fst q) j)
i = i1 ⊢ f (pt A)
j = i0 ⊢ f (snd A)
j = i1 ⊢ f (snd A)
-}

    lem : (p : typ (Ω (fiber f (f (pt A)) , pt A , refl)))
        → →∙∙lCancel (λ i → f (fst (p i))) refl (cong snd p)
        ≡ sym (rUnit _) ∙ flipSquare (cong snd p)
    lem p k i j =
      hcomp (λ r → λ {(i = i0) → rUnit (λ i₁ → f (fst (p i₁))) r j
                     ; (i = i1) → f (pt A)
                     ; (j = i0) → f (pt A)
                     ; (j = i1) → f (pt A)
                     ; (k = i0) → →∙∙lCancel-fill (λ i → f (fst (p i))) refl (cong snd p) r i j
                     ; (k = i1) → compPath-filler' (sym (rUnit _)) (flipSquare (cong snd p)) r i j})
            (cong snd p j i)


  help : (f : typ A → typ B) (p q : (typ (Ω (fiber f (f (pt A)) , (pt A) , refl))))
    → (PathP (λ i → Ω→ {B = typ B , f (pt A)} (f , refl) .fst (cong-∙ fst p q i) ≡ refl)
      (→∙∙lCancel (cong f (cong fst (p ∙ q))) refl
                      (cong snd (p ∙ q)))
      (Ω→pres∙ (f , refl) (cong fst p) (cong fst q)
     ∙ cong₂ _∙_ (→∙∙lCancel (λ i → f (fst (p i))) refl (cong snd p))
                 (→∙∙lCancel (λ i → f (fst (q i))) refl (cong snd q))
     ∙ sym (rUnit refl)))
  help f p q = {!!}
  {-
    hcomp (λ r → λ { (i = i0) → doubleCompPath-filler refl (cong f (cong-∙ fst p q k)) refl r j
                    ; (i = i1) → f (pt A)
                    ; (j = i0) → f (pt A)
                    ; (j = i1) → f (pt A)
                    ; (k = i0) → →∙∙lCancel-fill (cong f (cong fst (p ∙ q))) refl (cong snd (p ∙ q)) r i j
                    ; (k = i1) → {!doubleCompPath-filler refl (cong f (cong fst p ∙ cong fst q)) refl (r ∨ i) j!}})
          {!→∙∙lCancel (λ i → f (fst (p i))) refl (cong snd p)!}
    where -- r i j
    k=i1 : Cube
      {!r = i0 ⊢ ?1 i j
r = i1 ⊢ (Ω→pres∙ (f , refl) (cong fst p) (cong fst q) ∙
          cong₂ _∙_ (→∙∙lCancel (λ i₂ → f (fst (p i₂))) refl (cong snd p))
          (→∙∙lCancel (λ i₂ → f (fst (q i₂))) refl (cong snd q))
          ∙ sym (rUnit refl))
         i j
i = i0 ⊢ doubleCompPath-filler refl
         (cong f (cong fst p ∙ cong fst q)) refl r j
i = i1 ⊢ f (pt A)
j = i0 ⊢ f (pt A)
j = i1 ⊢ f (pt A)!}
                ((Ω→pres∙ (f , refl) (cong fst p) (cong fst q) ∙
                  cong₂ _∙_ (→∙∙lCancel (λ i₁ → f (fst (p i₁))) refl (cong snd p))
                  (→∙∙lCancel (λ i₁ → f (fst (q i₁))) refl (cong snd q))
                  ∙ sym (rUnit refl)))
                (λ r j → doubleCompPath-filler refl (cong f (cong fst p ∙ cong fst q)) refl r j) (λ r j → f (pt A))
                (λ r i → f (pt A)) λ r i → f (pt A)
    k=i1 r i j =
      hcomp (λ k → λ {(r = i0) → {!!}
                     ; (r = i1) → {!!}
                     ; (i = i0) → {!!}
                     ; (i = i1) → {!!}
                     ; (j = i0) → {!!}
                     ; (j = i1) → {!!}})
            {!!}
 -}
{-
k = i0 ⊢ →∙∙lCancel (cong f (cong fst (p ∙ q))) refl
         (cong snd (p ∙ q)) i j
k = i1 ⊢ (Ω→pres∙ (f , refl) (cong fst p) (cong fst q) ∙
          cong₂ _∙_ (→∙∙lCancel (λ i₁ → f (fst (p i₁))) refl (cong snd p))
          (→∙∙lCancel (λ i₁ → f (fst (q i₁))) refl (cong snd q))
          ∙ sym (rUnit refl))
         i j
i = i0 ⊢ Ω→ (f , refl) .fst (cong-∙ fst p q k) j
i = i1 ⊢ refl j
j = i0 ⊢ f (pt A)
j = i1 ⊢ f (pt A)
-}

ΩFibreIsopres∙ : {!!}
ΩFibreIsopres∙ = {!!}

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

_≃∙_ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
A ≃∙ B = Σ[ e ∈ fst A ≃ fst B ] fst e (pt A) ≡ pt B

invEquiv∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ≃∙ B → B ≃∙ A
fst (invEquiv∙ x) = invEquiv (fst x)
snd (invEquiv∙ {A = A} x) = sym (cong (fst (invEquiv (fst x))) (snd x)) ∙ retEq (fst x) (pt A)


compEquiv∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → A ≃∙ B → B ≃∙ C → A ≃∙ C
fst (compEquiv∙ e1 e2) = compEquiv (fst e1) (fst e2)
snd (compEquiv∙ e1 e2) = cong (fst (fst e2)) (snd e1) ∙ snd e2

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

Ω^Fibre≃∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → ((Ω^ n) (fiber (fst f) (pt B) , (pt A) , snd f))
              ≃∙ ((fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
                , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd))
Ω^Fibre≃∙ zero f =  (idEquiv _) , refl
Ω^Fibre≃∙ (suc n) f = 
  compEquiv∙
    (ΩIso (Ω^Fibre≃∙ n f))
    ((isoToEquiv (ΩFibreIso (Ω^→ n f))) , ΩFibreIso∙ (Ω^→ n f))

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

isHomΩ^Fibre≃∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
             → (p q : typ ((Ω^ (suc n)) (fiber (fst f) (pt B) , (pt A) , snd f)))
             → fst (fst (fst (Ω^Fibre≃∙ (suc n) f)) (p ∙ q))
             ≡ ((fst (fst (fst (Ω^Fibre≃∙ (suc n) f)) p) 
              ∙ fst (fst (fst (Ω^Fibre≃∙ (suc n) f)) q)))
isHomΩ^Fibre≃∙ zero f p q = (λ i → cong fst (fst (fst ((ΩIso (Ω^Fibre≃∙ zero f)))) {!!})) ∙ {!!}
isHomΩ^Fibre≃∙ (suc n) f p q = {!!}

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ} (f : A →∙ B) where
  iso1 : {!!}
  iso1 = {!!}

  fibf : Pointed _
  fibf = fiber (fst f) (pt B) , (pt A , snd f)

  fibF : (n : ℕ) → Pointed _
  fibF n = (fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
         , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd)

  fibComp : (n : ℕ) → fibF (suc n) .fst → fibF (suc n) .fst → fibF (suc n) .fst
  fst (fibComp n p q) = fst p ∙ fst q
  snd (fibComp n p q) = Ω^→pres∙ f n (fst p) (fst q)
                      ∙ cong₂ _∙_ (snd p) (snd q) ∙ sym (rUnit refl)

  fibComp0 : (n : ℕ) → fibF (suc n) .fst
  fst (fibComp0 n) = refl
  snd (fibComp0 n) = Ω^→ (suc n) f .snd

  fibComprUnit : (n : ℕ) → (p : fibF (suc n) .fst) → {!!}
  fibComprUnit = {!!}

  fibf^ : (n : ℕ) → Pointed _
  fibf^ n = (Ω^ n) fibf

  fibf^≃fibF : (n : ℕ) → fibf^ n ≃∙ fibF n
  fibf^≃fibF n = Ω^Fibre≃∙' n f
  
  presCompfibf^≃fibF : (n : ℕ) → (p q : fst (fibf^ (suc n)))
    → fst (fst (fibf^≃fibF (suc n))) (p ∙ q)
    ≡ fibComp n (fst (fst (fibf^≃fibF (suc n))) p)
                (fst (fst (fibf^≃fibF (suc n))) q)
  presCompfibf^≃fibF zero p q =
    ΣPathP (cong-∙ fst p q
         , {!cong-∙ fst p q!})
  presCompfibf^≃fibF (suc n) p q =
     (λ i → fst (fst (compEquiv∙
    (ΩIso (Ω^Fibre≃∙ (suc n) f))
    ((isoToEquiv (ΩFibreIso (Ω^→ (suc n) f))) , ΩFibreIso∙ (Ω^→ (suc n) f)))) (p ∙ q))
   ∙ {!!}
   ∙ {!!}

  fibF→A : (n : ℕ) → fibF n →∙ (Ω^ n) A
  fst (fibF→A n) = fst
  snd (fibF→A n) = refl

  fibf^→A' : (n : ℕ) → fibf^ n →∙ (Ω^ n) A
  fibf^→A' n = fst ∘ (fst (fst (Ω^Fibre≃∙ n f))) , cong fst (snd (Ω^Fibre≃∙ n f))

  fibf^→A : (n : ℕ) → fibf^ n →∙ (Ω^ n) A
  fibf^→A n = fibF→A n ∘∙ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))

  fib^→Aind : (n : ℕ) → fibf^→A (suc n) ≡ Ω→ (fibf^→A n)
  fib^→Aind zero =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      {!refl!}
  fib^→Aind (suc n) =
     {!(Ω→ (fibF→A (suc n)))!}
    ∙ sym (Ω→∘∙ (fibF→A (suc n))
                 (fst (fst (Ω^Fibre≃∙ (suc n) f))
                 , snd (Ω^Fibre≃∙ (suc n) f)))
    where
    kk : Ω→ (fibF→A (suc n)) ≡ {!fibF→A (suc (suc n))!} -- fibF→A (suc (suc n))
    kk = {!!}
  {-
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (({!!} ∙ {! (funExt (Ω→∘ (fibF→A n) (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))))!}) -- (funExt (λ p → {!fibf^→A (suc (suc n)) .fst p!} ∙ {!!})
      ∙ refl) -}

  isHom-fibf^→A : (n : ℕ) → (p q : fibf^ (suc n) .fst)
    → fibf^→A (suc n) .fst (p ∙ q)
     ≡ fibf^→A (suc n) .fst p
     ∙ fibf^→A (suc n) .fst q
  isHom-fibf^→A zero p q = {!!} -- cong (fst (fibF→A (suc zero))) {!fst (fst (Ω^Fibre≃∙ (suc zero) f)) (p ∙ q)!} ∙ {!!}
  isHom-fibf^→A (suc n) p q =
    cong (fibF→A (suc (suc n)) .fst)
      (cong (fst (fst (Ω^Fibre≃∙ (suc (suc n)) f)))
        (λ _ → p ∙ q))
      ∙ cong (fibF→A (suc (suc n)) .fst)
          (cong (Iso.fun (ΩFibreIso (Ω^→ (suc n) f)))
            (cong (fst (fst (ΩIso (Ω^Fibre≃∙ (suc n) f))))
              (λ _ → p ∙ q))
          ∙ cong (fun (ΩFibreIso (Ω^→ (suc n) f)))
                 (Ω→pres∙ ((fst (fst (Ω^Fibre≃∙ (suc n) f))) , (snd ((Ω^Fibre≃∙ (suc n) f)))) p q))
      ∙ {!compEquiv∙
          (ΩIso (Ω^Fibre≃∙ n f))
          ((isoToEquiv (ΩFibreIso (Ω^→ n f))) , ΩFibreIso∙ (Ω^→ n f))!}

  A→B : (n : ℕ) → (Ω^ n) A →∙ (Ω^ n) B
  A→B n = Ω^→ n f

  ΩB→fibF' : (n : ℕ) → ((Ω^ (suc n)) B) →∙ fibF n
  fst (ΩB→fibF' n) x = (snd ((Ω^ n) A)) , (Ω^→ n f .snd ∙ x)
  snd (ΩB→fibF' n) = ΣPathP (refl , (sym (rUnit _)))

  ΩB→fibF'-hom : (n : ℕ) → (p q : (typ ((Ω^ (suc (suc n))) B)))
               → fst (ΩB→fibF' (suc n)) (p ∙ q)
               ≡ fibComp n (fst (ΩB→fibF' (suc n)) p) (fst (ΩB→fibF' (suc n)) q)
  ΩB→fibF'-hom n p q =
    ΣPathP ((rUnit refl)
           , help)
    where
    lem : (Ω^→pres∙ f n refl refl
         ∙ cong₂ _∙_ (Ω^→ (suc n) f .snd ∙ p) (Ω^→ (suc n) f .snd ∙ q))
         ≡ {!!}
         ∙ cong₂ _∙_ p q
    lem = cong (_∙ cong₂ _∙_ (Ω^→ (suc n) f .snd ∙ p) (Ω^→ (suc n) f .snd ∙ q))
               (Ω→pres∙reflrefl (Ω^→ n f))
        ∙ (λ i → (cong (fst (Ω→ (Ω^→ n f))) (sym (rUnit refl))
                 ∙ snd (Ω→ (Ω^→ n f))
                 ∙ (compPath-filler (rUnit refl)
                   (cong₂ _∙_ (sym (Ω^→ (suc n) f .snd)) (sym (Ω^→ (suc n) f .snd))) (~ i)))
                 ∙ cong₂ _∙_ (compPath-filler' (Ω^→ (suc n) f .snd) p (~ i))
                             (compPath-filler' (Ω^→ (suc n) f .snd) q (~ i)))
        ∙ {!!}
        ∙ {!!}


    help : PathP (λ i → Ω^→ (suc n) f .fst (rUnit (λ _ → snd ((Ω^ n) A)) i) ≡ snd ((Ω^ suc n) B))
      (Ω^→ (suc n) f .snd ∙ p ∙ q)
      (Ω^→pres∙ f n refl refl
         ∙ cong₂ _∙_ (Ω^→ (suc n) f .snd ∙ p) (Ω^→ (suc n) f .snd ∙ q)
         ∙ sym (rUnit refl))
    help =
        {!!}
      ◁ (({!!}
      ▷ {!!})
      ▷ cong (_∙ cong₂ _∙_ (Ω^→ (suc n) f .snd ∙ p) (Ω^→ (suc n) f .snd ∙ q) ∙
      sym (rUnit refl)) (sym (Ω→pres∙reflrefl (Ω^→ n f))))

  ΩB→fibf^ : (n : ℕ) → (Ω^ (suc n)) B →∙ fibf^ n
  ΩB→fibf^ n =
       (fst (fst (invEquiv∙ (Ω^Fibre≃∙ n f))) , snd (invEquiv∙ (Ω^Fibre≃∙ n f)))
    ∘∙ ΩB→fibF' n

  ΩB→fibf^' : (n : ℕ) → (Ω^ (suc n)) B →∙ fibf^ n
  fst (ΩB→fibf^' n) p = fst (fst (invEquiv∙ (Ω^Fibre≃∙ n f)))
                             ((pt ((Ω^ n) A)) , (Ω^→ n f .snd ∙ p))
  snd (ΩB→fibf^' n) =
    cong (fst (invEquiv (fst (Ω^Fibre≃∙ n f))))
        (ΣPathP (refl , sym (rUnit (Ω^→ n f .snd))))
      ∙ snd (invEquiv∙ ((Ω^Fibre≃∙ n f)))

  ΩB→fibf^pres∙ : (n : ℕ) → (p q : typ ((Ω^ (2 + n)) B))
    → fst (ΩB→fibf^ (suc n)) (p ∙ q)
     ≡ fst (ΩB→fibf^ (suc n)) p ∙ fst (ΩB→fibf^ (suc n)) q 
  ΩB→fibf^pres∙ n p q =
    cong (fst (fst (invEquiv∙ (Ω^Fibre≃∙ (suc n) f))))
      (λ _ → fst (ΩB→fibF' (suc n)) (p ∙ q))
    ∙ {!ΩFibreIsopres∙fst!}

  isInIm∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
         → (x : typ B)
         → Type _
  isInIm∙ {A = A} {B = B} f x = Σ[ z ∈ typ A ] fst f z ≡ x

  isInKer∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
         → (x : fst A)
         → Type _
  isInKer∙ {B = B} f x = fst f x ≡ snd B

  imfibF→A⊂kerA→B : (n : ℕ) (x : _)
                     → isInIm∙ (fibF→A n) x
                     → isInKer∙ (A→B n) x
  imfibF→A⊂kerA→B n x =
    uncurry λ p → J (λ x _ → isInKer∙ (A→B n) x)
      (snd p)

  kerA→B⊂imfibF→A : (n : ℕ) (x : _)
                     → isInKer∙ (A→B n) x
                     → isInIm∙ (fibF→A n) x
  kerA→B⊂imfibF→A n x ker = (x , ker) , refl

  kerfibF→A⊂imΩB→fibF' : (n : ℕ) (x : _)
                     → isInKer∙ (fibF→A n) x
                     → isInIm∙ (ΩB→fibF' n) x
  kerfibF→A⊂imΩB→fibF' n x ker = (sym (Ω^→ n f .snd) ∙ cong (Ω^→ n f .fst) (sym ker) ∙ snd x) , ΣPathP ((sym ker) ,
    ((∙assoc (Ω^→ n f .snd) (sym (Ω^→ n f .snd)) (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)
    ∙∙ cong (_∙ (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)) (rCancel (Ω^→ n f .snd))
    ∙∙ sym (lUnit (sym (cong (Ω^→ n f .fst) ker) ∙ snd x)))
    ◁ (λ i j → compPath-filler' (cong (Ω^→ n f .fst) (sym ker)) (snd x) (~ i) j)))

  imΩB→fibF'⊂kerfibF→A : (n : ℕ) (x : _)
                     → isInIm∙ (ΩB→fibF' n) x
                     → isInKer∙ (fibF→A n) x
  imΩB→fibF'⊂kerfibF→A n x =
    uncurry λ p
      → J (λ x _ → isInKer∙ (fibF→A n) x)
        refl

  imA→B⊂kerΩB→fibF' : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInIm∙ (A→B (suc n)) x
                     → isInKer∙ (ΩB→fibF' n) x
  imA→B⊂kerΩB→fibF' n x =
    uncurry λ p
     → J (λ x _ → isInKer∙ (ΩB→fibF' n) x)
       (ΣPathP (p , (((λ i → (λ j → Ω^→ n f .snd (j ∧ ~ i))
                           ∙ ((λ j → Ω^→ n f .snd (~ j ∧ ~ i))
                           ∙∙ cong (Ω^→ n f .fst) p
                           ∙∙ Ω^→ n f .snd))
                    ∙ sym (lUnit (cong (Ω^→ n f .fst) p ∙ Ω^→ n f .snd)))
                  ◁ λ i j → compPath-filler' (cong (Ω^→ n f .fst) p) (Ω^→ n f .snd) (~ i) j)))
  kerΩB→fibF'⊂imA→B : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInKer∙ (ΩB→fibF' n) x
                     → isInIm∙ (A→B (suc n)) x
  fst (kerΩB→fibF'⊂imA→B n x inker) = cong fst inker
  snd (kerΩB→fibF'⊂imA→B n x inker) = pp
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

  map1 : (n : ℕ) → (Ω^ n) fibf →∙ (Ω^ n) A
  map1 n = Ω^→ n (fst , refl)

  map2' : (n : ℕ) → (Ω^ n) A →∙ (Ω^ n) B
  map2' n = Ω^→ n f

  map1∘map2 : (n : ℕ) → fst (map2' n) ∘ fst (map1 n) ≡ Ω^→ n (f ∘∙ (fst , refl)) .fst
  map1∘map2 n = sym (cong fst (Ω^→∘∙ n f (fst , refl)))

  ker→im₁₂ : (n : ℕ) → {!!} → (fst (map2' n) ∘ fst (map1 n)) {!!} ≡ {!!}
  ker→im₁₂ n = {!!}

  mani : Ω B →∙ fibf
  fst mani p = pt A , snd f ∙ p
  fst (snd mani i) = pt A
  snd (snd mani i) j = rUnit (snd f) (~ i) j

  map3 : (n : ℕ) → (Ω^ n) (Ω B) →∙ (Ω^ n) fibf
  map3 n = Ω^→ n mani

  map3* : (n : ℕ) → (Ω^ (suc n)) B →∙ (Ω^ n) fibf
  map3* n = map3 n ∘∙ (Iso.fun (flipΩIso n) , {!flipΩrefl!})

  map1-hom : (n : ℕ) (p q : _)
   → fst (map1 (suc n)) (p ∙ q) ≡
      fst (map1 (suc n)) p ∙ fst (map1 (suc n)) q
  map1-hom zero p q = Ω→pres∙ (fst , refl) p q
  map1-hom (suc n) p q = Ω→pres∙ (Ω^→ (suc n) (fst , refl)) p q

  hom1 : (n : ℕ) → GroupHom (πGr n fibf) (πGr n A) -- fib →hom1 A →hom2 B →hom3 fib
  fst (hom1 n) = sMap (fst (map1 (suc n)))
  snd (hom1 n) =
    makeIsGroupHom
     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
       λ f g → cong ∣_∣₂ (map1-hom n f g))

  hom2 : (n : ℕ) → GroupHom (πGr n A) (πGr n B)
  fst (hom2 n) = sMap (fst (map2' (suc n)))
  snd (hom2 n) =
    makeIsGroupHom
      (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
        λ g h → cong ∣_∣₂ (Ω^→pres∙ f n g h))

  hom3 : (n : ℕ) → GroupHom (πGr (suc n) B) (πGr n fibf)
  fst (hom3 n) = sMap λ p → fst (map3 (suc n)) (Iso.fun (flipΩIso (suc n)) p)
  snd (hom3 n) =
    makeIsGroupHom
     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ p q →
       cong ∣_∣₂ (cong (fst (map3 (suc n))) (flipΩIsopres· n p q)
               ∙ Ω^→pres∙ mani n _ _))


  help34 : Path (fibf →∙ B) (f ∘∙ (fst , (λ _ → snd A))) ((λ _ → pt B) , refl)
  fst (help34 i) x = snd x i
  snd (help34 i) j =
    hcomp (λ k → λ {(i = i1) → snd f k
                   ; (j = i0) → snd (snd fibf) (i ∧ k)
                   ; (j = i1) → snd f k})
          (fst f (snd A))

  ΩΣIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (x : Σ A B)
       → Iso (typ (Ω (Σ A B , x)))
              (Σ[ p ∈ typ (Ω (A , (fst x))) ] PathP (λ i → B (p i)) (snd x) (snd x))
  fun (ΩΣIso x) p = (cong fst p) , cong snd p
  inv (ΩΣIso x) (p , q) i = (p i) , (q i)
  rightInv (ΩΣIso x) _ = refl
  leftInv (ΩΣIso x) _ = refl

  Ωfibf : Iso (typ (Ω fibf)) {!!}
  Ωfibf = {!!}

  tripleCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y)
              → (sym q ∙∙ p ∙∙ q) ≡ refl → p ≡ refl
  tripleCancel {x = x} p q d i j =
    hcomp (λ k → λ {(i = i0) → doubleCompPath-filler (sym q) p q (~ k) j
                   ; (i = i1) → q (~ k)
                   ; (j = i0) → q (~ k)
                   ; (j = i1) → q (~ k)})
          (d i j)

  Ωfib : Iso (typ (Ω fibf)) (Σ[ x ∈ typ (Ω A) ] map2' 1 .fst x ≡ refl )
  fst (fun Ωfib x) = cong fst x
  snd (fun Ωfib x) i j = {!hcomp ? ?!}
  inv Ωfib =
    {!i = i0 ⊢ map2' 1 .fst (λ i₁ → fst (x i₁)) j
i = i1 ⊢ refl j
j = i0 ⊢ snd B
j = i1 ⊢ snd B!}
  rightInv Ωfib = {!!}
  leftInv Ωfib = {!!}



  mutual
    lem₁ : (n : ℕ) (p : typ (Ω ((Ω^ n) A))) → fst (map2' (suc n)) p ≡ (λ _ → snd ((Ω^ n) B))
           → typ (Ω ((Ω^ n) fibf))
    lem₁∙ : (n : ℕ) → lem₁ n refl (Ω^→ (suc n) f .snd) ≡ refl
    lem₁ zero p q = ΣPathP (p , flipSquare (doubleCompPath-filler (sym (snd f)) (cong (fst f) p) (snd f) ▷ q))
    lem₁ (suc n) p q = sym (lem₁∙ n) ∙∙ (λ i → lem₁ n (p i) (pp2 i)) ∙∙ lem₁∙ n
      where
      pp2 : PathP (λ i → fst (map2' (suc n)) (p i)
                ≡ (λ _ → snd ((Ω^ n) B))) (Ω^→ (suc n) f .snd) (Ω^→ (suc n) f .snd)
      pp2 = flipSquare (doubleCompPath-filler (sym (Ω^→ (suc n) f .snd))
                       (cong (fst (map2' (suc n))) p) (Ω^→ (suc n) f .snd)
                      ▷ q)

    lem₁∙ zero = {!!}
    lem₁∙ (suc n) = {!!}


{-
j = i0 ⊢ fst (map2' (suc n)) (p i) k
j = i1 ⊢ snd ((Ω^ n) B)
k = i0 ⊢ snd ((Ω^ n) B)
k = i1 ⊢ snd ((Ω^ n) B)
-}

--   ker⊂im-map1-map2 : (n : ℕ)
--     → (x : _)
--     → isInKer (hom2 n) x
--     → isInIm (hom1 n) x
--   ker⊂im-map1-map2 n =
--     sElim (λ _ → isSetΠ λ _ → isProp→isSet squash)
--       λ p q → pRec {!!} (λ q → ∣ ∣ transport (sym (isoToPath (Ω^Fibre≡ (suc n) f))) (p , q) ∣₂ , {!!} ∣) (fun PathIdTrunc₀Iso q)

--   im⊂ker-map1-map2 : (n : ℕ)
--     → (x : _)
--     → isInIm (hom1 n) x
--     → isInKer (hom2 n) x
--   im⊂ker-map1-map2 n =
--     sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _)
--      λ p → pRec (squash₂ _ _)
--              (uncurry
--               (sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _)
--                 λ q y → pRec (squash₂ _ _) (J (λ p _ → isInKer (hom2 n) ∣ p ∣₂)
--                   (help' n q))
--                  (fun PathIdTrunc₀Iso y)))
--      where
--      help' : (n : ℕ) (q : _) → isInKer (hom2 n) ∣ fst (map1 (suc n)) q ∣₂
--      help' n q = cong ∣_∣₂ ((funExt⁻ (map1∘map2 (suc n)) q)
--                ∙ (λ i → Ω^→ (suc n) (help34 i) .fst q)
--                ∙ funExt⁻ (cong fst (Ω^→const (suc n))) q)

-- module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {P : typ A → Type ℓ'}
--          (p-pt : P (pt A)) (homog : isHomogeneous (P (pt A) , p-pt))
--          (conA : isConnected 3 (typ A)) where

--   fib = P (pt A)
--   Total = Σ (typ A) P
--   BaseSp = typ A

--   Total∙ : Pointed _
--   Total∙ = Total , (pt A , p-pt)

--   fib∙ : Pointed _
--   fib∙ = fib , p-pt
--   BaseSp∙ = A

--   ↓map-pre : (n : ℕ) → S₊∙ (3 + n) →∙ BaseSp∙ → S₊∙ (2 + n) →∙ fib∙
--   fst (↓map-pre n f) x = subst P (sym (snd f) ∙∙ cong (fst f) (merid x ∙ sym (merid north)) ∙∙ snd f)
--                                        p-pt
--   snd (↓map-pre n f) =
--     cong (λ x → subst P x p-pt)
--          (cong (sym (snd f) ∙∙_∙∙ snd f)
--            (cong (cong (fst f)) (rCancel (merid north)))
--         ∙ ∙∙lCancel (snd f))
--     ∙ transportRefl p-pt

--   ↓map : (n : ℕ) → π' (3 + n) BaseSp∙ → π' (2 + n) fib∙
--   ↓map n = sMap (↓map-pre n)

--   ↓map-pre-id : (n : ℕ) → (f g : S₊∙ (3 + n) →∙ BaseSp∙) (x : _)
--     → fst (↓map-pre n (∙Π f g)) x ≡ fst (∙Π (↓map-pre n f) (↓map-pre n g)) x
--   ↓map-pre-id n f g x =
--       cong (λ x → subst P x p-pt) (sym (rUnit (cong (fst (∙Π f g)) (merid x ∙ sym (merid north))))
--                                  ∙ cong-∙ (fst (∙Π f g)) (merid x) (sym (merid north))
--                                  ∙ cong (cong (fst (∙Π f g)) (merid x) ∙_)
--                                         (cong sym
--                                           (cong₂ _∙_ (cong (sym (snd f) ∙∙_∙∙ snd f)
--                                             (cong (cong (fst f)) (rCancel (merid north)))
--                                           ∙ ∙∙lCancel (snd f))
--                                           ((cong (sym (snd g) ∙∙_∙∙ snd g)
--                                             (cong (cong (fst g)) (rCancel (merid north)))
--                                           ∙ ∙∙lCancel (snd g)))
--                                           ∙ sym (rUnit refl)))
--                                  ∙ sym (rUnit _))
--     ∙ {! subst P (λ i → fst (∙Π f g) (merid x i)) p-pt!}
--     where
--     help : (x : _) → subst P (λ i → fst (∙Π f g) (merid x i)) p-pt ≡
--       fst (∙Π (↓map-pre n f) (↓map-pre n g)) x
--     help x = {!↓map-pre n f!}

--   ↓hom : (n : ℕ) → GroupHom (π'Gr (2 + n) BaseSp∙) (π'Gr (1 + n) fib∙)
--   fst (↓hom n) = ↓map n
--   snd (↓hom n) =
--     makeIsGroupHom
--       (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
--         λ f g →
--           cong ∣_∣₂ (→∙Homogeneous≡ homog (funExt (↓map-pre-id n f g))))
