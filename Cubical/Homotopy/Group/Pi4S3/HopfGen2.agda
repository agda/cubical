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

→∙∙lCancel'-refl-refl :
  {ℓ : Level} {A : Type ℓ} {x : A} (p : refl {x = x} ≡ refl)
  → →∙∙lCancel' {x = x} {y = x} refl refl (sym (rUnit refl) ∙ p)
  ≡ flipSquare p
→∙∙lCancel'-refl-refl p k i j =
  hcomp (λ r → λ { (i = i0) → p i0 i0
             ; (i = i1) → p i0 i0
             ; (j = i0) → rUnit (λ _ → p i0 i0) (~ r) i
             ; (j = i1) → p i0 i0
             ; (k = i0) → →∙∙lCancel'-fill refl refl (sym (rUnit refl) ∙ p) r i j
             ; (k = i1) → compPath-filler' (sym (rUnit refl)) p (~ r) j i})
         (((sym (rUnit refl)) ∙ p) j i)

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

ΩFibreIso⁻pres∙snd : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) (p q : typ (Ω (Ω B))) 
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
    hcomp (λ r → λ {(i = i0) → →∙∙lCancel'-refl-refl (p ∙ q) (~ r) j k -- 
                   ; (i = i1) →
                     snd (compPath-filler
                         (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ p))
                         (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q)) r j) k
                   ; (j = i0) → f (snd A)
                   ; (j = i1) → snd (inv (ΩFibreIso (f , refl)) (refl , sym (rUnit refl) ∙ q) (r ∨ ~ i)) k
                   ; (k = i0) → pp r i j
                   ; (k = i1) → f (snd A)})
       (hcomp (λ r → λ {(i = i0) → (p ∙ q) k j
                   ; (i = i1) → →∙∙lCancel'-refl-refl p (~ r) j k
                   ; (j = i0) → f (snd A)
                   ; (j = i1) → →∙∙lCancel'-refl-refl q (~ r) (~ i) k
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

    pp : Cube refl
              (λ i j → f ((rUnit refl ∙ sym (cong-∙ fst P Q)) i j)) -- r i j
              (λ r j → f (snd A))
              (λ r j → f (fst (compPath-filler P Q r j)))
              (λ r i → f (snd A))
              λ r i → f (snd A)
    pp r i j =
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

fibcomp : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → fiber (Ω→ f .fst) refl → fiber (Ω→ f .fst) refl → fiber (Ω→ f .fst) refl
fst (fibcomp f p q) = fst p ∙ fst q
snd (fibcomp f p q) = Ω→pres∙ f (fst p) (fst q)
                    ∙ cong₂ _∙_ (snd p) (snd q)
                    ∙ sym (rUnit refl)

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

mainlem : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ((fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f)) ∘∙
       (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)))
       ≡ idfun∙ _
mainlem zero f = ΣPathP (refl , (sym (rUnit refl)))
mainlem (suc n) f =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt
      λ p → cong (fst (fst (ΩIso (Ω^Fibre≃∙⁻ n f))))
                   (leftInv (ΩFibreIso (Ω^→ n f))
                     ((fst (fst (ΩIso (Ω^Fibre≃∙ n f))) p)))
          ∙ sym (Ω→∘ (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
                 (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) p)
          ∙ (λ i → (Ω→ (mainlem n f i)) .fst p)
          ∙ sym (rUnit p))

mainleml : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → ((fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f)) ∘∙
           (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f)))
          ≡ idfun∙ _
mainleml zero f = ΣPathP (refl , (sym (rUnit refl)))
mainleml (suc n) f =
    →∙Homogeneous≡ (isHomogeneousΩ^→fib n f)
      (funExt (λ p →
        cong (fun (ΩFibreIso (Ω^→ n f)))
          ((sym (Ω→∘ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))
                     (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
               (inv (ΩFibreIso (Ω^→ n f)) p)))
         ∙ (λ i → Ω→ (mainleml n f i) .fst (inv (ΩFibreIso (Ω^→ n f)) p))
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

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  isInIm∙ : (x : typ B) → Type (ℓ-max ℓ ℓ')
  isInIm∙ x = Σ[ z ∈ typ A ] fst f z ≡ x

  ∥isInIm∙∥ : (x : typ B) → Type (ℓ-max ℓ ℓ')
  ∥isInIm∙∥ x = ∃[ z ∈ typ A ] fst f z ≡ x

  isInKer∙ : (x : fst A) → Type ℓ'
  isInKer∙ x = fst f x ≡ snd B

  ∥isInKer∙∥ : (x : fst A) → Type ℓ'
  ∥isInKer∙∥ x = ∥ fst f x ≡ snd B ∥

module _ {ℓ ℓ' ℓ'' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}  where
  Im∙_⊂Ker∙_ : (f : A →∙ B) (g : B →∙ C) → Type _
  Im∙ f ⊂Ker∙ g = (x : typ B) → isInIm∙ f x → isInKer∙ g x

  ∥Im∙_⊂Ker∙_∥ : (f : A →∙ B) (g : B →∙ C) → Type _
  ∥Im∙ f ⊂Ker∙ g ∥ = (x : typ B) → ∥isInIm∙∥ f x → ∥isInKer∙∥ g x

  Ker∙_⊂Im∙_ : (g : B →∙ C) (f : A →∙ B) → Type _
  Ker∙ g ⊂Im∙ f = (x : typ B) → isInKer∙ g x → isInIm∙ f x

  ∥Ker∙_⊂Im∙_∥ : (g : B →∙ C) (f : A →∙ B) → Type _
  ∥Ker∙ g ⊂Im∙ f ∥ = (x : typ B) → ∥isInKer∙∥ g x → ∥isInIm∙∥ f x

∥_∥₂∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
fst ∥ A ∥₂∙ = ∥ fst A ∥₂
snd ∥ A ∥₂∙ = ∣ pt A ∣₂

map∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
       (f : A →∙ B) → ∥ A ∥₂∙ →∙ ∥ B ∥₂∙
fst (map∙ f) = sMap (fst f)
snd (map∙ f) = cong ∣_∣₂ (snd f)

module _ {ℓ ℓ' ℓ'' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
         (f : A →∙ B) (g : B →∙ C) where
  Ker⊂Im∥₂ : Ker∙ g ⊂Im∙ f → ∥Ker∙ (map∙ g) ⊂Im∙ (map∙ f) ∥
  Ker⊂Im∥₂ ker⊂im =
    sElim (λ _ → isSetΠ λ _ → isProp→isSet squash)
      λ b →
        pRec squash
         (λ q → pRec squash
           (λ q →  ∣ ∣ fst (ker⊂im b q) ∣₂ , cong ∣_∣₂ (snd (ker⊂im b q)) ∣)
           (fun PathIdTrunc₀Iso q))

  Im⊂Ker∥₂ : Im∙ f ⊂Ker∙ g →  ∥Im∙ (map∙ f) ⊂Ker∙ (map∙ g) ∥
  Im⊂Ker∥₂ im⊂ker =
    sElim (λ _ → isSetΠ λ _ → isProp→isSet squash)
      λ b → pRec squash
        (uncurry (sElim (λ _ → isSetΠ λ _ → isProp→isSet squash)
          λ a p → pRec squash
            (λ p → ∣ cong ∣_∣₂ (im⊂ker b (a , p)) ∣)
            (fun PathIdTrunc₀Iso p)))

module ΩLES {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  fibf : Pointed _
  fibf = fiber (fst f) (pt B) , (pt A , snd f)

  fibF : (n : ℕ) → Pointed _
  fibF n = (fiber (Ω^→ n f .fst) (snd ((Ω^ n) (fst B , snd B))))
         , (snd ((Ω^ n) (fst A , snd A))) , (Ω^→ n f .snd)

  fibf^ : (n : ℕ) → Pointed _
  fibf^ n = (Ω^ n) fibf

  fibf^≃fibF : (n : ℕ) → fibf^ n ≃∙ fibF n
  fibf^≃fibF n = Ω^Fibre≃∙' n f

  fibF→A : (n : ℕ) → fibF n →∙ (Ω^ n) A
  fst (fibF→A n) = fst
  snd (fibF→A n) = refl

  fibf^→A' : (n : ℕ) → fibf^ n →∙ (Ω^ n) A
  fibf^→A' n = fst ∘ (fst (fst (Ω^Fibre≃∙ n f))) , cong fst (snd (Ω^Fibre≃∙ n f))

  fibf^→A : (n : ℕ) → fibf^ n →∙ (Ω^ n) A
  fibf^→A n = fibF→A n ∘∙ (fst (fst (Ω^Fibre≃∙ n f)) , snd (Ω^Fibre≃∙ n f))

  isHom-fibf^→A : (n : ℕ) → (p q : fibf^ (suc n) .fst)
    → fibf^→A (suc n) .fst (p ∙ q)
     ≡ fibf^→A (suc n) .fst p
     ∙ fibf^→A (suc n) .fst q
  isHom-fibf^→A n p q =
    cong (fst (fibF→A (suc n)))
      (cong (fun (ΩFibreIso (Ω^→ n f)))
        (Ω→pres∙ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f)))) p q))
    ∙ ΩFibreIsopres∙fst (Ω^→ n f)
        (fst (Ω→ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f))))) p)
        (fst (Ω→ ((fst (fst (Ω^Fibre≃∙ n f))) , (snd ((Ω^Fibre≃∙ n f))))) q)

  A→B : (n : ℕ) → (Ω^ n) A →∙ (Ω^ n) B
  A→B n = Ω^→ n f

  A→B-pres∙ : (n : ℕ) → (p q : typ ((Ω^ (suc n)) A))
            → fst (A→B (suc n)) (p ∙ q)
            ≡ fst (A→B (suc n)) p ∙ fst (A→B (suc n)) q
  A→B-pres∙ n p q = Ω^→pres∙ f n p q

  ΩB→fibF' : (n : ℕ) → ((Ω^ (suc n)) B) →∙ fibF n
  fst (ΩB→fibF' n) x = (snd ((Ω^ n) A)) , (Ω^→ n f .snd ∙ x)
  snd (ΩB→fibF' n) = ΣPathP (refl , (sym (rUnit _)))

  ΩB→fibf^ : (n : ℕ) → (Ω^ (suc n)) B →∙ fibf^ n
  ΩB→fibf^ n =
       (fst (fst (Ω^Fibre≃∙⁻ n f)) , snd (Ω^Fibre≃∙⁻ n f))
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

  -- corrected:
  fibf^→A⊂kerA→B' : (n : ℕ) (x : _)
                     → isInIm∙ (fibf^→A n) x
                     → isInKer∙ (A→B n) x
  fibf^→A⊂kerA→B' n x x₁ =
    imfibF→A⊂kerA→B n x
      ((((fst (fst (Ω^Fibre≃∙ n f)))) (fst x₁))
        , snd x₁)

  kerA→B⊂fibf^→A : (n : ℕ) (x : _)
                   → isInKer∙ (A→B n) x
                   → isInIm∙ (fibf^→A n) x
  kerA→B⊂fibf^→A n x ker =
      invEq (fst (Ω^Fibre≃∙ n f)) (x , ker)
    , (cong fst (secEq (fst (Ω^Fibre≃∙ n f)) (x , ker)))

  -- old
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

  -- corrected
  kerfibf^→A⊂imΩB→fibf^ : (n : ℕ) (x : _)
                     → isInKer∙ (fibf^→A n) x
                     → isInIm∙ (ΩB→fibf^ n) x
  kerfibf^→A⊂imΩB→fibf^ n x p =
      fst r
    , cong (fst ((fst (Ω^Fibre≃∙⁻ n f)))) (snd r)
    ∙ funExt⁻ (cong fst (mainlem n f)) x
    where
    r : isInIm∙ (ΩB→fibF' n) (fst (fst (Ω^Fibre≃∙ n f)) x)
    r = kerfibF→A⊂imΩB→fibF' n (fst (fst (Ω^Fibre≃∙ n f)) x) p

  imΩB→fibf^⊂kerfibf^→A : (n : ℕ) (x : _)
                     → isInIm∙ (ΩB→fibf^ n) x
                     → isInKer∙ (fibf^→A n) x
  imΩB→fibf^⊂kerfibf^→A n x =
    uncurry λ p →
      J (λ x _ → isInKer∙ (fibf^→A n) x)
        (cong (fst (fibF→A n))
          (funExt⁻ (cong fst (mainleml n f)) _))

  -- old
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

  -- corrected
  imA→B⊂kerΩB→fibf^ : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInIm∙ (A→B (suc n)) x
                     → isInKer∙ (ΩB→fibf^ n) x
  imA→B⊂kerΩB→fibf^ n x p =
      cong (fst ((fst (Ω^Fibre≃∙⁻ n f))))
           (imA→B⊂kerΩB→fibF' n x p)
    ∙ snd (Ω^Fibre≃∙⁻ n f)

  kerΩB→fibf^⊂imA→B : (n : ℕ) (x : fst (((Ω^ (suc n)) B)))
                     → isInKer∙ (ΩB→fibf^ n) x
                     → isInIm∙ (A→B (suc n)) x
  kerΩB→fibf^⊂imA→B n x p =
    kerΩB→fibF'⊂imA→B n x
         (funExt⁻ (cong fst (sym (mainleml n f))) (ΩB→fibF' n .fst x)
        ∙ cong (fst (fst (Ω^Fibre≃∙ n f))) p
        ∙ snd (Ω^Fibre≃∙ n f))




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

module πLES {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  module Ωs = ΩLES f 
  open Ωs renaming (A→B to A→B')

  fib = fibf

  fib→A : (n : ℕ) → GroupHom (πGr n fib) (πGr n A)
  fst (fib→A n) = sMap (fst (fibf^→A (suc n)))
  snd (fib→A n) =
    makeIsGroupHom
      (sElim2 (λ _  _ → isSetPathImplicit)
        λ p q → cong ∣_∣₂ (isHom-fibf^→A n p q))

  A→B : (n : ℕ) → GroupHom (πGr n A) (πGr n B)
  fst (A→B n) = sMap (fst (A→B' (suc n)))
  snd (A→B n) =
    makeIsGroupHom
      (sElim2 (λ _  _ → isSetPathImplicit)
        λ g h → cong ∣_∣₂ (Ω^→pres∙ f n g h))

  B→fib : (n : ℕ) → GroupHom (πGr (suc n) B) (πGr n fib)
  fst (B→fib n) = sMap (fst (ΩB→fibf^ (suc n)))
  snd (B→fib n) =
    makeIsGroupHom
      (sElim2
        (λ _  _ → isSetPathImplicit)
        λ p q → cong ∣_∣₂ (ΩB→fibf^pres∙ n p q))

  Ker-A→B⊂Im-fib→A : (n : ℕ) (x : π (suc n) A)
    → isInKer (A→B n) x
    → isInIm (fib→A n) x
  Ker-A→B⊂Im-fib→A n =
    setTruncLemmas.ker⊂im n n n
      (fibf^→A (suc n)) (A→B' (suc n))
      (snd (fib→A n)) (snd (A→B n))
      (kerA→B⊂fibf^→A (suc n))

  Im-fib→A⊂Ker-A→B : (n : ℕ) (x : π (suc n) A)
    → isInIm (fib→A n) x
    → isInKer (A→B n) x
  Im-fib→A⊂Ker-A→B n =
    setTruncLemmas.im⊂ker n n n
      (fibf^→A (suc n)) (A→B' (suc n))
      (snd (fib→A n)) (snd (A→B n))
      (fibf^→A⊂kerA→B' (suc n))

  Ker-fib→A⊂Im-B→fib : (n : ℕ) (x : π (suc n) fib)
    → isInKer (fib→A n) x
    → isInIm (B→fib n) x
  Ker-fib→A⊂Im-B→fib n =
    setTruncLemmas.ker⊂im (suc n) n n
      (ΩB→fibf^ (suc n)) (fibf^→A (suc n))
      (snd (B→fib n)) (snd (fib→A n))
      (kerfibf^→A⊂imΩB→fibf^ (suc n))

  Im-B→fib⊂Ker-fib→A : (n : ℕ) (x : π (suc n) fib)
    → isInIm (B→fib n) x
    → isInKer (fib→A n) x
  Im-B→fib⊂Ker-fib→A n =
    setTruncLemmas.im⊂ker (suc n) n n
      (ΩB→fibf^ (suc n)) (fibf^→A (suc n))
      (snd (B→fib n)) (snd (fib→A n))
      (imΩB→fibf^⊂kerfibf^→A (suc n))
