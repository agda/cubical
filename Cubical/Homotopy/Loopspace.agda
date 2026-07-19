
module Cubical.Homotopy.Loopspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Morphism
open import Cubical.Functions.Fibration

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)

open Iso

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- loop space map -}
Ω→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
      → (A →∙ B) → (Ω A →∙ Ω B)
fst (Ω→ {A = A} {B = B} (f , p)) q = sym p ∙∙ cong f q ∙∙ p
snd (Ω→ {A = A} {B = B} (f , p)) = ∙∙lCancel p

Ω^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → (A →∙ B) → ((Ω^ n) A →∙ (Ω^ n) B)
Ω^→ zero f = f
Ω^→ (suc n) f = Ω→ (Ω^→ n f)

{- loop space map functoriality (missing pointedness proof) -}
Ω→∘ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (g : B →∙ C) (f : A →∙ B)
  → ∀ p → Ω→ (g ∘∙ f) .fst p ≡ (Ω→ g ∘∙ Ω→ f) .fst p
Ω→∘ g f p k i =
  hcomp
    (λ j → λ
      { (i = i0) → compPath-filler' (cong (g .fst) (f .snd)) (g .snd) (~ k) j
      ; (i = i1) → compPath-filler' (cong (g .fst) (f .snd)) (g .snd) (~ k) j
      })
    (g .fst (doubleCompPath-filler (sym (f .snd)) (cong (f .fst) p) (f .snd) k i))

Ω→∘∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (g : B →∙ C) (f : A →∙ B)
  → Ω→ (g ∘∙ f) ≡ (Ω→ g ∘∙ Ω→ f)
Ω→∘∙ g f = →∙Homogeneous≡ (isHomogeneousPath _ _) (funExt (Ω→∘ g f))

Ω→const : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
          → Ω→ {A = A} {B = B} ((λ _ → pt B) , refl) ≡ ((λ _ → refl) , refl)
Ω→const = →∙Homogeneous≡ (isHomogeneousPath _ _) (funExt λ _ → sym (rUnit _))

{- Ω→ is a homomorphism -}
Ω→pres∙filler : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (p q : typ (Ω A))
        → I → I → I → fst B
Ω→pres∙filler f p q i j k =
  hfill
    (λ k → λ
       { (i = i0) → doubleCompPath-filler (sym (snd f)) (cong (fst f) (p ∙ q)) (snd f) k j
        ; (i = i1) →
          (doubleCompPath-filler
            (sym (snd f)) (cong (fst f) p) (snd f) k
         ∙ doubleCompPath-filler
            (sym (snd f)) (cong (fst f) q) (snd f) k) j
       ; (j = i0) → snd f k
       ; (j = i1) → snd f k})
    (inS (cong-∙ (fst f) p q i j))
    k

Ω→pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (p q : typ (Ω A))
        → fst (Ω→ f) (p ∙ q) ≡ fst (Ω→ f) p ∙ fst (Ω→ f) q
Ω→pres∙ f p q i j = Ω→pres∙filler f p q i j i1

Ω→pres∙reflrefl : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                  → Ω→pres∙ {A = A} {B = B} f refl refl
                   ≡ cong (fst (Ω→ f)) (sym (rUnit refl))
                   ∙ snd (Ω→ f)
                   ∙ rUnit _
                   ∙ cong₂ _∙_ (sym (snd (Ω→ f))) (sym (snd (Ω→ f)))
Ω→pres∙reflrefl {A = A} {B = B} =
  →∙J (λ b₀ f → Ω→pres∙ {A = A} {B = (fst B , b₀)} f refl refl
                   ≡ cong (fst (Ω→ f)) (sym (rUnit refl))
                   ∙ snd (Ω→ f)
                   ∙ rUnit _
                   ∙ cong₂ _∙_ (sym (snd (Ω→ f))) (sym (snd (Ω→ f))))
       λ f → lem f
         ∙ cong (cong (fst (Ω→ (f , refl))) (sym (rUnit refl)) ∙_)
                (((lUnit (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                                    (sym (snd (Ω→ (f , refl))))))
                ∙ cong (_∙ (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                                      (sym (snd (Ω→ (f , refl))))))
                   (sym (rCancel (snd (Ω→ (f , refl))))))
                ∙ sym (assoc (snd (Ω→ (f , refl)))
                  (sym (snd (Ω→ (f , refl))))
                    (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                               (sym (snd (Ω→ (f , refl)))))))
  where
  lem : (f : fst A → fst B) → Ω→pres∙ (f , refl) (λ _ → snd A) (λ _ → snd A) ≡
      (λ i → fst (Ω→ (f , refl)) (rUnit (λ _ → snd A) (~ i))) ∙
      (λ i → snd (Ω→ (f , refl)) (~ i) ∙ snd (Ω→ (f , refl)) (~ i))
  lem f k i j =
    hcomp (λ r → λ { (i = i0) → doubleCompPath-filler
                                   refl (cong f ((λ _ → pt A) ∙ refl)) refl (r ∨ k) j
                    ; (i = i1) → (∙∙lCancel (λ _ → f (pt A)) (~ r)
                                 ∙ ∙∙lCancel (λ _ → f (pt A)) (~ r)) j
                    ; (j = i0) → f (snd A)
                    ; (j = i1) → f (snd A)
                    ; (k = i0) → Ω→pres∙filler {A = A} {B = fst B , f (pt A)}
                                   (f , refl) refl refl i j r
                    ; (k = i1) → compPath-filler
                                   ((λ i → fst (Ω→ (f , refl))
                                                (rUnit (λ _ → snd A) (~ i))))
                                   ((λ i → snd (Ω→ (f , refl)) (~ i)
                                          ∙ snd (Ω→ (f , refl)) (~ i))) r i j})
     (hcomp (λ r → λ { (i = i0) → doubleCompPath-filler refl (cong f (rUnit (λ _ → pt A) r)) refl k j
                    ; (i = i1) → rUnit (λ _ → f (pt A)) (r ∨ k) j
                    ; (j = i0) → f (snd A)
                    ; (j = i1) → f (snd A)
                    ; (k = i0) → cong-∙∙-filler f (λ _ → pt A) (λ _ → pt A) (λ _ → pt A) r i j
                    ; (k = i1) → fst (Ω→ (f , refl)) (rUnit (λ _ → snd A) (~ i ∧ r)) j})
             (rUnit (λ _ → f (pt A)) k j))

{- Ω^→ is homomorphism -}
Ω^→pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (n : ℕ)
        → (p q : typ ((Ω^ (suc n)) A))
        → fst (Ω^→ (suc n) f) (p ∙ q)
         ≡ fst (Ω^→ (suc n) f) p ∙ fst (Ω^→ (suc n) f) q
Ω^→pres∙ {A = A} {B = B} f n p q = Ω→pres∙ (Ω^→ n f) p q

Ω^→∘∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} (n : ℕ)
  (g : B →∙ C) (f : A →∙ B)
  → Ω^→ n (g ∘∙ f) ≡ (Ω^→ n g ∘∙ Ω^→ n f)
Ω^→∘∙ zero g f = refl
Ω^→∘∙ (suc n) g f = cong Ω→ (Ω^→∘∙ n g f) ∙ Ω→∘∙ (Ω^→ n g) (Ω^→ n f)

Ω^→const : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
          → Ω^→ {A = A} {B = B} n ((λ _ → pt B) , refl)
          ≡ ((λ _ → snd ((Ω^ n) B)) , refl)
Ω^→const zero = refl
Ω^→const (suc n) = cong Ω→ (Ω^→const n) ∙ Ω→const

isEquivΩ→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
           → (f : (A →∙ B))
           → isEquiv (fst f) → isEquiv (Ω→ f .fst)
isEquivΩ→ {B = (B , b)} =
  uncurry λ f →
    J (λ b y → isEquiv f
             → isEquiv (λ q → (λ i → y (~ i)) ∙∙ (λ i → f (q i)) ∙∙ y))
      λ eqf → subst isEquiv (funExt (rUnit ∘ cong f))
                     (isoToIsEquiv (congIso (equivToIso (f , eqf))))

isEquivΩ^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
           → (f : A →∙ B)
           → isEquiv (fst f)
           → isEquiv (Ω^→ n f .fst)
isEquivΩ^→ zero f iseq = iseq
isEquivΩ^→ (suc n) f iseq = isEquivΩ→ (Ω^→ n f) (isEquivΩ^→ n f iseq)

Ω≃∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (Ω A) ≃∙ (Ω B)
fst (fst (Ω≃∙ e)) = fst (Ω→ (fst (fst e) , snd e))
snd (fst (Ω≃∙ e)) = isEquivΩ→ (fst (fst e) , snd e) (snd (fst e))
snd (Ω≃∙ e) = snd (Ω→ (fst (fst e) , snd e))

Ω≃∙pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (p q : typ (Ω A))
     → fst (fst (Ω≃∙ e)) (p ∙ q)
     ≡ fst (fst (Ω≃∙ e)) p
     ∙ fst (fst (Ω≃∙ e)) q
Ω≃∙pres∙ e p q = Ω→pres∙ (fst (fst e) , snd e) p q

Ω^≃∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
     → (e : A ≃∙ B)
     → ((Ω^ n) A) ≃∙ ((Ω^ n) B)
Ω^≃∙ zero e = e
fst (fst (Ω^≃∙ (suc n) e)) =
  fst (Ω→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)))
snd (fst (Ω^≃∙ (suc n) e)) =
  isEquivΩ→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)) (snd (fst (Ω^≃∙ n e)))
snd (Ω^≃∙ (suc n) e) =
  snd (Ω→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)))

ΩfunExtIso : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  → Iso (typ (Ω (A →∙ B ∙))) (A →∙ Ω B)
fst (fun (ΩfunExtIso A B) p) x = funExt⁻ (cong fst p) x
snd (fun (ΩfunExtIso A B) p) i j = snd (p j) i
fst (inv (ΩfunExtIso A B) (f , p) i) x = f x i
snd (inv (ΩfunExtIso A B) (f , p) i) j = p j i
rightInv (ΩfunExtIso A B) _ = refl
leftInv (ΩfunExtIso A B) _ = refl

relax→∙Ω-Iso : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (Σ[ b ∈ fst B ] (fst A → b ≡ pt B))
         (A →∙ (Ω B))
Iso.fun (relax→∙Ω-Iso {A = A}) (b , p) = (λ a → sym (p (pt A)) ∙ p a) , lCancel (p (snd A))
Iso.inv (relax→∙Ω-Iso {B = B}) a = (pt B) , (fst a)
Iso.rightInv (relax→∙Ω-Iso) a =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ x → cong (_∙ fst a x) (cong sym (snd a)) ∙ sym (lUnit (fst a x)))
Iso.leftInv (relax→∙Ω-Iso {A = A}) (b , p) =
  ΣPathP (sym (p (pt A))
       , λ i a j → compPath-filler' (sym (p (pt A))) (p a) (~ i) j)


{- Commutativity of loop spaces -}
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

private
  mainPath : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (α β : typ ((Ω^ (2 + n)) A))
           → (λ i → α i ∙ refl) ∙ (λ i → refl ∙ β i)
            ≡ (λ i → refl ∙ β i) ∙ (λ i → α i ∙ refl)
  mainPath n α β i = (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

EH-filler : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → typ ((Ω^ (2 + n)) A)
  → typ ((Ω^ (2 + n)) A) → I → I → I → _
EH-filler {A = A} n α β i j z =
  hfill (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α)
                                ∙ cong (λ x → lUnit x (~ k)) β) j
                  ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β)
                                ∙ cong (λ x → rUnit x (~ k)) α) j
                  ; (j = i0) → rUnit refl (~ k)
                  ; (j = i1) → rUnit refl (~ k)})
        (inS (mainPath n α β i j)) z

{- Eckmann-Hilton -}
EH : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
EH {A = A} n α β i j = EH-filler n α β i j i1

{- Lemmas for the syllepsis : EH α β ≡ (EH β α) ⁻¹ -}

EH-refl-refl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → EH {A = A} n refl refl ≡ refl
EH-refl-refl {A = A} n k i j =
  hcomp (λ r → λ { (k = i1) → (refl ∙ (λ _ → basep)) j
                  ; (j = i0) → rUnit basep (~ r ∧ ~ k)
                  ; (j = i1) → rUnit basep (~ r ∧ ~ k)
                  ; (i = i0) → (refl ∙ (λ _ → lUnit basep (~ r ∧ ~ k))) j
                  ; (i = i1) → (refl ∙ (λ _ → lUnit basep (~ r ∧ ~ k))) j})
        (((cong (λ x → rUnit x (~ k)) (λ _ → basep))
         ∙ cong (λ x → lUnit x (~ k)) (λ _ → basep)) j)
  where
  basep = snd (Ω ((Ω^ n) A))

{- Generalisations of EH α β when α or β is refl -}
EH-gen-l : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → {x y : typ ((Ω^ (suc n)) A)} (α : x ≡ y)
       → α ∙ refl ≡ refl ∙ α
EH-gen-l {ℓ = ℓ} {A = A} n {x = x} {y = y} α i j z =
  hcomp (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ refl) j z
                  ; (i = i1) → (refl ∙ cong (λ x → rUnit x (~ k)) α) j z
                  ; (j = i0) → rUnit (refl {x = x z}) (~ k) z
                  ; (j = i1) → rUnit (refl {x = y z}) (~ k) z
                  ; (z = i0) → x i1
                  ; (z = i1) → y i1})
        (((λ j → α (j ∧ ~ i) ∙ refl) ∙ λ j → α (~ i ∨ j) ∙ refl) j z)

EH-gen-r : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → {x y : typ ((Ω^ (suc n)) A)} (β : x ≡ y)
        → refl ∙ β ≡ β ∙ refl
EH-gen-r {A = A} n {x = x} {y = y} β i j z =
  hcomp (λ k → λ { (i = i0) → (refl ∙ cong (λ x → lUnit x (~ k)) β) j z
                  ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ refl) j z
                  ; (j = i0) → lUnit (λ k → x (k ∧ z)) (~ k) z
                  ; (j = i1) → lUnit (λ k → y (k ∧ z)) (~ k) z
                  ; (z = i0) → x i1
                  ; (z = i1) → y i1})
        (((λ j → refl ∙ β (j ∧ i)) ∙ λ j → refl ∙ β (i ∨ j)) j z)

{- characterisations of EH α β when α or β is refl  -}
EH-α-refl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (α : typ ((Ω^ (2 + n)) A))
             → EH n α refl ≡ sym (rUnit α) ∙ lUnit α
EH-α-refl {A = A} n α i j k =
  hcomp (λ r → λ { (i = i0) → EH-gen-l n (λ i → α (i ∧ r)) j k
                  ; (i = i1) → (sym (rUnit λ i → α (i ∧ r)) ∙ lUnit λ i → α (i ∧ r)) j k
                  ; (j = i0) → ((λ i → α (i ∧ r)) ∙ refl) k
                  ; (j = i1) → (refl ∙ (λ i → α (i ∧ r))) k
                  ; (k = i0) → refl
                  ; (k = i1) → α r})
        ((EH-refl-refl n ∙ sym (lCancel (rUnit refl))) i j k)

EH-refl-β : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (β : typ ((Ω^ (2 + n)) A))
             → EH n refl β ≡ sym (lUnit β) ∙ rUnit β
EH-refl-β {A = A} n β i j k =
  hcomp (λ r → λ { (i = i0) → EH-gen-r n (λ i → β (i ∧ r)) j k
                  ; (i = i1) → (sym (lUnit λ i → β (i ∧ r)) ∙ rUnit λ i → β (i ∧ r)) j k
                  ; (j = i0) → (refl ∙ (λ i → β (i ∧ r))) k
                  ; (j = i1) → ((λ i → β (i ∧ r)) ∙ refl) k
                  ; (k = i0) → refl
                  ; (k = i1) → β r})
        ((EH-refl-refl n ∙ sym (lCancel (rUnit refl))) i j k)

syllepsis : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (α β : typ ((Ω^ 3) A))
         → EH 0 α β ≡ sym (EH 0 β α)
syllepsis {A = A} n α β k i j =
  hcomp (λ r → λ { (i = i0) → i=i0 r j k
                  ; (i = i1) → i=i1 r j k
                  ; (j = i0) → j-filler r j k
                  ; (j = i1) → j-filler r j k
                  ; (k = i0) → EH-filler 1 α β i j r
                  ; (k = i1) → EH-filler 1 β α (~ i) j r})
        (btm-filler (~ k) i j)
  where
  guy = snd (Ω (Ω A))

  btm-filler : I → I → I → typ (Ω (Ω A))
  btm-filler j i k =
    hcomp (λ r
      → λ {(j = i0) → mainPath 1 β α (~ i) k
          ; (j = i1) → mainPath 1 α β i k
          ; (i = i0) → (cong (λ x → EH-α-refl 0 x r (~ j)) α
                       ∙ cong (λ x → EH-refl-β 0 x r (~ j)) β) k
          ; (i = i1) → (cong (λ x → EH-refl-β 0 x r (~ j)) β
                       ∙ cong (λ x → EH-α-refl 0 x r (~ j)) α) k
          ; (k = i0) → EH-α-refl 0 guy r (~ j)
          ; (k = i1) → EH-α-refl 0 guy r (~ j)})
      (((λ l → EH 0 (α (l ∧ ~ i)) (β (l ∧ i)) (~ j))
       ∙ λ l → EH 0 (α (l ∨ ~ i)) (β (l ∨ i)) (~ j)) k)

  link : I → I → I → _
  link z i j =
    hfill (λ k → λ { (i = i1) → refl
                    ; (j = i0) → rUnit refl (~ i)
                    ; (j = i1) → lUnit guy (~ i ∧ k)})
          (inS (rUnit refl (~ i ∧ ~ j))) z

  i=i1 : I → I → I → typ (Ω (Ω A))
  i=i1 r j k =
    hcomp (λ i → λ { (r = i0) → (cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) i k) β
                                ∙ cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) i k) α) j
                    ; (r = i1) → (β ∙ α) j
                    ; (k = i0) → (cong (λ x → lUnit x (~ r)) β ∙
                                   cong (λ x → rUnit x (~ r)) α) j
                    ; (k = i1) → (cong (λ x → rUnit x (~ r ∧ i)) β ∙
                                   cong (λ x → lUnit x (~ r ∧ i)) α) j
                    ; (j = i0) → link i r k
                    ; (j = i1) → link i r k})
          (((cong (λ x → lUnit x (~ r ∧ ~ k)) β
           ∙ cong (λ x → rUnit x (~ r ∧ ~ k)) α)) j)

  i=i0 : I → I → I → typ (Ω (Ω A))
  i=i0 r j k =
    hcomp (λ i → λ { (r = i0) → (cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) i k) α
                                ∙ cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) i k) β) j
                    ; (r = i1) → (α ∙ β) j
                    ; (k = i0) → (cong (λ x → rUnit x (~ r)) α ∙
                                   cong (λ x → lUnit x (~ r)) β) j
                    ; (k = i1) → (cong (λ x → lUnit x (~ r ∧ i)) α ∙
                                   cong (λ x → rUnit x (~ r ∧ i)) β) j
                    ; (j = i0) → link i r k
                    ; (j = i1) → link i r k})
          ((cong (λ x → rUnit x (~ r ∧ ~ k)) α
           ∙ cong (λ x → lUnit x (~ r ∧ ~ k)) β) j)

  j-filler : I → I → I → typ (Ω (Ω A))
  j-filler r i k =
    hcomp (λ j → λ { (i = i0) → link j r k
                    ; (i = i1) → link j r k
                    ; (r = i0) → compPath-filler (sym (rUnit guy))
                                                  (lUnit guy) j k
                    ; (r = i1) → refl
                    ; (k = i0) → rUnit guy (~ r)
                    ; (k = i1) → rUnit guy (j ∧ ~ r)})
          (rUnit guy (~ r ∧ ~ k))

------ Ωⁿ⁺¹ A ≃ Ωⁿ(Ω A) ------
flipΩPath : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                → ((Ω^ (suc n)) A) ≡ (Ω^ n) (Ω A)
flipΩPath {A = A} zero = refl
flipΩPath {A = A} (suc n) = cong Ω (flipΩPath {A = A} n)

flipΩIso : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
              → Iso (fst ((Ω^ (suc n)) A)) (fst ((Ω^ n) (Ω A)))
flipΩIso {A = A} n = pathToIso (cong fst (flipΩPath n))

flipΩIso⁻pres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst ((Ω^ (suc n)) (Ω A)))
                      → inv (flipΩIso (suc n)) (f ∙ g)
                      ≡ (inv (flipΩIso (suc n)) f)
                      ∙ (inv (flipΩIso (suc n)) g)
flipΩIso⁻pres· {A = A} n f g i =
    transp (λ j → flipΩPath {A = A} n (~ i ∧ ~ j) .snd
                 ≡ flipΩPath n (~ i ∧ ~ j) .snd) i
                  (transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) f
                 ∙ transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) g)

flipΩIsopres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst (Ω ((Ω^ (suc n)) A)))
                      → fun (flipΩIso (suc n)) (f ∙ g)
                      ≡ (fun (flipΩIso (suc n)) f)
                      ∙ (fun (flipΩIso (suc n)) g)
flipΩIsopres· n =
  morphLemmas.isMorphInv _∙_ _∙_
    (inv (flipΩIso (suc n)))
    (flipΩIso⁻pres· n)
    (fun (flipΩIso (suc n)))
    (Iso.leftInv (flipΩIso (suc n)))
    (Iso.rightInv (flipΩIso (suc n)))

flipΩrefl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → fun (flipΩIso {A = A} (suc n)) refl ≡ refl
flipΩrefl {A = A} n j =
  transp (λ i₁ → fst (Ω (flipΩPath {A = A} n ((i₁ ∨ j)))))
         j (snd (Ω (flipΩPath n j)))

---- Misc. ----

isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                    → isOfHLevel (suc n) (typ A)
                    → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
    ((λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (cong (trRec hlev (λ x → x)) (p ∙ q)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
 ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
 ∙∙ (λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B)
  → isComm∙ A → isComm∙ (B , fun e (pt A))
ptdIso→comm {A = (A , a)} {B = B} e comm p q =
       sym (rightInv (congIso e) (p ∙ q))
    ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                            ∙∙ (comm (inv (congIso e) p) (inv (congIso e) q))
                            ∙∙ (sym (invCongFunct e q p))))
    ∙∙ rightInv (congIso e) (q ∙ p)

{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₂
      → ∥ typ ((Ω^ (suc n)) A) ∥₂ → ∥ typ ((Ω^ (suc n)) A) ∥₂
π-comp n = elim2 (λ _ _ → isSetSetTrunc) λ p q → ∣ p ∙ q ∣₂

EH-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
EH-π  n = elim2 (λ x y → isOfHLevelPath 2 isSetSetTrunc _ _)
                             λ p q → cong ∣_∣₂ (EH n p q)

{-
  If A -> B -> C is a fiber sequence, and Ω B -> Ω C has a section,
  then Ω B is the product Ω A × Ω C.

  https://gist.github.com/ecavallo/5b75313d36977c51ca3563de82506123
-}

module _ {ℓ} {B C : Type ℓ} (b₀ : B) (π : B → C) where
  private
    c₀ = π b₀
    A = fiber π c₀
    a₀ : A
    a₀ = b₀ , refl
    ι : A → B
    ι = fst
    π∘ι≡0 : ∀ a → π (ι a) ≡ c₀
    π∘ι≡0 = snd

    A∙ B∙ C∙ : Pointed _
    A∙ = (A , a₀)
    B∙ = (B , b₀)
    C∙ = (C , c₀)

    TwistedProduct : Pointed _
    TwistedProduct = ((Σ[ p ∈ typ (Ω C∙) ] (b₀ , p) ≡ a₀) , refl , refl)

  -- The middle term of a fiber sequence always splits
  -- as a twisted product without any conditions.
  presplit : Ω B∙ ≡ TwistedProduct
  presplit = cong Ω (ua∙ (totalEquiv π) refl)
    ∙ sym (ua∙ ΣPath≃PathΣ refl)
    ∙ Σ-cong-equiv-snd∙ (λ p
      → PathP≃Path _ _ _ ∙ₑ
        compPathlEquiv (sym (fromPathP
          (ΣPathP (refl , λ i j → p (i ∧ j))))))
      (rCancel λ j → transp (λ _ → A) (~ j) a₀)

  module Split (s : typ (Ω C∙) → typ (Ω B∙))
      (section : ∀ p → cong π (s p) ≡ p) where
    movePoint : ∀ p → a₀ ≡ (b₀ , sym p)
    movePoint p = ΣPathP (s p ,
      λ i j → slideSquare (section p) i (~ j))

    splitting : typ (Ω B∙) ≡ typ (Ω C∙) × typ (Ω A∙)
    splitting = cong typ presplit ∙ ua
      (Σ-cong-equiv-snd λ p → compPathlEquiv (movePoint _))

    -- If the section furthermore respects the base point, then
    -- the splitting does too.
    module _ (h : s refl ≡ refl) (coh : cong (cong π) h ≡ section refl) where
      movePoint-refl : movePoint refl ≡ refl
      movePoint-refl i j = h i j , λ k →
        slideSquare (cong sym coh ∙ lemma _ _) (~ i) (~ k) j
        where
          lemma : ∀ {ℓ} {X : Type ℓ} {x : X} (p : x ≡ x) (q : p ≡ refl)
            → sym q ≡ flipSquare (slideSquare q)
          lemma {x = x} p q = J (λ p (q : refl ≡ p)
              → q ≡ flipSquare (slideSquare (sym q)))
            (λ i j k → hfill
              (slideSquareFaces
                {a₀₀ = x} {a₋ = refl} {a₁₋ = refl} {a₋₀ = refl}
                j k) (inS x) i)
            (sym q)

      twisted∙ : TwistedProduct ≡ Ω C∙ ×∙ Ω A∙
      twisted∙ = Σ-cong-equiv-snd∙
        (λ p → compPathlEquiv (movePoint _))
        (cong (λ t → compPathlEquiv t .fst refl) movePoint-refl ∙ sym (rUnit _))

      splitting∙ : Ω B∙ ≡ Ω C∙ ×∙ Ω A∙
      splitting∙ = presplit ∙ twisted∙

      -- splitting and splitting∙ agrees
      splitting-typ : cong typ splitting∙ ≡ splitting
      splitting-typ = congFunct typ presplit twisted∙
