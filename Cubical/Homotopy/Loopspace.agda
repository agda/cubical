{-# OPTIONS --safe #-}

module Cubical.Homotopy.Loopspace where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open Iso

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- homotopy Group -}
π : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π n A = ∥ typ ((Ω^ n) A) ∥ 2

{- loop space map -}
Ω→ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → (Ω A →∙ Ω B)
Ω→ (f , f∙) = (λ p → (sym f∙ ∙ cong f p) ∙ f∙) , cong (λ q → q ∙ f∙) (sym (rUnit (sym f∙))) ∙ lCancel f∙

ΩfunExtIso : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') → Iso (typ (Ω (A →∙ B ∙))) (A →∙ Ω B)
fst (fun (ΩfunExtIso A B) p) x = funExt⁻ (cong fst p) x
snd (fun (ΩfunExtIso A B) p) i j = snd (p j) i
fst (inv (ΩfunExtIso A B) (f , p) i) x = f x i
snd (inv (ΩfunExtIso A B) (f , p) i) j = p j i
rightInv (ΩfunExtIso A B) _ = refl
leftInv (ΩfunExtIso A B) _ = refl

{- Commutativity of loop spaces -}
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
Eckmann-Hilton n α β =
  transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
                 ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)
        λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)
  where
  h : PathP (λ i → rUnit refl (~ i) ≡ lUnit refl (~ i))
            (cong (_∙ refl) α ∙ cong (refl ∙_) β)
            (α ∙ β)
  h i = cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β

EH = Eckmann-Hilton

EH-alt-filler : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → typ ((Ω^ (2 + n)) A) → typ ((Ω^ (2 + n)) A) → I → I → I → _
EH-alt-filler {A = A} n α β i j z =
  hfill (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ cong (λ x → lUnit x (~ k)) β) j
                  ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ cong (λ x → rUnit x (~ k)) α) j
                  ; (j = i0) → rUnit refl (~ k)
                  ; (j = i1) → rUnit refl (~ k)})
        (inS (((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)) j))
        z

EH-alt : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
EH-alt {A = A} n α β i j = EH-alt-filler n α β i j i1

EH-alt-refl-β : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (β : typ ((Ω^ (2 + n)) A))
             → EH-alt n refl β ≡ sym (lUnit β) ∙ rUnit β
EH-alt-refl-β {A = A} n β k i j =
  hcomp (λ r → λ { (i = i0) → (refl ∙ cong (λ x → lUnit x (~ k ∧ ~ r)) β) j
                  ; (i = i1) → (cong (λ x → lUnit x (~ k ∧ ~ r)) β ∙ refl) j
                  ; (j = i0) → rUnit refl (~ k ∧ ~ r)
                  ; (j = i1) → rUnit refl (~ k ∧ ~ r)
                  ; (k = i0) → EH-alt-filler n refl β i j r
                  ; (k = i1) → (sym (lUnit β) ∙ rUnit β) i j})
    (hcomp (λ r → λ { (i = i0) → lUnit ((cong (λ x → lUnit x (~ k)) β)) r j
                     ; (i = i1) → (cong (λ x → lUnit x (~ k)) β ∙ refl) j
                     ; (j = i0) → rUnit refl (~ k)
                     ; (j = i1) → rUnit refl (~ k)
                     ; (k = i0) → (compPath-filler' (sym (lUnit (cong (λ x → refl ∙ x) β)))
                                                     (rUnit (cong (λ x → refl ∙ x) β))
                                  ▷ sym (endP≡)) r i j
                     ; (k = i1) → compPath-filler' (sym (lUnit β)) (rUnit β) r i j})
           (rUnit (cong (λ x → lUnit x (~ k)) β) i j))
  where
  endP≡ : (λ i j → ((λ j → refl ∙ β (j ∧ i)) ∙ λ j → refl ∙ β (i ∨ j)) j)
        ≡ sym (lUnit _) ∙ rUnit (cong (λ x → refl ∙ x) β)
  endP≡ k i j =
    hcomp (λ r → λ { (i = i0) → (refl ∙ (cong (λ x → refl ∙ x) β)) j
                    ; (i = i1) → rUnit (cong (λ x → refl ∙ x) β) r j
                    ; (j = i0) → refl ∙ refl
                    ; (j = i1) → refl ∙ refl
                    ; (k = i0) → lem r i j
                    ; (k = i1) → compPath-filler (sym (lUnit (cong (λ x → refl ∙ x) β)))
                                                  (rUnit (cong (λ x → refl ∙ x) β)) r i j})
          (lUnit (cong (λ x → refl ∙ x) β) (~ i) j)
    where
    lem : I → I → I → typ ((Ω^ (suc n)) A)
    lem k i j =
      hcomp (λ r → λ { (i = i0) → compPath-filler refl ((λ j → refl ∙ β j)) (~ k ∨ r) j
                      ; (i = i1) → rUnit (cong (_∙_ refl) β) (k ∧ r) j
                      ; (j = i0) → refl ∙ refl
                      ; (j = i1) → refl ∙ β (i ∨ r ∨ ~ k)
                      ; (k = i0) → lUnit (cong (λ x → refl ∙ x) β) (~ i) j
                      ; (k = i1) → compPath-filler (λ j → refl ∙ β (j ∧ i)) (λ j → refl ∙ β (i ∨ j)) r j})
            (lUnit-filler (cong (λ x → refl ∙ x) β) (~ k) (~ i) j)

EH-alt-α-refl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (α : typ ((Ω^ (2 + n)) A))
             → EH-alt n α refl ≡ sym (rUnit α) ∙ lUnit α
EH-alt-α-refl {A = A} n α k i j =
  hcomp (λ r → λ { (i = i0) → ((cong (λ x → rUnit x (~ k ∧ ~ r)) α) ∙ refl) j
                  ; (i = i1) → (refl ∙ cong (λ x → rUnit x (~ k ∧ ~ r)) α) j
                  ; (j = i0) → rUnit refl (~ k ∧ ~ r)
                  ; (j = i1) → rUnit refl (~ k ∧ ~ r)
                  ; (k = i0) → EH-alt-filler n α refl i j r
                  ; (k = i1) → (sym (rUnit α) ∙ lUnit α) i j})
        (hcomp (λ r → λ { (i = i0) → rUnit ((cong (λ x → rUnit x (~ k)) α)) r j
                         ; (i = i1) → (refl ∙ (cong (λ x → rUnit x (~ k)) α)) j
                         ; (j = i0) → rUnit refl (~ k)
                         ; (j = i1) → rUnit refl (~ k)
                         ; (k = i0) → s i j r
                         ; (k = i1) → compPath-filler' (sym (rUnit α)) (lUnit α) r i j})
               (lUnit (cong (λ x → rUnit x (~ k)) α) i j))
  where
  endP≡ : (λ i j → ((λ j → α (j ∧ ~ i) ∙ refl) ∙ λ j → α (~ i ∨ j) ∙ refl) j) ≡ sym (rUnit _) ∙ lUnit _
  endP≡ k i j =
    hcomp (λ r → λ { (i = i0) → (cong (λ x → x ∙ refl) α ∙ refl) j
                    ; (i = i1) → (lUnit (cong (λ x → x ∙ refl) α)) r j
                    ; (j = i0) → refl ∙ refl
                    ; (j = i1) → refl ∙ refl
                    ; (k = i0) → lem r i j
                    ; (k = i1) → compPath-filler (sym (rUnit (cong (λ x → x ∙ refl) α)))
                                                  (lUnit (cong (λ x → x ∙ refl) α)) r i j})
          (rUnit (cong (λ x → x ∙ refl) α) (~ i) j)
    where
    lem : I → I → I → typ ((Ω^ (suc n)) A)
    lem k i j =
      hcomp (λ r → λ { (i = i0) → compPath-filler ((λ j → α j ∙ refl)) (λ j → refl ∙ refl) (~ k ∨ r) j
                      ; (i = i1) → lUnit-filler (cong (λ x → x ∙ refl) α) r k j
                      ; (j = i0) → refl ∙ refl
                      ; (j = i1) → (α (~ i ∨ ~ k ∨ r) ∙ refl)
                      ; (k = i0) → rUnit (cong (λ x → x ∙ refl) α) (~ i) j
                      ; (k = i1) → compPath-filler ((λ j → α (j ∧ ~ i) ∙ refl)) (λ j → α (~ i ∨ j) ∙ refl) r j})
            (rUnit (λ j → α (j ∧ (~ i ∨ ~ k)) ∙ refl) (~ i ∧ ~ k) j)

  s : I → I → I → typ ((Ω^ (suc n)) A)
  s i j k = (compPath-filler' (sym (rUnit (cong (λ x → x ∙ refl) α))) (lUnit (cong (λ x → x ∙ refl) α))
                             ▷ sym (endP≡)) k i j

module _ {ℓ : Level} {A : Pointed ℓ} (α β : typ ((Ω^ 3) A)) where
  btm : cong (λ x → refl ∙ x) α ∙ cong (λ x → x ∙ refl) β ≡
        cong (λ x → x ∙ refl) β ∙ cong (λ x → refl ∙ x) α
  btm = (λ i → (λ j → β (j ∧ i) ∙ α (j ∧ ~ i)) ∙ λ j → β (i ∨ j) ∙ α (~ i ∨ j))

  btm-transp1 : cong (λ x → refl ∙ x) α ∙ cong (λ x → x ∙ refl) β ≡
                cong (λ x → x ∙ refl) β ∙ cong (λ x → refl ∙ x) α
  btm-transp1 =
    transport (λ i → cong (λ x → EH-alt 0 x refl i) α ∙ cong (λ x → EH-alt 0 refl x i) β
                    ≡ cong (λ x → EH-alt 0 refl x i) β ∙ cong (λ x → EH-alt 0 x refl i) α)
              (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))

  btm≡ : btm ≡ btm-transp1
  btm≡ k =
    transp (λ i → cong (λ x → EH-alt 0 x refl (i ∨ ~ k)) α ∙ cong (λ x → EH-alt 0 refl x (i ∨ ~ k)) β
          ≡ cong (λ x → EH-alt 0 refl x (i ∨ ~ k)) β ∙ cong (λ x → EH-alt 0 x refl (i ∨ ~ k)) α)
      (~ k)
      λ i → (λ j → EH-alt 0 (α ( j ∧ ~ i)) (β (j ∧ i)) (~ k))
            ∙ λ j → EH-alt 0 (α ( j ∨ ~ i)) (β (j ∨ i)) (~ k)

  btm≡₂ : btm-transp1
        ≡ transport (λ i → cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α
                          ∙ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ≡ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ∙ cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α)
             (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
  btm≡₂ k = transport (λ i → cong (λ x → EH-alt-α-refl 0 x k i) α ∙ cong (λ x → EH-alt-refl-β 0 x k i) β
                    ≡ cong (λ x → EH-alt-refl-β 0 x k i) β ∙ cong (λ x → EH-alt-α-refl 0 x k i) α)
              (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
  F : _ → _
  F = λ x → (transport (λ i → cong (λ x → lUnit x (~ i)) α ∙ cong (λ x → rUnit x (~ i)) β
                        ≡ cong (λ x → rUnit x (~ i)) β ∙ cong (λ x → lUnit x (~ i)) α))
                  (transport (λ i → cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α
                          ∙ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ≡ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ∙ cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α)
                             x)
  G : _ → _
  G = λ x → (transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
                 ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)) x

  F≡G : (x : _ )→ F x ≡ G x
  F≡G p k =
    transp ((λ i → cong (λ x → lUnit x (~ i ∧ ~ k)) α ∙ cong (λ x → rUnit x (~ i ∧ ~ k)) β
                  ≡ cong (λ x → rUnit x (~ i ∧ ~ k)) β ∙ cong (λ x → lUnit x (~ i ∧ ~ k)) α))
         k
         ((transport (λ i → cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) (~ k) i) α
                          ∙ cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) (~ k) i) β
                    ≡ cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) (~ k) i) β
                    ∙ cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) (~ k) i) α)
                             p))

  btm≡₃ : btm ≡ transport (λ i → cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α
                          ∙ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ≡ cong (λ x → (sym (lUnit x) ∙ rUnit x) i) β
                    ∙ cong (λ x → (sym (rUnit x) ∙ lUnit x) i) α)
             (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
  btm≡₃ = btm≡ ∙ btm≡₂

  syllepsis : EH 1 α β ≡ sym (EH 1 β α)
  syllepsis =
       sym (F≡G (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)))
     ∙ cong (transport (λ i → cong (λ x → lUnit x (~ i)) α ∙ cong (λ x → rUnit x (~ i)) β
                        ≡ cong (λ x → rUnit x (~ i)) β ∙ cong (λ x → lUnit x (~ i)) α))
             (sym btm≡₃)

isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                    → isOfHLevel (suc n) (typ A)
                    → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
    ((λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
 ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
 ∙∙ (λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , fun e (pt A))
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

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π  n = elim2 (λ x y → isOfHLevelPath 2 isSetSetTrunc _ _)
                             λ p q → cong ∣_∣₂ (Eckmann-Hilton n p q)
