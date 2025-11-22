module Cubical.HITs.SphereBouquet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Wedge
open import Cubical.HITs.SphereBouquet.Base

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

private
  variable
    ℓ ℓ' : Level

SphereBouquet→Prop : (n : ℕ) {A : Type ℓ} (a : A)
  → {B : SphereBouquet n A → Type ℓ'}
  → ((b : _) → isProp (B b))
  → ((x : _) (y : _) → B (inr (x , y)))
  → (s : _) → B s
SphereBouquet→Prop n a {B = B} pr d =
  elimProp _ pr (λ t → subst B (sym (push a)) (d a _))
    λ {(x , y) → d x y}

isContrSphereBouquetZero : (n : ℕ) → isContr (SphereBouquet n (Fin zero))
fst (isContrSphereBouquetZero n) = inl tt
snd (isContrSphereBouquetZero n) (inl x) = refl
snd (isContrSphereBouquetZero n) (inr x) = ⊥.rec (¬Fin0 (fst x))
snd (isContrSphereBouquetZero n) (push a i) j =
  ⊥.rec {A = Square {A = SphereBouquet n (Fin zero)}
        (λ _ → inl tt) (push a) (λ _ → inl tt)
        (⊥.rec (¬Fin0 a))} (¬Fin0 a) j i

isConnectedSphereBouquet : {n : ℕ} {A : Type ℓ}
  (x : SphereBouquet (suc n) A) → ∥ x ≡ inl tt ∥₁
isConnectedSphereBouquet {n = n} {A} =
  elimProp (λ x → ∥ x ≡ inl tt ∥₁) (λ x → squash₁) (λ x → ∣ refl ∣₁)
  (λ (a , s) → sphereToPropElim n {A = λ x → ∥ inr (a , x) ≡ inl tt ∥₁}
                                  (λ x → squash₁) ∣ sym (push a) ∣₁ s)

isConnectedSphereBouquet' : {n : ℕ} {A : Type ℓ}
  → isConnected (suc (suc n)) (SphereBouquet (suc n) A)
fst (isConnectedSphereBouquet' {n = n}) = ∣ inl tt ∣
snd (isConnectedSphereBouquet' {n = n} {A = A}) =
  TR.elim (λ _ → isOfHLevelPath (suc (suc n))
                   (isOfHLevelTrunc (suc (suc n))) _ _) (lem n)
  where
  lem : (n : ℕ) → (a : SphereBouquet (suc n) A)
    → Path (hLevelTrunc (suc (suc n)) (SphereBouquet (suc n) A))
            ∣ inl tt ∣ ∣ a ∣
  lem n (inl x) = refl
  lem n (inr (x , y)) =
    sphereElim n {A = λ y → ∣ inl tt ∣ ≡ ∣ inr (x , y) ∣}
      (λ _ → isOfHLevelTrunc (suc (suc n)) _ _)
      (cong ∣_∣ₕ (push x)) y
  lem zero (push a i) j = ∣ push a (i ∧ j) ∣ₕ
  lem (suc n) (push a i) j = ∣ push a (i ∧ j) ∣ₕ

sphereBouquetSuspIso₀ : {A : Type ℓ}
  → Iso (⋁gen A (λ a → Susp∙ (fst (S₊∙ zero))))
      (SphereBouquet 1 A)
Iso.fun sphereBouquetSuspIso₀ (inl x) = inl x
Iso.fun sphereBouquetSuspIso₀ (inr (a , b)) =
  inr (a , Iso.inv (IsoSucSphereSusp 0) b)
Iso.fun sphereBouquetSuspIso₀ (push a i) = push a i
Iso.inv sphereBouquetSuspIso₀ (inl x) = inl x
Iso.inv sphereBouquetSuspIso₀ (inr (a , b)) =
  inr (a , Iso.fun (IsoSucSphereSusp 0) b)
Iso.inv sphereBouquetSuspIso₀ (push a i) = push a i
Iso.rightInv sphereBouquetSuspIso₀ (inl x) = refl
Iso.rightInv sphereBouquetSuspIso₀ (inr (a , y)) i =
  inr (a , Iso.leftInv (IsoSucSphereSusp 0) y i)
Iso.rightInv sphereBouquetSuspIso₀ (push a i) = refl
Iso.leftInv sphereBouquetSuspIso₀ (inl x) = refl
Iso.leftInv sphereBouquetSuspIso₀ (inr (a , y)) i =
  inr (a , Iso.rightInv (IsoSucSphereSusp 0) y i)
Iso.leftInv sphereBouquetSuspIso₀ (push a i) = refl

SphereBouquet₀Iso : (n : ℕ)
  → Iso (SphereBouquet zero (Fin n))
         (Fin (suc n))
Iso.fun (SphereBouquet₀Iso n) (inl x) = fzero
Iso.fun (SphereBouquet₀Iso n) (inr ((x , p) , false)) = suc x , p
Iso.fun (SphereBouquet₀Iso n) (inr ((x , p) , true)) = fzero
Iso.fun (SphereBouquet₀Iso n) (push a i) = fzero
Iso.inv (SphereBouquet₀Iso n) (zero , p) = inl tt
Iso.inv (SphereBouquet₀Iso n) (suc x , p) = inr ((x , p) , false)
Iso.rightInv (SphereBouquet₀Iso n) (zero , p) = refl
Iso.rightInv (SphereBouquet₀Iso n) (suc x , p) = refl
Iso.leftInv (SphereBouquet₀Iso n) (inl x) = refl
Iso.leftInv (SphereBouquet₀Iso n) (inr (x , false)) = refl
Iso.leftInv (SphereBouquet₀Iso n) (inr (x , true)) = push x
Iso.leftInv (SphereBouquet₀Iso n) (push a i) j = push a (i ∧ j)

--a sphere bouquet is the wedge sum of A n-dimensional spheres
sphereBouquetSuspIso : {A : Type ℓ} {n : ℕ}
  → Iso (Susp (SphereBouquet n A)) (SphereBouquet (suc n) A)
sphereBouquetSuspIso {A = A} {n = zero} =
  compIso (Iso-SuspBouquet-Bouquet A λ _ → S₊∙ zero) sphereBouquetSuspIso₀
sphereBouquetSuspIso {A = A} {n = suc n} =
  Iso-SuspBouquet-Bouquet A λ _ → S₊∙ (suc n)

sphereBouquet≃Susp : {A : Type ℓ} {n : ℕ}
  → Susp (SphereBouquet n A) ≃ SphereBouquet (suc n) A
sphereBouquet≃Susp = isoToEquiv (sphereBouquetSuspIso)

sphereBouquetSuspFun : {A : Type ℓ} {n : ℕ}
  → Susp (SphereBouquet n A) → SphereBouquet (suc n) A
sphereBouquetSuspFun {A = A} {n = n} = sphereBouquetSuspIso .Iso.fun

sphereBouquetSuspInvFun : {A : Type ℓ} {n : ℕ}
  → SphereBouquet (suc n) A → Susp (SphereBouquet n A)
sphereBouquetSuspInvFun {A = A} {n = n} = sphereBouquetSuspIso .Iso.inv

--the suspension of a n-dimensional bouquet is a (n+1)-dimensional bouquet
--here is the action of suspension on morphisms
bouquetSusp→ : {n : ℕ} {A B : Type ℓ}
  → (SphereBouquet n A → SphereBouquet n B)
  → (SphereBouquet (suc n) A → SphereBouquet (suc n) B)
bouquetSusp→ {n = n} {A} {B} f =
     sphereBouquetSuspFun ∘ (suspFun f) ∘ sphereBouquetSuspInvFun

bouquetSusp→∘ : {n : ℕ} {A B C : Type ℓ}
  → (f : SphereBouquet n A → SphereBouquet n B)
  → (g : SphereBouquet n B → SphereBouquet n C)
  → bouquetSusp→ g ∘ bouquetSusp→ f ≡ bouquetSusp→ (g ∘ f)
bouquetSusp→∘ f g i =
  sphereBouquetSuspFun
    ∘ ((λ i → suspFun g ∘ (λ x → Iso.leftInv sphereBouquetSuspIso x i) ∘ suspFun f)
     ∙ sym (suspFunComp g f)) i
    ∘ sphereBouquetSuspInvFun

------ Sphere bouquets as cofibres ------
{-
Goal: show that given a pushout square

Fin m × Sⁿ⁻¹ → Fin m
    ∣            ∣
 αₙ ∣            ∣
    ↓        ⌜  ↓
    Cₙ -----→ Cₙ₊₁
         ι

we get an equivalence cofib ι ≃ ⋁ᵢ Sⁿ where
i ranges over Fin m
-}

-- Prelims for description of maps
preBTC : {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → (x : Fin mₙ)
    → S₊∙ n →∙ (cofib (invEq e ∘ inl) , inl tt)
fst (preBTC zero mₙ αₙ e x) false = inr (invEq e (inr x))
fst (preBTC zero mₙ αₙ e x) true = inl tt
fst (preBTC (suc zero) mₙ αₙ e x) base = inl tt
fst (preBTC (suc zero) mₙ αₙ e x) (loop i) =
    (push (αₙ (x , false))
  ∙∙ (λ j → inr (invEq e ((push (x , false) ∙ sym (push (x , true))) j)))
  ∙∙ sym (push (αₙ (x , true)))) i
fst (preBTC (suc (suc n)) mₙ αₙ e x) north = inl tt
fst (preBTC (suc (suc n)) mₙ αₙ e x) south = inl tt
fst (preBTC (suc (suc n)) mₙ αₙ e x) (merid a i) =
  (push (αₙ (x , a))
  ∙∙ (λ j → inr (invEq e ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) j)))
  ∙∙ sym (push (αₙ (x , ptSn (suc n))))) i
snd (preBTC zero mₙ αₙ e x) = refl
snd (preBTC (suc zero) mₙ αₙ e x) = refl
snd (preBTC (suc (suc n)) mₙ αₙ e x) = refl

module _  where
  Pushout→Bouquet : {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → Pushout αₙ fst → SphereBouquet n (Fin mₙ)
  Pushout→Bouquet n mₙ αₙ e (inl x) = inl tt
  Pushout→Bouquet zero mₙ αₙ e (inr x) = inr (x , false)
  Pushout→Bouquet (suc n) mₙ αₙ e (inr x) = inr (x , ptSn (suc n))
  Pushout→Bouquet (suc n) mₙ αₙ e (push a i) =
    (push (a .fst) ∙ λ i → inr (a .fst , σSn n (a .snd) i)) i

-- Maps back and forth
module BouquetFuns {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : cofib (invEq e ∘ inl) → SphereBouquet n (Fin mₙ)
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→Bouquet n mₙ αₙ e (fst e x)
  CTB (push a i) = Pushout→Bouquet n mₙ αₙ e (secEq e (inl a) (~ i))

  BTC : SphereBouquet n (Fin mₙ) → cofib (invEq e ∘ inl)
  BTC (inl x) = inl tt
  BTC (inr x) = preBTC n mₙ αₙ e (fst x) .fst (snd x)
  BTC (push a i) = preBTC n mₙ αₙ e a .snd (~ i)

-- Maps cancel out
CTB-BTC-cancel : {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → section (BouquetFuns.CTB n mₙ αₙ e) (BouquetFuns.BTC n mₙ αₙ e)
     × retract (BouquetFuns.CTB n mₙ αₙ e) (BouquetFuns.BTC n mₙ αₙ e)
CTB-BTC-cancel {Cₙ = Cₙ} n mₙ αₙ =
    EquivJ (λ C₊ e →
      section (BouquetFuns.CTB n mₙ αₙ e)
      (BouquetFuns.BTC n mₙ αₙ e)
      ×
      retract (BouquetFuns.CTB n mₙ αₙ e)
      (BouquetFuns.BTC n mₙ αₙ e))
     (retr-main n αₙ , section-main n αₙ)
  where
  module S (n : ℕ) (αₙ : Fin mₙ × S⁻ n → Cₙ) where
    module T = BouquetFuns n mₙ αₙ (idEquiv _)
    open T public

  retr-inr : (n : ℕ) (αₙ : Fin mₙ × S⁻ n → Cₙ) (a : _) (b : _)
    → S.CTB n αₙ (S.BTC n αₙ (inr (a , b))) ≡ inr (a , b)
  retr-inr zero aₙ a false = refl
  retr-inr zero aₙ a true = push a
  retr-inr (suc zero) αₙ a base = push a
  retr-inr (suc zero) αₙ  a (loop i) j =
    hcomp (λ r →
      λ {(i = i0) → push a j
       ; (i = i1) → push a j
       ; (j = i0) → S.CTB (suc zero) αₙ
                      (doubleCompPath-filler
                        (push (αₙ (a , false)))
                        (λ j → inr ((push (a , false)
                                   ∙ sym (push (a , true))) j))
                        (sym (push (αₙ (a , true)))) r i)
       ; (j = i1) → inr (a , loop i)})
     (hcomp (λ r →
       λ {(i = i0) → push a j
        ; (i = i1) → compPath-filler' (push a) refl (~ j) (~ r)
        ; (j = i0) → S.CTB (suc zero) αₙ
                       (inr (compPath-filler
                               (push (a , false))
                               (sym (push (a , true))) r i))
        ; (j = i1) → inr (a , loop i)})
       (hcomp (λ r →
         λ {(i = i0) → push a (j ∨ ~ r)
          ; (i = i1) → inr (a , base)
          ; (j = i0) → compPath-filler' (push a) (λ j → inr (a , loop j)) r i
          ; (j = i1) → inr (a , loop i)})
        (inr (a , loop i))))
  retr-inr (suc (suc n)) αₙ a north = push a
  retr-inr (suc (suc n)) αₙ a south =
    push a ∙ λ j → inr (a , merid (ptSn (suc n)) j)
  retr-inr (suc (suc n)) αₙ a (merid a₁ i) j =
    hcomp (λ r →
      λ {(i = i0) → push a j
       ; (i = i1) → compPath-filler
                      (push a)
                      (λ j₁ → inr (a , merid (ptSn (suc n)) j₁)) r j
       ; (j = i0) → S.CTB (suc (suc n)) αₙ
                       (doubleCompPath-filler
                        (push (αₙ (a , a₁)))
                        (λ i → inr ((push (a , a₁)
                                   ∙ sym (push (a , ptSn (suc n)))) i))
                        (sym (push (αₙ (a , ptSn (suc n))))) r i)
       ; (j = i1) → inr (a , compPath-filler (merid a₁)
                               (sym (merid (ptSn (suc n)))) (~ r) i)})
    (hcomp (λ r →
      λ {(i = i0) → push a j
       ; (i = i1) → compPath-filler' (push a)
                      (λ i → inr (a , σSn _ (ptSn (suc n)) i)) (~ j) (~ r)
       ; (j = i0) → S.CTB (suc (suc n)) αₙ
                       (inr (compPath-filler (push (a , a₁))
                             (sym (push (a , ptSn (suc n)))) r i) )
       ; (j = i1) → inr (a , help r i)})
        (hcomp (λ r → λ {(i = i0) → push a (j ∨ ~ r)
                      ; (i = i1) → inr (a , north)
                      ; (j = i0) → compPath-filler'
                                     (push a) (λ i → inr (a , σSn _ a₁ i)) r i
                      ; (j = i1) → inr (a , σSn _ a₁ i)})
               (inr (a , σSn _ a₁ i))))
    where
    help : Square (σSn _ a₁) (σSn _ a₁) refl (sym (σSn _ (ptSn (suc n))))
    help = flipSquare ((λ i _ → σSn _ a₁ i)
         ▷ λ i → sym (rCancel (merid (ptSn (suc n))) (~ i)))

  retr-main : (n : _) (αₙ : _) → section (S.CTB n αₙ) (S.BTC n αₙ)
  retr-main n αₙ (inl x) = refl
  retr-main n αₙ (inr (a , b)) = retr-inr n αₙ a b
  retr-main zero αₙ (push a i) j = push a (i ∧ j)
  retr-main (suc zero) αₙ (push a i) j = push a (i ∧ j)
  retr-main (suc (suc n)) αₙ (push a i) j = push a (i ∧ j)

  section-main : (n : _) (αₙ : _) → retract (S.CTB n αₙ) (S.BTC n αₙ)
  section-main n αₙ (inl x) = refl
  section-main n αₙ (inr (inl x)) = push x
  section-main zero αₙ (inr (inr x)) = refl
  section-main (suc zero) αₙ (inr (inr x)) =
    push (αₙ (x , true)) ∙ λ i → inr (push (x , true) i)
  section-main (suc (suc n)) αₙ (inr (inr x)) =
    push (αₙ (x , ptSn (suc n))) ∙ λ i → inr (push (x , ptSn (suc n)) i)
  section-main (suc zero) αₙ (inr (push (a , false) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , false)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) i1 j
                   ; (j = i0) →
                      S.BTC (suc zero) αₙ
                         (compPath-filler'
                           (push a)
                           (λ i → inr (a , σSn zero false i)) r i)
                   ; (j = i1) → inr (push (a , false) i)})
       (hcomp (λ r → λ {(i = i0) → push (αₙ (a , false)) (j ∨ ~ r)
                   ; (i = i1) →
                          compPath-filler'
                            (push (αₙ (a , true)))
                            (λ i → inr (push (a , true) i)) r j
                   ; (j = i1) → inr (push (a , false) i)})
              (inr (compPath-filler
                     (push (a , false))
                     (sym (push (a , true))) (~ j) i)))
  section-main (suc zero) αₙ (inr (push (a , true) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , true)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) r j
                   ; (j = i0) → S.BTC (suc zero) αₙ
                                  (compPath-filler'
                                   (push a)
                                   (λ i → inr (a , σSn zero true i)) r i)
                   ; (j = i1) → inr (push (a , true) (i ∧ r))})
            (push (αₙ (a , true)) j)
  section-main (suc (suc n)) αₙ (inr (push a i)) j =
    hcomp (λ r →
    λ {(i = i0) → push (αₙ a) j
     ; (i = i1) → (push (αₙ (fst a , ptSn (suc n)))
                ∙ (λ i₁ → inr (push (fst a , ptSn (suc n)) i₁))) j
     ; (j = i0) → S.BTC (suc (suc n)) αₙ
                    (compPath-filler' (push (fst a))
                      (λ i → inr (fst a , σSn (suc n) (snd a) i)) r i)
     ; (j = i1) → inr (push a i)})
    (hcomp (λ r →
      λ {(i = i0) → doubleCompPath-filler (push (αₙ a))
                    (λ j → inr ((push a ∙ sym (push (fst a , ptSn (suc n)))) j))
                    (sym (push (αₙ (fst a , ptSn (suc n))))) (~ j) (~ r)
       ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                        (λ i → inr (push (fst a , ptSn (suc n)) i)) r j
       ; (j = i0) → S.BTC (suc (suc n)) αₙ (inr (fst a
                   , compPath-filler' (merid (snd a))
                                      (sym (merid (ptSn (suc n)))) r i))
       ; (j = i1) → inr (compPath-filler'
                          (push a)
                          (sym (push (fst a , ptSn (suc n)))) (~ i) (~ r))})
    (hcomp (λ r
    → λ {(i = i0) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
        ; (i = i1) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
        ; (j = i1) → inr (inl (αₙ (fst a , ptSn (suc n))))})
       (inr (ugh (push (fst a , ptSn (suc n))) j i))))
    where
    ugh : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙' sym p ≡ refl
    ugh p = sym (compPath≡compPath' p (sym p)) ∙ rCancel p
  section-main n αₙ (push a i) j = push a (i ∧ j)


-- main theorem
module _ {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where

  open BouquetFuns n mₙ αₙ e

  BouquetIso-gen : Iso (cofib (invEq e ∘ inl)) (SphereBouquet n (Fin mₙ))
  Iso.fun BouquetIso-gen = CTB
  Iso.inv BouquetIso-gen = BTC
  Iso.rightInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .fst
  Iso.leftInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .snd

  Bouquet≃-gen : cofib (invEq e ∘ inl) ≃ SphereBouquet n (Fin mₙ)
  Bouquet≃-gen = isoToEquiv BouquetIso-gen

-- A 'normal form' for functions of type ⋁Sⁿ → ⋁Sⁿ
normalFormCofibFun : ∀ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k) ]
      (((inr , (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∘∙ f') ≡ f)
normalFormCofibFun {n = n} {m} {k} α f =
  PT.rec squash₁
    (λ g → TR.rec (isProp→isOfHLevelSuc n squash₁)
      (λ gid → ∣ ((λ x → g x .fst) , (cong fst gid))
               , ΣPathP ((λ i x → g x .snd i)
               , (lem _ _ _ _ _ _ _ _ _ _ (cong snd gid))) ∣₁)
      (isConnectedPath (suc n)
        (help (fst f (ptSn (suc n)))) (g (ptSn (suc n)))
          ((inl tt) , (((λ i → inr (α .snd (~ i)))
          ∙ sym (push (inl tt))) ∙ sym (snd f))) .fst))
    makefun
  where
  lem : ∀ {ℓ} {A : Type ℓ} (x y : A) (inrgid : x ≡ y)
    (z : _) (inrα : y ≡ z) (w : _) (pushtt : z ≡ w)
    (t : _) (snf : w ≡ t) (s : x ≡ t)
    → Square s ((inrα ∙ pushtt) ∙ snf) inrgid refl
    → Square (inrgid ∙ inrα ∙ pushtt) (sym snf) s refl
  lem x = J> (J> (J> (J> λ s sq → (sym (lUnit _) ∙ sym (rUnit _))
    ◁ λ i j → (sq ∙ sym (rUnit _) ∙ sym (rUnit _)) j i)))
  cool : (x : S₊ (suc n)) → Type
  cool x =
    Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ]
      Σ[ y ∈ ((ptSn (suc n) ≡ x) → inl tt ≡ x') ]
        Σ[ feq ∈ inr x' ≡ fst f x ]
          ((p : ptSn (suc n) ≡ x)
            → Square ((λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))) (snd f)
                      ((λ i → inr (y p i)) ∙∙ feq ∙∙ cong (fst f) (sym p)) refl)

  inr' : SphereBouquet (suc n) (Fin k) → cofib (fst α)
  inr' = inr

  help : isConnectedFun (suc (suc n)) inr'
  help = inrConnected _ _ _
          (isConnected→isConnectedFun _ isConnectedSphereBouquet')

  makefun : ∥ ((x : _)
           → Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ] inr x' ≡ fst f x) ∥₁
  makefun = sphereToTrunc _ λ x → help (fst f x) .fst

-- H-space structure
SphereBouquet∙Π : ∀ {ℓ ℓ'} {n : ℕ} {A : Type ℓ} {B : Pointed ℓ'}
  → (f g : SphereBouquet∙ (suc n) A →∙ B)
  → (SphereBouquet∙ (suc n) A →∙ B)
fst (SphereBouquet∙Π {B = B} f g) (inl x) = pt B
fst (SphereBouquet∙Π {B = B} f g) (inr (a , s)) =
  ∙Π ((λ x → fst f (inr (a , x))) , cong (fst f) (sym (push a)) ∙ snd f)
     ((λ x → fst g (inr (a , x))) , cong (fst g) (sym (push a)) ∙ snd g) .fst s
fst (SphereBouquet∙Π {B = B} f g) (push a i) =
  ∙Π ((λ x → fst f (inr (a , x))) , cong (fst f) (sym (push a)) ∙ snd f)
     ((λ x → fst g (inr (a , x))) , cong (fst g) (sym (push a)) ∙ snd g) .snd (~ i)
snd (SphereBouquet∙Π f g) = refl
