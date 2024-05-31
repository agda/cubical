{-# OPTIONS --safe #-}
module Cubical.HITs.Wedge.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Wedge.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.Loopspace


private
  variable
    ℓ ℓ' ℓ'' : Level

⋁-commFun : {A : Pointed ℓ} {B : Pointed ℓ'}
  → A ⋁ B → B ⋁ A
⋁-commFun (inl x) = inr x
⋁-commFun (inr x) = inl x
⋁-commFun (push a i) = push a (~ i)

⋁-commFun² : {A : Pointed ℓ} {B : Pointed ℓ'}
  → (x : A ⋁ B) → ⋁-commFun (⋁-commFun x) ≡ x
⋁-commFun² (inl x) = refl
⋁-commFun² (inr x) = refl
⋁-commFun² (push a i) = refl

⋁-commIso : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (A ⋁ B) (B ⋁ A)
Iso.fun ⋁-commIso = ⋁-commFun
Iso.inv ⋁-commIso = ⋁-commFun
Iso.rightInv ⋁-commIso = ⋁-commFun²
Iso.leftInv ⋁-commIso = ⋁-commFun²

cofibInl-⋁ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (cofib {B = A ⋁ B} inl) (fst B)
Iso.fun (cofibInl-⋁ {B = B}) (inl x) = pt B
Iso.fun (cofibInl-⋁ {B = B}) (inr (inl x)) = pt B
Iso.fun cofibInl-⋁ (inr (inr x)) = x
Iso.fun (cofibInl-⋁ {B = B}) (inr (push a i)) = pt B
Iso.fun (cofibInl-⋁ {B = B}) (push a i) = pt B
Iso.inv cofibInl-⋁ x = inr (inr x)
Iso.rightInv cofibInl-⋁ x = refl
Iso.leftInv (cofibInl-⋁ {A = A}) (inl x) =
  (λ i → inr (push tt (~ i))) ∙ sym (push (pt A))
Iso.leftInv (cofibInl-⋁ {A = A}) (inr (inl x)) =
  ((λ i → inr (push tt (~ i))) ∙ sym (push (pt A))) ∙ push x
Iso.leftInv cofibInl-⋁ (inr (inr x)) = refl
Iso.leftInv (cofibInl-⋁ {A = A}) (inr (push a i)) j =
  help (λ i → inr (push tt (~ i))) (sym (push (pt A))) (~ i) j
  where
  help : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → Square refl ((p ∙ q) ∙ sym q) refl p
  help p q =
    (λ i j → p (i ∧ j))
    ▷ (rUnit p
    ∙∙ cong (p ∙_) (sym (rCancel q))
    ∙∙ assoc p q (sym q))
Iso.leftInv (cofibInl-⋁ {A = A}) (push a i) j =
  compPath-filler
    ((λ i → inr (push tt (~ i))) ∙ sym (push (pt A)))
    (push a) i j

cofibInr-⋁ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (cofib {B = A ⋁ B} inr) (fst A)
cofibInr-⋁ {A = A} {B = B} =
  compIso (pushoutIso _ _ _ _
            (idEquiv _)
            (idEquiv Unit)
            (isoToEquiv ⋁-commIso)
            refl refl)
          (cofibInl-⋁ {A = B} {B = A})

-- Susp (⋁ᵢ Aᵢ) ≃ ⋁ᵢ (Susp Aᵢ)
private
  Bouquet→ΩBouquetSusp-filler : (A : Type ℓ) (B : A → Pointed ℓ')
    → (a : _) → (i j k : I) → ⋁gen A (λ a → Susp∙ (fst (B a)))
  Bouquet→ΩBouquetSusp-filler A B a i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → doubleCompPath-filler
                                  (push a)
                                  (λ i → inr (a
                                        , rCancel' (merid (snd (B a))) (~ k) i))
                                  (sym (push a)) k j
                   ; (j = i0) → push a (~ k ∧ i)
                   ; (j = i1) → push a (~ k ∧ i)})
          (inS (push a i))
          k

Bouquet→ΩBouquetSusp : (A : Type ℓ) (B : A → Pointed ℓ')
  → ⋁gen A B → Ω (⋁gen∙ A (λ a → Susp∙ (fst (B a)))) .fst
Bouquet→ΩBouquetSusp A B (inl x) = refl
Bouquet→ΩBouquetSusp A B (inr (a , b)) =
  (push a ∙∙ (λ i → inr (a , toSusp (B a) b i)) ∙∙ sym (push a))
Bouquet→ΩBouquetSusp A B (push a i) j = Bouquet→ΩBouquetSusp-filler A B a i j i1

SuspBouquet→Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Susp (⋁gen A B) → ⋁gen A (λ a → Susp∙ (fst (B a)))
SuspBouquet→Bouquet A B north = inl tt
SuspBouquet→Bouquet A B south = inl tt
SuspBouquet→Bouquet A B (merid a i) = Bouquet→ΩBouquetSusp A B a i

Bouquet→SuspBouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → ⋁gen A (λ a → Susp∙ (fst (B a))) → Susp (⋁gen A B)
Bouquet→SuspBouquet A B (inl x) = north
Bouquet→SuspBouquet A B (inr (a , north)) = north
Bouquet→SuspBouquet A B (inr (a , south)) = south
Bouquet→SuspBouquet A B (inr (a , merid b i)) = merid (inr (a , b)) i
Bouquet→SuspBouquet A B (push a i) = north

SuspBouquet-Bouquet-cancel : (A : Type ℓ) (B : A → Pointed ℓ')
    → section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
     × retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
SuspBouquet-Bouquet-cancel A B = sec , ret
  where
    sec : section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    sec (inl tt) i = inl tt
    sec (inr (a , north)) = push a
    sec (inr (a , south)) =
         (push a)
      ∙∙ (λ i → inr (a , merid (pt (B a)) i))
      ∙∙ (λ i → inr (a , south))
    sec (inr (a , merid b j)) i =
      hcomp (λ k → λ {(~ i ∧ j = i1) → push a (~ k)
                     ; (i = i1) → inr (a , merid b j)
                     ; (j = i0) → push a (i ∨ (~ k)) })
            (inr (a , (hcomp (λ k → λ {(i = i1) → merid b j
                            ; (j = i0) → north
                            ; (j = i1) → merid (pt (B a)) (i ∨ (~ k))})
                   (merid b j))))
    sec (push a j) i = push a (i ∧ j)

    module _ (a : A) (b : fst (B a)) (i j : I) where
      ret-fill₁ : I →  Susp (⋁gen A B)
      ret-fill₁ k =
        hfill (λ k → λ {(j = i0) → north
                       ; (j = i1) → merid (inr (a , pt (B a))) ((~ k) ∨ i)
                       ; (i = i0) → Bouquet→SuspBouquet A B
                                      (inr (a , compPath-filler (merid b)
                                                 (sym (merid (pt (B a)))) k j))
                       ; (i = i1) → merid (inr (a , b)) j})
              (inS (merid (inr (a , b)) j)) k

      ret-fill₂ : I → Susp (⋁gen A B)
      ret-fill₂ k =
        hfill (λ k → λ {(j = i0) → north
                     ; (j = i1) → merid (push a (~ k)) i
                     ; (i = i0) → Bouquet→SuspBouquet A B
                                    (doubleCompPath-filler (push a)
                                     (λ i → inr (a , toSusp (B a) b i))
                                     (sym (push a)) k j)
                     ; (i = i1) → merid (inr (a , b)) j})
               (inS (ret-fill₁ i1)) k

    ret : retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    ret north i = north
    ret south = merid (inl tt)
    ret (merid (inl tt) j) i = merid (inl tt) (i ∧ j)
    ret (merid (inr (a , b)) j) i = ret-fill₂ a b i j i1
    ret (merid (push a k) j) i =
      hcomp (λ r → λ {(i = i0) → Bouquet→SuspBouquet A B
                                   (Bouquet→ΩBouquetSusp-filler A B a k j r)
                     ; (i = i1) → merid (push a (~ r ∨ k)) j
                     ; (j = i0) → north
                     ; (j = i1) → merid (push a (~ r)) i
                     ; (k = i0) → merid (push a (~ r)) (i ∧ j)
                     ; (k = i1) → side r i j}
                     )
            (merid (inr (a , pt (B a))) (i ∧ j))
         where
         side : Cube {A = Susp (⋁gen A B)}
                   (λ i j → merid (inr (a , pt (B a))) (i ∧ j))
                   (λ i j → ret-fill₂ a (pt (B a)) i j i1)
                   (λ r j → Bouquet→SuspBouquet A B
                              (Bouquet→ΩBouquetSusp-filler A B a i1 j r))
                   (λ r j → merid (inr (a , (pt (B a)))) j)
                   (λ r i → north)
                   λ r i → merid (push a (~ r)) i
         side r i j =
           hcomp (λ k
             → λ {(r = i0) → Bouquet→SuspBouquet A B
                                (inr (a , rCancel-filler'
                                           (merid (pt (B a))) i k j))
                 ; (r = i1) →  ret-fill₂ a (pt (B a)) i j k
                 ; (i = i0) → Bouquet→SuspBouquet A B
                                (doubleCompPath-filler
                                  (push a)
                                  (λ j → inr (a
                                    , rCancel' (merid (pt (B a))) (~ r ∧ k) j))
                                  (sym (push a)) (r ∧ k) j)
                 ; (i = i1) → merid (inr (a , snd (B a))) j
                 ; (j = i0) → north
                 ; (j = i1) → merid (push a (~ r ∨ ~ k)) i})
             (hcomp (λ k
               → λ {(r = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , rCancel-filler'
                                             (merid (pt (B a))) (~ k ∨ i) i0 j))
                   ; (r = i1) → ret-fill₁ a (pt (B a)) i j k
                   ; (i = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , compPath-filler
                                             (merid (pt (B a)))
                                             (sym (merid (pt (B a)))) k j))
                   ; (i = i1) → merid (inr (a , snd (B a))) j
                   ; (j = i0) → north
                   ; (j = i1) →  merid (inr (a , snd (B a))) (~ k ∨ i)})
                   (merid (inr (a , snd (B a))) j))

Iso-SuspBouquet-Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Iso (Susp (⋁gen A B)) (⋁gen A (λ a → Susp∙ (fst (B a))))
Iso.fun (Iso-SuspBouquet-Bouquet A B) = SuspBouquet→Bouquet A B
Iso.inv (Iso-SuspBouquet-Bouquet A B) = Bouquet→SuspBouquet A B
Iso.rightInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .fst
Iso.leftInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .snd

SuspBouquet≃Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Susp (⋁gen A B) ≃ ⋁gen A (λ a → Susp∙ (fst (B a)))
SuspBouquet≃Bouquet A B = isoToEquiv (Iso-SuspBouquet-Bouquet A B)

module _ {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (f : A →∙ C) (g : B →∙ C)
  where
  private
    inst : 3x3-span
    3x3-span.A00 inst = Unit
    3x3-span.A02 inst = Unit
    3x3-span.A04 inst = Unit
    3x3-span.A20 inst = fst A
    3x3-span.A22 inst = Unit
    3x3-span.A24 inst = fst B
    3x3-span.A40 inst = fst C
    3x3-span.A42 inst = fst C
    3x3-span.A44 inst = fst C
    3x3-span.f10 inst = _
    3x3-span.f12 inst = _
    3x3-span.f14 inst = _
    3x3-span.f30 inst = fst f
    3x3-span.f32 inst = λ _ → pt C
    3x3-span.f34 inst = fst g
    3x3-span.f01 inst = _
    3x3-span.f21 inst = λ _ → pt A
    3x3-span.f41 inst = λ c → c
    3x3-span.f03 inst = _
    3x3-span.f23 inst = λ _ → pt B
    3x3-span.f43 inst = λ c → c
    3x3-span.H11 inst = λ _ → refl
    3x3-span.H13 inst = λ _ → refl
    3x3-span.H31 inst = λ _ → sym (snd f)
    3x3-span.H33 inst = λ _ → sym (snd g)

    open 3x3-span inst

    A□2≅C : A□2 ≃ (fst C)
    A□2≅C = isoToEquiv (PushoutAlongEquiv (idEquiv _) λ _ → pt C)

    A□○≅ : Iso (Pushout {B = cofib (fst f)} {C = cofib (fst g)} inr inr) A□○
    A□○≅ =
      pushoutIso _ _ _ _ (invEquiv A□2≅C) (idEquiv _) (idEquiv _)
             refl
             refl

    A0□≅ : A0□ ≃ Unit
    A0□≅ = isoToEquiv (PushoutAlongEquiv (idEquiv _) _)

    A4□≅ : A4□ ≃ fst C
    A4□≅ = isoToEquiv (PushoutAlongEquiv (idEquiv _) _)

    A○□≅ : Iso A○□ (cofib (f ∨→ g))
    A○□≅ = pushoutIso _ _ _ _ (idEquiv _) A0□≅ A4□≅ refl
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push tt i) j → help j i})
      where
      help : cong (fst A4□≅) (cong f3□ (push tt)) ≡ snd f ∙ sym (snd g)
      help = cong-∙∙ (fst A4□≅) (λ i → inl (snd f i))
                           refl (λ i → inl (snd g (~ i)))
           ∙ doubleCompPath≡compPath _ _ _
           ∙ cong (snd f ∙_) (sym (lUnit _))


    cofibf-Square : commSquare
    3-span.A0 (commSquare.sp cofibf-Square) = Unit
    3-span.A2 (commSquare.sp cofibf-Square) = fst A
    3-span.A4 (commSquare.sp cofibf-Square) = fst C
    3-span.f1 (commSquare.sp cofibf-Square) = _
    3-span.f3 (commSquare.sp cofibf-Square) = fst f
    commSquare.P cofibf-Square = cofib (fst f)
    commSquare.inlP cofibf-Square = λ _ → inl tt
    commSquare.inrP cofibf-Square = inr
    commSquare.comm cofibf-Square i x = push x i

    cofibf-PSquare : PushoutSquare
    fst cofibf-PSquare = cofibf-Square
    snd cofibf-PSquare =
      subst isEquiv (funExt (λ { (inl x) → refl
                               ; (inr x) → refl
                               ; (push a i) → refl}))
                     (idIsEquiv _)

    F : cofib (fst f)
      → cofib {B = cofib (fst g)} (λ x → inr (fst f x))
    F (inl x) = inl tt
    F (inr x) = inr (inr x)
    F (push a i) = push a i

    open PushoutPasteLeft
          cofibf-PSquare
            {B = cofib {B = cofib (fst g)} (λ x → inr (fst f x))}
            inr inr F refl

    isPushoutRight : isPushoutSquare rightSquare
    isPushoutRight = isPushoutTotSquare→isPushoutRightSquare
             (subst isEquiv
               (funExt (λ { (inl x) → refl
                          ; (inr x) → refl
                          ; (push a i) j → lUnit (sym (push a)) j (~ i)}))
               (idEquiv _ .snd))

  cofib∨→distrIso :
    Iso (cofib (f ∨→ g))
        (Pushout {B = cofib (fst f)} {C = cofib (fst g)} inr inr)
  cofib∨→distrIso = invIso (compIso (compIso A□○≅ 3x3-Iso) A○□≅)

  cofib∨→compIsoᵣ : Iso (cofib (f ∨→ g))
                        (cofib {B = cofib (fst g)} (λ x → inr (fst f x)))
  cofib∨→compIsoᵣ = compIso cofib∨→distrIso (equivToIso (_ , isPushoutRight))

cofib∨→compIsoₗ :
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (f : A →∙ C) (g : B →∙ C)
    → Iso (cofib (f ∨→ g))
           (cofib {B = cofib (fst f)} (λ x → inr (fst g x)))
cofib∨→compIsoₗ f g =
  compIso (pushoutIso _ _ _ _ (isoToEquiv ⋁-commIso)
            (idEquiv _) (idEquiv _)
            refl (funExt
            λ { (inl x) → refl
              ; (inr x) → refl
              ; (push a i) j → symDistr (snd g) (sym (snd f)) (~ j) i}))
          (cofib∨→compIsoᵣ g f)


module _ {A : Type ℓ} {B : Type ℓ'}
  {P : A → Pointed ℓ''} {Q : B → Pointed ℓ''}
  where
  private
    ⋁gen⊎→ : ⋁gen∙ A P ⋁ ⋁gen∙ B Q
            → ⋁gen (A ⊎ B) (⊎.rec P Q)
    ⋁gen⊎→ (inl (inl x)) = inl tt
    ⋁gen⊎→ (inl (inr (a , p))) = inr (inl a , p)
    ⋁gen⊎→ (inl (push a i)) = push (inl a) i
    ⋁gen⊎→ (inr (inl x)) = inl tt
    ⋁gen⊎→ (inr (inr (b , q))) = inr (inr b , q)
    ⋁gen⊎→ (inr (push b i)) = push (inr b) i
    ⋁gen⊎→ (push a i) = inl tt

    ⋁gen⊎← : ⋁gen (A ⊎ B) (⊎.rec P Q)
            → ⋁gen∙ A P ⋁ ⋁gen∙ B Q
    ⋁gen⊎← (inl x) = inl (inl tt)
    ⋁gen⊎← (inr (inl x , p)) = inl (inr (x , p))
    ⋁gen⊎← (inr (inr x , p)) = inr (inr (x , p))
    ⋁gen⊎← (push (inl x) i) = inl (push x i)
    ⋁gen⊎← (push (inr x) i) = (push tt ∙ λ i → inr (push x i)) i

  ⋁gen⊎Iso : Iso (⋁gen∙ A P ⋁ ⋁gen∙ B Q)
                   (⋁gen (A ⊎ B) (⊎.rec P Q))
  Iso.fun ⋁gen⊎Iso = ⋁gen⊎→
  Iso.inv ⋁gen⊎Iso = ⋁gen⊎←
  Iso.rightInv ⋁gen⊎Iso (inl tt) = refl
  Iso.rightInv ⋁gen⊎Iso (inr (inl x , p)) = refl
  Iso.rightInv ⋁gen⊎Iso (inr (inr x , p)) = refl
  Iso.rightInv ⋁gen⊎Iso (push (inl x) i) = refl
  Iso.rightInv ⋁gen⊎Iso (push (inr x) i) j =
    ⋁gen⊎→ (compPath-filler' (push tt) (λ i → inr (push x i)) (~ j) i)
  Iso.leftInv ⋁gen⊎Iso (inl (inl x)) = refl
  Iso.leftInv ⋁gen⊎Iso (inl (inr x)) = refl
  Iso.leftInv ⋁gen⊎Iso (inl (push a i)) = refl
  Iso.leftInv ⋁gen⊎Iso (inr (inl x)) = push tt
  Iso.leftInv ⋁gen⊎Iso (inr (inr x)) = refl
  Iso.leftInv ⋁gen⊎Iso (inr (push a i)) j =
    compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i
  Iso.leftInv ⋁gen⊎Iso (push a i) j = push a (i ∧ j)
