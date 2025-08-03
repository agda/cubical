module Cubical.HITs.Wedge.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.HITs.Wedge.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' ℓ'' : Level

-- commutativity
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

-- Pushout square using Unit* for convenience
⋁-PushoutSquare : ∀ (A : Pointed ℓ) (B : Pointed ℓ') ℓ'' → PushoutSquare
⋁-PushoutSquare A B ℓ'' .fst = cSq
  where
  open commSquare
  open 3-span
  cSq : commSquare
  cSq .sp .A0 = typ A
  cSq .sp .A2 = Unit* {ℓ''}
  cSq .sp .A4 = typ B
  cSq .sp .f1 _ = pt A
  cSq .sp .f3 _ = pt B
  cSq .P = A ⋁ B
  cSq .inlP = inl
  cSq .inrP = inr
  cSq .comm = funExt λ _ → push _
⋁-PushoutSquare A B ℓ'' .snd =
  isoToIsEquiv (iso _ inv lInv rInv)
  where
    inv : _
    inv (inl a) = inl a
    inv (inr b) = inr b
    inv (push _ i) = push _ i

    rInv : _
    rInv (inl a) = refl
    rInv (inr b) = refl
    rInv (push _ i) = refl

    lInv : _
    lInv (inl a) = refl
    lInv (inr b) = refl
    lInv (push _ i) = refl

-- cofibre of A --inl→ A ⋁ B is B
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

-- cofibre of B --inl→ A ⋁ B is A
cofibInr-⋁ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (cofib {B = A ⋁ B} inr) (fst A)
cofibInr-⋁ {A = A} {B = B} =
  compIso (pushoutIso _ _ _ _
            (idEquiv _)
            (idEquiv Unit)
            (isoToEquiv ⋁-commIso)
            refl refl)
          (cofibInl-⋁ {A = B} {B = A})

-- A ⋁ Unit ≃ A ≃ Unit ⋁ A
⋁-rUnitIso : {A : Pointed ℓ} → Iso (A ⋁ Unit*∙ {ℓ'}) (fst A)
Iso.fun ⋁-rUnitIso (inl x) = x
Iso.fun (⋁-rUnitIso {A = A}) (inr x) = pt A
Iso.fun (⋁-rUnitIso {A = A}) (push a i) = pt A
Iso.inv ⋁-rUnitIso = inl
Iso.rightInv ⋁-rUnitIso x = refl
Iso.leftInv ⋁-rUnitIso (inl x) = refl
Iso.leftInv ⋁-rUnitIso (inr x) = push tt
Iso.leftInv ⋁-rUnitIso (push tt i) j = push tt (i ∧ j)

⋁-lUnitIso : {A : Pointed ℓ} → Iso (Unit*∙ {ℓ'} ⋁ A) (fst A)
⋁-lUnitIso = compIso ⋁-commIso ⋁-rUnitIso

-- cofiber of constant function
module _ {A : Pointed ℓ} {B : Pointed ℓ'} where
  cofibConst→⋁ : cofib (const∙ A B .fst) → Susp∙ (fst A) ⋁ B
  cofibConst→⋁ (inl x) = inl north
  cofibConst→⋁ (inr x) = inr x
  cofibConst→⋁ (push a i) = ((λ i → inl (toSusp A a i)) ∙ push tt) i

  ⋁→cofibConst : Susp∙ (fst A) ⋁ B → cofib (const∙ A B .fst)
  ⋁→cofibConst (inl north) = inl tt
  ⋁→cofibConst (inl south) = inr (pt B)
  ⋁→cofibConst (inl (merid a i)) = push a i
  ⋁→cofibConst (inr x) = inr x
  ⋁→cofibConst (push a i) = push (pt A) i

  cofibConst-⋁-Iso : Iso (cofib (const∙ A B .fst))
                     (Susp∙ (fst A) ⋁ B)
  Iso.fun cofibConst-⋁-Iso = cofibConst→⋁
  Iso.inv cofibConst-⋁-Iso = ⋁→cofibConst
  Iso.rightInv cofibConst-⋁-Iso (inl north) = refl
  Iso.rightInv cofibConst-⋁-Iso (inl south) =
    sym (push tt) ∙ λ i → inl (merid (pt A) i)
  Iso.rightInv cofibConst-⋁-Iso (inl (merid a i)) j =
    hcomp (λ k →
      λ {(i = i0) → inl (compPath-filler (merid a) (sym (merid (pt A))) (~ j) (~ k))
       ; (i = i1) → (sym (push tt) ∙ λ i → inl (merid (pt A) i)) j
       ; (j = i0) → compPath-filler' (λ i → inl (toSusp A a i)) (push tt) k i
       ; (j = i1) → inl (merid a (~ k ∨ i))})
    (compPath-filler' (sym (push tt)) (λ i → inl (merid (pt A) i)) i j)
  Iso.rightInv cofibConst-⋁-Iso (inr x) = refl
  Iso.rightInv cofibConst-⋁-Iso (push tt i) j =
      (cong (_∙ push tt) (λ i j  → inl (rCancel (merid (pt A)) i j))
    ∙ sym (lUnit _)) j i
  Iso.leftInv cofibConst-⋁-Iso (inl x) = refl
  Iso.leftInv cofibConst-⋁-Iso (inr x) = refl
  Iso.leftInv cofibConst-⋁-Iso (push a i) j = help j i
    where
    help : cong ⋁→cofibConst (((λ i → inl (toSusp A a i)) ∙ push tt)) ≡ push a
    help = cong-∙ ⋁→cofibConst (λ i → inl (toSusp A a i)) (push tt)
         ∙ cong₂ _∙_ (cong-∙ (⋁→cofibConst ∘ inl) (merid a) (sym (merid (pt A)))) refl
         ∙ sym (assoc _ _ _)
         ∙ cong (push a ∙_) (lCancel (push (pt A)))
         ∙ sym (rUnit _)

  cofibConst-⋁-Iso' : (f : A →∙ B) → ((x : fst A) → fst f x ≡ pt B)
              → Iso (cofib (fst f)) ((Susp∙ (fst A) ⋁ B))
  cofibConst-⋁-Iso' f d =
    compIso (pushoutIso _ _ _ _
              (idEquiv _) (idEquiv _) (idEquiv _) refl (funExt d))
            cofibConst-⋁-Iso

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

-- cofibre of f ∨→ g : A ⋁ B → C is cofibre of
-- inr ∘ f : A → cofib g
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

-- cofibre of f ∨→ g : A ⋁ B → C is cofibre of
-- inr ∘ g : B → cofib f
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

-- (⋁ᵢ Aᵢ ∨ ⋁ⱼ Bᵢ) ≃ ⋁ᵢ₊ⱼ(Aᵢ + Bⱼ)
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

-- Chacaterisation of cofibres of first projections
-- cofib (Σ[ x ∈ A ] (B x) --fst→ A) ≃ ⋁[ x ∈ X ] (Susp (B x))
module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Pointed ℓ')
  where
  cofibFst : Type _
  cofibFst = cofib {A = Σ A (fst ∘ B)} {B = A} fst

  cofibFst→⋁ : cofibFst → ⋁gen A λ a → Susp∙ (fst (B a))
  cofibFst→⋁ (inl x) = inl x
  cofibFst→⋁ (inr a) = inr (a , north)
  cofibFst→⋁ (push (a , b) i) = (push a ∙ λ i → inr (a , toSusp (B a) b i)) i

  ⋁→cofibFst : ⋁gen A (λ a → Susp∙ (fst (B a))) → cofibFst
  ⋁→cofibFst (inl x) = inl x
  ⋁→cofibFst (inr (x , north)) = inl tt
  ⋁→cofibFst (inr (x , south)) = inr x
  ⋁→cofibFst (inr (x , merid a i)) = push (x , a) i
  ⋁→cofibFst (push a i) = inl tt

  Iso-cofibFst-⋁ : Iso cofibFst (⋁gen A (λ a → Susp∙ (fst (B a))))
  Iso.fun Iso-cofibFst-⋁ = cofibFst→⋁
  Iso.inv Iso-cofibFst-⋁ = ⋁→cofibFst
  Iso.rightInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , north)) = push x
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , south)) i = inr (x , merid (pt (B x)) i)
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , merid a i)) j =
    hcomp (λ k → λ {(i = i0) → push x (j ∨ ~ k)
                   ; (i = i1) → inr (x , merid (pt (B x)) j)
                   ; (j = i0) → compPath-filler' (push x)
                                   (λ i₁ → inr (x , toSusp (B x) a i₁)) k i
                   ; (j = i1) → inr (x , merid a i)})
          (inr (x , compPath-filler (merid a) (sym (merid (pt (B x)))) (~ j) i))
  Iso.rightInv Iso-cofibFst-⋁ (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.leftInv Iso-cofibFst-⋁ (inr x) = push (x , snd (B x))
  Iso.leftInv Iso-cofibFst-⋁ (push (a , b) i) j = help j i
    where
    help : Square (cong ⋁→cofibFst ((push a ∙ λ i → inr (a , toSusp (B a) b i))))
                  (push (a , b)) refl (push (a , (snd (B a))))
    help = (cong-∙ ⋁→cofibFst (push a) (λ i → inr (a , toSusp (B a) b i))
         ∙ sym (lUnit _)
         ∙ cong-∙ (⋁→cofibFst ∘ inr ∘ (a ,_)) (merid b) (sym (merid (snd (B a)))))
         ◁ λ i j → compPath-filler (push (a , b)) (sym (push (a , pt (B a)))) (~ i) j

-- f : ⋁ₐ Bₐ → C has cofibre the pushout of cofib (f ∘ inr) ← Σₐ → A
module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A → Pointed ℓB} (C : Pointed ℓC)
         (f : (⋁gen A B , inl tt) →∙ C) where
  private
    open 3x3-span
    inst : 3x3-span
    A00 inst = A
    A02 inst = Σ A (fst ∘ B)
    A04 inst = Σ A (fst ∘ B)
    A20 inst = A
    A22 inst = A
    A24 inst = Σ A (fst ∘ B)
    A40 inst = Unit
    A42 inst = Unit
    A44 inst = fst C
    f10 inst = idfun A
    f12 inst = λ x → x , snd (B x)
    f14 inst = idfun _
    f30 inst = λ _ → tt
    f32 inst = λ _ → tt
    f34 inst = fst f ∘ inr
    f01 inst = fst
    f21 inst = idfun A
    f41 inst = λ _ → tt
    f03 inst = idfun _
    f23 inst = λ x → x , snd (B x)
    f43 inst = λ _ → pt C
    H11 inst = λ _ → refl
    H13 inst = λ _ → refl
    H31 inst = λ _ → refl
    H33 inst = λ x → sym (snd f) ∙ cong (fst f) (push x)

    A0□Iso : Iso (A0□ inst) A
    A0□Iso = compIso (equivToIso (symPushout _ _))
                     (PushoutAlongEquiv (idEquiv _) fst)

    A2□Iso : Iso (A2□ inst) (Σ A (fst ∘ B))
    A2□Iso = PushoutAlongEquiv (idEquiv A) _

    A4□Iso : Iso (A4□ inst) (fst C)
    A4□Iso = PushoutAlongEquiv (idEquiv Unit) λ _ → pt C

    A○□Iso : Iso (A○□ inst) (Pushout (fst f ∘ inr) fst)
    A○□Iso = compIso (equivToIso (symPushout _ _))
                     (invIso (pushoutIso _ _ _ _
                       (isoToEquiv (invIso A2□Iso))
                       (isoToEquiv (invIso A4□Iso))
                       (isoToEquiv (invIso A0□Iso))
                       refl
                       λ i x → push x i))

    A□0Iso : Iso (A□0 inst) Unit
    A□0Iso = isContr→Iso
      (inr tt , λ { (inl x) → sym (push x)
                  ; (inr x) → refl
                  ; (push a i) j → push a (i ∨ ~ j)})
      (tt , (λ _ → refl))

    A□2Iso : Iso (A□2 inst) (⋁gen A B)
    A□2Iso = equivToIso (symPushout _ _)

    A□4Iso : Iso (A□4 inst) (fst C)
    A□4Iso = PushoutAlongEquiv (idEquiv _) _

    A□○Iso : Iso (A□○ inst) (cofib (fst f))
    A□○Iso = invIso (pushoutIso _ _ _ _
      (isoToEquiv (invIso A□2Iso))
      (isoToEquiv (invIso A□0Iso))
      (isoToEquiv (invIso A□4Iso))
      (funExt (λ { (inl x) → refl
                  ; (inr x) → sym (push (fst x)) ∙ refl
                  ; (push a i) j → (sym (push a) ∙ refl) (i ∧ j)}))
      (funExt λ { (inl x) i → inr (snd f i)
                ; (inr x) → sym (push x)
                ; (push a i) j
                → hcomp (λ k
                → (λ {(i = i0) → inr (compPath-filler' (sym (snd f))
                                        (cong (fst f) (push a)) j (~ k))
                     ; (i = i1) → push (a , snd (B a)) (~ j)
                     ; (j = i0) → inr (fst f (push a (~ k ∨ i)))}))
          (push (a , snd (B a)) (~ i ∨ ~ j))}))

  ⋁-cofib-Iso : Iso (Pushout (fst f ∘ inr) fst) (cofib (fst f))
  ⋁-cofib-Iso = compIso (compIso (invIso A○□Iso)
                                  (invIso (3x3-Iso inst)))
                                  A□○Iso

{-
  We prove the square
    X ⋁ Y --> X
      ↓       ↓
      Y ----> *
  is a pushout.
-}

module _ (X∙ @ (X , x₀) : Pointed ℓ) (Y∙ @ (Y , y₀) : Pointed ℓ') where

  open 3-span
  open commSquare

  private
    weirdSquare : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      → (f : X → Y) (g : Y → Z) → commSquare
    weirdSquare f g .sp = 3span (idfun _) f
    weirdSquare f g .P = _
    weirdSquare f g .inlP = f
    weirdSquare f g .inrP = idfun _
    weirdSquare f g .comm = refl ∙ refl ∙ refl

    weirdPushoutSquare : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      → (f : X → Y) (g : Y → Z) → isPushoutSquare (weirdSquare f g)
    weirdPushoutSquare f g = isoToIsEquiv (iso _ inr (λ _ → refl)
        λ { (inl x) → sym (push _)
          ; (inr x) → refl
          ; (push a i) j → subst
            (λ t → Square (sym (push _)) refl t (push _))
              (cong (cong Pushout.inr) (lUnit _ ∙ lUnit _))
              (λ i j → push a (i ∨ ~ j))
              i j
          })

    {-
    The proof proceeds by applying the pasting lemma twice:
      1 ----> Y
      ↓       ↓
      X --> X ⋁ Y --> X
      ↓  mid  ↓  bot  ↓
      1 ----> Y ----> 1
    -}

    midPushout : isPushoutSquare _
    midPushout = isPushoutTotSquare→isPushoutBottomSquare
      (weirdPushoutSquare _ (terminal Y))
      where
        open PushoutPasteDown
          (pushoutToSquare (3span (const x₀) (const y₀)))
          (terminal X) (const y₀) (⋁proj₂ X∙ Y∙) refl

    -- slight help to the unifier here
    botPushout : isPushoutSquare record { comm = refl }
    botPushout = isPushoutTotSquare→isPushoutBottomSquare $
      rotatePushoutSquare (record { comm = refl } , isoToIsEquiv
        (iso _ inl (λ _ → refl) λ {
          (inl _) i → inl _
        ; (inr a) i → push a i
        ; (push a j) i → push a (i ∧ j)
        })) .snd
      where
        open PushoutPasteDown (rotatePushoutSquare (_ , midPushout))
          (⋁proj₁ X∙ Y∙) (terminal X) (terminal Y) refl

  Pushout⋁≃Unit : Pushout (⋁proj₁ X∙ Y∙) (⋁proj₂ X∙ Y∙) ≃ Unit
  Pushout⋁≃Unit = _ , botPushout

-- Pushout along projections is contractible
module _ (A : Pointed ℓ) (B : Pointed ℓ') where
  private
    push-inl : (a : typ A)
      → Path (Pushout (proj⋁ₗ {A = A}) proj⋁ᵣ) (inl a) (inr (pt B))
    push-inl x = push (inl x)

    push-inr : (b : typ B)
      → Path (Pushout (proj⋁ₗ {B = B}) proj⋁ᵣ) (inl (pt A)) (inr b)
    push-inr x = push (inr x)

    push-push : push-inl (pt A) ≡ push-inr (pt B)
    push-push i = push (push tt i)

    F : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A)
         (push-inl push-inr : x ≡ y) (q : push-inl ≡ push-inr)
      → (z : A) (m : x ≡ z)
      → Square (push-inl ∙ sym push-inr) m refl m
    F y push-inl push-inr q z m = (cong₂ _∙_ q refl ∙ rCancel push-inr)
      ◁ λ i j → m (i ∧ j)

    F' : ∀ {ℓ} {A : Type ℓ} {x : A}
      → F x refl refl refl _ refl ≡ sym (rUnit refl)
    F' = sym (compPath≡compPath' _ _) ∙ sym (rUnit _) ∙ sym (lUnit _)

    H : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A)
        (push-inl push-inr : x ≡ y) (q : push-inl ≡ push-inr)
      → Cube (λ k j → compPath-filler push-inr (sym push-inl) (~ j) k)
             (λ k j → F _ push-inr push-inl (sym q) _ push-inr j k)
             (λ i j → x) q
             (λ i j →  (push-inr ∙ sym push-inl) j) λ i j → push-inr j
    H {x = x} = J> (J> (λ k i j →  F' {x = x} (~ k) j i))

  isContrPushout-proj⋁ : isContr (Pushout proj⋁ₗ proj⋁ᵣ)
  fst isContrPushout-proj⋁ = inl (pt A)
  snd isContrPushout-proj⋁ (inl x) = push-inr (pt B) ∙ sym (push-inl x)
  snd isContrPushout-proj⋁ (inr x) = push (inr x)
  snd isContrPushout-proj⋁ (push (inl x) i) =
    compPath-filler (push-inr (pt B)) (sym (push-inl x)) (~ i)
  snd isContrPushout-proj⋁ (push (inr x) i) =
    F _ (push-inr (pt B)) (push-inl (pt A)) (sym push-push) _ (push (inr x)) i
  snd isContrPushout-proj⋁ (push (push a i) j) k =
    H _ (push-inl (pt A)) (push-inr (pt B)) push-push i k j

open Iso
Iso-⋁genFinSuc-⋁genFin⋁ : ∀ {ℓ} {n : ℕ} {A : Fin (suc n) → Pointed ℓ}
  → Iso (⋁gen (Fin (suc n)) A) (⋁gen∙ (Fin n) (A ∘ fsuc) ⋁ A fzero)
fun Iso-⋁genFinSuc-⋁genFin⋁ (inl x) = inl (inl tt)
fun Iso-⋁genFinSuc-⋁genFin⋁ (inr ((zero , w) , t)) = inr t
fun (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inr ((suc f , w) , t)) =
  inl (inr ((f , w) , t))
fun Iso-⋁genFinSuc-⋁genFin⋁ (push (zero , w) i) = push tt i
fun (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (push (suc x , w) i) =
  inl (push (x , w) i)
inv Iso-⋁genFinSuc-⋁genFin⋁ (inl (inl x)) = inl tt
inv Iso-⋁genFinSuc-⋁genFin⋁ (inl (inr x)) = inr ((fsuc (fst x)) , (snd x))
inv Iso-⋁genFinSuc-⋁genFin⋁ (inl (push a i)) = push (fsuc a) i
inv Iso-⋁genFinSuc-⋁genFin⋁ (inr x) = inr (fzero , x)
inv Iso-⋁genFinSuc-⋁genFin⋁ (push a i) = push fzero i
rightInv Iso-⋁genFinSuc-⋁genFin⋁ (inl (inl tt)) i = inl (inl tt)
rightInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inl (inr ((zero , w) , t))) = refl
rightInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inl (inr ((suc a , w) , t))) = refl
rightInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inl (push (zero , w) i)) = refl
rightInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inl (push (suc a , w) i)) = refl
rightInv Iso-⋁genFinSuc-⋁genFin⋁ (inr x) i = inr x
rightInv Iso-⋁genFinSuc-⋁genFin⋁ (push a i) j = push a i
leftInv Iso-⋁genFinSuc-⋁genFin⋁ (inl x) i = inl tt
leftInv Iso-⋁genFinSuc-⋁genFin⋁ (inr ((zero , tt) , t)) i = inr ((0 , tt) , t)
leftInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (inr ((suc x , w) , t)) i =
  inr ((suc x , w) , t)
leftInv Iso-⋁genFinSuc-⋁genFin⋁ (push (zero , w) i) j = push (0 , w) i
leftInv (Iso-⋁genFinSuc-⋁genFin⋁ {n = suc n}) (push (suc x , w) i) = refl
