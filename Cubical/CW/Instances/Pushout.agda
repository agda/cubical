{-# OPTIONS --cubical #-}
module Cubical.CW.Instances.Pushout where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.CW.Strictification renaming (strictCWskel to str)

IsoSphereSusp : (n : ℕ) → Iso (S₊ n) (Susp (S⁻ n))
IsoSphereSusp zero = BoolIsoSusp⊥
IsoSphereSusp (suc n) = IsoSucSphereSusp n

EquivSphereSusp : (n : ℕ) → (Susp (S⁻ n)) ≃ (S₊ n)
EquivSphereSusp n = isoToEquiv (invIso (IsoSphereSusp n))

IsoFinSplit3 : ∀ n m l → Iso (Fin ((n +ℕ m) +ℕ l)) (((Fin n) ⊎ (Fin m)) ⊎ (Fin l))
IsoFinSplit3 n m l =
  compIso (invIso (Iso-Fin⊎Fin-Fin+ {n +ℕ m}{l}))
          (⊎Iso {A = Fin (n +ℕ m)}{C = (Fin n) ⊎ (Fin m)}{B = Fin l}{D = Fin l} (invIso (Iso-Fin⊎Fin-Fin+ {n}{m})) idIso)

finSplit3 : ∀ n m l → (Fin ((n +ℕ m) +ℕ l)) ≃ (((Fin n) ⊎ (Fin m)) ⊎ (Fin l))
finSplit3 n m l = isoToEquiv (IsoFinSplit3 n m l)

invSides-hfill : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS x)

invSides-hfill1 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill1 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p j
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i)})
        (inS (p ((~ i) ∧ j)))

invSides-hfill2 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill2 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j)
                 ; (j = i0) → q (i)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS (q (i ∧ (~ j))))

-- This module defines a CW structure when B, C, D are strict CW skeleta
-- The non-strict version can be derived from there using the fact that every
-- CW skeleton is isomorphic to a strict one
module CWPushout (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ)
  (fʷ : cellMap (str Bʷ) (str Cʷ))
  (gʷ : cellMap (str Bʷ) (str Dʷ)) where

  B = str Bʷ
  C = str Cʷ
  D = str Dʷ

  f = strictCwMap fʷ
  g = strictCwMap gʷ

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  pushoutA : ℕ → Type ℓ
  pushoutA zero = B .fst zero
  pushoutA (suc n) = Pushout {A = B .fst n} {B = C .fst (suc n)} {C = D .fst (suc n)} (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

  pushoutCells : ℕ → ℕ
  pushoutCells zero = (card C zero) +ℕ (card D zero)
  pushoutCells (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) = inl (e C n .fst (α C (suc n) (c , (EquivSphereSusp n) .fst x)))
  pushoutMapₛ n (inl (inr b) , north) = inl (∣ f ∣ (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , south) = inr (∣ g ∣ (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , merid x i) =
    ((λ i → inl (∣ f ∣ (suc n) (push (b , x) (~ i))))
    ∙∙ (push (α B n (b , x)))
    ∙∙ (λ i → inr (∣ g ∣ (suc n) (push (b , x) i)))) i
  pushoutMapₛ n (inr d , x) = inr (e D n .fst (α D (suc n) (d , (EquivSphereSusp n) .fst x )))

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card B n) (card D (suc n)) .fst a
                                                   , invEq (EquivSphereSusp n) x)

  pushoutSpanₛ : (n : ℕ) → 3-span
  pushoutSpanₛ n = record { A0 = pushoutA (suc n)
                          ; A2 = (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n))
                          ; A4 = (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n)))
                          ; f1 = pushoutMapₛ n
                          ; f3 = fst }

  pushoutSpan : (n : ℕ) → 3-span
  pushoutSpan n = record { A0 = pushoutA (suc n)
                         ; A2 = (Fin (pushoutCells (suc n))) × (S⁻ (suc n))
                         ; A4 = (Fin (pushoutCells (suc n)))
                         ; f1 = pushoutMap (suc n)
                         ; f3 = fst }

  pushoutSpanEquiv : (n : ℕ) → 3-span-equiv (pushoutSpan n) (pushoutSpanₛ n)
  pushoutSpanEquiv n = record { e0 = idEquiv (pushoutA (suc n))
                              ; e2 = ≃-× (finSplit3 (card C (suc n)) (card B n) (card D (suc n))) (isoToEquiv (IsoSphereSusp n))
                              ; e4 = finSplit3 (card C (suc n)) (card B n) (card D (suc n))
                              ; H1 = λ x → refl
                              ; H3 = λ x → refl }

  -- spanPushoutIso : (n : ℕ) → Iso (spanPushout (pushoutSpan n)) (spanPushout (pushoutSpanₛ n))
  -- spanPushoutIso n =
  --   pushoutIso _ _ _ _ (Σ-cong-equiv (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
  --     λ _ → isoToEquiv (IsoSphereSusp n)) (idEquiv _)
  --    (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
  --    refl
  --    refl

  pushoutₛIso : (n : ℕ) → Iso (spanPushout (pushoutSpan n)) (spanPushout (pushoutSpanₛ n))
  pushoutₛIso n = pushoutIso _ _ _ _
    (Σ-cong-equiv (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
      λ _ → isoToEquiv (IsoSphereSusp n)) (idEquiv _)
     (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
     refl
     refl
  -- transp (λ i → Iso (spanPushout (pushoutSpan n)) (p i)) i0 idIso
  --   where
  --     p : (spanPushout (pushoutSpan n)) ≡ (spanPushout (pushoutSpanₛ n))
  --     p = spanEquivToPushoutPath (pushoutSpanEquiv n)

  pushoutIso₀-fun : pushoutA (suc zero) → Pushout pushoutMap₀ fst
  pushoutIso₀-fun (inl x) = inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inl (CW₁-discrete C .fst x)))
  pushoutIso₀-fun (inr x) = inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inr (CW₁-discrete D .fst x)))
  pushoutIso₀-fun (push a i) with (B .snd .snd .snd .fst a)
  pushoutIso₀-fun (push a i) | ()

  pushoutIso₀-helper : Fin (card C zero) ⊎ Fin (card D zero) → pushoutA (suc zero)
  pushoutIso₀-helper (inl x) = inl (invEq (CW₁-discrete C) x)
  pushoutIso₀-helper (inr x) = inr (invEq (CW₁-discrete D) x)

  pushoutIso₀-inv : Pushout pushoutMap₀ fst → pushoutA (suc zero)
  pushoutIso₀-inv (inl x) with (B .snd .snd .snd .fst x)
  pushoutIso₀-inv (inl x) | ()
  pushoutIso₀-inv (inr x) = pushoutIso₀-helper (Iso.inv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)

  pushoutIso₀-leftInv : (x : pushoutA (suc zero)) → pushoutIso₀-inv (pushoutIso₀-fun x) ≡ x
  pushoutIso₀-leftInv (inl x) =
    (λ i → pushoutIso₀-helper (Iso.leftInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inl (CW₁-discrete C .fst x)) i))
    ∙ λ i → inl (retEq (CW₁-discrete C) x i)
  pushoutIso₀-leftInv (inr x) =
    (λ i → pushoutIso₀-helper (Iso.leftInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inr (CW₁-discrete D .fst x)) i))
    ∙ λ i → inr (retEq (CW₁-discrete D) x i)
  pushoutIso₀-leftInv (push a i) with (B .snd .snd .snd .fst a)
  pushoutIso₀-leftInv (push a i) | ()

  pushoutIso₀-helper₁ : (x : Fin (card C zero) ⊎ Fin (card D zero))
                      → pushoutIso₀-fun (pushoutIso₀-helper x) ≡ inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)
  pushoutIso₀-helper₁ (inl x) = λ i → inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inl (secEq (CW₁-discrete C) x i)))
  pushoutIso₀-helper₁ (inr x) = λ i → inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) (inr (secEq (CW₁-discrete D) x i)))

  pushoutIso₀-rightInv : (x : Pushout pushoutMap₀ fst) → pushoutIso₀-fun (pushoutIso₀-inv x) ≡ x
  pushoutIso₀-rightInv (inl x) with (B .snd .snd .snd .fst x)
  pushoutIso₀-rightInv (inl x) | ()
  pushoutIso₀-rightInv (inr x) =
    pushoutIso₀-helper₁ (Iso.inv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)
    ∙ λ i → inr (Iso.rightInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x i)

  pushoutIso₀ : Iso (pushoutA (suc zero)) (Pushout pushoutMap₀ fst)
  pushoutIso₀ = iso pushoutIso₀-fun pushoutIso₀-inv pushoutIso₀-rightInv pushoutIso₀-leftInv

  -- Technical tool because the definition of S₊ n in the library is messed up
  modifySₙ : CWskel ℓ → ℕ → Type ℓ
  modifySₙ X zero = X .fst zero
  modifySₙ X (suc zero) = X .fst 1
  modifySₙ X (suc (suc n)) = Pushout (λ (a , x) → e X n .fst (α X (suc n) (a , (EquivSphereSusp n) .fst x))) fst

  modifySₙ→id : (X : CWskel ℓ) → (n : ℕ) → modifySₙ (str X) (suc (suc n)) → (str X) .fst (suc (suc n))
  modifySₙ→id X n (inl x) = inl x
  modifySₙ→id X n (inr x) = inr x
  modifySₙ→id X n (push (a , x) i) = push (a , (EquivSphereSusp n) .fst x) i

  id→modifySₙ : (X : CWskel ℓ) → (n : ℕ) → (str X) .fst (suc (suc n)) → modifySₙ (str X) (suc (suc n))
  id→modifySₙ X n (inl x) = inl x
  id→modifySₙ X n (inr x) = inr x
  id→modifySₙ X n (push (a , x) i) =
    ((λ i → inl (e (str X) n .fst (α (str X) (suc n) (a , secEq (EquivSphereSusp n) x (~ i)))))
     ∙∙ (push (a , invEq (EquivSphereSusp n) x))
     ∙∙ refl) i

  id→modifySₙ→id : (X : CWskel ℓ) → (n : ℕ) → (x : (str X) .fst (suc (suc n))) → modifySₙ→id X n (id→modifySₙ X n x) ≡ x
  id→modifySₙ→id X n (inl x) = refl
  id→modifySₙ→id X n (inr x) = refl
  id→modifySₙ→id X n (push (a , x) i) j =
    hcomp (λ k → λ { (i = i0) → inl (strictifyFamα X (suc n) (a , leftInv x (j ∨ k)))
                   ; (i = i1) → inr a
                   ; (j = i0) → modifySₙ→id X n (doubleCompPath-filler (λ i → inl (e (str X) n .fst (α (str X) (suc n) (a , leftInv x (~ i)))))
                                                                       (push (a , fun x)) refl k i)
                   ; (j = i1) → push (a , x) i })
          (push (a , leftInv x j) i)
    where
      fun = invEq (EquivSphereSusp n)
      inv = (EquivSphereSusp n) .fst
      leftInv = secEq (EquivSphereSusp n)

  modifySₙ→id→modifySₙ : (X : CWskel ℓ) → (n : ℕ) → (x : modifySₙ (str X) (suc (suc n))) → id→modifySₙ X n (modifySₙ→id X n x) ≡ x
  modifySₙ→id→modifySₙ X n (inl x) = refl
  modifySₙ→id→modifySₙ X n (inr x) = refl
  modifySₙ→id→modifySₙ X n (push (a , x) i) j =
    hcomp (λ k → λ { (i = i0) → inl (e (str X) n .fst (α (str X) (suc n)
                                      (a , compPath→Square {p = leftInv (inv x)}{refl}{λ i → inv (rightInv x i)}{refl}
                                                           (cong (λ X → X ∙ refl) (commPathIsEq (EquivSphereSusp n .snd) x)) k j)))
                   ; (i = i1) → inr a
                   ; (j = i0) → doubleCompPath-filler (λ i → inl (e (str X) n .fst (α (str X) (suc n) (a , leftInv (inv x) (~ i)))))
                                                      (push (a , fun (inv x))) refl k i
                   ; (j = i1) → push (a , x) i })
          (push (a , rightInv x j) i)
    where
      fun = invEq (EquivSphereSusp n)
      inv = (EquivSphereSusp n) .fst
      leftInv = secEq (EquivSphereSusp n)
      rightInv = retEq (EquivSphereSusp n)

  modifiedPushout : (n : ℕ) → Type ℓ
  modifiedPushout n = (Pushout {A = B .fst (suc n)} {B = modifySₙ C (suc (suc n))} {C = modifySₙ D (suc (suc n))}
                             (inl ∘ ∣ f ∣ (suc n)) (inl ∘ ∣ g ∣ (suc n)))

  modifiedPushout→Pushout : (n : ℕ) → modifiedPushout n → pushoutA (suc (suc n))
  modifiedPushout→Pushout n (inl x) = inl (modifySₙ→id Cʷ n x)
  modifiedPushout→Pushout n (inr x) = inr (modifySₙ→id Dʷ n x)
  modifiedPushout→Pushout n (push a i) = push a i

  Pushout→modifiedPushout : (n : ℕ) → pushoutA (suc (suc n)) → modifiedPushout n
  Pushout→modifiedPushout n (inl x) = inl (id→modifySₙ Cʷ n x)
  Pushout→modifiedPushout n (inr x) = inr (id→modifySₙ Dʷ n x)
  Pushout→modifiedPushout n (push a i) = push a i

  Pushout→modP→Pushout : (n : ℕ) → (x : pushoutA (suc (suc n))) → modifiedPushout→Pushout n (Pushout→modifiedPushout n x) ≡ x
  Pushout→modP→Pushout n (inl x) j = inl (id→modifySₙ→id Cʷ n x j)
  Pushout→modP→Pushout n (inr x) j = inr (id→modifySₙ→id Dʷ n x j)
  Pushout→modP→Pushout n (push a i) j = push a i

  modP→Pushout→modP : (n : ℕ) → (x : modifiedPushout n) → Pushout→modifiedPushout n (modifiedPushout→Pushout n x) ≡ x
  modP→Pushout→modP n (inl x) j = inl (modifySₙ→id→modifySₙ Cʷ n x j)
  modP→Pushout→modP n (inr x) j = inr (modifySₙ→id→modifySₙ Dʷ n x j)
  modP→Pushout→modP n (push a i) j = push a i

  IsoModifiedPushout : (n : ℕ) → Iso (pushoutA (suc (suc n))) (modifiedPushout n)
  IsoModifiedPushout n = iso (Pushout→modifiedPushout n) (modifiedPushout→Pushout n) (modP→Pushout→modP n) (Pushout→modP→Pushout n)

  pushoutIsoₛ-filler0 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → pushoutA (suc n)
  pushoutIsoₛ-filler0 n b x i j = (doubleCompPath-filler (λ i → inl (∣ f ∣ (suc n) (push (b , x) (~ i))))
                                                         (push (α B n (b , x)))
                                                         (λ i → inr (∣ g ∣ (suc n) (push (b , x) i))) i j)

  pushoutIsoₛ-filler1 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ-filler1 n b x i j k =
    hfill (λ k → λ { (i = i0) → invSides-hfill2 (push (inl (inr b) , north))
                                                (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (i = i1) → invSides-hfill2 (push (inl (inr b) , south))
                                                (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (j = i0) → inl (pushoutIsoₛ-filler0 n b x (~ k) i)
                   ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) k i })
          (inS (push (inl (inr b) , merid x i) j)) k

  pushoutIsoₛ-inv↪ : (n : ℕ) → pushoutA (suc n) → modifiedPushout n
  pushoutIsoₛ-inv↪ n (inl c) = inl (inl c)
  pushoutIsoₛ-inv↪ n (inr d) = inr (inl d)
  pushoutIsoₛ-inv↪ n (push b i) = push (inl b) i

  pushoutIsoₛ-filler2 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → modifiedPushout n
  pushoutIsoₛ-filler2 n b x i j k =
    hfill (λ k → λ { (i = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x k j)
                   ; (i = i1) → push (inr b) ((~ k) ∧ j)
                   ; (j = i0) → invSides-hfill1 (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                                                (λ _ → push (inr b) i0) i (~ k) i1
                   ; (j = i1) → invSides-hfill1 (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                                                (λ i → push (inr b) (~ i)) i (~ k) i1 })
          (inS (push (push (b , x) i) j)) k

  pushoutIsoₛ-filler3 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-filler3 n b j k l =
    hfill (λ l → λ { (j = i0) → push (inl (inr b) , south) i0
                   ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l)
                   ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ l ∨ ~ j)
                   ; (k = i1) → push (inl (inr b) , south) j })
          (inS (push (inl (inr b) , south) (j ∧ k))) l

  pushoutIsoₛ-filler4 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-filler4 n b i k j =
    hfill (λ j → λ { (i = i0) → push (inl (inr b) , south) i0
                   ; (i = i1) → pushoutIsoₛ-filler3 n b j k i1
                   ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ i ∨ ~ j)
                   ; (k = i1) → push (inl (inr b) , south) (i ∧ j) })
          (inS (push (inl (inr b) , south) i0)) j

  pushoutIsoₛ-fun : (n : ℕ) → modifiedPushout n → (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ-fun n (inl (inl c)) = inl (inl c)
  pushoutIsoₛ-fun n (inl (inr c)) = inr (inl (inl c))
  pushoutIsoₛ-fun n (inl (push (c , x) i)) = push (inl (inl c) , x) i
  pushoutIsoₛ-fun n (inr (inl d)) = inl (inr d)
  pushoutIsoₛ-fun n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-fun n (inr (push (d , x) i)) = push (inr d , x) i
  pushoutIsoₛ-fun n (push (inl b) i) = inl (push b i)
  pushoutIsoₛ-fun n (push (inr b) i) = (push (inl (inr b) , north) ∙∙ refl ∙∙ (λ i → push (inl (inr b) , south) (~ i))) i
  pushoutIsoₛ-fun n (push (push (b , x) j) i) = pushoutIsoₛ-filler1 n b x i j i1

  pushoutIsoₛ-inv : (n : ℕ) → (Pushout (pushoutMapₛ n) fst) → modifiedPushout n
  pushoutIsoₛ-inv n (inl x) = pushoutIsoₛ-inv↪ n x
  pushoutIsoₛ-inv n (inr (inl (inl c))) = inl (inr c)
  pushoutIsoₛ-inv n (inr (inl (inr b))) = push (inr b) i0 --inl (inl (∣ f ∣ (suc n) (inr b)))
  pushoutIsoₛ-inv n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-inv n (push (inl (inl c) , x) i) = inl (push (c , x) i)
  pushoutIsoₛ-inv n (push (inl (inr b) , north) i) = push (inr b) i0 --inl (inl (∣ f ∣ (suc n) (inr b)))
  pushoutIsoₛ-inv n (push (inl (inr b) , south) i) = push (inr b) (~ i)
  pushoutIsoₛ-inv n (push (inl (inr b) , merid x j) i) = pushoutIsoₛ-filler2 n b x i j i1
  pushoutIsoₛ-inv n (push (inr d , x) i) = inr (push (d , x) i)

  pushoutIsoₛ-rightInv↪ : (n : ℕ) → (x : pushoutA (suc n)) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n x) ≡ inl x
  pushoutIsoₛ-rightInv↪ n (inl c) = refl
  pushoutIsoₛ-rightInv↪ n (inr d) = refl
  pushoutIsoₛ-rightInv↪ n (push b i) = refl

  pushoutIsoₛ-rightInv : (n : ℕ) → (x : Pushout (pushoutMapₛ n) fst) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv n x) ≡ x
  pushoutIsoₛ-rightInv n (inl x) = pushoutIsoₛ-rightInv↪ n x
  pushoutIsoₛ-rightInv n (inr (inl (inl c))) = refl
  pushoutIsoₛ-rightInv n (inr (inl (inr b))) = push (inl (inr b) , north)
  pushoutIsoₛ-rightInv n (inr (inr d)) = refl
  pushoutIsoₛ-rightInv n (push (inl (inl c) , x) i) = refl
  pushoutIsoₛ-rightInv n (push (inl (inr b) , north) i) k = push (inl (inr b) , north) (i ∧ k)
  pushoutIsoₛ-rightInv n (push (inl (inr b) , south) i) k = pushoutIsoₛ-filler4 n b i k i1
  pushoutIsoₛ-rightInv n (push (inl (inr b) , merid x j) i) k =
    hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i0)
                                               ; (j = i1) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i1)
                                               ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x (l ∧ i) j))
                                               ; (k = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) i1
                                               ; (l = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ k) j)
                                               ; (l = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) k })
                                      (inl (push (α B n (b , x)) j))
                   ; (i = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l ∧ j)
                   ; (j = i0) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i0)
                                               ; (i = i1) → push (inl (inr b) , north) (k ∧ j)
                                               ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                                                                (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                                                                (λ _ → push (inr b) i0) i (~ l) j)
                                               ; (k = i1) → push (inl (inr b) , north) (i ∧ j) --?
                                               ; (l = i0) → invSides-hfill2 (push (inl (inr b) , north))
                                                                            (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                                                                            (~ i) ( k) j
                                               ; (l = i1) → push (inl (inr b) , north) (i ∧ k ∧ j) })
                                      (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i0))
                   ; (j = i1) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i1)
                                               ; (i = i1) → pushoutIsoₛ-filler3 n b j k l
                                               ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                                                                (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                                                                (λ i → push (inr b) (~ i)) i (~ l) j)
                                               ; (k = i1) → push (inl (inr b) , south) (i ∧ j)
                                               ; (l = i0) → invSides-hfill2 (push (inl (inr b) , south))
                                                                            (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                                                                            (~ i) ( k) j
                                               ; (l = i1) → pushoutIsoₛ-filler4 n b i k j })
                                      (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i1))
                   ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-filler2 n b x i j l)
                   ; (k = i1) → push (inl (inr b) , merid x j) i })
          (pushoutIsoₛ-filler1 n b x j i (~ k))
  pushoutIsoₛ-rightInv n (push (inr d , x) i) = refl

  pushoutIsoₛ-leftInv : (n : ℕ) → (x : modifiedPushout n) → pushoutIsoₛ-inv n (pushoutIsoₛ-fun n x) ≡ x
  pushoutIsoₛ-leftInv n (inl (inl c)) = refl
  pushoutIsoₛ-leftInv n (inl (inr c)) = refl
  pushoutIsoₛ-leftInv n (inl (push (c , x) i)) = refl
  pushoutIsoₛ-leftInv n (inr (inl d)) = refl
  pushoutIsoₛ-leftInv n (inr (inr d)) = refl
  pushoutIsoₛ-leftInv n (inr (push (d , x) i)) = refl
  pushoutIsoₛ-leftInv n (push (inl b) i) = refl
  pushoutIsoₛ-leftInv n (push (inr b) i) k =
    hcomp (λ j → λ { (i = i0) → inl (inl (∣ f ∣ (suc n) (inr b)))
                   ; (i = i1) → push (inr b) (k ∨ j)
                   ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl
                                                                         (λ i → push (inl (inr b) , south) (~ i)) j i)
                   ; (k = i1) → push (inr b) i })
          (push (inr b) (i ∧ k))
  pushoutIsoₛ-leftInv n (push (push (b , x) j) i) k =
    hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (inl (∣ f ∣ (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → inl (inl (e C n .fst (∣ f ∣ (suc n) (invEq (e B n) (inr b)))))
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , north))
                                                                              (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inl (inl (∣ f ∣ (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                                                                            (λ _ → push (inr b) i0) (~ k) (~ j) i
                                               ; (l = i1) → inl (inl (∣ f ∣ (suc n) (push (b , x) j))) })
                                      (inl (inl (∣ f ∣ (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (i = i1) → hcomp (λ i → λ { (j = i0) → inr (inl (∣ g ∣ (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → push (inr b) (k ∨ ~ i ∨ l)
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , south))
                                                                              (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inr (inl (∣ g ∣ (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                                                                            (λ i → push (inr b) (~ i)) (~ k) (~ j) i
                                               ; (l = i1) → inr (inl (∣ g ∣ (suc n) (push (b , x) j))) })
                                      (inr (inl (∣ g ∣ (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (j = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x ((~ k) ∧ (~ l)) i)
                   ; (j = i1) → hfill (λ j → λ { (i = i0) → inl (inl (∣ f ∣ (suc n) (inr b)))
                                               ; (i = i1) → push (inr b) (k ∨ j)
                                               ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl (λ i → push (inl (inr b) , south) (~ i)) j i)
                                               ; (k = i1) → push (inr b) i })
                                      (inS (push (inr b) (i ∧ k))) l
                   ; (k = i0) → pushoutIsoₛ-inv n (pushoutIsoₛ-filler1 n b x i j l)
                   ; (k = i1) → push (push (b , x) j) i })
          (pushoutIsoₛ-filler2 n b x j i (~ k))

  pushoutIsoₛ : (n : ℕ) → Iso (modifiedPushout n) (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)

  pushoutIsoₜ : (n : ℕ) → Iso (pushoutA (suc n)) (Pushout (pushoutMap n) fst)
  pushoutIsoₜ zero = pushoutIso₀
  pushoutIsoₜ (suc n) = compIso (IsoModifiedPushout n) (compIso (pushoutIsoₛ n) (invIso (pushoutₛIso n)))

  pushoutSkel : CWskel ℓ
  pushoutSkel = pushoutA , (pushoutCells , pushoutMap , (B .snd .snd .snd .fst) , λ n → isoToEquiv (pushoutIsoₜ n))

  realisePushoutSkel→pts : (n : ℕ) (x : fst pushoutSkel n) → 
                           (Pushout (realiseCellMap {C = B} {D = C} f)
                           (realiseCellMap {C = B} {D = D} g))
  realisePushoutSkel→pts zero x = ⊥.rec {!¬CW₀!}
  realisePushoutSkel→pts (suc n) (inl x) = inl (incl {n = suc n} x)
  realisePushoutSkel→pts (suc n) (inr x) = inr (incl {n = suc n} x)
  realisePushoutSkel→pts (suc n) (push a i) =
    ((λ i → inl (push {n = n} (∣ f ∣ n a) (~ i)))
      ∙∙ push (incl {n = n} a)
      ∙∙ λ i → inr (push {n = n} (∣ g ∣ n a) i)) i

  realisePushoutSkel→ :   realise pushoutSkel → 
                           (Pushout (realiseCellMap {C = B} {D = C} f)
                           (realiseCellMap {C = B} {D = D} g))
  realisePushoutSkel→ (incl {n = n} x) = realisePushoutSkel→pts n x
  realisePushoutSkel→ (push {n = zero} x i) = {!⊥.rec ?!}
  realisePushoutSkel→ (push {n = suc n} (inl x) i) = inl (push {n = (suc n)} x i)
  realisePushoutSkel→ (push {n = suc n} (inr x) i) = inr (push {n = (suc n)} x i)
  realisePushoutSkel→ (push {n = suc n} (push a j) i) =
    hcomp (λ k →
    λ {(i = i0) → doubleCompPath-filler
                   ((λ i₂ → inl (push {n = n} (∣ f ∣ n a) (~ i₂))))
                   (push (incl {n = n} a))
                   (λ i₂ → inr (push {n = n} (∣ g ∣ n a) i₂)) i1 j
     ; (i = i1) → doubleCompPath-filler
                   (λ i₂ → inl (push {n = (suc n)} (inl (∣ f ∣ n a)) (~ i₂)))
                   (push (incl {n = suc n} (inl a)))
                   (λ i₂ → inr (push {n = (suc n)} (inl (∣ g ∣ n a)) i₂)) k j
     ; (j = i0) → inl (push {n = suc n} (∣ f ∣ (suc n) (inl a)) (k ∧ i))
     ; (j = i1) → inr (push {n = suc n} (∣ g ∣ (suc n) (inl a)) (k ∧ i))})
     (hcomp (λ k →
    λ {(i = i0) → doubleCompPath-filler
                   ((λ i₂ → inl (push {n = n} (∣ f ∣ n a) (~ i₂))))
                   (push (incl {n = n} a))
                   (λ i₂ → inr (push {n = n} (∣ g ∣ n a) i₂)) k j
     ; (i = i1) → push (push {n = n} a k) j
     ; (j = i0) → inl (rUnit (push {n = n}(∣ f ∣ n a)) i k)
     ; (j = i1) → inr (rUnit (push {n = n}(∣ g ∣ n a)) i k)
     })
     (push (incl {n = n} a) j))

  realisePushoutSkel←L : SequenceMap (realiseSeq C) (realiseSeq pushoutSkel)
  ∣ realisePushoutSkel←L ∣ zero x = ⊥.rec {!!}
  ∣ realisePushoutSkel←L ∣ (suc n) = inl
  comm realisePushoutSkel←L zero x = ⊥.rec {!!}
  comm realisePushoutSkel←L (suc n) x = refl

  realisePushoutSkel←R : SequenceMap (realiseSeq D) (realiseSeq pushoutSkel)
  ∣ realisePushoutSkel←R ∣ zero x = ⊥.rec {!!}
  ∣ realisePushoutSkel←R ∣ (suc n) = inr
  comm realisePushoutSkel←R zero x = ⊥.rec {!!}
  comm realisePushoutSkel←R (suc n) x = refl

  realisePushoutSkel← : (Pushout (realiseCellMap {C = B} {D = C} f)
                           (realiseCellMap {C = B} {D = D} g)) → realise pushoutSkel
  realisePushoutSkel← (inl x) = realiseSequenceMap realisePushoutSkel←L x
  realisePushoutSkel← (inr x) = realiseSequenceMap realisePushoutSkel←R x
  realisePushoutSkel← (push (incl {n = zero} x) i) = {!⊥.rec !} -- ⊥.rec {A = incl (⊥.rec {!!}) ≡ incl (⊥.rec {!!})} {!!} i
  realisePushoutSkel← (push (incl {n = suc n} x) i) =
    (push (inl (∣ f ∣ (suc n) x)) ∙∙ (λ i → incl {n = suc (suc n)} (push x i)) ∙∙ sym (push (inr (∣ g ∣ (suc n) x)))) i
  -- (({!refl!} ∙ sym (push (inl (inl (∣ f ∣ n x))))) ∙∙ (λ i → incl {n = suc n} (push x i)) ∙∙ {!push ?!}) i
  realisePushoutSkel← (push (push x i₁) i) = {!!}

  shiftPushoutStrSeqIso : SequenceIso (realiseSeq pushoutSkel) (PushoutSequence f g)
  fst shiftPushoutStrSeqIso zero = {!refl!}
  fst shiftPushoutStrSeqIso (suc n) = pushoutIso _ _ _ _ {!idEquiv _!} {!!} (idEquiv _) {!!} {!!}
  snd shiftPushoutStrSeqIso = {!!}

  shiftPushoutStrIso : Iso (realise pushoutSkel) (SeqColim (PushoutSequence f g))
  
  shiftPushoutStrIso = sequenceEquiv→ColimIso (SequenceIso→SequenceEquiv shiftPushoutStrSeqIso)

  f' : SequenceMap (realiseSeq B) (ShiftSeq (realiseSeq C))
  ∣_∣ f' n x = inl (∣ f ∣ n x)
  comm f' n x i = inl (comm f n x i)

  g' : SequenceMap (realiseSeq B) (ShiftSeq (realiseSeq D))
  ∣_∣ g' n x = inl (∣ g ∣ n x)
  comm g' n x i = inl (comm g n x i)

  hh : Iso (Pushout (realiseSequenceMap f') (realiseSequenceMap g'))
           (Pushout (realiseCellMap {C = B} {D = C} f)
                                    (realiseCellMap {C = B} {D = D} g))
           
  hh = pushoutIso _ _ _ _ (idEquiv _)
    (isoToEquiv (invIso (Iso-SeqColim→SeqColimSuc (realiseSeq C))))
    (isoToEquiv (invIso (Iso-SeqColim→SeqColimSuc (realiseSeq D))))
    (λ { i (incl {n = n} x) → push {n = n} (∣ f ∣ n x) (~ i)
       ; i (push {n = n} x j) → {!n!}}) {!!}

  realisePushoutSkel' : Iso (realise pushoutSkel)
                           (Pushout (realiseCellMap {C = B} {D = C} f)
                                    (realiseCellMap {C = B} {D = D} g))
  realisePushoutSkel' = compIso {!f!} (invIso (Iso-PushoutColim-ColimPushout f g))

  realisePushoutSkel : Iso (realise pushoutSkel)
                           (Pushout (realiseCellMap {C = B} {D = C} f)
                                    (realiseCellMap {C = B} {D = D} g))
  Iso.fun realisePushoutSkel = realisePushoutSkel→
  Iso.inv realisePushoutSkel = realisePushoutSkel←
  Iso.rightInv realisePushoutSkel = {!!}
  Iso.leftInv realisePushoutSkel = {!!}

-- Iso-PushoutColim-ColimPushout

  Pushoutᶜʷstr : isCW (Pushout (realiseCellMap {C = B} {D = C} f)
                              (realiseCellMap {C = B} {D = D} g))
  fst Pushoutᶜʷstr = pushoutSkel
  snd Pushoutᶜʷstr = isoToEquiv (invIso realisePushoutSkel)

  -- show finite if B C D are finite

  isFin : ∀ {ℓ} (C : CWskel ℓ) → Type ℓ 
  isFin C = Σ[ m ∈ ℕ ] ((k : ℕ) → isEquiv (CW↪ C (k +ℕ m)))

  PushoutᶜʷfinStr : isFin B → isFin C → isFin D → isFin pushoutSkel
  fst (PushoutᶜʷfinStr (dimB , eB) (dimC , eC) (dimD , eD)) = suc (dimB +ℕ (dimC +ℕ dimD))
  snd (PushoutᶜʷfinStr (dimB , eB) (dimC , eC) (dimD , eD)) = {!!}


open import Cubical.Foundations.HLevels
isPushoutᶜʷ : ∀ {ℓ} (B : finCW ℓ) (C D : CW ℓ)
  (f : finCW→CW B →ᶜʷ C) (g : finCW→CW B →ᶜʷ D)
  → ∥ isCW (Pushout f g) ∥₁
isPushoutᶜʷ {ℓ = ℓ} = uncurry λ B
  → PT.elim (λ _ → isPropΠ4 λ _ _ _ _ → squash₁) λ isFinCWB
    → uncurry λ C → PT.elim (λ _ → isPropΠ3 λ _ _ _ → squash₁) λ isFinCWC
      → uncurry λ C → PT.elim (λ _ → isPropΠ2 λ _ _ → squash₁) λ isFinCWD
        → λ f g → {!!}
  where
  module _ (B C D : Type ℓ) (finCW : {!!}) where


  -- Todo: show that colim pushoutSkel is the indended thing


open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

PushoutEmptyDomainIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (Pushout {A = ⊥} {B = A} {C = B} (λ()) (λ())) (A ⊎ B)
Iso.fun PushoutEmptyDomainIso (inl x) = inl x
Iso.fun PushoutEmptyDomainIso (inr x) = inr x
Iso.inv PushoutEmptyDomainIso (inl x) = inl x
Iso.inv PushoutEmptyDomainIso (inr x) = inr x
Iso.rightInv PushoutEmptyDomainIso (inl x) = refl
Iso.rightInv PushoutEmptyDomainIso (inr x) = refl
Iso.leftInv PushoutEmptyDomainIso (inl x) = refl
Iso.leftInv PushoutEmptyDomainIso (inr x) = refl
