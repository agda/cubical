module Cubical.CW.Instances.Pushout where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
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
open import Cubical.CW.Approximation

-- Lemmas
module pushoutCWLemmas where
  IsoFinSplit3 : ∀ n m l
    → Iso (Fin ((n +ℕ m) +ℕ l)) (((Fin n) ⊎ (Fin m)) ⊎ (Fin l))
  IsoFinSplit3 n m l =
    compIso (invIso (Iso-Fin⊎Fin-Fin+ {n +ℕ m}{l}))
            (⊎Iso {A = Fin (n +ℕ m)}
                  {C = (Fin n) ⊎ (Fin m)}
                  {B = Fin l}
                  {D = Fin l}
                  (invIso (Iso-Fin⊎Fin-Fin+ {n}{m})) idIso)

  finSplit3 : ∀ n m l → Fin ((n +ℕ m) +ℕ l)
                      ≃ ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
  finSplit3 n m l = isoToEquiv (IsoFinSplit3 n m l)

  module _ {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) where
    invSides-hfill : I → I → I → A
    invSides-hfill i j =
      hfill (λ k → λ { (i = i0) → p (k ∧ j)
                     ; (i = i1) → q (~ j ∧ k)
                     ; (j = i0) → q (i ∧ k)
                     ; (j = i1) → p (~ i ∧ k)})
            (inS x)

    invSides-hfill1 : I → I → I → A
    invSides-hfill1 i j =
      hfill (λ k → λ { (i = i0) → p j
                     ; (i = i1) → q (~ j ∧ k)
                     ; (j = i0) → q (i ∧ k)
                     ; (j = i1) → p (~ i)})
            (inS (p ((~ i) ∧ j)))

    invSides-hfill2 : I → I → I → A
    invSides-hfill2 i j =
      hfill (λ k → λ { (i = i0) → p (k ∧ j)
                     ; (i = i1) → q (~ j)
                     ; (j = i0) → q (i)
                     ; (j = i1) → p (~ i ∧ k)})
            (inS (q (i ∧ (~ j))))

open pushoutCWLemmas

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
  pushoutA (suc n) =
    Pushout {A = B .fst n} {B = C .fst (suc n)} {C = D .fst (suc n)}
      (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

  pushoutCells : ℕ → ℕ
  pushoutCells zero = (card C zero) +ℕ (card D zero)
  pushoutCells (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMapₛ : (n : ℕ)
    → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n))
    → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) =
    inl (e C n .fst (α C (suc n) (c , (EquivSphereSusp n) .fst x)))
  pushoutMapₛ n (inl (inr b) , north) = inl (∣ f ∣ (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , south) = inr (∣ g ∣ (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , merid x i) =
    ((λ i → inl (∣ f ∣ (suc n) (push (b , x) (~ i))))
    ∙∙ (push (α B n (b , x)))
    ∙∙ (λ i → inr (∣ g ∣ (suc n) (push (b , x) i)))) i
  pushoutMapₛ n (inr d , x) =
    inr (e D n .fst (α D (suc n) (d , (EquivSphereSusp n) .fst x )))

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) (a , x) =
    pushoutMapₛ n (finSplit3 (card C (suc n)) (card B n) (card D (suc n)) .fst a
                  , invEq (EquivSphereSusp n) x)
  pushoutSpanₛ : (n : ℕ) → 3-span
  3-span.A0 (pushoutSpanₛ n) = pushoutA (suc n)
  3-span.A2 (pushoutSpanₛ n) =
    (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × Susp (S⁻ n)
  3-span.A4 (pushoutSpanₛ n) = ((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))
  3-span.f1 (pushoutSpanₛ n) = pushoutMapₛ n
  3-span.f3 (pushoutSpanₛ n) = fst

  pushoutSpan : (n : ℕ) → 3-span
  3-span.A0 (pushoutSpan n) = pushoutA (suc n)
  3-span.A2 (pushoutSpan n) = Fin (pushoutCells (suc n)) × S⁻ (suc n)
  3-span.A4 (pushoutSpan n) = Fin (pushoutCells (suc n))
  3-span.f1 (pushoutSpan n) = pushoutMap (suc n)
  3-span.f3 (pushoutSpan n) = fst

  pushoutSpanEquiv : (n : ℕ) → 3-span-equiv (pushoutSpan n) (pushoutSpanₛ n)
  3-span-equiv.e0 (pushoutSpanEquiv n) = idEquiv (pushoutA (suc n))
  3-span-equiv.e2 (pushoutSpanEquiv n) =
    ≃-× (finSplit3 (card C (suc n)) (card B n) (card D (suc n)))
        (isoToEquiv (IsoSphereSusp n))
  3-span-equiv.e4 (pushoutSpanEquiv n) =
    finSplit3 (card C (suc n)) (card B n) (card D (suc n))
  3-span-equiv.H1 (pushoutSpanEquiv n) _ = refl
  3-span-equiv.H3 (pushoutSpanEquiv n) _ = refl

  pushoutₛIso : (n : ℕ)
    → Iso (spanPushout (pushoutSpan n)) (spanPushout (pushoutSpanₛ n))
  pushoutₛIso n = pushoutIso _ _ _ _
     (Σ-cong-equiv
      (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
      λ _ → isoToEquiv (IsoSphereSusp n))
     (idEquiv _)
     (isoToEquiv (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))))
     refl
     refl

  pushoutIso₀-fun : pushoutA (suc zero) → Pushout pushoutMap₀ fst
  pushoutIso₀-fun (inl x) =
    inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
                 (inl (CW₁-discrete C .fst x)))
  pushoutIso₀-fun (inr x) =
    inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
                 (inr (CW₁-discrete D .fst x)))
  pushoutIso₀-fun (push a i) with (B .snd .snd .snd .fst a)
  pushoutIso₀-fun (push a i) | ()

  pushoutIso₀-helper : Fin (card C zero) ⊎ Fin (card D zero)
    → pushoutA (suc zero)
  pushoutIso₀-helper (inl x) = inl (invEq (CW₁-discrete C) x)
  pushoutIso₀-helper (inr x) = inr (invEq (CW₁-discrete D) x)

  pushoutIso₀-inv : Pushout pushoutMap₀ fst → pushoutA (suc zero)
  pushoutIso₀-inv (inl x) with (B .snd .snd .snd .fst x)
  pushoutIso₀-inv (inl x) | ()
  pushoutIso₀-inv (inr x) =
    pushoutIso₀-helper
      (Iso.inv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)

  pushoutIso₀-leftInv : (x : pushoutA (suc zero))
    → pushoutIso₀-inv (pushoutIso₀-fun x) ≡ x
  pushoutIso₀-leftInv (inl x) =
    (λ i → pushoutIso₀-helper
             (Iso.leftInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
               (inl (CW₁-discrete C .fst x)) i))
    ∙ λ i → inl (retEq (CW₁-discrete C) x i)
  pushoutIso₀-leftInv (inr x) =
    (λ i → pushoutIso₀-helper
             (Iso.leftInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
               (inr (CW₁-discrete D .fst x)) i))
    ∙ λ i → inr (retEq (CW₁-discrete D) x i)
  pushoutIso₀-leftInv (push a i) with (B .snd .snd .snd .fst a)
  pushoutIso₀-leftInv (push a i) | ()

  pushoutIso₀-helper₁ : (x : Fin (card C zero) ⊎ Fin (card D zero))
    → pushoutIso₀-fun (pushoutIso₀-helper x)
     ≡ inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)
  pushoutIso₀-helper₁ (inl x) i =
    inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
                 (inl (secEq (CW₁-discrete C) x i)))
  pushoutIso₀-helper₁ (inr x) i =
    inr (Iso.fun (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero})
                 (inr (secEq (CW₁-discrete D) x i)))

  pushoutIso₀-rightInv : (x : Pushout pushoutMap₀ fst)
    → pushoutIso₀-fun (pushoutIso₀-inv x) ≡ x
  pushoutIso₀-rightInv (inl x) with (B .snd .snd .snd .fst x)
  pushoutIso₀-rightInv (inl x) | ()
  pushoutIso₀-rightInv (inr x) =
      pushoutIso₀-helper₁
        (Iso.inv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x)
    ∙ λ i → inr (Iso.rightInv (Iso-Fin⊎Fin-Fin+ {card C zero} {card D zero}) x i)

  pushoutIso₀ : Iso (pushoutA (suc zero)) (Pushout pushoutMap₀ fst)
  pushoutIso₀ =
    iso pushoutIso₀-fun pushoutIso₀-inv pushoutIso₀-rightInv pushoutIso₀-leftInv

  -- Technical tool because the definition of S₊ n in the library is messed up
  modifySₙ : CWskel ℓ → ℕ → Type ℓ
  modifySₙ X zero = X .fst zero
  modifySₙ X (suc zero) = X .fst 1
  modifySₙ X (suc (suc n)) = Pushout (λ (a , x) → e X n .fst (α X (suc n) (a , (EquivSphereSusp n) .fst x))) fst

  modifySₙ→id : (X : CWskel ℓ) → (n : ℕ)
    → modifySₙ (str X) (suc (suc n)) → (str X) .fst (suc (suc n))
  modifySₙ→id X n (inl x) = inl x
  modifySₙ→id X n (inr x) = inr x
  modifySₙ→id X n (push (a , x) i) = push (a , (EquivSphereSusp n) .fst x) i

  id→modifySₙ : (X : CWskel ℓ) → (n : ℕ)
    → (str X) .fst (suc (suc n)) → modifySₙ (str X) (suc (suc n))
  id→modifySₙ X n (inl x) = inl x
  id→modifySₙ X n (inr x) = inr x
  id→modifySₙ X n (push (a , x) i) =
    ((λ i → inl (e (str X) n .fst (α (str X) (suc n)
                    (a , secEq (EquivSphereSusp n) x (~ i)))))
     ∙∙ (push (a , invEq (EquivSphereSusp n) x))
     ∙∙ refl) i

  id→modifySₙ→id : (X : CWskel ℓ) (n : ℕ)
    (x : (str X) .fst (suc (suc n))) → modifySₙ→id X n (id→modifySₙ X n x) ≡ x
  id→modifySₙ→id X n (inl x) = refl
  id→modifySₙ→id X n (inr x) = refl
  id→modifySₙ→id X n (push (a , x) i) j =
    hcomp (λ k →
      λ{ (i = i0) → inl (strictifyFamα X (suc n) (a , leftInv x (j ∨ k)))
       ; (i = i1) → inr a
       ; (j = i0) → modifySₙ→id X n
                      (doubleCompPath-filler
                       (λ i → inl (e (str X) n .fst
                                    (α (str X) (suc n) (a , leftInv x (~ i)))))
                       (push (a , fun x)) refl k i)
       ; (j = i1) → push (a , x) i})
      (push (a , leftInv x j) i)
    where
      fun = invEq (EquivSphereSusp n)
      inv = (EquivSphereSusp n) .fst
      leftInv = secEq (EquivSphereSusp n)

  modifySₙ→id→modifySₙ : (X : CWskel ℓ) (n : ℕ)
    (x : modifySₙ (str X) (suc (suc n))) → id→modifySₙ X n (modifySₙ→id X n x) ≡ x
  modifySₙ→id→modifySₙ X n (inl x) = refl
  modifySₙ→id→modifySₙ X n (inr x) = refl
  modifySₙ→id→modifySₙ X n (push (a , x) i) j =
    hcomp (λ k →
     λ{ (i = i0) → inl (e (str X) n .fst (α (str X) (suc n)
                        (a , compPath→Square
                              {p = leftInv (inv x)} {refl}
                              {λ i → inv (rightInv x i)} {refl}
                              (cong (λ X → X ∙ refl)
                               (commPathIsEq (EquivSphereSusp n .snd) x)) k j)))
      ; (i = i1) → inr a
      ; (j = i0) → doubleCompPath-filler
                      (λ i → inl (e (str X) n .fst (α (str X) (suc n)
                                   (a , leftInv (inv x) (~ i)))))
                      (push (a , fun (inv x))) refl k i
      ; (j = i1) → push (a , x) i})
          (push (a , rightInv x j) i)
    where
      fun = invEq (EquivSphereSusp n)
      inv = (EquivSphereSusp n) .fst
      leftInv = secEq (EquivSphereSusp n)
      rightInv = retEq (EquivSphereSusp n)

  modifiedPushout : (n : ℕ) → Type ℓ
  modifiedPushout n = Pushout {A = B .fst (suc n)} {B = modifySₙ C (suc (suc n))}
                              {C = modifySₙ D (suc (suc n))}
                              (inl ∘ ∣ f ∣ (suc n)) (inl ∘ ∣ g ∣ (suc n))

  modifiedPushout→Pushout : (n : ℕ) → modifiedPushout n → pushoutA (suc (suc n))
  modifiedPushout→Pushout n (inl x) = inl (modifySₙ→id Cʷ n x)
  modifiedPushout→Pushout n (inr x) = inr (modifySₙ→id Dʷ n x)
  modifiedPushout→Pushout n (push a i) = push a i

  Pushout→modifiedPushout : (n : ℕ) → pushoutA (suc (suc n)) → modifiedPushout n
  Pushout→modifiedPushout n (inl x) = inl (id→modifySₙ Cʷ n x)
  Pushout→modifiedPushout n (inr x) = inr (id→modifySₙ Dʷ n x)
  Pushout→modifiedPushout n (push a i) = push a i

  Pushout→modP→Pushout : (n : ℕ) → (x : pushoutA (suc (suc n)))
    → modifiedPushout→Pushout n (Pushout→modifiedPushout n x) ≡ x
  Pushout→modP→Pushout n (inl x) j = inl (id→modifySₙ→id Cʷ n x j)
  Pushout→modP→Pushout n (inr x) j = inr (id→modifySₙ→id Dʷ n x j)
  Pushout→modP→Pushout n (push a i) j = push a i

  modP→Pushout→modP : (n : ℕ) → (x : modifiedPushout n)
    → Pushout→modifiedPushout n (modifiedPushout→Pushout n x) ≡ x
  modP→Pushout→modP n (inl x) j = inl (modifySₙ→id→modifySₙ Cʷ n x j)
  modP→Pushout→modP n (inr x) j = inr (modifySₙ→id→modifySₙ Dʷ n x j)
  modP→Pushout→modP n (push a i) j = push a i

  IsoModifiedPushout : (n : ℕ) → Iso (pushoutA (suc (suc n))) (modifiedPushout n)
  Iso.fun (IsoModifiedPushout n) = Pushout→modifiedPushout n
  Iso.inv (IsoModifiedPushout n) = modifiedPushout→Pushout n
  Iso.rightInv (IsoModifiedPushout n) = modP→Pushout→modP n
  Iso.leftInv (IsoModifiedPushout n) = Pushout→modP→Pushout n

  pushoutIsoₛ-filler0 : (n : ℕ) (b : A B n) (x : S⁻ n) → I → I → pushoutA (suc n)
  pushoutIsoₛ-filler0 n b x i j =
    doubleCompPath-filler
      (λ i → inl (∣ f ∣ (suc n) (push (b , x) (~ i))))
      (push (α B n (b , x)))
      (λ i → inr (∣ g ∣ (suc n) (push (b , x) i))) i j

  pushoutIsoₛ-filler1 : (n : ℕ) (b : A B n) (x : S⁻ n)
    → I → I → I → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-filler1 n b x i j k =
    hfill (λ k →
     λ{ (i = i0) → invSides-hfill2 (push (inl (inr b) , north))
                     (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                     (~ j) (~ k) i1
      ; (i = i1) → invSides-hfill2 (push (inl (inr b) , south))
                     (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                     (~ j) (~ k) i1
      ; (j = i0) → inl (pushoutIsoₛ-filler0 n b x (~ k) i)
      ; (j = i1) → doubleCompPath-filler
                     (push (inl (inr b) , north))
                     (λ _ → inr (inl (inr b)))
                     (λ i → push (inl (inr b) , south) (~ i)) k i})
    (inS (push (inl (inr b) , merid x i) j)) k

  pushoutIsoₛ-inv↪ : (n : ℕ) → pushoutA (suc n) → modifiedPushout n
  pushoutIsoₛ-inv↪ n (inl c) = inl (inl c)
  pushoutIsoₛ-inv↪ n (inr d) = inr (inl d)
  pushoutIsoₛ-inv↪ n (push b i) = push (inl b) i

  pushoutIsoₛ-filler2 : (n : ℕ) (b : A B n) (x : S⁻ n)
    → I → I → I → modifiedPushout n
  pushoutIsoₛ-filler2 n b x i j k =
    hfill (λ k →
      λ{ (i = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x k j)
       ; (i = i1) → push (inr b) ((~ k) ∧ j)
       ; (j = i0) → invSides-hfill1
                       (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                       (λ _ → push (inr b) i0) i (~ k) i1
       ; (j = i1) → invSides-hfill1
                       (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                       (λ i → push (inr b) (~ i)) i (~ k) i1})
          (inS (push (push (b , x) i) j)) k

  pushoutIsoₛ-filler3 : (n : ℕ) (b : A B n)
    → I → I → I → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-filler3 n b j k l =
    hfill (λ l →
      λ{ (j = i0) → inl (inr (∣ gʷ ∣ (suc n) (inr b)))
       ; (j = i1) → doubleCompPath-filler
                      (push (inl (inr b) , north))
                      (λ _ → inr (inl (inr b)))
                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l)
       ; (k = i0) → (push (inl (inr b) , north)
                 ∙∙ (λ _ → inr (inl (inr b)))
                 ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ l ∨ ~ j)
       ; (k = i1) → push (inl (inr b) , south) j})
      (inS (push (inl (inr b) , south) (j ∧ k))) l

  pushoutIsoₛ-filler4 : (n : ℕ) (b : A B n)
    → I → I → I → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-filler4 n b i k j =
    hfill (λ j →
      λ{ (i = i0) → inl (inr (∣ gʷ ∣ (suc n) (inr b)))
       ; (i = i1) → pushoutIsoₛ-filler3 n b j k i1
       ; (k = i0) → (push (inl (inr b) , north)
                 ∙∙ (λ _ → inr (inl (inr b)))
                 ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ i ∨ ~ j)
       ; (k = i1) → push (inl (inr b) , south) (i ∧ j)})
      (inS (push (inl (inr b) , south) i0)) j

  pushoutIsoₛ-fun : (n : ℕ) → modifiedPushout n → Pushout (pushoutMapₛ n) fst
  pushoutIsoₛ-fun n (inl (inl c)) = inl (inl c)
  pushoutIsoₛ-fun n (inl (inr c)) = inr (inl (inl c))
  pushoutIsoₛ-fun n (inl (push (c , x) i)) = push (inl (inl c) , x) i
  pushoutIsoₛ-fun n (inr (inl d)) = inl (inr d)
  pushoutIsoₛ-fun n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-fun n (inr (push (d , x) i)) = push (inr d , x) i
  pushoutIsoₛ-fun n (push (inl b) i) = inl (push b i)
  pushoutIsoₛ-fun n (push (inr b) i) =
    (push (inl (inr b) , north) ∙∙ refl
    ∙∙ (λ i → push (inl (inr b) , south) (~ i))) i
  pushoutIsoₛ-fun n (push (push (b , x) j) i) = pushoutIsoₛ-filler1 n b x i j i1

  pushoutIsoₛ-inv : (n : ℕ) → Pushout (pushoutMapₛ n) fst → modifiedPushout n
  pushoutIsoₛ-inv n (inl x) = pushoutIsoₛ-inv↪ n x
  pushoutIsoₛ-inv n (inr (inl (inl c))) = inl (inr c)
  pushoutIsoₛ-inv n (inr (inl (inr b))) = push (inr b) i0
  pushoutIsoₛ-inv n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-inv n (push (inl (inl c) , x) i) = inl (push (c , x) i)
  pushoutIsoₛ-inv n (push (inl (inr b) , north) i) = push (inr b) i0
  pushoutIsoₛ-inv n (push (inl (inr b) , south) i) = push (inr b) (~ i)
  pushoutIsoₛ-inv n (push (inl (inr b) , merid x j) i) =
    pushoutIsoₛ-filler2 n b x i j i1
  pushoutIsoₛ-inv n (push (inr d , x) i) = inr (push (d , x) i)

  pushoutIsoₛ-rightInv↪ : (n : ℕ) (x : pushoutA (suc n))
    → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n x) ≡ inl x
  pushoutIsoₛ-rightInv↪ n (inl c) = refl
  pushoutIsoₛ-rightInv↪ n (inr d) = refl
  pushoutIsoₛ-rightInv↪ n (push b i) = refl

  pushoutIsoₛ-rightInv : (n : ℕ) (x : Pushout (pushoutMapₛ n) fst)
    → pushoutIsoₛ-fun n (pushoutIsoₛ-inv n x) ≡ x
  pushoutIsoₛ-rightInv n (inl x) = pushoutIsoₛ-rightInv↪ n x
  pushoutIsoₛ-rightInv n (inr (inl (inl c))) = refl
  pushoutIsoₛ-rightInv n (inr (inl (inr b))) = push (inl (inr b) , north)
  pushoutIsoₛ-rightInv n (inr (inr d)) = refl
  pushoutIsoₛ-rightInv n (push (inl (inl c) , x) i) = refl
  pushoutIsoₛ-rightInv n (push (inl (inr b) , north) i) k = push (inl (inr b) , north) (i ∧ k)
  pushoutIsoₛ-rightInv n (push (inl (inr b) , south) i) k = pushoutIsoₛ-filler4 n b i k i1
  pushoutIsoₛ-rightInv n (push (inl (inr b) , merid x j) i) k =
    hcomp (λ l →
      λ{ (i = i0) → i=i0 j k l
       ; (i = i1) → doubleCompPath-filler
                      (push (inl (inr b) , north)) refl
                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l ∧ j)
       ; (j = i0) → j=i0 i k l
       ; (j = i1) → j=i1 i k l
       ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-filler2 n b x i j l)
       ; (k = i1) → push (inl (inr b) , merid x j) i})
      (pushoutIsoₛ-filler1 n b x j i (~ k))
    where
    i=i0 j=i0 j=i1 : I → I → I → Pushout (pushoutMapₛ n) fst
    i=i0 j k l = hcomp (λ i →
      λ {(j = i0) → inl (inl (∣ f ∣ (suc n) (push (b , x) (i ∧ k ∨ l))))
       ; (j = i1) → inl (inr (∣ g ∣ (suc n) (push (b , x) (i ∧ k ∨ l))))
       ; (k = i0) → pushoutIsoₛ-fun n
                      (pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x (l ∧ i) j))
       ; (k = i1) → inl (pushoutIsoₛ-filler0 n b x i j)
       ; (l = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ k) j)
       ; (l = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) k})
      (inl (push (α B n (b , x)) j))
    j=i0 i k l = hcomp (λ j →
      λ {(i = i0) → inl (inl (∣ f ∣ (suc n) (push (b , x) (k ∨ l))))
       ; (i = i1) → push (inl (inr b) , north) (k ∧ j)
       ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                        (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                        refl i (~ l) j)
       ; (k = i1) → push (inl (inr b) , north) (i ∧ j)
       ; (l = i0) → invSides-hfill2 (push (inl (inr b) , north))
                      (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                      (~ i) ( k) j
       ; (l = i1) → push (inl (inr b) , north) (i ∧ k ∧ j)})
      (inl (inl (∣ f ∣ (suc n) (push (b , x) (i ∨ k ∨ l)))))
    j=i1 i k l = hcomp (λ j →
      λ {(i = i0) → inl (inr (∣ g ∣ (suc n) (push (b , x) (k ∨ l))))
       ; (i = i1) → pushoutIsoₛ-filler3 n b j k l
       ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                        (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                        (λ i → push (inr b) (~ i)) i (~ l) j)
       ; (k = i1) → push (inl (inr b) , south) (i ∧ j)
       ; (l = i0) → invSides-hfill2 (push (inl (inr b) , south))
                      (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                      (~ i) ( k) j
       ; (l = i1) → pushoutIsoₛ-filler4 n b i k j})
      (inl (inr (∣ g ∣ (suc n) (push (b , x) (i ∨ k ∨ l)))))

  pushoutIsoₛ-rightInv n (push (inr d , x) i) = refl

  pushoutIsoₛ-leftInv : (n : ℕ) (x : modifiedPushout n)
    → pushoutIsoₛ-inv n (pushoutIsoₛ-fun n x) ≡ x
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
                   ; (k = i0) → pushoutIsoₛ-inv n
                                 (doubleCompPath-filler
                                   (push (inl (inr b) , north)) refl
                                   (λ i → push (inl (inr b) , south) (~ i)) j i)
                   ; (k = i1) → push (inr b) i })
          (push (inr b) (i ∧ k))
  pushoutIsoₛ-leftInv n (push (push (b , x) j) i) k =
    hcomp (λ l → λ {(i = i0) → i=i0 j k l
                   ; (i = i1) → i=i1 j k l
                   ; (j = i0) → pushoutIsoₛ-inv↪ n
                                  (pushoutIsoₛ-filler0 n b x ((~ k) ∧ (~ l)) i)
                   ; (k = i0) → pushoutIsoₛ-inv n
                                  (pushoutIsoₛ-filler1 n b x i j l)
                   ; (k = i1) → push (push (b , x) j) i})
          (pushoutIsoₛ-filler2 n b x j i (~ k))
    where
    i=i0 i=i1 : I → I → I → modifiedPushout n
    i=i0 j k l = hcomp (λ i →
      λ {(j = i0) → inl (inl (∣ f ∣ (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
       ; (j = i1) → inl (inl (e C n .fst (∣ f ∣ (suc n)
                               (invEq (e B n) (inr b)))))
       ; (k = i0) → pushoutIsoₛ-inv n
                       (invSides-hfill2 (push (inl (inr b) , north))
                        (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                        (~ j) (~ l) i)
       ; (k = i1) → inl (inl (∣ f ∣ (suc n) (push (b , x) j)))
       ; (l = i0) → invSides-hfill1
                      (λ i → inl (inl (∣ f ∣ (suc n) (push (b , x) (~ i)))))
                      refl (~ k) (~ j) i
       ; (l = i1) → inl (inl (∣ f ∣ (suc n) (push (b , x) j)))})
      (inl (inl (∣ f ∣ (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
    i=i1 j k l = hcomp (λ i →
      λ{ (j = i0) → inr (inl (∣ g ∣ (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
       ; (j = i1) → push (inr b) (k ∨ ~ i ∨ l)
       ; (k = i0) → pushoutIsoₛ-inv n
                      (invSides-hfill2 (push (inl (inr b) , south))
                       (λ i → inl (inr (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                       (~ j) (~ l) i)
       ; (k = i1) → inr (inl (∣ g ∣ (suc n) (push (b , x) j)))
       ; (l = i0) → invSides-hfill1
                      (λ i → inr (inl (∣ g ∣ (suc n) (push (b , x) (~ i)))))
                      (λ i → push (inr b) (~ i)) (~ k) (~ j) i
       ; (l = i1) → inr (inl (∣ g ∣ (suc n) (push (b , x) j)))})
      (inr (inl (∣ g ∣ (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))

  pushoutIsoₛ : (n : ℕ) → Iso (modifiedPushout n) (Pushout (pushoutMapₛ n) fst)
  Iso.fun (pushoutIsoₛ n) = pushoutIsoₛ-fun n
  Iso.inv (pushoutIsoₛ n) = pushoutIsoₛ-inv n
  Iso.rightInv (pushoutIsoₛ n) = pushoutIsoₛ-rightInv n
  Iso.leftInv (pushoutIsoₛ n) = pushoutIsoₛ-leftInv n

  pushoutIsoₜ : (n : ℕ) → Iso (pushoutA (suc n)) (Pushout (pushoutMap n) fst)
  pushoutIsoₜ zero = pushoutIso₀
  pushoutIsoₜ (suc n) = compIso (IsoModifiedPushout n)
                         (compIso (pushoutIsoₛ n) (invIso (pushoutₛIso n)))

  pushoutSkel : CWskel ℓ
  fst pushoutSkel = pushoutA
  fst (snd pushoutSkel) = pushoutCells
  fst (snd (snd pushoutSkel)) = pushoutMap
  fst (snd (snd (snd pushoutSkel))) = B .snd .snd .snd .fst
  snd (snd (snd (snd pushoutSkel))) n = isoToEquiv (pushoutIsoₜ n)

  f' : SequenceMap (realiseSeq B) (ShiftSeq (realiseSeq C))
  ∣_∣ f' n x = inl (∣ f ∣ n x)
  comm f' n x i = inl (comm f n x i)

  g' : SequenceMap (realiseSeq B) (ShiftSeq (realiseSeq D))
  ∣_∣ g' n x = inl (∣ g ∣ n x)
  comm g' n x i = inl (comm g n x i)

  PushoutIsoRealise :
    Iso (Pushout (realiseSequenceMap f') (realiseSequenceMap g'))
        (Pushout (realiseCellMap {C = B} {D = C} f)
                                 (realiseCellMap {C = B} {D = D} g))

  PushoutIsoRealise = pushoutIso _ _ _ _ (idEquiv _)
    (isoToEquiv (invIso (Iso-SeqColim→SeqColimSuc (realiseSeq C))))
    (isoToEquiv (invIso (Iso-SeqColim→SeqColimSuc (realiseSeq D))))
    (λ { i (incl {n = n} x) → push {n = n} (∣ f ∣ n x) (~ i)
       ; i (push {n = n} x j) → lem Bʷ Cʷ fʷ n x i j})
     λ { i (incl {n = n} x) → push {n = n} (∣ g ∣ n x) (~ i)
       ; i (push {n = n} x j) → lem Bʷ Dʷ gʷ n x i j}
    where
    module _ (Bʷ Cʷ : CWskel ℓ) (fʷ : cellMap (str Bʷ) (str Cʷ)) where
      B' = str Bʷ
      C' = str Cʷ
      f'' = strictCwMap fʷ -- strMap fʷ
      lem : (n : ℕ) (x : fst B' n)
        → Square {A = SeqColim (realiseSeq C')}
                  (cong (Iso.inv (Iso-SeqColim→SeqColimSuc (realiseSeq C')))
                        ((push {n = n} (inl (∣ f'' ∣ n x))
                       ∙ (λ i → incl {n = suc n} (inl (comm f'' n x i))))))
                  (cong (realiseCellMap {C = B'} {D = C'} f'') (push x))
                  (sym (push {n = n} (∣ f'' ∣ n x)))
                  (sym (push {n = suc n} (∣ f'' ∣ (suc n) (inl x))))
      lem n x =
        cong-∙ (Iso.inv (Iso-SeqColim→SeqColimSuc (realiseSeq C')))
               (push {n = n} (inl (∣ f'' ∣ n x)))
               (λ i → incl {n = suc n} (inl (comm f'' n x i)))
        ◁ (sym (rUnit _)
        ◁ (invSides-filler {A = SeqColim (realiseSeq C')}
             (push {n = suc n} (∣ f'' ∣ (suc n) (inl x)))
             (sym (push {n = n} (∣ f'' ∣ n x)))
        ▷ rUnit _))

  SeqIs : SequenceIso (ShiftSeq (realiseSeq pushoutSkel))
                      (PushoutSequence f' g')
  fst SeqIs n = idIso
  snd SeqIs n (inl x) = refl
  snd SeqIs n (inr x) = refl
  snd SeqIs n (push a i) j =
    doubleCompPath-filler
      ((λ i₁ → inl (inl (comm f n a i₁))))
      (push (CW↪ B n a))
      (λ i₁ → inr (inl (comm g n a (~ i₁)))) (~ j) i

  realisePushoutSkel : Iso (realise pushoutSkel)
                           (Pushout (realiseCellMap {C = B} {D = C} f)
                                    (realiseCellMap {C = B} {D = D} g))
  realisePushoutSkel =
    compIso (Iso-SeqColim→SeqColimSuc _)
      (compIso (sequenceEquiv→ColimIso
                (SequenceIso→SequenceEquiv SeqIs))
       (compIso (invIso (Iso-PushoutColim-ColimPushout f' g'))
         PushoutIsoRealise))

  hasCWskelPushout : hasCWskel (Pushout (realiseCellMap {C = B} {D = C} f)
                                        (realiseCellMap {C = B} {D = D} g))
  fst hasCWskelPushout = pushoutSkel
  snd hasCWskelPushout = isoToEquiv (invIso realisePushoutSkel)

  hasFinCWskelPushout : isFinCWskel B → isFinCWskel C → isFinCWskel D
    → isFinCWskel pushoutSkel
  fst (hasFinCWskelPushout (dimB , eB) (dimC , eC) (dimD , eD)) =
    suc (dimB +ℕ (dimC +ℕ dimD))
  snd (hasFinCWskelPushout (dimB , eB) (dimC , eC) (dimD , eD)) =
    λ k → transport (λ j
        → isEquiv (CW↪ pushoutSkel (+-suc k (dimB +ℕ (dimC +ℕ dimD)) (~ j))))
            (subst isEquiv (funExt
              (λ { (inl x) → refl
                 ; (inr x) → refl
                 ; (push a i) j → rUnit (push (inl a)) (~ j) i}))
      (pushoutEquiv _ _ _ _
        (inl , subst (isEquiv ∘ CW↪ B)
                     (sym (+-assoc k (dimC +ℕ dimD) dimB)
                     ∙ cong (k +ℕ_) (+-comm (dimC +ℕ dimD) dimB))
        (eB (k +ℕ (dimC +ℕ dimD))))
        (inl , subst (isEquiv ∘ CW↪ C)
                     (cong suc (sym (+-assoc (k +ℕ dimD) dimB dimC)
                              ∙ sym (+-assoc k dimD (dimB +ℕ dimC))
                              ∙ cong (k +ℕ_ ) (+-comm dimD _
                              ∙ sym (+-assoc dimB dimC dimD))))
                     (eC (suc (k +ℕ dimD +ℕ dimB))))
        (inl , subst (isEquiv ∘ CW↪ D)
                     (cong suc (sym (+-assoc (k +ℕ dimC) dimB dimD)
                              ∙ sym (+-assoc k dimC (dimB +ℕ dimD))
                              ∙ cong (k +ℕ_) (+-assoc dimC dimB dimD
                              ∙ cong (_+ℕ dimD) (+-comm dimC dimB)
                              ∙ sym (+-assoc dimB dimC dimD))))
                     (eD (suc (k +ℕ dimC +ℕ dimB))))
        refl
        refl .snd))

isFinCWPushout : ∀ {ℓ} (B C D : finCW ℓ)
  (f : finCW→CW B →ᶜʷ finCW→CW C) (g : finCW→CW B →ᶜʷ finCW→CW D)
  → isFinCW (Pushout f g)
isFinCWPushout {ℓ = ℓ} =
   uncurry λ B  → PT.elim (λ _ → isPropΠ4 λ _ _ _ _ → squash₁) λ isFinCWB
    → uncurry λ C → PT.elim (λ _ → isPropΠ3 λ _ _ _ → squash₁) λ isCWC
      → uncurry λ D → PT.elim (λ _ → isPropΠ2 λ _ _ → squash₁) λ isCWD
        → subst (λ B∞ → (f : B∞ → C) (g : B∞ → D)
          → isFinCW (Pushout f g))
                (sym (ua (isFinCWB .snd .snd)))
           (subst2 (λ C∞ D∞ → (f : realise ((isFinCWB .snd .fst .fst)
                                          , (isFinCWB .snd .fst .snd .fst)) → C∞)
                               (g : realise ((isFinCWB .snd .fst .fst)
                                          , (isFinCWB .snd .fst .snd .fst)) → D∞)
                           → isFinCW (Pushout f g))
            (sym (ua (isCWC .snd .snd)))
            (sym (ua (isCWD .snd .snd)))
            λ f g → PT.rec squash₁ (λ {(f' , fid)
              → PT.rec squash₁ (λ {(g' , gid)
                → subst2 (λ f g → isFinCW (Pushout f g))
                         fid gid
                    ∣ main (hasFinCWskel→hasCWskel _ isFinCWB .fst)
                           (hasFinCWskel→hasCWskel _ isCWC .fst)
                           (hasFinCWskel→hasCWskel _ isCWD .fst)
                           (_ , isFinCWB .snd .fst .snd .snd)
                           (_ , isCWC .snd .fst .snd .snd)
                           (_ , isCWD .snd .fst .snd .snd) _ _ ∣₁})
                (finCWmap→CellMap (isFinCWB .fst) (isFinCWB .snd .fst)
                 (hasFinCWskel→hasCWskel _ isCWD .fst) g)})
               (finCWmap→CellMap (isFinCWB .fst) (isFinCWB .snd .fst)
                 (hasFinCWskel→hasCWskel _ isCWC .fst) f))
  where
  main : ∀ {ℓ} (B C D : CWskel ℓ)
       → isFinCWskel B
       → isFinCWskel C
       → isFinCWskel D
       → (f' : cellMap B C) (g' : cellMap B D)
       → hasFinCWskel (Pushout (realiseCellMap {C = B} {D = C} f')
                        (realiseCellMap {C = B} {D = D} g'))
  main = elimStrictCW λ B → elimStrictCW λ C → elimStrictCW λ D
    → λ fB fC fD f' g'
    → subst2 (λ f' g'
       → hasFinCWskel (Pushout (realiseCellMap {C = str B} {D = str C}  f')
                       (realiseCellMap {C = str B} {D = str D}  g')))
          (strictCwMap≡ f') (strictCwMap≡ g')
          ((CWPushout.hasFinCWskelPushout _ B C D f' g' fB fC fD .fst)
         , ((CWPushout.hasCWskelPushout _ B C D f' g' .fst .fst
         , (CWPushout.hasCWskelPushout _ B C D f' g' .fst .snd
         , (CWPushout.hasFinCWskelPushout _ B C D f' g' fB fC fD .snd)))
         , CWPushout.hasCWskelPushout _ B C D f' g' .snd))

isPushoutᶜʷ : ∀ {ℓ} (B : finCW ℓ) (C D : CW ℓ)
  (f : finCW→CW B →ᶜʷ C) (g : finCW→CW B →ᶜʷ D)
  → isCW (Pushout f g)
isPushoutᶜʷ {ℓ = ℓ} = uncurry λ B
  → PT.elim (λ _ → isPropΠ4 λ _ _ _ _ → squash₁) λ isFinCWB
    → uncurry λ C → PT.elim (λ _ → isPropΠ3 λ _ _ _ → squash₁) λ isCWC
      → uncurry λ D → PT.elim (λ _ → isPropΠ2 λ _ _ → squash₁) λ isCWD
        → subst (λ B∞ → (f : B∞ → C) (g : B∞ → D)
          → isCW (Pushout f g))
                (sym (ua (isFinCWB .snd .snd)))
           (subst2 (λ C∞ D∞ → (f : realise ((isFinCWB .snd .fst .fst)
                                          , (isFinCWB .snd .fst .snd .fst)) → C∞)
                               (g : realise ((isFinCWB .snd .fst .fst)
                                          , (isFinCWB .snd .fst .snd .fst)) → D∞)
                           → isCW (Pushout f g))
            (sym (ua (isCWC .snd)))
            (sym (ua (isCWD .snd)))
            λ f g → PT.rec squash₁ (λ {(f' , fid)
              → PT.rec squash₁ (λ {(g' , gid)
                → subst2 (λ f g → isCW (Pushout f g))
                         fid gid
                    ∣ main (isFinCWB .snd .fst .fst , isFinCWB .snd .fst .snd .fst)
                           (isCWC .fst) (isCWD .fst) f' g' ∣₁})
                (finCWmap→CellMap (isFinCWB .fst) (isFinCWB .snd .fst)
                 (fst isCWD) g)})
               (finCWmap→CellMap (isFinCWB .fst) (isFinCWB .snd .fst)
                 (fst isCWC) f))
  where
  main : ∀ {ℓ} (B C D : CWskel ℓ) (f' : cellMap B C) (g' : cellMap B D)
       → hasCWskel (Pushout (realiseCellMap {C = B} {D = C} f')
                             (realiseCellMap {C = B} {D = D} g'))
  main = elimStrictCW λ B → elimStrictCW λ C → elimStrictCW λ D
    → λ f' g'
    → subst2 (λ f' g'
       → hasCWskel (Pushout (realiseCellMap {C = str B} {D = str C}  f')
                       (realiseCellMap {C = str B} {D = str D}  g')))
       (strictCwMap≡ f') (strictCwMap≡ g')
       (CWPushout.hasCWskelPushout _ B C D f' g')

-- Consequence: elimination principle for predicates stable under
-- pushouts (suggested by Reid Barton)
module _ {ℓ ℓ' : Level} (P : Type ℓ → Type ℓ') (P1 : P Unit*) (P0 : P ⊥*)
         (Ppush : (A B C : Type ℓ) (f : A → B) (g : A → C)
                → P A → P B → P C → P (Pushout f g)) where
  private
   PFin1 : P (Lift (Fin 1))
   PFin1 = subst P (cong Lift (isoToPath Iso-Unit-Fin1)) P1

   P⊎ : {B C : Type ℓ} → P B → P C → P (B ⊎ C)
   P⊎ {B = B} {C} pB pC =
     subst P (isoToPath
       (compIso (pushoutIso _ _ _ _
         (invEquiv LiftEquiv) (idEquiv _) (idEquiv _) refl refl)
         PushoutEmptyDomainIso))
             (Ppush ⊥* B C (λ ()) (λ ()) P0 pB pC)

   PFin : (n : ℕ) → P (Lift (Fin n))
   PFin zero =
     subst P
       (cong Lift
         (ua (propBiimpl→Equiv isProp⊥
              (λ x → ⊥.rec (¬Fin0 x)) (λ()) ¬Fin0)))
       P0
   PFin (suc n) =
     subst P (cong Lift (sym (isoToPath Iso-Fin-Unit⊎Fin)))
       (subst P (isoToPath (Lift⊎Iso ℓ))
         (P⊎ P1 (PFin n)))

   PS : (n : ℕ) → P (Lift (S⁻ n))
   PS zero = P0
   PS (suc zero) = subst P (cong Lift (isoToPath (invIso Iso-Bool-Fin2))) (PFin 2)
   PS (suc (suc n)) =
     subst P
       (cong Lift (isoToPath (compIso PushoutSuspIsoSusp (invIso (IsoSucSphereSusp n)))))
       (subst P (isoToPath (LiftPushoutIso ℓ))
         (Ppush (Lift (S₊ n)) Unit* Unit* (λ _ → tt*) (λ _ → tt*)
           (PS (suc n)) P1 P1))

   PFin×S : (n m : ℕ) → P (Lift (Fin n × S⁻ m))
   PFin×S zero m =
     subst P (ua (compEquiv (uninhabEquiv (λ()) λ()) LiftEquiv)) P0
   PFin×S (suc n) m = subst P (isoToPath is) (P⊎ (PS m) (PFin×S n m))
     where
     is : Iso (Lift (S⁻ m) ⊎ Lift (Fin n × S⁻ m))
               (Lift (Fin (suc n) × S⁻ m))
     is =
       compIso (Lift⊎Iso ℓ)
        (compIso (invIso LiftIso)
          (compIso
            (compIso (compIso (⊎Iso (invIso rUnit×Iso) Σ-swap-Iso)
                        (compIso (invIso ×DistR⊎Iso) Σ-swap-Iso))
                        (Σ-cong-iso-fst (invIso Iso-Fin-Unit⊎Fin)))
             LiftIso))

   PCWskel : (B : CWskel ℓ) → (n : ℕ) → P (fst B n)
   PCWskel B zero = subst P (ua (uninhabEquiv (λ()) (CW₀-empty B))) P0
   PCWskel B (suc n) =
     subst P
       (ua (compEquiv
            (pushoutEquiv _ _ _ _
              (invEquiv LiftEquiv) (idEquiv _) (invEquiv LiftEquiv)
              refl refl)
            (invEquiv (B .snd .snd .snd .snd n))))
       (Ppush _ _ _
        (λ { (lift r) → CWskel-fields.α B n r}) (liftFun fst)
        (PFin×S (CWskel-fields.card B n) n)
          (PCWskel B n) (PFin (CWskel-fields.card B n)))

  elimPropFinCWFun : (B : Type ℓ) → hasFinCWskel B → P B
  elimPropFinCWFun B fCWB =
    subst P (ua (compEquiv (isoToEquiv (realiseFin _ (fCWB .snd .fst)))
            (invEquiv (fCWB .snd .snd))))
            (PCWskel (finCWskel→CWskel _ (fCWB .snd .fst)) (fCWB .fst))

  -- main result
  elimPropFinCW : (B : finCW ℓ) → isProp (P (fst B)) → P (fst B)
  elimPropFinCW (B , Bstr) isp = PT.rec isp (elimPropFinCWFun B) Bstr
