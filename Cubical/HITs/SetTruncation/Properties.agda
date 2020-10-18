{-

This file contains:

- Properties of set truncations

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.SetTruncation.Properties where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ

rec : isSet B → (A → B) → ∥ A ∥₂ → B
rec Bset f ∣ x ∣₂ = f x
rec Bset f (squash₂ x y p q i j) =
  Bset _ _ (cong (rec Bset f) p) (cong (rec Bset f) q) i j

rec2 : isSet C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
rec2 Cset f ∣ x ∣₂ ∣ y ∣₂ = f x y
rec2 Cset f ∣ x ∣₂ (squash₂ y z p q i j) =
  Cset _ _ (cong (rec2 Cset f ∣ x ∣₂) p) (cong (rec2 Cset f ∣ x ∣₂) q) i j
rec2 Cset f (squash₂ x y p q i j) z =
  Cset _ _ (cong (λ a → rec2 Cset f a z) p) (cong (λ a → rec2 Cset f a z) q) i j

-- Old version:
-- rec2 Cset f = rec (isSetΠ λ _ → Cset) λ x → rec Cset (f x)

-- lemma 6.9.1 in HoTT book
elim : {B : ∥ A ∥₂ → Type ℓ}
       (Bset : (x : ∥ A ∥₂) → isSet (B x))
       (f : (a : A) → B (∣ a ∣₂))
       (x : ∥ A ∥₂) → B x
elim Bset f ∣ a ∣₂ = f a
elim Bset f (squash₂ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset _ _
    (cong (elim Bset f) p) (cong (elim Bset f) q) (squash₂ x y p q) i j

elim2 : {C : ∥ A ∥₂ → ∥ B ∥₂ → Type ℓ}
        (Cset : ((x : ∥ A ∥₂) (y : ∥ B ∥₂) → isSet (C x y)))
        (f : (a : A) (b : B) → C ∣ a ∣₂ ∣ b ∣₂)
        (x : ∥ A ∥₂) (y : ∥ B ∥₂) → C x y
elim2 Cset f ∣ x ∣₂ ∣ y ∣₂ = f x y
elim2 Cset f ∣ x ∣₂ (squash₂ y z p q i j) =
  isOfHLevel→isOfHLevelDep 2 (λ a → Cset ∣ x ∣₂ a) _ _
     (cong (elim2 Cset f ∣ x ∣₂) p) (cong (elim2 Cset f ∣ x ∣₂) q) (squash₂ y z p q) i j
elim2 Cset f (squash₂ x y p q i j) z =
  isOfHLevel→isOfHLevelDep 2 (λ a → Cset a z) _ _
    (cong (λ a → elim2 Cset f a z) p) (cong (λ a → elim2 Cset f a z) q) (squash₂ x y p q) i j

-- Old version:
-- elim2 Cset f = elim (λ _ → isSetΠ (λ _ → Cset _ _))
--                     (λ a → elim (λ _ → Cset _ _) (f a))

-- TODO: generalize
elim3 : {B : (x y z : ∥ A ∥₂) → Type ℓ}
        (Bset : ((x y z : ∥ A ∥₂) → isSet (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₂ ∣ b ∣₂ ∣ c ∣₂)
        (x y z : ∥ A ∥₂) → B x y z
elim3 Bset g = elim2 (λ _ _ → isSetΠ (λ _ → Bset _ _ _))
                     (λ a b → elim (λ _ → Bset _ _ _) (g a b))

setTruncUniversal : isSet B → (∥ A ∥₂ → B) ≃ (A → B)
setTruncUniversal {B = B} Bset =
  isoToEquiv (iso (λ h x → h ∣ x ∣₂) (rec Bset) (λ _ → refl) rinv)
  where
  rinv : (f : ∥ A ∥₂ → B) → rec Bset (λ x → f ∣ x ∣₂) ≡ f
  rinv f i x =
    elim (λ x → isProp→isSet (Bset (rec Bset (λ x → f ∣ x ∣₂) x) (f x)))
         (λ _ → refl) x i

setTruncIsSet : isSet ∥ A ∥₂
setTruncIsSet a b p q = squash₂ a b p q

setTruncIdempotent≃ : isSet A → ∥ A ∥₂ ≃ A
setTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₂ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₂
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isSet→isGroupoid setTruncIsSet _ _) (λ _ → refl)

setTruncIdempotent : isSet A → ∥ A ∥₂ ≡ A
setTruncIdempotent hA = ua (setTruncIdempotent≃ hA)

isContr→isContrSetTrunc : isContr A → isContr (∥ A ∥₂)
isContr→isContrSetTrunc contr = ∣ fst contr ∣₂
                                , elim (λ _ → isOfHLevelPath 2 (setTruncIsSet) _ _)
                                       λ a → cong ∣_∣₂ (snd contr a)


setTruncIso : Iso A B → Iso ∥ A ∥₂ ∥ B ∥₂
Iso.fun (setTruncIso is) = rec setTruncIsSet (λ x → ∣ Iso.fun is x ∣₂)
Iso.inv (setTruncIso is) = rec setTruncIsSet (λ x → ∣ Iso.inv is x ∣₂)
Iso.rightInv (setTruncIso is) =
  elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ a → cong ∣_∣₂ (Iso.rightInv is a)
Iso.leftInv (setTruncIso is) =
  elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ a → cong ∣_∣₂ (Iso.leftInv is a)

setSigmaIso : {B : A → Type ℓ} → Iso ∥ Σ A B ∥₂ ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂
setSigmaIso {A = A} {B = B} = iso fun funinv sect retr
  where
  {- writing it out explicitly to avoid yellow highlighting -}
  fun : ∥ Σ A B ∥₂ → ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂
  fun = rec setTruncIsSet λ {(a , p) → ∣ a , ∣ p ∣₂ ∣₂}
  funinv : ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂ → ∥ Σ A B ∥₂
  funinv = rec setTruncIsSet (λ {(a , p) → rec setTruncIsSet (λ p → ∣ a , p ∣₂) p})
  sect : section fun funinv
  sect = elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
              λ { (a , p) → elim {B = λ p → fun (funinv ∣ a , p ∣₂) ≡ ∣ a , p ∣₂}
              (λ p → isOfHLevelPath 2 setTruncIsSet _ _) (λ _ → refl) p }
  retr : retract fun funinv
  retr = elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
              λ { _ → refl }

sigmaElim : {B : ∥ A ∥₂ → Type ℓ} {C : Σ ∥ A ∥₂ B  → Type ℓ'}
            (Bset : (x : Σ ∥ A ∥₂ B) → isSet (C x))
            (g : (a : A) (b : B ∣ a ∣₂) → C (∣ a ∣₂ , b))
            (x : Σ ∥ A ∥₂ B) → C x
sigmaElim {B = B} {C = C} set g (x , y) =
  elim {B = λ x → (y : B x) → C (x , y)} (λ _ → isSetΠ λ _ → set _) g x y

sigmaProdElim : {C : ∥ A ∥₂ × ∥ B ∥₂ → Type ℓ} {D : Σ (∥ A ∥₂ × ∥ B ∥₂) C  → Type ℓ'}
                (Bset : (x : Σ (∥ A ∥₂ × ∥ B ∥₂) C) → isSet (D x))
                (g : (a : A) (b : B) (c : C (∣ a ∣₂ , ∣ b ∣₂)) → D ((∣ a ∣₂ , ∣ b ∣₂) , c))
                (x : Σ (∥ A ∥₂ × ∥ B ∥₂) C) → D x
sigmaProdElim {B = B} {C = C} {D = D} set g ((x , y) , c) =
  elim {B = λ x → (y : ∥ B ∥₂) (c : C (x , y)) → D ((x , y) , c)}
       (λ _ → isSetΠ λ _ → isSetΠ λ _ → set _)
       (λ x → elim (λ _ → isSetΠ λ _ → set _) (g x))
       x y c

prodElim : {C : ∥ A ∥₂ × ∥ B ∥₂ → Type ℓ}
         → ((x : ∥ A ∥₂ × ∥ B ∥₂) → isSet (C x))
         → ((a : A) (b : B) → C (∣ a ∣₂ , ∣ b ∣₂))
         → (x : ∥ A ∥₂ × ∥ B ∥₂) → C x
prodElim setC f (a , b) = elim2 (λ x y → setC (x , y)) f a b

prodRec : {C : Type ℓ} → isSet C → (A → B → C) → ∥ A ∥₂ × ∥ B ∥₂ → C
prodRec setC f (a , b) = rec2 setC f a b

prodElim2 : {E : (∥ A ∥₂ × ∥ B ∥₂) → (∥ C ∥₂ × ∥ D ∥₂) → Type ℓ}
         → ((x : ∥ A ∥₂ × ∥ B ∥₂) (y : ∥ C ∥₂ × ∥ D ∥₂) → isSet (E x y))
         → ((a : A) (b : B) (c : C) (d : D) → E (∣ a ∣₂ , ∣ b ∣₂) (∣ c ∣₂ , ∣ d ∣₂))
         → ((x : ∥ A ∥₂ × ∥ B ∥₂) (y : ∥ C ∥₂ × ∥ D ∥₂) → (E x y))
prodElim2 isset f = prodElim (λ _ → isSetΠ λ _ → isset _ _)
                             λ a b → prodElim (λ _ → isset _ _)
                                     λ c d → f a b c d

setTruncOfProdIso :  Iso ∥ A × B ∥₂ (∥ A ∥₂ × ∥ B ∥₂)
Iso.fun setTruncOfProdIso = rec (isSet× setTruncIsSet setTruncIsSet) λ { (a , b) → ∣ a ∣₂ , ∣ b ∣₂ }
Iso.inv setTruncOfProdIso = prodRec setTruncIsSet λ a b → ∣ a , b ∣₂
Iso.rightInv setTruncOfProdIso =
  prodElim (λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _) λ _ _ → refl
Iso.leftInv setTruncOfProdIso =
  elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ {(a , b) → refl}
