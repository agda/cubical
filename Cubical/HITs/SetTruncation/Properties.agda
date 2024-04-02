{-

This file contains:

- Properties of set truncations

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SetTruncation.Properties where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed.Base
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim) hiding (elim2 ; elim3 ; rec2 ; map)

private
  variable
    ℓ ℓ' ℓ'' ℓa ℓb ℓc ℓd : Level
    A : Type ℓa
    B : Type ℓb
    C : Type ℓc
    D : Type ℓd

isSetPathImplicit : {x y : ∥ A ∥₂} → isSet (x ≡ y)
isSetPathImplicit = isOfHLevelPath 2 squash₂ _ _

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
elim3 : {D : ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂ → Type ℓ}
        (Dset : ((x : ∥ A ∥₂) (y : ∥ B ∥₂) (z : ∥ C ∥₂) → isSet (D x y z)))
        (g : (a : A) (b : B) (c : C) → D ∣ a ∣₂ ∣ b ∣₂ ∣ c ∣₂)
        (x : ∥ A ∥₂) (y : ∥ B ∥₂) (z : ∥ C ∥₂) → D x y z
elim3 Dset g = elim2 (λ _ _ → isSetΠ (λ _ → Dset _ _ _))
                     (λ a b → elim (λ _ → Dset _ _ _) (g a b))

elim4 : {E : ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂ → ∥ D ∥₂ → Type ℓ}
        (Eset : ((w : ∥ A ∥₂) (x : ∥ B ∥₂) (y : ∥ C ∥₂) (z : ∥ D ∥₂)
              → isSet (E w x y z)))
        (g : (a : A) (b : B) (c : C) (d : D) → E ∣ a ∣₂ ∣ b ∣₂ ∣ c ∣₂ ∣ d ∣₂)
        (w : ∥ A ∥₂) (x : ∥ B ∥₂) (y : ∥ C ∥₂) (z : ∥ D ∥₂) → E w x y z
elim4 Eset g = elim3 (λ _ _ _ → isSetΠ λ _ → Eset _ _ _ _)
                     λ a b c → elim (λ _ → Eset _ _ _ _) (g a b c)


-- the recursor for maps into groupoids following the "HIT proof" in:
-- https://arxiv.org/abs/1507.01150
-- i.e. for any type A and groupoid B we can construct a map ∥ A ∥₂ → B
-- from a map A → B satisfying the condition
--    ∀ (a b : A) (p q : a ≡ b) → cong f p ≡ cong f q
-- TODO: prove that this is an equivalence
module rec→Gpd {A : Type ℓ} {B : Type ℓ'} (Bgpd : isGroupoid B) (f : A → B)
               (congFConst : ∀ (a b : A) (p q : a ≡ b) → cong f p ≡ cong f q) where

 data H : Type ℓ where
  η : A → H
  ε : ∀ (a b : A) → ∥ a ≡ b ∥₁ → η a ≡ η b -- prop. trunc. of a≡b
  δ : ∀ (a b : A) (p : a ≡ b) → ε a b ∣ p ∣₁ ≡ cong η p
  gtrunc : isGroupoid H

 -- write elimination principle for H
 module Helim {P : H → Type ℓ''} (Pgpd : ∀ h → isGroupoid (P h))
              (η* : (a : A) → P (η a))
              (ε* : ∀ (a b : A) (∣p∣₁ : ∥ a ≡ b ∥₁)
                  → PathP (λ i → P (ε a b ∣p∣₁ i)) (η* a) (η* b))
              (δ* : ∀ (a b : A) (p : a ≡ b)
                  → PathP (λ i → PathP (λ j → P (δ a b p i j)) (η* a) (η* b))
                          (ε* a b ∣ p ∣₁) (cong η* p)) where

  fun : (h : H) → P h
  fun (η a) = η* a
  fun (ε a b ∣p∣₁ i) = ε* a b ∣p∣₁ i
  fun (δ a b p i j) = δ* a b p i j
  fun (gtrunc x y p q α β i j k) = isOfHLevel→isOfHLevelDep 3 Pgpd
                                   (fun x) (fun y)
                                   (cong fun p) (cong fun q)
                                   (cong (cong fun) α) (cong (cong fun) β)
                                   (gtrunc x y p q α β) i j k

 module Hrec {C : Type ℓ''} (Cgpd : isGroupoid C)
             (η* : A → C)
             (ε* : ∀ (a b : A) → ∥ a ≡ b ∥₁ → η* a ≡ η* b)
             (δ* : ∀ (a b : A) (p : a ≡ b) → ε* a b ∣ p ∣₁ ≡ cong η* p) where

  fun : H → C
  fun (η a) = η* a
  fun (ε a b ∣p∣₁ i) = ε* a b ∣p∣₁ i
  fun (δ a b p i j) = δ* a b p i j
  fun (gtrunc x y p q α β i j k) = Cgpd (fun x) (fun y) (cong fun p) (cong fun q)
                                   (cong (cong fun) α) (cong (cong fun) β) i j k

 module HelimProp {P : H → Type ℓ''} (Pprop : ∀ h → isProp (P h))
                  (η* : (a : A) → P (η a)) where

  fun : ∀ h → P h
  fun = Helim.fun (λ _ → isSet→isGroupoid (isProp→isSet (Pprop _))) η*
                  (λ a b ∣p∣₁ → isOfHLevel→isOfHLevelDep 1 Pprop _ _ (ε a b ∣p∣₁))
                   λ a b p → isOfHLevel→isOfHLevelDep 1
                              {B = λ p → PathP (λ i → P (p i)) (η* a) (η* b)}
                              (λ _ → isOfHLevelPathP 1 (Pprop _) _ _) _ _ (δ a b p)

 -- The main trick: eliminating into hsets is easy
 -- i.e. H has the universal property of set truncation...
 module HelimSet {P : H → Type ℓ''} (Pset : ∀ h → isSet (P h))
                 (η* : ∀ a → P (η a)) where

  fun : (h : H) → P h
  fun = Helim.fun (λ _ → isSet→isGroupoid (Pset _)) η* ε*
                   λ a b p → isOfHLevel→isOfHLevelDep 1
                             {B = λ p → PathP (λ i → P (p i)) (η* a) (η* b)}
                             (λ _ → isOfHLevelPathP' 1 (Pset _) _ _) _ _ (δ a b p)
   where
   ε* : (a b : A) (∣p∣₁ : ∥ a ≡ b ∥₁) → PathP (λ i → P (ε a b ∣p∣₁ i)) (η* a) (η* b)
   ε* a b = pElim (λ _ → isOfHLevelPathP' 1 (Pset _) (η* a) (η* b))
                   λ p → subst (λ x → PathP (λ i → P (x i)) (η* a) (η* b))
                               (sym (δ a b p)) (cong η* p)


 -- Now we need to prove that H is a set.
 -- We start with a  little lemma:
 localHedbergLemma : {X : Type ℓ''} (P : X → Type ℓ'')
                   → (∀ x → isProp (P x))
                   → ((x : X) → P x → (y : X) → P y → x ≡ y)
                  --------------------------------------------------
                   → (x : X) → P x → (y : X) → isProp (x ≡ y)
 localHedbergLemma {X = X} P Pprop P→≡ x px y = isPropRetract
                   (λ p → subst P p px) (λ py → sym (P→≡ x px x px) ∙ P→≡ x px y py)
                   isRetract (Pprop y)
  where
  isRetract : (p : x ≡ y) → (sym (P→≡ x px x px)) ∙ P→≡ x px y (subst P p px) ≡ p
  isRetract = J (λ y' p' → (sym (P→≡ x px x px)) ∙ P→≡ x px y' (subst P p' px) ≡ p')
                (subst (λ px' → sym (P→≡ x px x px) ∙ P→≡ x px x px' ≡ refl)
                (sym (substRefl {B = P} px)) (lCancel (P→≡ x px x px)))

 Hset : isSet H
 Hset = HelimProp.fun (λ _ → isPropΠ λ _ → isPropIsProp) baseCaseLeft
  where
  baseCaseLeft : (a₀ : A) (y : H) → isProp (η a₀ ≡ y)
  baseCaseLeft a₀ = localHedbergLemma (λ x → Q x .fst) (λ x → Q x .snd) Q→≡ _ ∣ refl ∣₁
   where
   Q : H → hProp ℓ
   Q = HelimSet.fun (λ _ → isSetHProp) λ b → ∥ a₀ ≡ b ∥₁ , isPropPropTrunc
   -- Q (η b) = ∥ a ≡ b ∥₁

   Q→≡ : (x : H) → Q x .fst → (y : H) → Q y .fst → x ≡ y
   Q→≡ = HelimSet.fun (λ _ → isSetΠ3 λ _ _ _ → gtrunc _ _)
       λ a p → HelimSet.fun (λ _ → isSetΠ λ _ → gtrunc _ _)
       λ b q → sym (ε a₀ a p) ∙ ε a₀ b q

 -- our desired function will split through H,
 -- i.e. we get a function ∥ A ∥₂ → H → B
 fun : ∥ A ∥₂ → B
 fun = f₁ ∘ f₂
  where
  f₁ : H → B
  f₁ = Hrec.fun Bgpd f εᶠ λ _ _ _ → refl
   where
   εᶠ : (a b : A) → ∥ a ≡ b ∥₁ → f a ≡ f b
   εᶠ a b = rec→Set (Bgpd _ _) (cong f) λ p q → congFConst a b p q
   -- this is the inductive step,
   -- we use that maps ∥ A ∥₁ → B for an hset B
   -- correspond to 2-Constant maps A → B (which cong f is by assumption)
  f₂ : ∥ A ∥₂ → H
  f₂ = rec Hset η


map : (A → B) → ∥ A ∥₂ → ∥ B ∥₂
map f = rec squash₂ λ x → ∣ f x ∣₂

map∙ : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
       (f : A →∙ B) → ∥ A ∥₂∙ →∙ ∥ B ∥₂∙
fst (map∙ f) = map (fst f)
snd (map∙ f) = cong ∣_∣₂ (snd f)

setTruncUniversal : isSet B → (∥ A ∥₂ → B) ≃ (A → B)
setTruncUniversal {B = B} Bset =
  isoToEquiv (iso (λ h x → h ∣ x ∣₂) (rec Bset) (λ _ → refl) rinv)
  where
  rinv : (f : ∥ A ∥₂ → B) → rec Bset (λ x → f ∣ x ∣₂) ≡ f
  rinv f i x =
    elim (λ x → isProp→isSet (Bset (rec Bset (λ x → f ∣ x ∣₂) x) (f x)))
         (λ _ → refl) x i

isSetSetTrunc : isSet ∥ A ∥₂
isSetSetTrunc a b p q = squash₂ a b p q

setTruncIdempotentIso : isSet A → Iso ∥ A ∥₂ A
Iso.fun (setTruncIdempotentIso hA) = rec hA (idfun _)
Iso.inv (setTruncIdempotentIso hA) x = ∣ x ∣₂
Iso.rightInv (setTruncIdempotentIso hA) _ = refl
Iso.leftInv (setTruncIdempotentIso hA) = elim (λ _ → isSet→isGroupoid isSetSetTrunc _ _) (λ _ → refl)

setTruncIdempotent≃ : isSet A → ∥ A ∥₂ ≃ A
setTruncIdempotent≃ {A = A} hA = isoToEquiv (setTruncIdempotentIso hA)

setTruncIdempotent : isSet A → ∥ A ∥₂ ≡ A
setTruncIdempotent hA = ua (setTruncIdempotent≃ hA)

isContr→isContrSetTrunc : isContr A → isContr (∥ A ∥₂)
isContr→isContrSetTrunc contr = ∣ fst contr ∣₂
                                , elim (λ _ → isOfHLevelPath 2 (isSetSetTrunc) _ _)
                                       λ a → cong ∣_∣₂ (snd contr a)


setTruncIso : Iso A B → Iso ∥ A ∥₂ ∥ B ∥₂
Iso.fun (setTruncIso is) = rec isSetSetTrunc (λ x → ∣ Iso.fun is x ∣₂)
Iso.inv (setTruncIso is) = rec isSetSetTrunc (λ x → ∣ Iso.inv is x ∣₂)
Iso.rightInv (setTruncIso is) =
  elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
        λ a → cong ∣_∣₂ (Iso.rightInv is a)
Iso.leftInv (setTruncIso is) =
  elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
        λ a → cong ∣_∣₂ (Iso.leftInv is a)

setSigmaIso : {B : A → Type ℓ} → Iso ∥ Σ A B ∥₂ ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂
setSigmaIso {A = A} {B = B} = iso fun funinv sect retr
  where
  {- writing it out explicitly to avoid yellow highlighting -}
  fun : ∥ Σ A B ∥₂ → ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂
  fun = rec isSetSetTrunc λ {(a , p) → ∣ a , ∣ p ∣₂ ∣₂}
  funinv : ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂ → ∥ Σ A B ∥₂
  funinv = rec isSetSetTrunc (λ {(a , p) → rec isSetSetTrunc (λ p → ∣ a , p ∣₂) p})
  sect : section fun funinv
  sect = elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
              λ { (a , p) → elim {B = λ p → fun (funinv ∣ a , p ∣₂) ≡ ∣ a , p ∣₂}
              (λ p → isOfHLevelPath 2 isSetSetTrunc _ _) (λ _ → refl) p }
  retr : retract fun funinv
  retr = elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
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
Iso.fun setTruncOfProdIso = rec (isSet× isSetSetTrunc isSetSetTrunc) λ { (a , b) → ∣ a ∣₂ , ∣ b ∣₂ }
Iso.inv setTruncOfProdIso = prodRec isSetSetTrunc λ a b → ∣ a , b ∣₂
Iso.rightInv setTruncOfProdIso =
  prodElim (λ _ → isOfHLevelPath 2 (isSet× isSetSetTrunc isSetSetTrunc) _ _) λ _ _ → refl
Iso.leftInv setTruncOfProdIso =
  elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _) λ {(a , b) → refl}

IsoSetTruncateSndΣ : {A : Type ℓ} {B : A → Type ℓ'} → Iso ∥ Σ A B ∥₂ ∥ Σ A (λ x → ∥ B x ∥₂) ∥₂
Iso.fun IsoSetTruncateSndΣ = map λ a → (fst a) , ∣ snd a ∣₂
Iso.inv IsoSetTruncateSndΣ = rec isSetSetTrunc (uncurry λ x → map λ b → x , b)
Iso.rightInv IsoSetTruncateSndΣ =
  elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
        (uncurry λ a → elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
        λ _ → refl)
Iso.leftInv IsoSetTruncateSndΣ =
  elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
         λ _ → refl

PathIdTrunc₀Iso : {a b : A} → Iso (∣ a ∣₂ ≡ ∣ b ∣₂) ∥ a ≡ b ∥₁
Iso.fun (PathIdTrunc₀Iso {b = b}) p =
  transport (λ i → rec {B = TypeOfHLevel _ 1} (isOfHLevelTypeOfHLevel 1)
                        (λ a → ∥ a ≡ b ∥₁ , squash₁) (p (~ i)) .fst)
            ∣ refl ∣₁
Iso.inv PathIdTrunc₀Iso = pRec (squash₂ _ _) (cong ∣_∣₂)
Iso.rightInv PathIdTrunc₀Iso _ = squash₁ _ _
Iso.leftInv PathIdTrunc₀Iso _ = squash₂ _ _ _ _

mapFunctorial : {A B C : Type ℓ} (f : A → B) (g : B → C)
  → map g ∘ map f ≡ map (g ∘ f)
mapFunctorial f g =
  funExt (elim (λ x → isSetPathImplicit) λ a → refl)
