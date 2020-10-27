{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Properties2 where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to § ; map to sMap)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_) hiding (+-comm)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup

open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Homotopy.WedgeConnectivity

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ

infixr 34 +ₖ-syntax
infixr 34 +ₕ-syntax

infixr 34 -'ₖ-syntax
infixr 34 -'ₕ-syntax

infixl 35 -ₖ-syntax
infixl 35 -ₕ-syntax

0ₖ : (n : ℕ) → loopK n
0ₖ = coHom'-pt

_+ₖ_ : {n : ℕ} → loopK n → loopK n → loopK n
_+ₖ_ {n = n} = map2 _∙_

-ₖ_ : {n : ℕ} →  loopK n → loopK n
-ₖ_ {n = n} = trMap sym

+ₖ-syntax : (n : ℕ) → loopK n → loopK n → loopK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → loopK n → loopK n
-ₖ-syntax n = -ₖ_ {n = n}


-- ΩKn+1→Kn n (Kn→ΩKn+1 n x ∙ sym (Kn→ΩKn+1 n y))

{-
+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

-'ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
-'ₖ-syntax n = _-ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x
syntax -'ₖ-syntax n x y = x -[ n ]ₖ y -}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x

_-ₖ_ : {n : ℕ} → loopK n → loopK n → loopK n
_-ₖ_ {n = n} x y = x +[ n ]ₖ -[ n ]ₖ y

-'ₖ-syntax : (n : ℕ) → loopK n → loopK n → loopK n
-'ₖ-syntax n x y = _-ₖ_ {n = n} x y

syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ = refl

isConnectedKn : (n : ℕ) → isConnected (2 + n) (coHomK (suc n))
isConnectedKn n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (2 + n) 1))
                                             (sphereConnected (suc n))


-- Induction principle for cohomology groups. Given n ≥ 1 and x : Hⁿ(A) and a proposition P : Hⁿ(A) → Type,
-- one may assume that x is on the form ∣ f ∣₂ and satisfies f(pt A) ≡ 0 when proving P(x).
coHomPointedElim : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom' (suc n) A → Type ℓ'}
                 → ((x : coHom' (suc n) A) → isProp (B x))
                 → ((f : A → loopK (suc n)) → f a ≡ coHom'-pt (suc n) → B ∣ f ∣₂)
                 → (x : coHom' (suc n) A) → B x
coHomPointedElim {ℓ' = ℓ'} {A = A} n a {B = B} isprop indp =
  sElim (λ _ → isOfHLevelSuc 1 (isprop _)) λ f →
    Iso.inv (elim.isIsoPrecompose {A = Unit} (λ _ → ∣ refl ∣) 1 (λ x → (f a ≡ x → B ∣ f ∣₂) , isPropΠ λ _ → isprop _)
            (trElim (λ _ → isProp→isOfHLevelSuc (2 + n) isPropIsContr)
                    λ q → trRec (isProp→isOfHLevelSuc _ (isOfHLevelTrunc 1)) (λ id → ∣ _ , (λ i → ∣ id (~ i) ∣) ∣)
                                 (Iso.fun (PathIdTruncIso _) (isOfHLevelSuc 0
                                          (isConnectedPath _ (sphereConnected (2 + n)) north north) ∣ q ∣ ∣ refl ∣))
                  , (λ _ → isOfHLevelTrunc 1 _ _)))
            (λ _ → indp f) (f a) refl

coHomPointedElim2 : ∀ {ℓ''} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (a : A) (b : B) {C : coHom' (suc n) A → coHom' (suc n) B → Type ℓ''}
                 → ((x : coHom' (suc n) A) (y : coHom' (suc n) B) → isProp (C x y))
                 → ((f : A → loopK (suc n)) (g : B → loopK (suc n)) → f a ≡ coHom'-pt (suc n) → g b ≡ coHom'-pt (suc n) → C ∣ f ∣₂ ∣ g ∣₂)
                 → (x : coHom' (suc n) A) (y : coHom' (suc n) B) → C x y
coHomPointedElim2 {ℓ' = ℓ'} {A = A} n a b {C = C} isprop indp =
  sElim2 (λ _ _ → isOfHLevelSuc 1 (isprop _ _)) λ f g →
         Iso.inv (elim.isIsoPrecompose {A = Unit} (λ _ → ∣ refl ∣ , ∣ refl ∣) 1
                                       (λ x → ((f a ≡ fst x) → (g b ≡ snd x) → C ∣ f ∣₂ ∣ g ∣₂), isPropΠ2 λ _ _ → isprop _ _)
                                       (uncurry (elim2 (λ _ _ → isProp→isOfHLevelSuc (2 + n) isPropIsContr)
                                                  λ p q → trRec (isProp→isOfHLevelSuc _ isPropIsContr)
                                                                 (λ pid → trRec (isProp→isOfHLevelSuc _ isPropIsContr)
                                                                 (λ qid → ∣ _ , (ΣPathP ((λ i → ∣ pid i ∣) , λ i → ∣ qid i ∣)) ∣
                                                                         , λ _ → isOfHLevelTrunc 1 _ _)
                                                                 (Iso.fun (PathIdTruncIso _) (isOfHLevelSuc 0
                                                                           (isConnectedPath _ (sphereConnected (2 + n)) north north) ∣ refl ∣ ∣ q  ∣)))
                                                                 (Iso.fun (PathIdTruncIso _) (isOfHLevelSuc 0
                                                                           (isConnectedPath _ (sphereConnected (2 + n)) north north) ∣ refl ∣ ∣ p ∣)))))
                 (λ _ → indp f g) _ refl refl

{-
{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                  (A : Type ℓ) →
                  (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₂
  module coHomRed+1 where
  helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
  helpLemma {C = C} = isoToPath (iso map1
                                     map2
                                     (λ b → linvPf b)
                                     (λ _  → refl))
    where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
    map1 f = map1' , refl
      module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)

    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
      where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
      helper (inl x) = refl
      helper (inr tt) = sym snd
coHomRed+1Equiv (suc zero) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK 1 , ∣ base ∣)} i ∥₂
coHomRed+1Equiv (suc (suc n)) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK (2 + n) , ∣ north ∣)} i ∥₂
-}
-----------


---------- Algebra/Group stuff --------

lUnitₖ : (n : ℕ) (x : loopK n) → (0ₖ n) +[ n ]ₖ x ≡ x
lUnitₖ n = trElim (λ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ p i → ∣ lUnit p (~ i) ∣

rUnitₖ : (n : ℕ) (x : loopK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ n = trElim (λ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ p i → ∣ rUnit p (~ i) ∣

rCancelₖ  : (n : ℕ) (x : loopK n) → x +[ n ]ₖ (-[ n ]ₖ x) ≡ (0ₖ n)
rCancelₖ n = trElim (λ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ p i → ∣ rCancel p i ∣

lCancelₖ : (n : ℕ) (x : loopK n) → (-[ n ]ₖ x) +[ n ]ₖ x  ≡ (0ₖ n)
lCancelₖ n = trElim (λ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ p i → ∣ lCancel p i ∣

assocₖ : (n : ℕ) (x y z : loopK n) → ((x +[ n ]ₖ y) +[ n ]ₖ z) ≡ (x +[ n ]ₖ (y +[ n ]ₖ z))
assocₖ n = trElim3 (λ _ _ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ p q r i → ∣ assoc p q r (~ i) ∣

{-
abstract
  isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A → isOfHLevel (suc n) (typ A) → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
  isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
      ((λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
   ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
   ∙∙ (λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

  isCommΩK1 : (n : ℕ) → isComm∙ ((Ω^ n) (coHomK-ptd 1))
  isCommΩK1 zero = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK1 (suc n) = Eckmann-Hilton n

  open Iso renaming (inv to inv')
  ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , Iso.fun e (pt A))
  ptdIso→comm {A = (A , a)} {B = B} e comm p q =
         sym (rightInv (congIso e) (p ∙ q))
      ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                              ∙∙ (comm (inv' (congIso e) p) (inv' (congIso e) q))
                              ∙∙ (sym (invCongFunct e q p))))
      ∙∙ rightInv (congIso e) (q ∙ p)

  isCommΩK : (n : ℕ) → isComm∙ (coHomK-ptd n)
  isCommΩK zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
  isCommΩK (suc zero) = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK (suc (suc n)) = subst isComm∙ (λ i → coHomK (2 + n) , ΩKn+1→Kn-refl (2 + n) i) (ptdIso→comm {A = (_ , _)} (invIso (Iso-Kn-ΩKn+1 (2 + n))) (Eckmann-Hilton 0))
-}
{-
commₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) ≡ (y +[ n ]ₖ x)
commₖ 0 x y i = ΩKn+1→Kn 0 (isCommΩK1 0 (Kn→ΩKn+1 0 x) (Kn→ΩKn+1 0 y) i)
commₖ 1 x y i = ΩKn+1→Kn 1 (ptdIso→comm {A = ((∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (coHomK 3 , ∣ north ∣)))}
                                        {B = coHomK 2}
                                        (invIso (Iso-Kn-ΩKn+1 2)) (Eckmann-Hilton 0) (Kn→ΩKn+1 1 x) (Kn→ΩKn+1 1 y) i)
commₖ 2 x y i = ΩKn+1→Kn 2 (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (coHomK 4 , ∣ north ∣))}
                                        {B = coHomK 3}
                                        (invIso (Iso-Kn-ΩKn+1 3)) (Eckmann-Hilton 0) (Kn→ΩKn+1 2 x) (Kn→ΩKn+1 2 y) i)
commₖ 3 x y i = ΩKn+1→Kn 3 (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (coHomK 5 , ∣ north ∣))}
                                        {B = coHomK 4}
                                        (invIso (Iso-Kn-ΩKn+1 4)) (Eckmann-Hilton 0) (Kn→ΩKn+1 3 x) (Kn→ΩKn+1 3 y) i)
commₖ (suc (suc (suc (suc n)))) x y i =
  ΩKn+1→Kn (4 + n) (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (coHomK (6 + n) , ∣ north ∣))}
                                {B = coHomK (5 + n)}
                                (invIso (Iso-Kn-ΩKn+1 (5 + n))) (Eckmann-Hilton 0) (Kn→ΩKn+1 (4 + n) x) (Kn→ΩKn+1 (4 + n) y) i)


rUnitₖ' : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ' n x = commₖ n x (0ₖ n) ∙ lUnitₖ n x
-}

commₖ : (n : ℕ) (x y : loopK n) → (x +[ n ]ₖ y) ≡ (y +[ n ]ₖ x)
commₖ zero = elim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                    λ p q → cong ∣_∣ (comm-ΩS¹ p q)
commₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (WedgeConnectivity.extension 1 1
          (_ , refl) (isConnectedPath 2 (sphereConnected 2) _ _)
          (_ , refl) (isConnectedPath 2 (sphereConnected 2) _ _)
          (λ p q → _ , isOfHLevelTrunc 3 _ _)
          (λ p → rUnitₖ _ ∣ p ∣ ∙ (sym (lUnitₖ _ ∣ p ∣)))
          (λ p → lUnitₖ _ ∣ p ∣ ∙ (sym (rUnitₖ _ ∣ p ∣)))
          refl)
commₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (WedgeConnectivity.extension (2 + n) (2 + n)
        (_ , refl) (isConnectedPath (3 + n) (sphereConnected _) _ _)
        (_ , refl) (isConnectedPath (3 + n) (sphereConnected _) _ _)
        (λ p q → _ , λ p q → isOfHLevelPlus (suc n) (isOfHLevelTrunc (4 + n) _ _ _ _))
        (λ p → rUnitₖ _ ∣ p ∣ ∙ (sym (lUnitₖ _ ∣ p ∣)))
        (λ p → lUnitₖ _ ∣ p ∣ ∙ (sym (rUnitₖ _ ∣ p ∣)))
        refl)

-distrₖ : (n : ℕ) (x y : loopK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ n =
  elim2 (λ _ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _)
        λ p q → cong ∣_∣ (symDistr p q) ∙ commₖ n ∣ sym q ∣ ∣ sym p ∣

---- Group structure of cohomology groups ---
_+ₕ_ : {n : ℕ} → coHom' n A → coHom' n A → coHom' n A
_+ₕ_ {n = n} = sRec2 § λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom' n A → coHom' n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

+ₕ-syntax : (n : ℕ) → coHom' n A → coHom' n A → coHom' n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom' n A → coHom' n A
-ₕ-syntax n = -ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x

_-ₕ_ : {n : ℕ} → coHom' n A → coHom' n A → coHom' n A
_-ₕ_ {n = n} x y = x +[ n ]ₕ -[ n ]ₕ y

-'ₕ-syntax : (n : ℕ) → coHom' n A → coHom' n A → coHom' n A
-'ₕ-syntax n = _-ₕ_ {n = n}

syntax -'ₕ-syntax n x y = x -[ n ]ₕ y

0ₕ : (n : ℕ) → coHom' n A
0ₕ n = ∣ (λ _ → (0ₖ n)) ∣₂

rUnitₕ : (n : ℕ) (x : coHom' n A) → x +[ n ]ₕ (0ₕ n) ≡ x
rUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ n (a x)) i ∣₂

lUnitₕ : (n : ℕ) (x : coHom' n A) → (0ₕ n) +[ n ]ₕ x ≡ x
lUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → lUnitₖ n (a x)) i ∣₂

rCancelₕ : (n : ℕ) (x : coHom' n A) → x +[ n ]ₕ (-[ n ]ₕ x) ≡ 0ₕ n
rCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ n (a x)) i ∣₂

lCancelₕ : (n : ℕ) (x : coHom' n A) → (-[ n ]ₕ x) +[ n ]ₕ x  ≡ 0ₕ n
lCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ n (a x)) i ∣₂

assocₕ : (n : ℕ) (x y z : coHom' n A) → ((x +[ n ]ₕ y) +[ n ]ₕ z) ≡ (x +[ n ]ₕ (y +[ n ]ₕ z))
assocₕ n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ n (a x) (b x) (c x)) i ∣₂

commₕ : (n : ℕ) (x y : coHom' n A) → (x +[ n ]ₕ y) ≡ (y +[ n ]ₕ x)
commₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ funExt (λ x → commₖ n (a x) (b x)) i ∣₂

-ₖ-ₖ : (n : ℕ) (x : loopK n) → (-[ n ]ₖ (-[ n ]ₖ x)) ≡ x
-ₖ-ₖ n = trElim (λ _ → isOfHLevelPath (2 + n) (isOfHLevelTrunc (2 + n)) _ _) λ _ → refl

coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group {ℓ}
fst (coHomGr n A) = coHom' n A
GroupStr.0g (snd (coHomGr n A)) = 0ₕ n
GroupStr._+_ (snd (coHomGr n A)) x y = x +[ n ]ₕ y
(GroupStr.- snd (coHomGr n A)) x = -[ n ]ₕ x
GroupStr.isGroup (snd (coHomGr n A)) = helper
  where
  abstract
    helper : IsGroup (0ₕ n) (λ x y → x +[ n ]ₕ y) λ x → -[ n ]ₕ x
    helper = makeIsGroup § (λ x y z → sym (assocₕ n x y z)) (rUnitₕ n) (lUnitₕ n) (rCancelₕ n) (lCancelₕ n)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)

coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom' n B → coHom' n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

open GroupHom
-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom' n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma {A = A} {B = B} n m f x y =
                         isHom f x (-[ n ]ₕ y)
                       ∙ cong (λ y → fun f x +[ m ]ₕ y) (morphMinus (coHomGr n A) (coHomGr m B) f y)
  

{-
-- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x) , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
+ₕ∙ (suc zero) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ 1 ]ₖ b x) , (λ i → pa i +[ 1 ]ₖ pb i) ∙ lUnitₖ 1 (0ₖ 1) ∣₂ }
+ₕ∙ (suc (suc n)) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (2 + n) ]ₖ b x) , (λ i → pa i +[ (2 + n) ]ₖ pb i) ∙ lUnitₖ (2 + n) (0ₖ (2 + n)) ∣₂ }

open IsSemigroup
open IsMonoid
open GroupStr
open GroupHom

coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group {ℓ}
coHomGr n A = coHom n A , coHomGrnA
  where
  coHomGrnA : GroupStr (coHom n A)
  0g coHomGrnA = 0ₕ n
  GroupStr._+_ coHomGrnA = λ x y → x +[ n ]ₕ y
  - coHomGrnA = λ x → -[ n ]ₕ x
  isGroup coHomGrnA = helper
    where
    abstract
      helper : IsGroup (0ₕ n) (λ x y → x +[ n ]ₕ y) (λ x → -[ n ]ₕ x)
      helper = makeIsGroup § (λ x y z → sym (assocₕ n x y z)) (rUnitₕ n) (lUnitₕ n) (rCancelₕ n) (lCancelₕ n)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)

coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma n m f' x y = sym (-cancelRₕ m (f y) (f (x -[ n ]ₕ y)))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) (sym (isHom f' (x -[ n ]ₕ y) y))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) ( cong f (-+cancelₕ n _ _))
  where
  f = fun f'

--- the loopspace of Kₙ is commutative regardless of base

addIso : (n : ℕ) (x : coHomK n) → Iso (coHomK n) (coHomK n)
fun (addIso n x) y = y +[ n ]ₖ x
inv' (addIso n x) y = y -[ n ]ₖ x
rightInv (addIso n x) y = -+cancelₖ n y x
leftInv (addIso n x) y = -cancelRₖ n x y

isCommΩK-based : (n : ℕ) (x : coHomK n) → isComm∙ (coHomK n , x)
isCommΩK-based zero x p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc zero) x =
  subst isComm∙ (λ i → coHomK 1 , lUnitₖ 1 x i)
                (ptdIso→comm {A = (_ , 0ₖ 1)} (addIso 1 x)
                              (isCommΩK 1))
isCommΩK-based (suc (suc n)) x =
  subst isComm∙ (λ i → coHomK (suc (suc n)) , lUnitₖ (suc (suc n)) x i)
                (ptdIso→comm {A = (_ , 0ₖ (suc (suc n)))} (addIso (suc (suc n)) x)
                              (isCommΩK (suc (suc n))))

addLemma : (a b : Int) → a +[ 0 ]ₖ b ≡ (a ℤ+ b)
addLemma a b = (cong (ΩKn+1→Kn 0) (sym (congFunct ∣_∣ (intLoop a) (intLoop b))))
            ∙∙ (λ i → ΩKn+1→Kn 0 (cong ∣_∣ (intLoop-hom a b i)))
            ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 0) (a ℤ+ b)

---
-- hidden versions of cohom stuff using the "lock" hack. The locked versions can be used when proving things.
-- Swapping "key" for "tt*" will then give computing functions.

Unit' : Type₀
Unit' = lockUnit {ℓ-zero}

lock : ∀ {ℓ} {A : Type ℓ} → Unit' → A → A
lock unlock = λ x → x

module lockedCohom (key : Unit') where
  +K : (n : ℕ) → coHomK n → coHomK n → coHomK n
  +K n = lock key (_+ₖ_ {n = n})

  -K : (n : ℕ) → coHomK n → coHomK n
  -K n = lock key (-ₖ_ {n = n})

  -Kbin : (n : ℕ) → coHomK n → coHomK n → coHomK n
  -Kbin n = lock key (_-ₖ_ {n = n})

  rUnitK : (n : ℕ) (x : coHomK n) → +K n x (0ₖ n) ≡ x
  rUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (0ₖ n) ≡ x
    pm unlock = rUnitₖ n x

  lUnitK : (n : ℕ) (x : coHomK n) → +K n (0ₖ n) x ≡ x
  lUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (0ₖ n) x ≡ x
    pm unlock = lUnitₖ n x

  rCancelK : (n : ℕ) (x : coHomK n) → +K n x (-K n x) ≡ 0ₖ n
  rCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (lock t (-ₖ_ {n = n}) x) ≡ 0ₖ n
    pm unlock = rCancelₖ n x

  lCancelK : (n : ℕ) (x : coHomK n) → +K n (-K n x) x ≡ 0ₖ n
  lCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (-ₖ_ {n = n}) x) x ≡ 0ₖ n
    pm unlock = lCancelₖ n x

  -cancelRK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n y x) x ≡ y
  -cancelRK n x y = pm key
    where
    pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) y x) x ≡ y
    pm unlock = -cancelRₖ n x y

  -cancelLK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n x y) x ≡ y
  -cancelLK n x y = pm key
    where
    pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) x ≡ y
    pm unlock = -cancelLₖ n x y

  -+cancelK : (n : ℕ) (x y : coHomK n) → +K n (-Kbin n x y) y ≡ x
  -+cancelK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_-ₖ_ {n = n}) x y) y ≡ x
    pm unlock = -+cancelₖ n x y

  cancelK : (n : ℕ) (x : coHomK n) → -Kbin n x x ≡ 0ₖ n
  cancelK n x = pm key
    where
    pm : (t : Unit') → (lock t (_-ₖ_ {n = n}) x x) ≡ 0ₖ n
    pm unlock = cancelₖ n x

  assocK : (n : ℕ) (x y z : coHomK n) → +K n (+K n x y) z ≡ +K n x (+K n y z)
  assocK n x y z = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) z
                     ≡ lock t (_+ₖ_ {n = n}) x (lock t (_+ₖ_ {n = n}) y z)
    pm unlock = assocₖ n x y z

  commK : (n : ℕ) (x y : coHomK n) → +K n x y ≡ +K n y x
  commK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x y ≡ lock t (_+ₖ_ {n = n}) y x
    pm unlock = commₖ n x y

  -- cohom

  +H : (n : ℕ) (x y : coHom n A) → coHom n A
  +H n = sRec2 § λ a b → ∣ (λ x → +K n (a x) (b x)) ∣₂

  -H : (n : ℕ) (x : coHom n A) → coHom n A
  -H n = sRec § λ a → ∣ (λ x → -K n (a x)) ∣₂

  -Hbin : (n : ℕ) → coHom n A → coHom n A → coHom n A
  -Hbin n = sRec2 § λ a b → ∣ (λ x → -Kbin n (a x) (b x)) ∣₂

  rUnitH : (n : ℕ) (x : coHom n A) → +H n x (0ₕ n) ≡ x
  rUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → rUnitK n (a x)) i ∣₂

  lUnitH : (n : ℕ) (x : coHom n A) → +H n (0ₕ n) x ≡ x
  lUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                    λ a i → ∣ funExt (λ x → lUnitK n (a x)) i ∣₂

  rCancelH : (n : ℕ) (x : coHom n A) → +H n x (-H n x) ≡ 0ₕ n
  rCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → rCancelK n (a x)) i ∣₂

  lCancelH : (n : ℕ) (x : coHom n A) → +H n (-H n x) x  ≡ 0ₕ n
  lCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → lCancelK n (a x)) i ∣₂

  assocH : (n : ℕ) (x y z : coHom n A) → (+H n (+H n x y) z) ≡ (+H n x (+H n y z))
  assocH n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
                 λ a b c i → ∣ funExt (λ x → assocK n (a x) (b x) (c x)) i ∣₂

  commH : (n : ℕ) (x y : coHom n A) → (+H n x y) ≡ (+H n y x)
  commH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                          λ a b i → ∣ funExt (λ x → commK n (a x) (b x)) i ∣₂

  -cancelRH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n y x) x ≡ y
  -cancelRH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelRK n (a x) (b x) i) ∣₂

  -cancelLH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n x y) x ≡ y
  -cancelLH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelLK n (a x) (b x) i) ∣₂

  -+cancelH : (n : ℕ) (x y : coHom n A) → +H n (-Hbin n x y) y ≡ x
  -+cancelH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -+cancelK n (a x) (b x) i) ∣₂


+K→∙ : (key : Unit') (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (lockedCohom.+K key n a b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
+K→∙ unlock = +ₖ→∙

+H≡+ₕ : (key : Unit') (n : ℕ) → lockedCohom.+H key {A = A} n ≡ _+ₕ_ {n = n}
+H≡+ₕ unlock _ = refl

rUnitlUnit0K : (key : Unit') (n : ℕ) → lockedCohom.rUnitK key n (0ₖ n) ≡ lockedCohom.lUnitK key n (0ₖ n)
rUnitlUnit0K unlock = rUnitlUnit0
-}
