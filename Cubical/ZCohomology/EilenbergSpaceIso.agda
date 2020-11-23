{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.EilenbergSpaceIso where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties

open import Cubical.HITs.S1 hiding (encode ; decode)
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Nat renaming (+-assoc to +-assocℕ ; +-comm to +-commℕ)
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3 ; map2 to trMap2)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Data.HomotopyGroup

open import Cubical.ZCohomology.GroupStructure
open import Cubical.Functions.Morphism


open Iso renaming (inv to inv')

Kₙ≃Kₙ : (n : ℕ) (x : coHomK (suc n)) → Iso (coHomK (suc n)) (coHomK (suc n))
fun (Kₙ≃Kₙ n x) y = x +ₖ y
inv' (Kₙ≃Kₙ n x) y = y -ₖ x
rightInv (Kₙ≃Kₙ n x) y = commₖ (suc n) x (y -ₖ x) ∙ -+cancelₖ (suc n) y x
leftInv (Kₙ≃Kₙ n x) y = -cancelLₖ (suc n) x y

private
  σ : {n : ℕ} → coHomK (suc n) → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
  σ {n = n} = trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a ∙ sym (merid (ptSn (suc n))))

  σ-hom : {n : ℕ} (x y : coHomK (suc n)) → σ (x +ₖ y) ≡ σ x ∙ σ y
  σ-hom {n = zero} =
    elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
          (wedgeConSn _ _
            (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
            (λ x → lUnit _
                  ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (λ y → cong σ (rUnitₖ 1 ∣ y ∣)
                 ∙∙ rUnit _
                 ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (sym (Kn→ΩKn+1-hom-helper (σ ∣ base ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))) .fst)
  σ-hom {n = suc n} =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
          (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
                      (λ x → lUnit _
                            ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (λ y → cong σ (rUnitₖ (2 + n) ∣ y ∣)
                           ∙∙ rUnit _
                           ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (sym (Kn→ΩKn+1-hom-helper (σ ∣ north ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))) .fst)

  σ-minusDistr : {n : ℕ} (x : coHomK (suc n)) → σ (-ₖ x) ≡ sym (σ x)
  σ-minusDistr {n = n} =
    morphLemmas.distrMinus
      _+ₖ_ _∙_
      σ σ-hom
      ∣ (ptSn (suc n)) ∣ refl
      -ₖ_ sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ (suc n)) rCancel
      assoc∙
      (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

  σ-minusDistr' : {n : ℕ} (x y : coHomK (suc n)) → σ (x -ₖ y) ≡ σ x ∙ sym (σ y)
  σ-minusDistr' {n = n} =
    morphLemmas.distrMinus'
      _+ₖ_ _∙_
      σ σ-hom ∣ (ptSn (suc n)) ∣ refl
      -ₖ_ sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (rUnitₖ (suc n))
      (lCancelₖ (suc n)) rCancel
      (assocₖ (suc n)) assoc∙
      (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

open Iso renaming (inv to inv')

Code' : (n : ℕ) → (S₊ (2 + n)) → Type₀
Code' n north = coHomK (suc n)
Code' n south = coHomK (suc n)
Code' n (merid a i) = isoToPath (Kₙ≃Kₙ n ∣ a ∣) i

hLevCode' : (n : ℕ) → (x : S₊ (2 + n)) → isOfHLevel (3 + n) (Code' n x)
hLevCode' n = suspToPropElim (ptSn (suc n)) (λ _ → isPropIsOfHLevel (3 + n)) (isOfHLevelTrunc (3 + n))

Code : (n : ℕ) →  coHomK (2 + n) → Type₀
Code n x = (trElim {B = λ _ → TypeOfHLevel ℓ-zero (3 + n)} (λ _ → isOfHLevelTypeOfHLevel (3 + n))
                   λ a → Code' n a , hLevCode' n a) x .fst

symMeridLem : (n : ℕ) → (x : S₊ (suc n)) (y : coHomK (suc n))
                      → subst (Code n) (cong ∣_∣ (sym (merid x))) y ≡ y -ₖ ∣ x ∣
symMeridLem n x = trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
                          (λ y → cong (_-ₖ ∣ x ∣) (transportRefl ∣ y ∣))

decode : {n : ℕ} (x : coHomK (2 + n)) → Code n x → ∣ north ∣ ≡ x
decode {n = n} = trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
                        decode-elim
  where
  north≡merid : (a : S₊ (suc n))
              → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
              ≡ (Path (coHomK (2 + n)) ∣ north ∣ ∣ south ∣)
  north≡merid a i = Path (coHomK (2 + n)) ∣ north ∣ ∣ merid a i ∣

  decode-elim : (a : S₊ (2 + n)) → Code n ∣ a ∣ → Path (coHomK (2 + n)) ∣ north ∣ ∣ a ∣
  decode-elim north = σ
  decode-elim south = trRec (isOfHLevelTrunc (4 + n) _ _)
                            λ a → cong ∣_∣ (merid a)
  decode-elim (merid a i) =
    hcomp (λ k → λ { (i = i0) → σ
                    ; (i = i1) → mainPath a k})
          (funTypeTransp (Code n) (λ x → ∣ north ∣ ≡ x) (cong ∣_∣ (merid a)) σ i)
    where
    mainPath : (a : (S₊ (suc n))) →
           transport (north≡merid a) ∘ σ ∘ transport (λ i → Code n ∣ merid a (~ i) ∣)
         ≡ trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a)
    mainPath a = funExt (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
                                (λ x → (λ i → transport (north≡merid a) (σ (symMeridLem n a ∣ x ∣ i)))
                                     ∙∙ cong (transport (north≡merid a)) (-distrHelp x)
                                     ∙∙ (substAbove x)))
      where
      -distrHelp : (x : S₊ (suc n)) → σ (∣ x ∣ -ₖ ∣ a ∣) ≡ cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a))
      -distrHelp x =
        σ-minusDistr' ∣ x ∣ ∣ a ∣
         ∙  (λ i → (cong ∣_∣ (compPath-filler (merid x) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))
                  ∙ (cong ∣_∣ (sym (compPath-filler (merid a) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))))

      substAbove : (x : S₊ (suc n)) → transport (north≡merid a) (cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a)))
                 ≡ cong ∣_∣ (merid x)
      substAbove x i = transp (λ j → north≡merid a (i ∨ j)) i
                              (compPath-filler (cong ∣_∣ (merid x)) (λ j → ∣ merid a (~ j ∨ i) ∣) (~ i))


encode : {n : ℕ} {x : coHomK (2 + n)} → Path (coHomK (2 + n)) ∣ north ∣ x → Code n x
encode {n = n} p = transport (cong (Code n) p) ∣ (ptSn (suc n)) ∣

encode-decode : {n : ℕ} {x : coHomK (2 + n)} (p : Path (coHomK (2 + n)) ∣ north ∣ x) → decode _ (encode p) ≡ p
encode-decode {n = n} =
  J (λ y p → decode _ (encode p) ≡ p)
      (cong (decode ∣ north ∣) (transportRefl ∣ ptSn (suc n) ∣)
     ∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

stabSpheres : (n : ℕ) → Iso (coHomK (suc n)) (typ (Ω (coHomK-ptd (2 + n))))
fun (stabSpheres n) = decode _
inv' (stabSpheres n) = encode
rightInv (stabSpheres n) p = encode-decode p 
leftInv (stabSpheres n) =
  trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
    λ a → cong encode (congFunct ∣_∣ (merid a) (sym (merid (ptSn (suc n)))))
        ∙∙ (λ i → transport (congFunct (Code n) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid (ptSn (suc n))))) i) ∣ ptSn (suc n) ∣)
        ∙∙ (substComposite (λ x → x) (cong (Code n) (cong ∣_∣ (merid a))) (cong (Code n) (cong ∣_∣ (sym (merid (ptSn (suc n)))))) ∣ ptSn (suc n) ∣
        ∙∙ cong (transport (λ i → Code n ∣ merid (ptSn (suc n)) (~ i) ∣)) (transportRefl (∣ a ∣ +ₖ ∣ (ptSn (suc n)) ∣) ∙ rUnitₖ (suc n) ∣ a ∣)
        ∙∙ symMeridLem n (ptSn (suc n)) ∣ a ∣
        ∙∙ cong (∣ a ∣ +ₖ_) -0ₖ
        ∙∙ rUnitₖ (suc n) ∣ a ∣)

Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS¹)) ΩS¹IsoInt)
Iso-Kn-ΩKn+1 (suc n) = stabSpheres n


-- Some properties of the Iso
Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = sym (rUnit refl)
Kn→ΩKn+10ₖ (suc n) i j = ∣ (rCancel (merid (ptSn (suc n))) i j) ∣

ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
ΩKn+1→Kn-refl zero = refl
ΩKn+1→Kn-refl (suc zero) = refl
ΩKn+1→Kn-refl (suc (suc n)) = refl

Kn→ΩKn+1-hom : (n : ℕ) (x y : coHomK n) → Kn→ΩKn+1 n (x +[ n ]ₖ y) ≡ Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y
Kn→ΩKn+1-hom zero x y = (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                         (inS (∣ intLoop (x ℤ+ y) i ∣)) (~ j))
                      ∙∙ (λ j i → ∣ intLoop-hom x y (~ j) i ∣)
                      ∙∙ (congFunct ∣_∣ (intLoop x) (intLoop y)
                        ∙ cong₂ _∙_ (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                                    (inS (∣ intLoop x i ∣)) j)
                                     λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                                    (inS (∣ intLoop y i ∣)) j)
Kn→ΩKn+1-hom (suc n) = σ-hom

ΩKn+1→Kn-hom : (n : ℕ) (x y : Path (coHomK (suc n)) (0ₖ _) (0ₖ _))
             → ΩKn+1→Kn n (x ∙ y) ≡ ΩKn+1→Kn n x +[ n ]ₖ ΩKn+1→Kn n y
ΩKn+1→Kn-hom n =
  morphLemmas.isMorphInv
    (λ x y → x +[ n ]ₖ y) _∙_
    (Kn→ΩKn+1 n) (Kn→ΩKn+1-hom n)
    (ΩKn+1→Kn n)
    (Iso.rightInv (Iso-Kn-ΩKn+1 n))
    (Iso.leftInv (Iso-Kn-ΩKn+1 n))


{-
With the equivalence Kn≃ΩKn+1, we get the following alternative definition of Hⁿ(_)
-}

open GroupHom
coHom≅coHomΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → GroupIso (coHomGr n A) (coHomGrΩ n A)
fun (GroupIso.map (coHom≅coHomΩ n A)) = map λ f a → Kn→ΩKn+1 n (f a)
isHom (GroupIso.map (coHom≅coHomΩ n A)) =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ f g → cong ∣_∣₂ (funExt λ x → Kn→ΩKn+1-hom n (f x) (g x))
GroupIso.inv (coHom≅coHomΩ n A) = map λ f a → ΩKn+1→Kn n (f a)
GroupIso.rightInv (coHom≅coHomΩ n A) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → rightInv (Iso-Kn-ΩKn+1 n) (f x))
GroupIso.leftInv (coHom≅coHomΩ n A) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → leftInv (Iso-Kn-ΩKn+1 n) (f x))

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


module lockedKnIso (key : Unit') where
  Kn→ΩKn+1' : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
  Kn→ΩKn+1' n = lock key (Iso.fun (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn' : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
  ΩKn+1→Kn' n = lock key (Iso.inv (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn→ΩKn+1 : (n : ℕ) → (x : typ (Ω (coHomK-ptd (suc n)))) → Kn→ΩKn+1' n (ΩKn+1→Kn' n x) ≡ x
  ΩKn+1→Kn→ΩKn+1 n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) (lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.rightInv (Iso-Kn-ΩKn+1 n) x

  Kn→ΩKn+1→Kn : (n : ℕ) → (x : coHomK n) → ΩKn+1→Kn' n (Kn→ΩKn+1' n x) ≡ x
  Kn→ΩKn+1→Kn n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) (lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.leftInv (Iso-Kn-ΩKn+1 n) x
