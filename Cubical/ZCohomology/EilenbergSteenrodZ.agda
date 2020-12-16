{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.ZCohomology.EilenbergSteenrodZ where

open import Cubical.Core.Everything

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.Data.Nat
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Function
open import Cubical.HITs.SetTruncation renaming (map to sMap ; rec to sRec ; elim to sElim ; rec2 to sRec2)
open import Cubical.HITs.PropositionalTruncation renaming (map to pMap ; rec to pRec ; elim to pElim ; elim2 to pElim2)
open import Cubical.HITs.Truncation renaming (rec to trRec ; map to trMap ; elim to trEilim ; elim2 to trElim2)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

open import Cubical.HITs.Pushout
open import Cubical.Algebra.Group
open import Cubical.HITs.Susp

open IsGroup
open GroupStr
open GroupIso
open import Cubical.Data.Bool

open import Cubical.HITs.Wedge

open GroupHom

open import Cubical.HITs.Sn

open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)

characSuspFuns : {!(x y : )!}
characSuspFuns = {!!}

open import Cubical.ZCohomology.Groups.Sn
pointerElimFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f : Pointer A → coHomK (suc n)) → (f pt₀ ≡ 0ₖ _) → Pointer A → coHomK (suc n)
pointerElimFun n f p pt₀ = 0ₖ _
pointerElimFun n f p ⌊ x ⌋ = f ⌊ x ⌋
pointerElimFun n f p (id i) = (cong f id ∙ p) i

pointerElim : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointer A → Type ℓ'}
              → ((x : typ A) → B ⌊ x ⌋)
              → (x : _) → B x
pointerElim {A = A} {B = B} ind pt₀ = subst B id (ind (pt A))
pointerElim ind ⌊ x ⌋ = ind x
pointerElim {B = B} ind (id i) = transp (λ j → B (id (i ∧ j))) (~ i) (ind (pt _))

≡PointerFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _) → pointerElimFun n f p ≡ f 
≡PointerFun n f p i pt₀ = p (~ i)
≡PointerFun n f p i ⌊ x ⌋ = f ⌊ x ⌋ 
≡PointerFun n f p i (id j) = compPath-filler (cong f id) p (~ i) j

coHomPointerElim : ∀ {ℓ ℓ'} {A : Pointed ℓ} (n : ℕ) {B : coHom (suc n) (Pointer A) → Type ℓ'}
                 → ((x : coHom (suc n) (Pointer A)) → isProp (B x))
                 → ((f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _) → B ∣ pointerElimFun n f p ∣₂)
                 → (x : coHom (suc n) (Pointer A)) → B x
coHomPointerElim {A = A} n {B = B} isprop =
  transport (λ i → ((f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _)
                   → B ∣ ≡PointerFun n f p (~ i) ∣₂)
                   → (x : coHom (suc n) (Pointer A)) → B x)
            (coHomPointedElim _ _ isprop)

suspΩFun' : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → Path _ (0ₖ _) (0ₖ _)) → Susp A → coHomK (suc n)
suspΩFun' n f north = 0ₖ _
suspΩFun' n f south = 0ₖ _
suspΩFun' n f (merid a i) = f a i

suspΩFun : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → coHomK n) → Susp A → coHomK (suc n)
suspΩFun n f = suspΩFun' n λ a → Kn→ΩKn+1 n (f a)

≡suspΩFun : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) (f : Susp (typ A) → coHomK (suc n)) (p : f north ≡ 0ₖ _) → f ≡ suspΩFun' n λ a → sym p ∙∙ (cong f (merid a)) ∙∙ (cong f (sym (merid (pt A))) ∙ p)
≡suspΩFun n s f p i north = p i
≡suspΩFun n s f p i south = (cong f (sym (merid (pt s))) ∙ p) i
≡suspΩFun n s f p i (merid a j) =
  doubleCompPath-filler (sym p) (cong f (merid a)) (cong f (sym (merid (pt s))) ∙ p) i j

SuspCohomElim : ∀ {ℓ ℓ'} {A : Pointed ℓ} (n : ℕ) {B : coHom (suc n) (Susp (typ A)) → Type ℓ'}
             → ((x : coHom (suc n) (Susp (typ A))) → isProp (B x))
             → ((f : typ A → Path _ (0ₖ _) (0ₖ _)) → f (pt A) ≡ refl → B ∣ suspΩFun' n f ∣₂)
             → (x : _) → B x
SuspCohomElim {A = A} n {B = B} isprop f =
  coHomPointedElim _ north isprop λ g gid
    → subst (B ∘ ∣_∣₂) (sym (≡suspΩFun n A g gid))
                       (f _ ((λ i → (sym gid ∙∙ (λ j → g (merid (pt A) (~ i ∧ j))) ∙∙ ((λ j → g (merid (pt A) (~ i ∧ ~ j))) ∙ gid)))
                                  ∙∙ (λ i → (λ j → gid (i ∨ ~ j)) ∙∙ refl ∙∙ lUnit (λ j → gid (i ∨ j)) (~ i))
                                  ∙∙ sym (rUnit refl)))

open import Cubical.HITs.S1
open isCohomTheory
open import Cubical.Data.Int
open import Cubical.Algebra.AbGroup
-- open import Cubical.Data.Unit

coHomFunctor : {ℓ : Level}  (n : Int) → Pointed ℓ → AbGroup {ℓ}
coHomFunctor (pos n) = coHomRedGroup n
coHomFunctor (negsuc n) _ = Group→AbGroup trivialAbGroup λ _ _ → refl

coHomFunctor' : {ℓ : Level} (n : Int) → Pointed ℓ → AbGroup {ℓ}
coHomFunctor' (pos zero) = coHomFunctor 0
coHomFunctor' (pos (suc n)) A = coHomGroup (suc n) (typ A)
coHomFunctor' (negsuc n) = coHomFunctor (negsuc n)

coHomFunctor≡coHomFunctor' : ∀ {ℓ} → coHomFunctor {ℓ} ≡ coHomFunctor'
coHomFunctor≡coHomFunctor' = funExt λ {(pos zero) → refl
                                     ; (pos (suc n)) → funExt λ A → coHomGroup≡coHomRedGroup n A
                                     ; (negsuc n) → refl}
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

H0-susp : ∀ {ℓ} {A : Pointed ℓ} → isContr (coHomRed 0 (Susp (typ A) , north))
fst H0-susp = 0ₕ∙ _
snd (H0-susp {A = A}) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                                       (funExt λ {north → sym p
                                                ; south → sym p ∙ cong f (merid (pt A))
                                                ; (merid a i) j → isSet→isSet' (isSetInt)
                                                                                 (sym p)
                                                                                 (sym p ∙ cong f (merid (pt A)))
                                                                                 refl (cong f (merid a)) i j}))}
{-
suspFunCharacFun : ∀ {ℓ} {A : Pointed ℓ} → ((Susp (typ A)) → coHomK 1) → (typ A → Int)
suspFunCharacFun {A = A} f x = ΩKn+1→Kn 0 (sym (rCancelₖ _ (f north))
                                                   ∙∙ cong (λ x → f x -ₖ f north) ((merid x) ∙ sym (merid (pt A)))
                                                   ∙∙ rCancelₖ _ (f north)) -}
suspFunCharacFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
                   → ((Susp (typ A)) → coHomK (suc n))
                   → (typ A → (coHomK n))
suspFunCharacFun {A = A} n f x = ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north))
                                                   ∙∙ cong (λ x → f x -[ (suc n) ]ₖ f north) ((merid x) ∙ sym (merid (pt A)))
                                                   ∙∙ rCancelₖ (suc n) (f north))

suspFunCharac : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → Iso (coHom (suc (suc n)) (Susp (typ A))) (coHom (suc n) (typ A))
fun (suspFunCharac {A = A} n) =
  sMap λ f → suspFunCharacFun {A = A} (suc n) f
inv (suspFunCharac {A = A} n) = sMap (suspΩFun (suc n))
rightInv (suspFunCharac {A = A} n) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
    (λ f → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                  (λ fId → cong ∣_∣₂ (funExt λ x → (cong (ΩKn+1→Kn (suc n))
                                                            ((λ i → (sym (transportRefl (λ _ → 0ₖ _) i)
                                                                ∙∙ cong (λ x → suspΩFun (suc n) f x +ₖ 0ₖ _)
                                                                        (merid x ∙ sym (merid (pt A)))
                                                                ∙∙ transportRefl (λ _ → 0ₖ _) i))
                                                         ∙∙ (sym (rUnit (cong (λ x → suspΩFun (suc n) f x +ₖ 0ₖ _)
                                                                                          ((merid x) ∙ sym (merid (pt A))))))
                                                         ∙∙ (λ i → congFunct (λ x → rUnitₖ _ (suspΩFun (suc n) f x) i)
                                                                              (merid x) (sym (merid (pt A))) i)))
                                                 ∙∙ ΩKn+1→Kn-hom (suc n) (Kn→ΩKn+1 (suc n) (f x))
                                                                  (sym (Kn→ΩKn+1 (suc n) (f (pt A))))
                                                 ∙∙ cong₂ _+ₖ_ (Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (f x))
                                                               (cong (λ x → ΩKn+1→Kn (suc n) (sym (Kn→ΩKn+1 (suc n) x))) fId)
                                                 ∙∙ cong (λ y → f x +ₖ ΩKn+1→Kn (suc n) (sym y)) (Kn→ΩKn+10ₖ (suc n))
                                                 ∙∙ cong (f x +ₖ_) (ΩKn+1→Kn-refl (suc n))
                                                  ∙ rUnitₖ _ (f x)))
                  (fst (isConnectedPathKn n (f (pt A)) (0ₖ _))))
leftInv (suspFunCharac {A = A} n) =
  SuspCohomElim {A = A} _ (λ _ → setTruncIsSet _ _)
    λ f fId → cong ∣_∣₂ (funExt λ {north → refl ; south → refl ; (merid a i) j → helper f a fId j i})
  where
  helper : (f : typ A → Path (coHomK (suc (suc n))) (0ₖ _) (0ₖ _)) (a : typ A) (fId : f (pt A) ≡ refl)
         → Kn→ΩKn+1 (suc n) (suspFunCharacFun {A = A} (suc n) (suspΩFun' (suc n) f) a) ≡ f a
  helper f a fId =
       Iso.rightInv (Iso-Kn-ΩKn+1 (suc n))
                         (sym (rCancelₖ _ (0ₖ (suc (suc n))))
                      ∙∙ cong (λ x → suspΩFun' (suc n) f x +ₖ 0ₖ (suc (suc n))) (merid a ∙ (sym (merid (pt A))))
                      ∙∙ rCancelₖ _ (0ₖ (suc (suc n))))
    ∙∙ ((λ i → sym (transportRefl (λ _ → 0ₖ (suc (suc n))) i)
                 ∙∙ cong (λ x → rUnitₖ (suc (suc n)) (suspΩFun' (suc n) f x) i) (merid a ∙ (sym (merid (pt A))))
                 ∙∙ transportRefl (λ _ → 0ₖ (suc (suc n))) i))
    ∙∙ (λ i → rUnit (congFunct (suspΩFun' (suc n) f) (merid a) (sym (merid (pt A))) i) (~ i))
    ∙∙ cong (λ p → f a ∙ sym p) fId
    ∙∙ sym (rUnit (f a))

suspFunCharac0 : ∀ {ℓ} {A : Pointed ℓ} → Iso (∥ ((Susp (typ A)) → coHomK 1) ∥₂) ∥ A →∙ (Int , 0) ∥₂
fun (suspFunCharac0 {A = A}) =
    sMap λ f → suspFunCharacFun {A = A} 0 f
  ,  (cong (ΩKn+1→Kn 0) ((λ i → sym (rCancelₖ _ (f north)) ∙∙ cong (λ x → f x -ₖ f north) (rCancel (merid (pt A)) i) ∙∙ rCancelₖ _ (f north))
                      ∙∙ (doubleCompPath-elim (sym (rCancelₖ _ (f north))) refl (rCancelₖ _ (f north)))
                      ∙∙ (cong (_∙ (rCancelₖ _ (f north))) (sym (rUnit (sym (rCancelₖ _ (f north))))))
                       ∙ (lCancel (rCancelₖ _ (f north)))))
inv suspFunCharac0 = sMap λ f → suspΩFun 0 (fst f)
rightInv (suspFunCharac0 {A = A}) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
    λ {(f , p)
      → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                   (funExt (λ x → (λ j → transp (λ i → helix (wedgeMapS¹ (intLoop (p j) (~ i)) base)) j
                                             ((transport (λ i → helix (trRec isGroupoidS¹ (λ x → x)
                                                                              (rUnitₖ 1 ∣ intLoop (f x) i ∣ j)))
                                                         (pos 0))))
                                        ∙ windingIntLoop (f x))))}
leftInv (suspFunCharac0 {A = A}) =
  SuspCohomElim {A = A} _ (λ _ → setTruncIsSet _ _)
    λ f fId → cong ∣_∣₂ (funExt λ {north → refl ; south → refl ; (merid a i) j → helper f a fId j i})
  where
  helper : (f : typ A → Path (coHomK 1) (0ₖ 1) (0ₖ 1)) (a : typ A) (fId : f (pt A) ≡ refl)
         → Kn→ΩKn+1 0 (suspFunCharacFun {A = A} 0 (suspΩFun' 0 f) a) ≡ f a
  helper f a fId =
      Iso.rightInv (Iso-Kn-ΩKn+1 0) (sym (rCancelₖ _ (0ₖ 1))
                                  ∙∙ cong (λ x → suspΩFun' 0 f x +ₖ 0ₖ 1) (merid a ∙ (sym (merid (pt A))))
                                  ∙∙ rCancelₖ _ (0ₖ 1))
   ∙∙ (λ i → sym (transportRefl (λ _ → 0ₖ 1) i)
           ∙∙ cong (λ x → rUnitₖ 1 (suspΩFun' 0 f x) i) (merid a ∙ (sym (merid (pt A))))
           ∙∙ transportRefl (λ _ → 0ₖ 1) i)
   ∙∙ (λ i → rUnit (congFunct (suspΩFun' 0 f) (merid a) (sym (merid (pt A))) i) (~ i))
   ∙∙ cong (λ p → f a ∙ sym p) fId
   ∙∙ sym (rUnit (f a))

isCohomTheoryZ' : ∀ {ℓ} → isCohomTheory {ℓ} coHomFunctor'
theMorph : ∀ {ℓ} (n : Int) → contravar {ℓ} (coHomFunctor' n)
fun (theMorph (pos zero) f) = sMap λ g → (λ x → fst g (fst f x)) , cong (fst g) (snd f) ∙ snd g
isHom (theMorph (pos zero) f) =
  sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f g → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
theMorph (pos (suc n)) f = coHomMorph _ (fst f)
fun (theMorph (negsuc n) f) = idfun _
isHom (theMorph (negsuc n) f) _ _ = refl

-- Contravariant functor
f* isCohomTheoryZ' n f = theMorph n f

-- Suspension --

-- existence of suspension equivalence
fst (Suspension (isCohomTheoryZ' {ℓ})) (pos zero) =
  invGroupEquiv
    (GrIsoToGrEquiv
      (Iso+Hom→GrIso (invIso suspFunCharac0)
                      (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                              λ f g → cong ∣_∣₂ (funExt λ {north → refl
                                                         ; south → refl
                                                         ; (merid a i) → {!!}}))))
fst (Suspension (isCohomTheoryZ' {ℓ})) (pos (suc n)) {A = A} =
  invGroupEquiv
    (GrIsoToGrEquiv
      (Iso+Hom→GrIso (invIso (suspFunCharac {A = A} n))
                      (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                              λ f g → cong ∣_∣₂ (funExt λ {north → refl
                                                         ; south → refl
                                                         ; (merid a i) → {!!}}))))
fst (Suspension (isCohomTheoryZ' {ℓ})) (negsuc zero) {A = A} =
  GrIsoToGrEquiv (Iso+Hom→GrIso (isContr→Iso (H0-susp {A = _ , pt A}) isContrUnit*)
                 λ _ _ → refl)
fst (Suspension (isCohomTheoryZ' {ℓ})) (negsuc (suc n)) = idGroupEquiv _
snd (Suspension (isCohomTheoryZ' {ℓ})) (f , p) (pos zero) =
  funExt (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ {(f , _) → cong ∣_∣₂ (funExt λ {north → refl
                                        ; south → refl
                                        ; (merid a i) → refl})})
snd (Suspension (isCohomTheoryZ' {ℓ})) (f , p) (pos (suc n)) =
  funExt (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f → cong ∣_∣₂ (funExt λ {north → refl
                                  ; south → refl
                                  ; (merid a i) → refl}))
snd (Suspension (isCohomTheoryZ' {ℓ})) (f , p) (negsuc zero) = refl
snd (Suspension (isCohomTheoryZ' {ℓ})) (f , p) (negsuc (suc n)) = refl

-- Exactness
fst (Exactness isCohomTheoryZ' f (pos zero)) =
  sElim (λ _ → isSetΠ λ _ → isProp→isSet propTruncIsProp)
    λ {(g , p) inker → pRec propTruncIsProp
                             (λ gId → ∣ ∣ (λ { (inl tt) → 0
                                            ; (inr b) → g b
                                            ; (push a i) → funExt⁻ (cong fst gId) a (~ i)}) , p ∣₂
                                            , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl) ∣)
                             (Iso.fun PathIdTrunc₀Iso inker)}
snd (Exactness isCohomTheoryZ' {A = A} {B = B} f (pos zero)) =
  sElim (λ _ → isSetΠ λ _ → isProp→isSet (setTruncIsSet _ _))
    λ {(g , p) → pRec (setTruncIsSet _ _)
                       (uncurry
                         (sElim (λ _ → isProp→isSet (isPropΠ λ _ → setTruncIsSet _ _))
                           λ {(pushmap , pushId)
                           → λ q → pRec (setTruncIsSet _ _)
                                          (λ q → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                                                             (funExt λ a → sym (funExt⁻ (cong fst q) (fst f a))
                                                                         ∙∙ cong pushmap ((sym (push a))
                                                                                       ∙∙ push (pt A)
                                                                                       ∙∙ cong inr (snd f))
                                                                         ∙∙ pushId)))
                                          (Iso.fun PathIdTrunc₀Iso q)}))}
fst (Exactness isCohomTheoryZ' {A = A} {B = B} f (pos (suc n))) =
  coHomPointedElim _ (pt B) (λ _ → isPropΠ λ _ → propTruncIsProp)
    λ g gId inker → pRec propTruncIsProp
                         (λ gIdTot → ∣ ∣ (λ { (inl tt) → 0ₖ _
                                            ; (inr b) → g b
                                            ; (push a i) → funExt⁻ gIdTot a (~ i)}) ∣₂
                                       , cong ∣_∣₂ (funExt λ b → refl) ∣)
                         (Iso.fun PathIdTrunc₀Iso inker)
snd (Exactness isCohomTheoryZ' {A = A} {B = B} f (pos (suc n))) =
  coHomPointedElim _ (pt B) (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
    λ g gId → pRec (setTruncIsSet _ _)
                    (uncurry λ cg p
                      → subst (isInKer (coHomGr (suc n) (typ B)) (coHomGr (suc n) (typ A))
                                                                  (coHomMorph (suc n) (fst f)))
                               p
                               (helper cg))
   where
   helper : (cg : _) → coHomFun (suc n) (fst f) (coHomFun (suc n) (cfcod (fst f)) cg) ≡ 0ₕ _
   helper = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ cg → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                                (λ p → (cong ∣_∣₂ (funExt λ x → cong cg (sym (push x))
                                                              ∙ p)))
                                (isConnectedPathKn _ (cg (inl tt)) (0ₖ (suc n)) .fst)

Exactness isCohomTheoryZ' f (negsuc n) =  (λ {tt* y → ∣ tt* , refl ∣})
                                         , λ {tt* y → refl}
-- Dimension
Dimension isCohomTheoryZ' n =
    ((0ₕ _)
      , (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          (λ f → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                        (λ f-true → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                                          (λ f-false → cong ∣_∣₂ (funExt (λ {(lift true) → f-true
                                                                          ; (lift false) → f-false})))
                                          (isConnectedPathKn n (0ₖ _) (f (lift false)) .fst))
                        (isConnectedPathKn n (0ₖ _) (f (lift true)) .fst))))
  , isContrUnit*

-- Binary wedges
BinaryWedge isCohomTheoryZ' (pos zero) =
  {!GrIsoToGrEquiv ?!}
BinaryWedge isCohomTheoryZ' (pos (suc n)) =
  {!!} -- GrIsoToGrEquiv (Hⁿ-⋁ _ _ n)
BinaryWedge isCohomTheoryZ' (negsuc n) =
  GrIsoToGrEquiv
    (compGroupIso (IsoContrGroupTrivialGroup {!!})
                  (invGroupIso (IsoContrGroupTrivialGroup (isOfHLevel× 0 isContrUnit* isContrUnit*))))

test : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → GroupIso (coHomRedGrDir 0 (A ⋁ B , inl (pt A)))
                 (dirProd (coHomRedGrDir 0 A) (coHomRedGrDir 0 B))
fun (GroupIso.map test) =
  sRec (isSet× setTruncIsSet setTruncIsSet)
       λ {(f , p) → ∣ (f ∘ inl) , p ∣₂
                   , ∣ (f ∘ inr) , cong f (sym (push tt)) ∙ p ∣₂}
isHom (GroupIso.map test) =
  sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
         λ {(f , p) (g , q) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
                                     , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl))}
inv test =
  uncurry (sRec2 setTruncIsSet
            λ {(f , p) (g , q) → ∣ (λ {(inl a) → f a
                                     ; (inr b) → g b
                                     ; (push tt i) → (p ∙ sym q) i})
                                     , p ∣₂})
rightInv test =
  uncurry
    (sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
      λ {(_ , _) (_ , _) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
                                  , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl))})
leftInv test =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
    λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                               (funExt λ {(inl a) → refl
                                        ; (inr b) → refl
                                        ; (push tt i) j → (cong (p ∙_) (symDistr (cong f (sym (push tt))) p)
                                                         ∙∙ assoc∙ p (sym p) (cong f (push tt))
                                                         ∙∙ cong (_∙ (cong f (push tt))) (rCancel p)
                                                          ∙ sym (lUnit (cong f (push tt)))) j i}))}
                                        -- Alt. use isOfHLevel→isOfHLevelDep
-- isCohomTheoryZ : isCohomTheory coHomGr (λ n → coHomMorph n)
-- Suspension isCohomTheoryZ =
--   transport (λ i → Σ[ F ∈ ((n : ℕ) {A : Pointed ℓ-zero}
--                           → GroupIso (coHomGr (suc n) (Susp (isoToPath (IsoPointedPointer {A = A}) (~ i))))
--                                       (coHomGr n (isoToPath (IsoPointedPointer {A = A}) (~ i)))) ]
--                     ({A B : Pointed ℓ-zero} (f : isoToPath (IsoPointedPointer {A = A}) (~ i) → isoToPath (IsoPointedPointer {A = B}) (~ i)) (n : ℕ) →
--                      coHomFun (suc n) (suspFun f) ∘ inv (F n) ≡
--                      inv (F n) ∘ coHomFun n f))
--             (pointerIso)
--   where
--   hom : (n : ℕ) → {A : Pointed ℓ-zero} → coHom (suc n) (Susp (Pointer A)) → coHom n (Pointer A)
--   hom n = sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid pt₀)) ∙∙ rCancelₖ (suc n) (f north))

--   hom⁻ : (n : ℕ) {A : Pointed ℓ-zero} → coHom n (Pointer A) → coHom (suc n) (Susp (Pointer A))
--   hom⁻ n = sMap (suspΩFun n)

--   ishom⁻ : (n : ℕ) {A : Pointed ℓ-zero}
--         → isGroupHom (coHomGr n (Pointer A)) (coHomGr (suc n) (Susp (Pointer A))) (hom⁻ n)
--   ishom⁻ zero {A = A} =
--     elim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--       λ f g → cong ∣_∣₂ (funExt λ {north → refl
--                                 ; south → refl
--                                 ; (merid a i) j → (Kn→ΩKn+1-hom 0 (f a) (g a)
--                                                  ∙ ∙≡+₁ (Kn→ΩKn+1 0 (f a)) (Kn→ΩKn+1 0 (g a))) j i})
--   ishom⁻ (suc n) {A = A} = elim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--       λ f g → cong ∣_∣₂ (funExt λ {north → refl
--                                 ; south → refl
--                                 ; (merid a i) j → (Kn→ΩKn+1-hom (suc n) (f a) (g a)
--                                                  ∙ ∙≡+₂ n (Kn→ΩKn+1 (suc n) (f a)) (Kn→ΩKn+1 (suc n) (g a))) j i})

--   pointerIso : Σ _ _
--   fst pointerIso n {A = A} = invGroupIso theIso
--     where
--     theIso : GroupIso (coHomGr n (Pointer A)) (coHomGr (suc n) (Susp (Pointer A)))
--     fun (map theIso) = hom⁻ n
--     isHom (map theIso) = ishom⁻ n
--     inv theIso = hom n
--     rightInv theIso =
--       SuspCohomElim {A = Pointer A , pt₀} _ (λ _ → setTruncIsSet _ _)
--                     λ f fId → cong ∣_∣₂ (funExt λ {north → refl
--                                              ; south → refl
--                                              ; (merid a i) j → helper n a f fId j i})
--       where
--       helper : (n : ℕ) (a : Pointer A) (f : (Pointer A) →  Path (coHomK (suc n)) (0ₖ (suc n)) (0ₖ (suc n))) → f pt₀ ≡ refl →
--                               cong (suspΩFun n
--          (λ x →
--             ΩKn+1→Kn n
--             ((λ i₁ → rCancelₖ (suc n) (0ₖ _) (~ i₁)) ∙∙
--              (λ i₁ →
--                 suspΩFun' n f ((merid x ∙ (λ i₂ → merid pt₀ (~ i₂))) i₁) -ₖ
--                 suspΩFun' n f north)
--              ∙∙ rCancelₖ (suc n) (suspΩFun' n f north))))
--          (merid a) ≡ f a
--       helper zero a f fId =
--           (λ i → Iso.rightInv (Iso-Kn-ΩKn+1 0)
--                    (transportRefl refl i
--                  ∙∙ cong (λ x → suspΩFun' 0 f x +ₖ 0ₖ _) (merid a ∙ sym (merid pt₀))
--                  ∙∙ transportRefl refl i) i)
--        ∙∙ sym (rUnit _)
--        ∙∙ (λ i → cong (λ x → rUnitₖ _ (suspΩFun' 0 f x) i) (merid a ∙ sym (merid pt₀)))
--        ∙∙ congFunct (suspΩFun' 0 f) (merid a) (sym (merid pt₀)) -- (λ i → cong {!!} {!merid a!} ∙ {!!})
--        ∙∙ (cong (f a ∙_) (cong sym fId)
--         ∙ sym (rUnit (f a)))
--       helper (suc n) a f fId = 
--         (λ i → Iso.rightInv (Iso-Kn-ΩKn+1 (suc n))
--                    (transportRefl refl i
--                  ∙∙ cong (λ x → suspΩFun' (suc n) f x +ₖ 0ₖ _) (merid a ∙ sym (merid pt₀))
--                  ∙∙ transportRefl refl i) i)
--        ∙∙ sym (rUnit _)
--        ∙∙ (λ i → cong (λ x → rUnitₖ _ (suspΩFun' (suc n) f x) i) (merid a ∙ sym (merid pt₀)))
--        ∙∙ congFunct (suspΩFun' (suc n) f) (merid a) (sym (merid pt₀))
--        ∙∙ (cong (f a ∙_) (cong sym fId)
--         ∙ sym (rUnit (f a)))
--     leftInv theIso = helper n
--       where
--       helper : (n : ℕ) → retract (hom⁻ n) (hom n)
--       helper zero = {!!}
--       helper (suc n) =
--         coHomPointerElim n (λ _ → setTruncIsSet _ _)
--           λ f fId →
--             cong ∣_∣₂ (funExt
--                        (pointerElim λ x →
--                          cong (ΩKn+1→Kn (suc n))
--                               (λ i → transportRefl refl i ∙∙ (λ i →
--                                      suspΩFun (suc n) (pointerElimFun n f fId)
--                                      ((merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁))) i)
--                                      -ₖ suspΩFun (suc n) (pointerElimFun n f fId) north)
--                                    ∙∙ transportRefl refl i)
--                      ∙∙ cong (ΩKn+1→Kn (suc n)) (sym (rUnit ((λ i →
--                                      suspΩFun (suc n) (pointerElimFun n f fId)
--                                      ((merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁))) i)
--                                      -ₖ suspΩFun (suc n) (pointerElimFun n f fId) north))))
--                      ∙∙ cong (ΩKn+1→Kn (suc n)) (λ i → cong (λ x → rUnitₖ _ x i)
--                                                  (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁)))))
--                      ∙∙ (λ i → ΩKn+1→Kn (suc n) (congFunct (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋) (sym (merid pt₀)) i))
--                      ∙∙ ΩKn+1→Kn-hom (suc n) (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋))
--                                               (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (sym (merid pt₀)))
--                      ∙∙ cong₂ _+ₖ_ (Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (f ⌊ x ⌋))
--                                    (cong (ΩKn+1→Kn (suc n)) (cong (cong ∣_∣) (cong sym (rCancel (merid (ptSn (suc n)))))))
--                      ∙∙ (cong (f ⌊ x ⌋ +ₖ_) (transportRefl (0ₖ _))
--                       ∙ rUnitₖ _ (f ⌊ x ⌋))))
--   snd pointerIso f zero = {!!}
--   snd pointerIso f (suc n) =
--     funExt
--       (coHomPointerElim _ (λ _ → setTruncIsSet _ _)
--         λ f fId → cong ∣_∣₂ (funExt λ {north → refl
--                                      ; south → refl
--                                      ; (merid a i) → refl}))
--   {-
--   where
--   grIso : GroupIso _ _
--   fun (map grIso) = sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid pt₀)) ∙∙ rCancelₖ (suc n) (f north))
--   isHom (map grIso) = {!!}
--   inv grIso = {!!}
--   rightInv grIso = {!!}
--   leftInv grIso = {!!} -}
-- {- fun (map (Suspension₁ isCohomTheoryZ n {A = (A , a)})) =
--   sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid a)) ∙∙ rCancelₖ (suc n) (f north))
-- isHom (map (Suspension₁ isCohomTheoryZ zero)) =
--   coHomPointedElim2 _ north (λ _ _ → setTruncIsSet _ _)
--     {!!}
-- isHom (map (Suspension₁ isCohomTheoryZ (suc n))) = {!!}
-- inv (Suspension₁ isCohomTheoryZ n) = {!!}
-- rightInv (Suspension₁ isCohomTheoryZ n) = {!!}
-- leftInv (Suspension₁ isCohomTheoryZ n) = {!!} -}
-- fst (Exactness isCohomTheoryZ f zero) = {!!}
-- fst (Exactness isCohomTheoryZ {A = A} {B = B} f (suc n)) =
--   coHomPointedElim _ (pt B)
--     (λ _ → isPropΠ λ _ → propTruncIsProp)
--     λ g gId inker
--       → pRec propTruncIsProp
--               (λ gIdTot → ∣ ∣ (λ {(inl tt) → 0ₖ _ ; (inr b) → g b ; (push a i) → funExt⁻ gIdTot a (~ i)}) ∣₂
--                             , cong ∣_∣₂ (funExt λ b → refl) ∣)
--               (Iso.fun PathIdTrunc₀Iso inker)
-- snd (Exactness isCohomTheoryZ {A = A} {B = B} f n) =
--   sElim {!snd (Exactness isCohomTheoryZ {A = A} {B = B} f n)!}
--         λ g → pRec {!!}
--                     (uncurry
--                       (sElim {!!}
--                              λ cg p → pRec (setTruncIsSet _ _)
--                                             (λ gId → cong ∣_∣₂ (funExt λ x → {!g!} ∙∙ {!cg (cfcod (fst f) (fst f x)) ≡ g (fst f x)!} ∙∙ {!cg!}))
--                                             (Iso.fun PathIdTrunc₀Iso p)))
--   where
--   helper : (n : ℕ) → (cg : _) → coHomFun n (fst f) (coHomFun n (cfcod (fst f)) cg) ≡ 0ₕ _
--   helper zero =
--     sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--           λ g → cong ∣_∣₂ (funExt λ a → cong g (sym (push a) ∙ push (pt A))
--                                      ∙∙ {!!}
--                                      ∙∙ {!g!})
--     where
--     help : {!!}
--     help = {!!}
--   helper (suc n) =
--     sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--            λ cg → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
--                          (λ p → (cong ∣_∣₂ (funExt λ x → cong cg (sym (push x))
--                                                        ∙ p)))
--                          (isConnectedPathKn _ (cg (inl tt)) (0ₖ (suc n)) .fst)
-- {-
-- snd (Exactness isCohomTheoryZ {A = A} {B = B} f (suc n)) =
--   coHomPointedElim _ (pt B) (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
--     λ g gId → pRec (setTruncIsSet _ _)
--                     (uncurry λ cg p
--                       → subst (isInKer (coHomGr (suc n) (typ B)) (coHomGr (suc n) (typ A))
--                                         (coHomMorph (suc n) (fst f)))
--                                 p
--                                 (helper cg))
--   where
--   helper : (cg : _) → coHomFun (suc n) (fst f) (coHomFun (suc n) (cfcod (fst f)) cg) ≡ 0ₕ _
--   helper = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--                  λ cg → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
--                                (λ p → (cong ∣_∣₂ (funExt λ x → cong cg (sym (push x))
--                                                              ∙ p)))
--                                (isConnectedPathKn _ (cg (inl tt)) (0ₖ (suc n)) .fst) -}
-- Dimension isCohomTheoryZ zero =
--   (0ₕ _) , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--                  λ f → {!pRec ? ?!}
-- Dimension isCohomTheoryZ (suc n) = {!!}
-- BinaryWedge isCohomTheoryZ n = Hⁿ-⋁ _ _ n
