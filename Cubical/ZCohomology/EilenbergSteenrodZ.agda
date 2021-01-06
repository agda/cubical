{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}

module Cubical.ZCohomology.EilenbergSteenrodZ where

open import Cubical.Homotopy.EilenbergSteenrod

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Int
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.SetTruncation
  renaming (map to sMap ; rec to sRec ; elim2 to sElim2; elim to sElim ; rec2 to sRec2)
open import Cubical.HITs.PropositionalTruncation
  renaming (map to pMap ; rec to pRec ; elim to pElim ; elim2 to pElim2)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; map to trMap ; elim to trEilim ; elim2 to trElim2)
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.HITs.Sn
open import Cubical.HITs.S1

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup

open coHomTheory
open Iso
open IsGroup
open GroupStr
open GroupIso
open GroupHom

private
  suspΩFun' : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → Path _ (0ₖ _) (0ₖ _))
           → Susp A → coHomK (suc n)
  suspΩFun' n f north = 0ₖ _
  suspΩFun' n f south = 0ₖ _
  suspΩFun' n f (merid a i) = f a i

  suspΩFun : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → coHomK n) → Susp A → coHomK (suc n)
  suspΩFun n f = suspΩFun' n λ a → Kn→ΩKn+1 n (f a)

  ≡suspΩFun : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) (f : Susp (typ A) → coHomK (suc n)) (p : f north ≡ 0ₖ _)
            → f ≡ suspΩFun' n λ a → sym p ∙∙ (cong f (merid a)) ∙∙ (cong f (sym (merid (pt A))) ∙ p)
  ≡suspΩFun n s f p i north = p i
  ≡suspΩFun n s f p i south = (cong f (sym (merid (pt s))) ∙ p) i
  ≡suspΩFun n s f p i (merid a j) =
    doubleCompPath-filler (sym p) (cong f (merid a)) (cong f (sym (merid (pt s))) ∙ p) i j

-- induction principle for Hⁿ(Susp A)
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

-- (Reduced) cohomology functor
coHomFunctor : {ℓ : Level}  (n : Int) → Pointed ℓ → AbGroup {ℓ}
coHomFunctor (pos n) = coHomRedGroup n
coHomFunctor (negsuc n) _ = trivialAbGroup

-- Alternative definition with reduced groups replaced by unrecued one for n ≥ 1
coHomFunctor' : {ℓ : Level} (n : Int) → Pointed ℓ → AbGroup {ℓ}
coHomFunctor' (pos zero) = coHomFunctor 0
coHomFunctor' (pos (suc n)) A = coHomGroup (suc n) (typ A)
coHomFunctor' (negsuc n) = coHomFunctor (negsuc n)

coHomFunctor≡coHomFunctor' : ∀ {ℓ} → coHomFunctor {ℓ} ≡ coHomFunctor'
coHomFunctor≡coHomFunctor' = funExt λ {(pos zero) → refl
                                     ; (pos (suc n)) → funExt λ A → sym (coHomGroup≡coHomRedGroup n A)
                                     ; (negsuc n) → refl}

-- Ĥ⁰(Susp A) is contractible
H0-susp : ∀ {ℓ} {A : Pointed ℓ} → isContr (coHomRed 0 (Susp (typ A) , north))
fst H0-susp = 0ₕ∙ _
snd (H0-susp {A = A}) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ {(f , p)
          → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                        (funExt λ {north → sym p
                                 ; south → sym p ∙ cong f (merid (pt A))
                                 ; (merid a i) j → isSet→isSet' (isSetInt)
                                                                  (sym p)
                                                                  (sym p ∙ cong f (merid (pt A)))
                                                                  refl (cong f (merid a)) i j}))}
-- We need that Hⁿ⁺¹(Susp A) ≃ Hⁿ(A)

private
  suspFunCharacFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
                     → ((Susp (typ A)) → coHomK (suc n))
                     → (typ A → (coHomK n))
  suspFunCharacFun {A = A} n f x = ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north))
                                                     ∙∙ cong (λ x → f x -[ (suc n) ]ₖ f north) ((merid x) ∙ sym (merid (pt A)))
                                                     ∙∙ rCancelₖ (suc n) (f north))

  linvLem : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f : typ A → Path (coHomK (suc n)) (0ₖ _) (0ₖ _))
                        (fId : f (pt A) ≡ refl)
                     → (x : _) → suspΩFun n (suspFunCharacFun {A = A} n (suspΩFun' n f)) x
                                 ≡ suspΩFun' n f x
  linvLem n f fId north = refl
  linvLem n f fId south = refl
  linvLem {A = A} n f fId (merid x i) j = helper n x f fId j i
    where
    helper : (n : ℕ) (a : typ A) (f : typ A → Path (coHomK (suc n)) (0ₖ _) (0ₖ _))
                       (fId : f (pt A) ≡ refl)
                     → Kn→ΩKn+1 n (suspFunCharacFun {A = A} n (suspΩFun' n f) a) ≡ f a
    helper zero a f fId =
        Iso.rightInv (Iso-Kn-ΩKn+1 0) (sym (rCancelₖ _ (0ₖ 1))
                                    ∙∙ cong (λ x → suspΩFun' 0 f x +ₖ 0ₖ 1) (merid a ∙ (sym (merid (pt A))))
                                    ∙∙ rCancelₖ _ (0ₖ 1))
     ∙∙ (λ i → sym (transportRefl (λ _ → 0ₖ 1) i)
             ∙∙ cong (λ x → rUnitₖ 1 (suspΩFun' 0 f x) i) (merid a ∙ (sym (merid (pt A))))
             ∙∙ transportRefl (λ _ → 0ₖ 1) i)
     ∙∙ (λ i → rUnit (congFunct (suspΩFun' 0 f) (merid a) (sym (merid (pt A))) i) (~ i))
     ∙∙ cong (λ p → f a ∙ sym p) fId
     ∙∙ sym (rUnit (f a))
    helper (suc n) a f fId =
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
    λ f fId → cong ∣_∣₂ (funExt (linvLem (suc n) f fId))

-- We also need that H¹(Susp A) ≃ Ĥ⁰(A)
suspFunCharac0 : ∀ {ℓ} {A : Pointed ℓ} → Iso (∥ ((Susp (typ A)) → coHomK 1) ∥₂) ∥ A →∙ (Int , 0) ∥₂
fun (suspFunCharac0 {A = A}) =
    sMap λ f → suspFunCharacFun {A = A} 0 f
  ,  (cong (ΩKn+1→Kn 0) ((λ i → sym (rCancelₖ _ (f north))
                                   ∙∙ cong (λ x → f x -ₖ f north) (rCancel (merid (pt A)) i)
                                   ∙∙ rCancelₖ _ (f north))
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
    λ f fId → cong ∣_∣₂ (funExt (linvLem 0 f fId))

-- We now prove that the alternative definition of cohomology is a cohomology theory.
private
  -- First, we need to that coHomFunctor' is contravariant
  theMorph : ∀ {ℓ} (n : Int) {A B : Pointed ℓ} (f : A →∙ B)
          → AbGroupHom (coHomFunctor' n B) (coHomFunctor' n A)
  fun (theMorph (pos zero) f) = sMap λ g → (λ x → fst g (fst f x)) , cong (fst g) (snd f) ∙ snd g
  isHom (theMorph (pos zero) f) =
    sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
           λ f g → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
  theMorph (pos (suc n)) f = coHomMorph _ (fst f)
  fun (theMorph (negsuc n) f) = idfun _
  isHom (theMorph (negsuc n) f) _ _ = refl

  open coHomTheory
  isCohomTheoryZ' : ∀ {ℓ} → coHomTheory {ℓ} coHomFunctor'
  Hmap isCohomTheoryZ' = theMorph

  -------------------------- Suspension --------------------------
  -- existence of suspension isomorphism
  fst (Suspension isCohomTheoryZ') (pos zero) {A = A} =
      invGroupEquiv
      (GrIsoToGrEquiv
        (Iso+Hom→GrIso (invIso suspFunCharac0)
                        (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                λ f g → cong ∣_∣₂ (funExt λ { north → refl
                                                           ; south → refl
                                                           ; (merid a i) j → helper a (fst f) (fst g) j i}))))
    where
    helper : (a : typ A) (f g : typ A → coHomK 0)
          → Kn→ΩKn+1 0 (f a +[ 0 ]ₖ g a)
           ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 0 (f a)) (Kn→ΩKn+1 0 (g a))
    helper a f g = Kn→ΩKn+1-hom 0 (f a) (g a)
                ∙ ∙≡+₁ (Kn→ΩKn+1 _ (f a)) (Kn→ΩKn+1 _ (g a))
  fst (Suspension isCohomTheoryZ') (pos (suc n)) {A = A} =
      invGroupEquiv
      (GrIsoToGrEquiv
        (Iso+Hom→GrIso (invIso (suspFunCharac {A = A} n))
                        (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                λ f g → cong ∣_∣₂ (funExt λ { north → refl
                                                           ; south → refl
                                                           ; (merid a i) j → helper a f g j i}))))
    where
    helper : (a : typ A) (f g : typ A → coHomK (suc n))
          → Kn→ΩKn+1 (suc n) (f a +ₖ g a)
           ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 (suc n) (f a)) (Kn→ΩKn+1 (suc n) (g a))
    helper a f g = Kn→ΩKn+1-hom (suc n) (f a) (g a)
                ∙ ∙≡+₂ n (Kn→ΩKn+1 _ (f a)) (Kn→ΩKn+1 _ (g a))
  fst (Suspension isCohomTheoryZ') (negsuc zero) {A = A} =
      GrIsoToGrEquiv (Iso+Hom→GrIso (isContr→Iso (H0-susp {A = _ , pt A}) isContrUnit*)
                      λ _ _ → refl)
  fst (Suspension isCohomTheoryZ') (negsuc (suc n)) = idGroupEquiv _

  -- naturality of the suspension isomorphism
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

  -------------------------- Exactness ---------------------------
  Exactness isCohomTheoryZ' {A = A} {B = B} f n = isoToPath (exactnessIso n f)
    where
    exactnessIso : (n : Int) (f : A →∙ B)
                → Iso (Ker (theMorph n f)) (Im (theMorph n (cfcod (fst f) , refl)))
    fun (exactnessIso (pos zero) (f , p)) =
      uncurry (sElim (λ _ → isSetΠ λ _ → isSetΣ setTruncIsSet λ _ → isProp→isSet propTruncIsProp)
                     λ {(g , q) inker → ∣ g , q ∣₂
                                       , pRec propTruncIsProp
                                              (λ gId → ∣ ∣ (λ { (inl tt) → 0
                                                              ; (inr b) → g b
                                                              ; (push a i) → funExt⁻ (cong fst gId) a (~ i)}) , q ∣₂
                                                       , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl) ∣)
                                              (Iso.fun PathIdTrunc₀Iso inker)})
    inv (exactnessIso (pos zero) (f , p)) =
      uncurry (sElim (λ _ → isSetΠ λ _ → isSetΣ setTruncIsSet λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                λ {(g , q) inim'
                  → ∣ g , q ∣₂
                   , pRec (setTruncIsSet _ _)
                          (uncurry
                            (sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 setTruncIsSet _ _))
                                   (λ pushmap pushId'
                                     → pRec (setTruncIsSet _ _)
                                             (λ pushId
                                               → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                                                             (funExt λ x → sym (funExt⁻ (cong fst pushId) (f x))
                                                                         ∙∙ cong (fst pushmap) (sym (push x) ∙ push (pt A))
                                                                         ∙∙ (cong (fst pushmap ∘ inr) p
                                                                           ∙ snd pushmap))))
                                             (Iso.fun PathIdTrunc₀Iso pushId'))))
                          inim'})
    rightInv (exactnessIso (pos zero) (f , p)) =
      uncurry (sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2
                                              (isSetΣ setTruncIsSet
                                                      (λ _ → isProp→isSet propTruncIsProp)) _ _)
                     λ {(p , q) _ → Σ≡Prop (λ _ → propTruncIsProp) refl})
    leftInv (exactnessIso (pos zero) (f , p)) =
      uncurry (sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2
                                              (isSetΣ setTruncIsSet
                                                      (λ _ → isProp→isSet (setTruncIsSet _ _))) _ _)
                     λ {(p , q) _ → Σ≡Prop (λ _ → setTruncIsSet _ _) refl})
    fun (exactnessIso (pos (suc n)) f) ker = (fst ker) , inIm-helper (fst ker) (snd ker)
      where
      inIm-helper : (x : coHom (suc n) (typ B))
                  → isInKer _ _ (theMorph (pos (suc n)) {A = A} {B = B} f) x
                  → isInIm _ _ (theMorph (pos (suc n)) {A = B} {B = _ , inr (pt B)} (cfcod (fst f) , refl)) x
      inIm-helper =
        coHomPointedElim _ (pt B) (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ g gId inker → pRec propTruncIsProp
                               (λ gIdTot → ∣ ∣ (λ { (inl tt) → 0ₖ _
                                                  ; (inr b) → g b
                                                  ; (push a i) → funExt⁻ gIdTot a (~ i)}) ∣₂
                                             , cong ∣_∣₂ (funExt λ b → refl) ∣)
                               (Iso.fun PathIdTrunc₀Iso inker)
    inv (exactnessIso (pos (suc n)) f) im = fst im , inKer-helper (fst im) (snd im)
      where
      inKer-helper : (x : coHom (suc n) (typ B))
                  → isInIm _ _ (theMorph (pos (suc n)) {A = B} {B = _ , inr (pt B)} (cfcod (fst f) , refl)) x
                  → isInKer _ _ (theMorph (pos (suc n)) {A = A} {B = B} f) x
      inKer-helper =
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
    rightInv (exactnessIso (pos (suc n)) f) _ = Σ≡Prop (λ _ → propTruncIsProp) refl
    leftInv (exactnessIso (pos (suc n)) f) _ = Σ≡Prop (λ _ → setTruncIsSet _ _) refl
    exactnessIso (negsuc n) (f , p) =
      isContr→Iso ((tt* , refl)
                   , λ {(tt* , p) → Σ≡Prop (λ _ → isOfHLevelPath 1 isPropUnit* _ _)
                                            refl})
                   ((tt* , ∣ tt* , refl ∣)
                   , λ {(tt* , p) → Σ≡Prop (λ _ → propTruncIsProp)
                                            refl})

  -------------------------- Dimension ---------------------------
  Dimension isCohomTheoryZ' (pos zero) p = ⊥-rec (p refl)
  fst (Dimension isCohomTheoryZ' (pos (suc n)) _) = 0ₕ _
  snd (Dimension isCohomTheoryZ' (pos (suc n)) _) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          (λ f → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                        (λ f-true → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                                          (λ f-false → cong ∣_∣₂ (funExt (λ {(lift true) → f-true
                                                                          ; (lift false) → f-false})))
                                          (isConnectedPathKn n (0ₖ _) (f (lift false)) .fst))
                        (isConnectedPathKn n (0ₖ _) (f (lift true)) .fst))
  Dimension isCohomTheoryZ' (negsuc n) _ = isContrUnit*

  ------------------------ Binary wedges -------------------------
  BinaryWedge isCohomTheoryZ' (pos zero) = GrIsoToGrEquiv (H⁰Red-⋁ _ _)
  BinaryWedge isCohomTheoryZ' (pos (suc n)) = GrIsoToGrEquiv (Hⁿ-⋁ _ _ n)
  BinaryWedge isCohomTheoryZ' (negsuc n) =
    GrIsoToGrEquiv
      (compGroupIso (IsoContrGroupTrivialGroup isContrUnit*)
                    (invGroupIso (IsoContrGroupTrivialGroup (isOfHLevel× 0 isContrUnit* isContrUnit*))))

-- Substituting back for our original theory, we are done
isCohomTheoryZ : ∀ {ℓ} → coHomTheory {ℓ} coHomFunctor
isCohomTheoryZ = subst coHomTheory (sym coHomFunctor≡coHomFunctor')
                       isCohomTheoryZ'
