{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.K-G-n-facts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.EilenbergMacLane1 renaming (rec to recEM1)
open import Cubical.HITs.SetTruncation
              renaming (rec to recSetTrunc ; elim to elimSetTrunc ;
                        elim2 to elim2SetTrunc ; map to mapSetTrunc ;
                        rec2 to sRec2)
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
              renaming (rec to recTrunc ; elim to elimTrunc)

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
              renaming (elim to elimEM)
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.ConnectedCovers.GeneralisingFreudenthal
open import Cubical.Homotopy.Serre.ConnectedCovers.PointedEquivalences
open import Cubical.Homotopy.Serre.ConnectedCovers.UsefulLemmas
open import Cubical.Homotopy.Serre.ConnectedCovers.EquivPreservation

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.LongExactSequence

open import Cubical.Homotopy.WhiteheadsLemma

private
  variable
    ℓ : Level
--not sure etc.
compEquivInv : {X Y Z : Type ℓ} (e : X ≃ Y) (e' : Y ≃ Z)
            → fst (invEquiv (e ∙ₑ e'))
            ≡ fst ((invEquiv e') ∙ₑ (invEquiv e))
compEquivInv {X = X} {Y = Y} {Z = Z} =
  EquivJ {A = X} {B = Y} (λ A e → (e' : Y ≃ Z)
         → fst (invEquiv (e ∙ₑ e')) ≡ fst ((invEquiv e') ∙ₑ (invEquiv e)))
  (EquivJ {A = Y} {B = Z} (λ A e'
         → fst (invEquiv ((idEquiv _) ∙ₑ e'))
          ≡ fst ((invEquiv e') ∙ₑ (invEquiv (idEquiv _))))
  refl)

compEquivInvEquiv : {U V : Pointed ℓ} {W X Y Z : Group ℓ}
                   (e : (U →∙ V) ≃ (GroupHom W X))
                   (e' : (GroupHom W X) ≃ (GroupHom Y Z))
                → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                                      → isEquiv (fst ((fst (invEquiv e')) f)))
                → (∀ (f : GroupHom W X) → isEquiv (fst f)
                                      → isEquiv
                                         (fst ((fst (invEquiv e)) f)))
                → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                                      → isEquiv
                                         (fst ((fst (invEquiv (e ∙ₑ e'))) f)))
compEquivInvEquiv e e' he' he f hf =
  transport (λ i → isEquiv (fst ((compEquivInv e e' (~ i)) f)))
            (he ((fst (invEquiv e')) f)
            (he' f hf))

compEquivInvEquiv' : {U V W X : Pointed ℓ} {Y Z : Group ℓ}
                     (e : (U →∙ V) ≃ (W →∙ X))
                     (e' : (W →∙ X) ≃ (GroupHom Y Z))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                     → isEquiv (fst ((fst (invEquiv e')) f)))
                  → (∀ (f : (W →∙ X)) → isEquiv (fst f)
                     → isEquiv (fst ((fst (invEquiv e)) f)))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                     → isEquiv (fst ((fst (invEquiv (e ∙ₑ e'))) f)))
compEquivInvEquiv' e e' he' he f hf =
  transport (λ i → isEquiv (fst ((compEquivInv e e' (~ i)) f)))
            (he ((fst (invEquiv e')) f)
            (he' f hf))

compEquivInvEquiv'' : {U V W X Y Z : Pointed ℓ} (n : ℕ)
                      (e : (U →∙ V) ≃ (W →∙ X))
                      (e' : (W →∙ X) ≃ (Y →∙ Z))
                   → (∀ (f : Y →∙ Z) → isEquiv (fst f)
                      → isEquiv (πFun n (fst (invEquiv e') f)))
                   → (∀ (f : W →∙ X) → isEquiv (πFun n f)
                      → isEquiv (πFun n (fst (invEquiv e) f)))
                   → (∀ (f : Y →∙ Z) → isEquiv (fst f)
                      → isEquiv (πFun n (fst (invEquiv (e ∙ₑ e')) f)))
compEquivInvEquiv'' n e e' he' he f hf =
  transport (λ i → isEquiv (πFun n ((compEquivInv e e' (~ i)) f)))
            (he ((fst (invEquiv e')) f)
            (he' f hf))

compEquivInvEquiv''' : {U V W X Y Z : Pointed ℓ} (n : ℕ)
                       (e : (U →∙ V) ≃ (W →∙ X))
                       (e' : (W →∙ X) ≃ (Y →∙ Z))
                    → (∀ (f : Y →∙ Z) → isEquiv (πFun n f)
                       → isEquiv (πFun n (fst (invEquiv e') f)))
                    → (∀ (f : W →∙ X) → isEquiv (πFun n f)
                       → isEquiv (πFun n (fst (invEquiv e) f)))
                    → (∀ (f : Y →∙ Z) → isEquiv (πFun n f)
                       → isEquiv (πFun n (fst (invEquiv (e ∙ₑ e')) f)))
compEquivInvEquiv''' n e e' he' he f hf =
  transport (λ i → isEquiv (πFun n ((compEquivInv e e' (~ i)) f)))
            (he ((fst (invEquiv e')) f)
            (he' f hf))

compEquivInvEquiv4 : {U V W X : Pointed ℓ} {Y Z : Group ℓ} (n : ℕ)
                     (e : (U →∙ V) ≃ (W →∙ X))
                     (e' : (W →∙ X) ≃ (GroupHom Y Z))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                       → isEquiv (πFun n (fst (invEquiv e') f)))
                  → (∀ (f : W →∙ X) → isEquiv (πFun n f)
                       → isEquiv (πFun n (fst (invEquiv e) f)))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                       → isEquiv (πFun n (fst (invEquiv (e ∙ₑ e')) f)))
compEquivInvEquiv4 n e e' he' he f hf =
  transport (λ i → isEquiv (πFun n ((compEquivInv e e' (~ i)) f)))
            (he (fst (invEquiv e') f)
            (he' f hf))

compEquivInvEquiv5 : {U V W X : Pointed ℓ} {Y Z : Group ℓ} (n : ℕ)
                     (e : (U →∙ V) ≃ (W →∙ X))
                     (e' : (W →∙ X) ≃ (GroupHom Y Z))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                       → isEquiv (fst (fst (invEquiv e') f)))
                  → (∀ (f : W →∙ X) → isEquiv (fst f)
                       → isEquiv (πFun n (fst (invEquiv e) f)))
                  → (∀ (f : GroupHom Y Z) → isEquiv (fst f)
                       → isEquiv (πFun n (fst (invEquiv (e ∙ₑ e')) f)))
compEquivInvEquiv5 n e e' he' he f hf =
  transport (λ i → isEquiv (πFun n ((compEquivInv e e' (~ i)) f)))
            (he (fst (invEquiv e') f)
            (he' f hf))

Ω→PathEquiv→Ω→ReflEquiv' : (X : Pointed ℓ) (Y : Type ℓ) (f : typ X → Y)
 (n : ℕ) → (y : Y) → (p : f (pt X) ≡ y)
 → isEquiv (fst (πHom {A = X} {B = (Y , y)} n (f , p)))
 → isEquiv (fst (πHom {A = X} {B = (Y , f (pt X))} n (f , refl)))
Ω→PathEquiv→Ω→ReflEquiv' X Y f n y =
  J (λ y' p → isEquiv (fst (πHom {A = X} {B = (Y , y')} n (f , p)))
 → isEquiv (fst (πHom {A = X} {B = (Y , f (pt X))} n (f , refl))))
   λ x → x

πHomEquivPath→WhiteheadHyp : (X Y : Pointed ℓ) (f : X →∙ Y) (n : ℕ)
 → isEquiv (fst (πHom n f))
 → isEquiv (fst (πHom {A = (typ X , pt X)}
                       {B = (typ Y , (fst f) (pt X))}
                       n
                       ((fst f) , refl)))
πHomEquivPath→WhiteheadHyp X Y f n =
  Ω→PathEquiv→Ω→ReflEquiv' X (typ Y) (fst f) n (pt Y) (snd f)

πHomEquivPath→πHomEquivPath : (X Y : Pointed ℓ) (f : X →∙ Y) (n : ℕ)
  {y : typ Y} (p : (fst f) (pt X) ≡ y)
  → isEquiv (fst (πHom n f))
  → isEquiv (fst (πHom {A = X} {B = (typ Y , y)} n ((fst f) , p)))
πHomEquivPath→πHomEquivPath X Y f n =
  J (λ y p → isEquiv (fst (πHom n f))
           → isEquiv (fst (πHom {A = X} {B = (typ Y , y)} n ((fst f) , p))))
    (πHomEquivPath→WhiteheadHyp X Y f n)

ConnConnIsEquiv : (A B : Type ℓ) (n : ℕ) → isConnected (2 + n) A
  → isConnected (2 + n) B → (f : ∥ A ∥₂ → ∥ B ∥₂) → isEquiv f
ConnConnIsEquiv A B n hA hB =
  ContrContrIsEquiv ∥ A ∥₂ ∥ B ∥₂
  (transport (λ i → isContr (propTrunc≡Trunc2 {A = A} (~ i)))
             (isConnSubtr' A n 2 hA))
  (transport (λ i → isContr (propTrunc≡Trunc2 {A = B} (~ i)))
             (isConnSubtr' B n 2 hB))


setMapIso : (A B : Type ℓ) (f : A → B) → isIso f → isIso (mapSetTrunc f)
fst (setMapIso A B f (g , secfg , retfg)) = mapSetTrunc g
fst (snd (setMapIso A B f (g , secfg , retfg))) =
  elimSetTrunc
  ( λ x → isSetPathImplicit)
  λ b → cong ∣_∣₂ (secfg b)
snd (snd (setMapIso A B f (g , secfg , retfg))) =
  elimSetTrunc
  ( λ x → isSetPathImplicit)
  λ a → cong ∣_∣₂ (retfg a)

setMapIsEquiv : (A B : Type ℓ) (f : A → B) → isEquiv f
  → isEquiv (mapSetTrunc f)
setMapIsEquiv A B f hyp =
  isoToIsEquiv
  (iso
   (mapSetTrunc f)
   (fst (setMapIso A B f ((Iso.inv (equivToIso (f , hyp)))
                       , (Iso.sec (equivToIso (f , hyp))
                        , Iso.ret (equivToIso (f , hyp))))))
   (fst (snd (setMapIso A B f ((Iso.inv (equivToIso (f , hyp)))
                       , (Iso.sec (equivToIso (f , hyp))
                        , Iso.ret (equivToIso (f , hyp)))))))
   (snd (snd (setMapIso A B f ((Iso.inv (equivToIso (f , hyp)))
                       , (Iso.sec (equivToIso (f , hyp))
                        , Iso.ret (equivToIso (f , hyp))))))))

1TypHomGr : (X : Pointed ℓ) → isOfHLevel 3 (typ X) → Group ℓ
fst (1TypHomGr X hX) = fst (Ω X)
GroupStr.1g (snd (1TypHomGr X hX)) = refl
GroupStr._·_ (snd (1TypHomGr X hX)) = _∙_
GroupStr.inv (snd (1TypHomGr X hX)) = _⁻¹
IsSemigroup.is-set
  (IsMonoid.isSemigroup
  (IsGroup.isMonoid
  (GroupStr.isGroup
  (snd (1TypHomGr X hX))))) = isOfHLevelPath' 2 hX (pt X) (pt X)
IsSemigroup.·Assoc
  (IsMonoid.isSemigroup
  (IsGroup.isMonoid
  (GroupStr.isGroup
  (snd (1TypHomGr X hX))))) = λ x y z → assoc x y z
IsMonoid.·IdR
  (IsGroup.isMonoid
  (GroupStr.isGroup
  (snd (1TypHomGr X hX)))) = λ x → (rUnit x) ⁻¹
IsMonoid.·IdL
  (IsGroup.isMonoid
  (GroupStr.isGroup
  (snd (1TypHomGr X hX)))) = λ x → (lUnit x) ⁻¹
IsGroup.·InvR
  (GroupStr.isGroup
  (snd (1TypHomGr X hX))) = rCancel'
IsGroup.·InvL
  (GroupStr.isGroup
  (snd (1TypHomGr X hX))) = lCancel

TruncIsosRespectComp : (X : Type ℓ) (hX : isOfHLevel 3 X) (x y : X)
  (p : ∥ x ≡ y ∥₂) (z : X) (q : ∥ y ≡ z ∥₂)
  → (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x z)))
         (((sRec2 squash₂ (λ p' q' → ∣ p' ∙ q' ∣₂)) p) q)
   ≡ (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x y))) p ∙
   (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX y z)) q)
TruncIsosRespectComp X hX x y =
  elimSetTrunc
  (λ p' → isSetΠ
  (λ z → isSetΠ
  (λ q → isOfHLevelPath 2
  (isOfHLevelPath' 2 hX _ _) _ _)))
  (J (λ y' p' → (z : X) (q : ∥ y' ≡ z ∥₂)
  → (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x z)))
     (((sRec2 squash₂ (λ p'' q'' → ∣ p'' ∙ q'' ∣₂)) ∣ p' ∣₂) q)
   ≡ (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x y'))) ∣ p' ∣₂ ∙
   (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX y' z)) q))
  λ z →
  elimSetTrunc
  (λ q → isOfHLevelPath 2
  (isOfHLevelPath' 2 hX _ _) _ _)
  (J (λ z' q'
  → (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x z')))
     (((sRec2 squash₂ (λ p'' q'' → ∣ p'' ∙ q'' ∣₂)) ∣ refl ∣₂) ∣ q' ∣₂)
   ≡ (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x x))) ∣ refl ∣₂ ∙
   (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x z')) ∣ q' ∣₂))
  refl))

TruncIsosRespectInv : (X : Type ℓ) (hX  : isOfHLevel 3 X) (x y : X)
  (p : ∥ x ≡ y ∥₂) →
  (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX y x))) (mapSetTrunc sym p)
  ≡ ((fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x y))) p) ⁻¹
TruncIsosRespectInv X hX x y =
  elimSetTrunc
  (λ p' →
  isOfHLevelPath 2 (isOfHLevelPath' 2 hX _ _) _ _)
  (J
  (λ y' p →
  (fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX y' x)))
  (mapSetTrunc sym ∣ p ∣₂)
  ≡ ((fst (setTrunc≃Trunc2 ∙ₑ truncIdempotent≃ 2 (hX x y'))) ∣ p ∣₂) ⁻¹)
  refl)

1TypHomGr≃πGr : (X : Pointed ℓ) (hX : isOfHLevel 3 (typ X))
  → GroupEquiv (πGr 0 X) (1TypHomGr X hX)
fst (1TypHomGr≃πGr X hX) =
  setTrunc≃Trunc2
  ∙ₑ truncIdempotent≃ 2 (isOfHLevelPath' 2 hX (pt X) (pt X))
IsGroupHom.pres· (snd (1TypHomGr≃πGr X hX)) p q =
  TruncIsosRespectComp (typ X) hX (pt X) (pt X) p (pt X) q
IsGroupHom.pres1 (snd (1TypHomGr≃πGr X hX)) = refl
IsGroupHom.presinv (snd (1TypHomGr≃πGr X hX)) =
  TruncIsosRespectInv (typ X) hX (pt X) (pt X)

GroupHomExtAux : (G H : Group ℓ) (f : (fst G) → (fst H))
  (r s : IsGroupHom (snd G) f (snd H)) → r ≡ s
IsGroupHom.pres· (GroupHomExtAux G H f r s i) x y =
  isSetGroup H _ _ (IsGroupHom.pres· r x y) (IsGroupHom.pres· s x y) i
IsGroupHom.pres1 (GroupHomExtAux G H f r s i) =
  isSetGroup H _ _ (IsGroupHom.pres1 r) (IsGroupHom.pres1 s) i
IsGroupHom.presinv (GroupHomExtAux G H f r s i) x =
  isSetGroup H _ _ (IsGroupHom.presinv r x) (IsGroupHom.presinv s x) i

GroupHomExt : (G H : Group ℓ) (h k : GroupHom G H)
  → (∀ (g : (fst G)) → (fst h) g ≡ (fst k) g) → h ≡ k
GroupHomExt G H h k hyp =
  ΣPathP ((funExt hyp) , toPathP (GroupHomExtAux G H _ _ _))

EM1UniversalPropertyAuxComp : (G : Group ℓ) (X : Pointed ℓ)
  → (hX : isOfHLevel 3 (typ X))
  → (h : fst G → fst (Ω X))
  → IsGroupHom (G .snd) h (1TypHomGr X hX .snd)
  → (g k : fst G)
     → PathP (λ j → h g j ≡ h ((snd G GroupStr.· g) k) j) (λ _ → pt X) (h k)
EM1UniversalPropertyAuxComp G X hX h
  record { pres· = p ; pres1 = pres1 ; presinv = presinv } g k =
  toPathP
  (movingTransportPathLemma (typ X) (pt X) (pt X) (h g)
  (h ((snd G GroupStr.· g) k)) (λ _ → pt X) ∙ cong (h g ⁻¹ ∙_)
  (((lUnit _) ⁻¹) ∙ p g k) ∙ assoc (h g ⁻¹) (h g) (h k)
  ∙ cong (_∙ h k) (lCancel (h g))
  ∙ lUnit (h k) ⁻¹)

Ω→presinv : {X Y : Pointed ℓ} (f : X →∙ Y) (x : typ (Ω X))
  → (fst (Ω→ f)) (x ⁻¹) ≡ ((fst (Ω→ f)) x) ⁻¹
Ω→presinv f x = refl

-- not sure where to find this

Ω→presrefl : {X Y : Pointed ℓ} (f : X →∙ Y)
  → (fst (Ω→ f)) refl ≡ refl
Ω→presrefl f = doubleCompPath-elim _ _ _
              ∙ cong (_∙ snd f) (rUnit (sym (snd f)) ⁻¹)
              ∙ lCancel (snd f)

EM1UnivPropGrpHom : (G : Group ℓ) (X : Pointed ℓ)
  (hX : isOfHLevel 3 (typ X))
  → (f : (EM₁ G , embase) →∙ X)
  → IsGroupHom (snd G) (fst (Ω→ f) ∘ emloop) (snd (1TypHomGr X hX))
IsGroupHom.pres· (EM1UnivPropGrpHom G X hX f) x y =
  cong (fst (Ω→ f)) (emloop-comp G x y) ∙ Ω→pres∙ f (emloop x) (emloop y)
IsGroupHom.pres1 (EM1UnivPropGrpHom G X hX f) =
  cong (fst (Ω→ f)) (emloop-1g G) ∙ Ω→presrefl f
IsGroupHom.presinv (EM1UnivPropGrpHom G X hX f) x =
  cong (fst (Ω→ f)) (emloop-inv G x)

repAssoc : {X : Type ℓ} {a b c d : X} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → ((p ∙ q) ∙ r) ∙ r ⁻¹ ∙ q ⁻¹ ≡ p
repAssoc p q r = ((p ∙ q) ∙ r) ∙ (r ⁻¹ ∙ q ⁻¹)
                   ≡⟨ assoc (p ∙ q) r (r ⁻¹ ∙ q ⁻¹) ⁻¹ ⟩
                 (p ∙ q) ∙ (r ∙ (r ⁻¹ ∙ q ⁻¹))
                   ≡⟨ cong ((p ∙ q) ∙_) (assoc r (r ⁻¹) (q ⁻¹)) ⟩
                 (p ∙ q) ∙ ((r ∙ r ⁻¹) ∙ q ⁻¹)
                   ≡⟨ cong (λ s → (p ∙ q) ∙ (s ∙ q ⁻¹)) (rCancel r) ⟩
                 (p ∙ q) ∙ (refl ∙ q ⁻¹)
                   ≡⟨ cong ((p ∙ q) ∙_) ((lUnit (q ⁻¹)) ⁻¹) ⟩
                 (p ∙ q) ∙ q ⁻¹
                   ≡⟨ (assoc p q (q ⁻¹)) ⁻¹ ⟩
                 p ∙ (q ∙ q ⁻¹)
                   ≡⟨ cong (p ∙_) (rCancel q) ⟩
                 p ∙ refl
                   ≡⟨ (rUnit p) ⁻¹ ⟩
                 p ∎

repAssoc' : {X : Type ℓ} {a b c d : X} (p : a ≡ b) (q : c ≡ b) (r : c ≡ d)
  → ((p ∙ (q ⁻¹)) ∙ r) ∙ r ⁻¹ ∙ q ≡ p
repAssoc' p q r = transport
                  (λ i → (((p ∙ q ⁻¹) ∙ r) ∙ r ⁻¹ ∙ (symInvo q (~ i)) ≡ p))
                  (repAssoc p (q ⁻¹) r)

EM1UniversalPropertyAux : (G : Group ℓ) (X : Pointed ℓ)
  → (hX : isOfHLevel 3 (typ X))
  → Iso ((EM₁ G , embase) →∙ X) (GroupHom G (1TypHomGr X hX))
fst (Iso.fun (EM1UniversalPropertyAux G X hX) f) = fst (Ω→ f) ∘ emloop
snd (Iso.fun (EM1UniversalPropertyAux G X hX) (f , p)) =
  EM1UnivPropGrpHom G X hX (f , p)
fst (Iso.inv (EM1UniversalPropertyAux G X hX) (h , p)) =
  elimGroupoid G (λ _ → hX) (pt X) (λ g → h g)
                 (EM1UniversalPropertyAuxComp G X hX h p)
snd (Iso.inv (EM1UniversalPropertyAux G X hX) (h , p)) = refl
Iso.sec (EM1UniversalPropertyAux G X hX) h =
  GroupHomExt G (1TypHomGr X hX) _ h
              λ g → (rUnit ((fst h) g)) ⁻¹
Iso.ret (EM1UniversalPropertyAux G X hX) f =
 ΣPathP ((funExt (elimSet G (λ g → isOfHLevelPathP' 2 hX _ _) (sym (snd f))
                 λ g → toPathP
                        (movFunTransportPathLemma
                        (fst f) (emloop g)
                        (fst (Ω→ f) (emloop g)) (snd f)
                ∙ cong (_∙ snd f ⁻¹ ∙ cong (fst f) (emloop g))
                  (doubleCompPath-elim (snd f ⁻¹) (cong (fst f) (emloop g) ⁻¹)
                                       (snd f))
                ∙ repAssoc' (snd f ⁻¹) (cong (fst f) (emloop g)) (snd f))))
                , toPathP (transportPathLemma' (snd f) refl
                           ∙ (rUnit (snd f)) ⁻¹))

CharInvComp : (G : Group ℓ) (X : Pointed ℓ)
              (hX : isOfHLevel 3 (typ X))
           → (h : GroupHom G (1TypHomGr X hX))
           → (fst (Ω→ (Iso.inv (EM1UniversalPropertyAux G X hX) h))) ∘ emloop
            ≡ (fst h)
CharInvComp G X hX h =
  cong fst (Iso.sec (EM1UniversalPropertyAux G X hX) h)

2Connected→pathConnected : {A : Type ℓ}
                            (cA : isConnected 2 A)
                            (a a' : A)
                            → ∥ a ≡ a' ∥ 1
2Connected→pathConnected cA a a' =
  Iso.fun (PathIdTruncIso 1) (isContr→isProp cA ∣ a ∣ ∣ a' ∣)


ΩPathEquiv→ReflEquiv' : {A B : Type ℓ} {a : A}
                         (f : A → B)
                         {b : B} (p : f a ≡ b)
                      → isEquiv (fst (Ω→ {A = (A , a)} {B = (B , b)} (f , p)))
                      → isEquiv
                           (fst (Ω→ {A = (A , a)} {B = (B , f a)} (f , refl)))
ΩPathEquiv→ReflEquiv' {A = A} {B = B} {a = a} f =
  J (λ b p → isEquiv (fst (Ω→ {A = (A , a)} {B = (B , b)} (f , p)))
           → isEquiv (fst (Ω→ {A = (A , a)} {B = (B , f a)} (f , refl))))
    λ x → x

ΩEquiv→Equiv' : {A B : Type ℓ} {a : A}
                 (cA : isConnected 2 A)
                 (f : A → B)
                 (hf0 : isEquiv (mapSetTrunc f))
                 {b : B} (p : f a ≡ b)
              → isEquiv (fst (Ω→ {A = (A , a)} {B = (B , b)} (f , p)))
              → isEquiv f
ΩEquiv→Equiv' {A = A} {B = B} {a = a} cA f hf0 p hfΩ =
  ΩEquiv→Equiv f hf0
    (λ a' → recTrunc (isPropIsEquiv _)
                      (J (λ a'' p → isEquiv (fst (Ω→ {A = (A , a'')}
                                                  {B = (B , f a'')}
                                                  (f , refl))))
                         (ΩPathEquiv→ReflEquiv' f p hfΩ))
                      (2Connected→pathConnected cA a a'))

is2Conn→InvEM1UPAPreservesIsEquiv : (G : Group ℓ) (X : Pointed ℓ)
  (hX : isOfHLevel 3 (typ X)) → isConnected 2 (typ X)
  → (h : GroupHom G (1TypHomGr X hX))
  → isEquiv (fst h)
  → isEquiv (fst (Iso.inv (EM1UniversalPropertyAux G X hX) h))
is2Conn→InvEM1UPAPreservesIsEquiv G X hX cX h hEq =
  ΩEquiv→Equiv'
    (isConnectedEM₁ G)
    (fst (Iso.inv (EM1UniversalPropertyAux G X hX) h))
    (ConnConnIsEquiv (EM₁ G) (typ X) 0 (isConnectedEM₁ G) cX
       (mapSetTrunc (fst (Iso.inv (EM1UniversalPropertyAux G X hX) h))))
    (snd (Iso.inv (EM1UniversalPropertyAux G X hX) h))
    (isIso→isEquiv (fst (Ω→ (Iso.inv (EM1UniversalPropertyAux G X hX) h)))
       (342-case1 emloop _ (Iso→isIso (invIso (ΩEM₁Iso G)))
         (isEquiv→isIso
          (fst (Ω→ (Iso.inv (EM1UniversalPropertyAux G X hX) h)) ∘ emloop)
          (transport (λ i → isEquiv (CharInvComp G X hX h (~ i))) hEq))))

EM1UniversalProperty : (G : Group ℓ) (X : Pointed ℓ)
  → isOfHLevel 3 (typ X)
  → ((EM₁ G , embase) →∙ X) ≃ (GroupHom G (πGr 0 X))
EM1UniversalProperty G X hX =
  isoToEquiv (EM1UniversalPropertyAux G X hX)
  ∙ₑ GroupHomEq' (πGr 0 X) (1TypHomGr X hX) (1TypHomGr≃πGr X hX) G

-- funny type-checking problems
EM1UniversalPropertyInvPreservesEquiv : (G : Group ℓ) (X : Pointed ℓ)
  (hX : isOfHLevel 3 (typ X))
  (cX : isConnected 2 (typ X))
  (h : GroupHom G (πGr 0 X))
  → isEquiv (fst h)
  → isEquiv (fst (fst (invEquiv (EM1UniversalProperty G X hX)) h))
EM1UniversalPropertyInvPreservesEquiv G X hX cX =
  compEquivInvEquiv (isoToEquiv (EM1UniversalPropertyAux G X hX))
                    _
                    (GroupHomEq'PreservesEquiv (πGr 0 X) (1TypHomGr X hX)
                                               (1TypHomGr≃πGr X hX) G)
                    (is2Conn→InvEM1UPAPreservesIsEquiv G X hX cX)


-- copied from Cubical.Algebra.Group.Instances.Unit with the universe level
-- changed
isContr→≡UnitGroup' : {G : Group ℓ} → isContr (fst G) → UnitGroup ≡ G
isContr→≡UnitGroup' {G = G} c =
  fst (GroupPath UnitGroup G)
    (invGroupEquiv ((isContr→≃Unit* c)
                  , (makeIsGroupHom (λ _ _ → refl))))
-- Not a permanent solution

HomogeneityFun : (X Y : Pointed ℓ) (f : X →∙ Y) → isHomogeneous X
  → typ X → typ Y
HomogeneityFun X Y f HX =
  λ x → ((fst f) ∘ fst (fst (au∙ X (typ X , x) (HX x)))) x

HomogeneityFun∙ : (X Y : Pointed ℓ) (f : X →∙ Y) (HX : isHomogeneous X)
  → (HomogeneityFun X Y f HX) (pt X) ≡ pt Y
HomogeneityFun∙ X Y f HX =
  cong (fst f) (snd (au∙ X (typ X , pt X) (HX (pt X)))) ∙ snd f

isConnectedPath^ : (m n : ℕ) (X : Pointed ℓ)
  → isConnected (m + n) (typ X) → isConnected m (typ ((Ω^ n) X))
isConnectedPath^ m zero X cX =
  transport (λ i → isConnected ((+-zero m) i) (typ X)) cX
isConnectedPath^ m (suc n) X cX =
  isConnectedPath m
  ( isConnectedPath^ (suc m) n X
    (transport (λ i → isConnected ((+-suc m n) i) (typ X)) cX)) _ _

isConnectedPath^' : (m n : ℕ) (X : Pointed ℓ)
  → isConnected (m + n) (typ X) → isConnected n (typ ((Ω^ m) X))
isConnectedPath^' m n X =
  transport
  (λ i → isConnected ((+-comm m n) (~ i)) (typ X)
       → isConnected n (typ ((Ω^ m) X)))
  (isConnectedPath^ n m X)

isConnected→TrivπGrfst : (n : ℕ) (X : Pointed ℓ)
  → isConnected (3 + n) (typ X) → isConnected 2 (typ ((Ω^ (1 + n)) X))
isConnected→TrivπGrfst n X cX =
  isConnectedPath 2 (isConnectedPath^ 3 n X cX) _ _

UnitMapEquiv : (F : Unit* {ℓ} → Unit* {ℓ}) → isEquiv F
fst (equiv-proof (UnitMapEquiv F) tt*) = tt* , refl
snd (equiv-proof (UnitMapEquiv F) tt*) (tt* , _) = refl

UnitMapEquivTransp : (G H : Type ℓ) → G ≡ Unit* → H ≡ Unit*
  → ∀ (h : G → H) → isEquiv h
UnitMapEquivTransp G H GUnit HUnit =
  transport (λ i → ((h : (GUnit (~ i)) → (HUnit (~ i))) → isEquiv h))
            UnitMapEquiv

UnitGroupHomEquiv : (G H : Group ℓ) → G ≡ UnitGroup → H ≡ UnitGroup
  → ∀ (h : GroupHom G H) → isEquiv (fst h)
UnitGroupHomEquiv G H GUnit HUnit h =
  UnitMapEquivTransp (fst G) (fst H)
                     (λ i → fst (GUnit i)) (λ i → fst (HUnit i))
                     (fst h)

Homogeneity→WhiteheadAux : (X Y : Pointed ℓ) (f : X →∙ Y)
  → (∀ (n : ℕ)
      → isEquiv (fst (πHom {A = X} {B = (typ Y , (fst f) (pt X))} n
                            (fst f , refl))))
  → ∀ (x : typ X) (p : pt X ≡ x)
  → (∀ (n : ℕ)
      → isEquiv (fst (πHom {A = (typ X , x)} {B = (typ Y , (fst f) x)} n
                            (fst f , refl))))
Homogeneity→WhiteheadAux X Y f hf x =
  J (λ x p → ∀ (n : ℕ)
           → isEquiv (fst (πHom {A = (typ X , x)} {B = (typ Y , (fst f) x)} n
                                 (fst f , refl))))
    hf

Homogeneity→WhiteheadHyp : (X Y : Pointed ℓ) (f : X →∙ Y)
  (HX : isConnected 2 (typ X))
  → (∀ (n : ℕ) → isEquiv (fst (πHom n f)))
  → (∀ (x : typ X) (n : ℕ)
        → isEquiv
           ( fst (πHom { A = (typ X , x)}
                       { B = (typ Y , ((fst f) x))}
                       ( n)
                       ( (fst f) , refl))))
Homogeneity→WhiteheadHyp X Y f HX eqf x =
  elimTrunc {A = pt X ≡ x} {n = 1}
            {B = λ _ → (∀ (n : ℕ)
                  → isEquiv
                     ( fst (πHom { A = (typ X , x)}
                                 { B = (typ Y , ((fst f) x))}
                                 ( n)
                                 ( (fst f) , refl))))}
            (λ _ → isPropΠ (λ _ → isPropIsEquiv _))
            (Homogeneity→WhiteheadAux X Y f
            (λ n → πHomEquivPath→WhiteheadHyp X Y f n (eqf n)) x)
            (Iso.fun (PathIdTruncIso 1) (((snd HX) ∣ pt X ∣) ⁻¹ ∙ (snd HX) ∣ x ∣))

AuxKGnUniversal1 : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → isOfHLevel (4 + n) (typ X)
  → (EM∙ G (2 + n) →∙ X) ≃ (EM-raw∙ G (2 + n) →∙ X)
AuxKGnUniversal1 G X n hX =
  isoToEquiv
  (Σ-cong-iso
  (univTrunc
   {A = EM-raw G (2 + n)}
   {ℓ = _}
   (4 + n)
   {B = (fst X) , hX})
   (λ x → idIso))

CharInvAux : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → (f : EM-raw∙ G (2 + n) →∙ X)
  → (fst (fst (invEquiv (AuxKGnUniversal1 G X n hX)) f))
   ≡ recTrunc hX (fst f)
CharInvAux G X n hX f = refl

CharInvAux' : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
           → (hX : isOfHLevel (4 + n) (typ X))
           → (f : EM-raw∙ G (2 + n) →∙ X)
           → isEquiv (πFun (suc n) (recTrunc∙ (4 + n) hX f))
           → isEquiv
              (πFun (suc n) (fst (invEquiv (AuxKGnUniversal1 G X n hX)) f))
CharInvAux' G X n hX f =
  πHomEquivPath→πHomEquivPath
  (EM∙ G (2 + n))
  X
  (recTrunc∙ (4 + n) hX f)
  (1 + n)
  (snd (fst (invEquiv (AuxKGnUniversal1 G X n hX)) f))

InvAuxKGnUniversal1PreservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → (f : EM-raw∙ G (2 + n) →∙ X)
  → isEquiv (πFun (1 + n) f)
  → isEquiv (πFun (1 + n) (fst (invEquiv (AuxKGnUniversal1 G X n hX)) f))
InvAuxKGnUniversal1PreservesEquiv G X n hX f hf =
  CharInvAux' G X n hX f
  (isIso→isEquiv
   (πFun (1 + n) (recTrunc∙ (4 + n) hX f))
   (SpΩRecConcl f n hX (isEquiv→isIso (πFun (1 + n) f) hf)))

AuxKGnUniversal2 : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → isOfHLevel (4 + n) (typ X)
  → (EM∙ G 1 →∙ ((Ω^ (1 + n)) X)) ≃ (AbGroupHom G (πAb n X))
AuxKGnUniversal2 G X zero hX =
  EM1UniversalProperty _ _ (isOfHLevelPath' 3 hX _ _)
  ∙ₑ LoopAbHomZero G X
AuxKGnUniversal2 G X (suc n) hX =
  →∙CommEquivΩ^ X (EM∙ G 1) (1 + n)
  ∙ₑ AuxKGnUniversal2 G (Ω X) n (isOfHLevelPath' (4 + n) hX _ _)
  ∙ₑ LoopAbHomN G X n

InvAuxKGnUniversal2PreservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → (cX : isConnected (3 + n) (typ X))
  → (f : AbGroupHom G (πAb n X))
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (AuxKGnUniversal2 G X n hX)) f))
InvAuxKGnUniversal2PreservesEquiv G X zero hX cX f hf =
  compEquivInvEquiv (EM1UniversalProperty _ _ (isOfHLevelPath' 3 hX _ _))
                    (LoopAbHomZero G X)
                    (LoopAbHomZeroPreservesEquiv G X)
                    (EM1UniversalPropertyInvPreservesEquiv (AbGroup→Group G)
                       (Ω X) (isOfHLevelPath' 3 hX _ _)
                       (isConnectedPath 2 cX _ _))
                    f hf
InvAuxKGnUniversal2PreservesEquiv G X (suc n) hX cX =
  compEquivInvEquiv
  (→∙CommEquivΩ^ X (EM∙ G 1) (1 + n)
  ∙ₑ AuxKGnUniversal2 G (Ω X) n (isOfHLevelPath' (4 + n) hX _ _))
  (LoopAbHomN G X n)
  (LoopAbHomNPreservesEquiv G X n)
  (compEquivInvEquiv'
   (→∙CommEquivΩ^ X (EM∙ G 1) (1 + n))
   (AuxKGnUniversal2 G (Ω X) n (isOfHLevelPath' (4 + n) hX _ _))
   (InvAuxKGnUniversal2PreservesEquiv G (Ω X) n
      (isOfHLevelPath' (4 + n) hX _ _)
      (isConnectedPath (3 + n) cX _ _))
   (→∙CommEquivΩ^-preservesEquiv X (EM∙ G 1) (1 + n)))

AuxKGnUniversal3 : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → isOfHLevel (4 + n) (typ X)
  → (EM-raw∙ G (2 + n) →∙ X) ≃ (EM∙ G 1 →∙ ((Ω^ (1 + n)) X))
AuxKGnUniversal3 G X n hX =
  EM-raw∙-SuspEM1Eq G X n
  ∙ₑ →∙CommEquivSusp^ (EM∙ G 1) X n
  ∙ₑ isoToEquiv (Loop^Susp^AdjunctionIso (EM∙ G 1) X (1 + n))

invAuxKGnUniversal3-preservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → (f : EM∙ G 1 →∙ ((Ω^ (1 + n)) X))
  → (isEquiv (fst f))
  → isEquiv (πFun (1 + n)
             (fst (invEquiv
             (AuxKGnUniversal3 G X n hX)) f))
invAuxKGnUniversal3-preservesEquiv G X n hX =
  compEquivInvEquiv'' (1 + n)
  (EM-raw∙-SuspEM1Eq G X n)
  (→∙CommEquivSusp^ (EM∙ G 1) X n
  ∙ₑ isoToEquiv (Loop^Susp^AdjunctionIso (EM∙ G 1) X (1 + n)))
  (compEquivInvEquiv'' (1 + n)
   (→∙CommEquivSusp^ (EM∙ G 1) X n)
   (isoToEquiv (Loop^Susp^AdjunctionIso (EM∙ G 1) X (1 + n)))
   (LoopSuspIsoπFunEquiv' G X n)
   (→∙CommEquivSusp^-preservesEquiv (EM∙ G 1) X (1 + n) n))
  (EM-raw∙-SuspEM1Eq-preservesEquiv G X (1 + n) n)

KGnUniversal : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → isOfHLevel (4 + n) (typ X)
  → (EM∙ G (2 + n) →∙ X) ≃ (AbGroupHom G (πAb n X))
KGnUniversal G X n hX =
  AuxKGnUniversal1 G X n hX
  ∙ₑ AuxKGnUniversal3 G X n hX
  ∙ₑ AuxKGnUniversal2 G X n hX

invKGnUniversalPreservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  (hX : isOfHLevel (4 + n) (typ X))
  → isConnected (3 + n) (typ X)
  → (h : AbGroupHom G (πAb n X))
  → isEquiv (fst h)
  → isEquiv (πFun (1 + n) (fst (invEquiv (KGnUniversal G X n hX)) h))
invKGnUniversalPreservesEquiv G X n hX cX =
  compEquivInvEquiv4 (1 + n)
  (AuxKGnUniversal1 G X n hX)
  (AuxKGnUniversal3 G X n hX
  ∙ₑ AuxKGnUniversal2 G X n hX)
  (compEquivInvEquiv5 (1 + n)
    (AuxKGnUniversal3 G X n hX)
    (AuxKGnUniversal2 G X n hX)
    (InvAuxKGnUniversal2PreservesEquiv G X n hX cX)
    (invAuxKGnUniversal3-preservesEquiv G X n hX))
  (InvAuxKGnUniversal1PreservesEquiv G X n hX)

KGnWhiteheadFun : (X : Pointed ℓ) (n : ℕ) → isOfHLevel (4 + n) (typ X)
  → EM∙ (πAb n X) (2 + n) →∙ X
KGnWhiteheadFun X n hX = fst (invEquiv (KGnUniversal (πAb n X) X n hX))
                         idGroupHom

3+h+1+k=h+1+3+k : (h k : ℕ) → (suc (suc (suc (h + suc k))))
                             ≡ (h + 1) + (suc (suc (suc k)))
3+h+1+k=h+1+3+k h k =
  cong (λ n → suc (suc n)) (cong (_+ suc k) (+-comm 1 h)
                             ∙ +-assoc h 1 (suc k) ⁻¹)
  ∙ cong (λ n → suc n) (cong (_+ suc (suc k)) (+-comm 1 h)
                         ∙ +-assoc h 1 (suc (suc k)) ⁻¹)
  ∙ cong (_+ (suc (suc (suc k)))) (+-comm 1 h)

3+h+1+kConn→3+kConn : {A : Type ℓ} (h k : ℕ)
                                → isConnected (suc (suc (suc (h + suc k)))) A
                                → isConnected (suc (suc (suc k))) A
3+h+1+kConn→3+kConn {A = A} h k hA =
  isConnectedSubtr (suc (suc (suc k))) (h + 1)
  (transport (λ i → isConnected (3+h+1+k=h+1+3+k h k i) A) hA)

KGnWhthdFnHypTrLT : (X : Pointed ℓ) (n : ℕ)
  → isConnected (3 + n) (typ X) → (hX : isOfHLevel (4 + n) (typ X))
  → (k : ℕ) → (k < 1 + n) → isEquiv (fst (πHom k (KGnWhiteheadFun X n hX)))
KGnWhthdFnHypTrLT X n cX hX k (zero , p) =
  UnitGroupHomEquiv
  (πGr k (EM∙ (πAb n X) (2 + n))) (πGr k X)
  (sym (isContr→≡UnitGroup'
        (transport (λ i → isContr (π (p (~ i)) (EM∙ (πAb n X) (2 + n))))
        (transport (λ i → isContr (propTrunc≡Trunc2
                                    {A = typ ((Ω^ (1 + n))
                                    (EM∙ (πAb n X) (2 + n)))} (~ i)))
                   (isConnected→TrivπGrfst n (EM∙ (πAb n X) (2 + n))
                                              (isConnectedEM (2 + n)))))))
  (sym (isContr→≡UnitGroup' (transport (λ i → isContr (π (p (~ i)) X))
       (transport (λ i → isContr (propTrunc≡Trunc2 {A = typ ((Ω^ (1 + n)) X)}
                  (~ i))) (isConnected→TrivπGrfst n X cX)))))
  (πHom k (KGnWhiteheadFun X n hX))
KGnWhthdFnHypTrLT X n cX hX k (suc h , p) =
  UnitGroupHomEquiv (πGr k (EM∙ (πAb n X) (2 + n))) (πGr k X)
  (sym (isContr→≡UnitGroup'
         (transport (λ i → isContr (propTrunc≡Trunc2
                                     {A = typ ((Ω^ (1 + k))
                                     (EM∙ (πAb n X) (2 + n)))} (~ i)))
                    (isConnected→TrivπGrfst k (EM∙ (πAb n X) (2 + n))
                       (3+h+1+kConn→3+kConn h k
                         (transport (λ i → isConnected
                                            (suc (suc (p (~ i))))
                                            (typ (EM∙ (πAb n X) (suc (suc n)))))
                                    (isConnectedEM (2 + n))))))))
  (sym (isContr→≡UnitGroup'
         (transport (λ i → isContr (propTrunc≡Trunc2
                                     {A = typ ((Ω^ (1 + k)) X)} (~ i)))
                    (isConnected→TrivπGrfst k X
                      (3+h+1+kConn→3+kConn h k
                        (transport (λ i → isConnected (suc (suc (p (~ i))))
                                                       (typ X))
                                           cX))))))
  (πHom k (KGnWhiteheadFun X n hX))

KGnWhthdFnHypTrEQ : (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → isConnected (3 + n) (typ X)
  → isEquiv (fst (πHom (1 + n) (KGnWhiteheadFun X n hX)))
KGnWhthdFnHypTrEQ X n hX cX =
  invKGnUniversalPreservesEquiv
  (πAb n X) X n hX cX idGroupHom (snd (idEquiv _))

isOfHLevel→isOfHLevelTruncLT : (A : Type ℓ) (m n : ℕ) → isOfHLevel n A
  → (m < n) → isOfHLevel n (∥ A ∥ m)
isOfHLevel→isOfHLevelTruncLT A m n hA (h , p) =
  transport (λ i → isOfHLevel (p i) (∥ A ∥ m))
  (transport (λ i → isOfHLevel ((+-assoc h 1 m) (~ i)) (∥ A ∥ m))
  (isOfHLevelPlus (h + 1) (isOfHLevelTrunc m)))

isOfHLevel→isOfHLevelTruncGT : (A : Type ℓ) (m n : ℕ) → isOfHLevel n A
  → (n < m) → isOfHLevel n (∥ A ∥ m)
isOfHLevel→isOfHLevelTruncGT A m n hA (h , p) =
  transport (λ i → isOfHLevel n (truncIdempotent {A = A} m
                                  (transport (λ i → isOfHLevel (p i) A)
                                  (transport (λ i → isOfHLevel
                                                     (+-assoc h 1 n (~ i)) A)
                                             (isOfHLevelPlus (h + 1) hA)))
                                  (~ i)))
            hA

isOfHLevel→isOfHLevelTruncTrich : (A : Type ℓ) (m n : ℕ) → isOfHLevel n A
  → Trichotomy m n → isOfHLevel n (∥ A ∥ m)
isOfHLevel→isOfHLevelTruncTrich A m n hA (lt T) =
  isOfHLevel→isOfHLevelTruncLT A m n hA T
isOfHLevel→isOfHLevelTruncTrich A m n hA (eq T) =
  transport (λ i → isOfHLevel (T i) (∥ A ∥ m)) (isOfHLevelTrunc m)
isOfHLevel→isOfHLevelTruncTrich A m n hA (gt T) =
  isOfHLevel→isOfHLevelTruncGT A m n hA T

isOfHLevel→isOfHLevelTrunc : (A : Type ℓ) (m n : ℕ) → isOfHLevel n A
  → isOfHLevel n (∥ A ∥ m)
isOfHLevel→isOfHLevelTrunc A m n hA =
   isOfHLevel→isOfHLevelTruncTrich A m n hA (m ≟ n)

isOfHLevel→isOfHLevelΩ^ : (A : Pointed ℓ) (n m : ℕ) → isOfHLevel n (typ A)
  → isOfHLevel n (typ ((Ω^ m) A))
isOfHLevel→isOfHLevelΩ^ A n zero hA = hA
isOfHLevel→isOfHLevelΩ^ A n (suc m) hA =
  isOfHLevelPath n (isOfHLevel→isOfHLevelΩ^ A n m hA) _ _

isOfHLevel→isOfHLevelΩ^' : (A : Pointed ℓ) (n m : ℕ)
  → isOfHLevel (m + n) (typ A) → isOfHLevel n (typ ((Ω^ m) A))
isOfHLevel→isOfHLevelΩ^' A n zero hA = hA
isOfHLevel→isOfHLevelΩ^' A n (suc m) hA =
  isOfHLevelPath' n
  (isOfHLevel→isOfHLevelΩ^' A (suc n) m
  (transport (λ i → isOfHLevel ((+-suc m n) (~ i)) (typ A)) hA)) _ _

isOfHLevel→isPropΩ^ : (A : Pointed ℓ) (n : ℕ)
  → isOfHLevel (1 + n) (typ A) → isProp (typ ((Ω^ n) A))
isOfHLevel→isPropΩ^ A n hA =
  isOfHLevel→isOfHLevelΩ^' A 1 n
  (transport (λ i → isOfHLevel ((+-comm 1 n) i) (typ A)) hA)

2+1+h+2+n=1+h+4+n : (h n : ℕ) → 1 + (1 + (suc h + suc (1 + n)))
                               ≡ (1 + h) + (4 + n)
2+1+h+2+n=1+h+4+n h n =
  cong suc (cong (_+ suc (suc n)) (+-comm 1 (suc h))
            ∙ +-assoc (suc h) 1 (suc (suc n)) ⁻¹)
  ∙ cong (_+ suc (suc (suc n))) (+-comm 1 (suc h))
  ∙ +-assoc (suc h) 1 (suc (suc (suc n))) ⁻¹

isOfHLevelArith : {X : Type ℓ} (h k n : ℕ) → (suc h + suc (1 + n) ≡ k)
               → isOfHLevel (4 + n) X
               → isOfHLevel (1 + (1 + k)) X
isOfHLevelArith {X = X} h k n p hX =
  transport (λ i → isOfHLevel (1 + (1 + (p i))) X)
  (transport (λ i → isOfHLevel (2+1+h+2+n=1+h+4+n h n (~ i)) X)
             (isOfHLevelPlus (1 + h) hX))

KGnWhthdFnHypTrGT : (X : Pointed ℓ) (n : ℕ)
  → (hX : isOfHLevel (4 + n) (typ X))
  → (k : ℕ) → (k > 1 + n) → isEquiv (fst (πHom k (KGnWhiteheadFun X n hX)))
KGnWhthdFnHypTrGT X n hX k (zero , p) =
  UnitGroupHomEquiv
  (πGr k (EM∙ (πAb n X) (2 + n))) (πGr k X)
  (sym (isContr→≡UnitGroup'
       (transport (λ i → isContr (π (suc (p i)) (EM∙ (πAb n X) (suc (suc n)))))
       (transport (λ i → isContr (propTrunc≡Trunc2
                          {A = typ ((Ω^ (3 + n)) (EM∙ (πAb n X) (2 + n)))}
                          (~ i)))
                          (inhProp→isContr
                          ∣ pt ((Ω^ (3 + n)) (EM∙ (πAb n X) (2 + n))) ∣
                          (isOfHLevel→isOfHLevelTrunc
                           (typ ((Ω^ (3 + n))
                           (EM∙ (πAb n X) (2 + n)))) 2 1
                           (isOfHLevel→isPropΩ^ (EM∙ (πAb n X) (2 + n)) (3 + n)
                           (transport
                           (λ i → isOfHLevel ((+-assoc 1 3 n) (~ i))
                           (typ (EM∙ (πAb n X) (2 + n))))
                           (hLevelEM (πAb n X) (2 + n))))))))))
  (sym (isContr→≡UnitGroup'
       (transport (λ i → isContr (π (suc (p i)) X))
       (transport (λ i → isContr (propTrunc≡Trunc2
                                  {A = typ ((Ω^ (3 + n)) X)} (~ i)))
       (isOfHLevel→isOfHLevelTrunc (typ ((Ω^ (3 + n)) X)) 2 0
       (inhProp→isContr (pt ((Ω^ (3 + n)) X))
       (isOfHLevel→isPropΩ^ X (3 + n)
       (transport (λ i → isOfHLevel ((+-assoc 1 3 n) (~ i)) (typ X))
       hX))))))))
  (πHom k (KGnWhiteheadFun X n hX))
KGnWhthdFnHypTrGT X n hX k (suc h , p) =
  UnitGroupHomEquiv
  (πGr k (EM∙ (πAb n X) (2 + n)))
  (πGr k X)
  (sym (isContr→≡UnitGroup'
       (transport (λ i → isContr (propTrunc≡Trunc2
                                  {A = typ ((Ω^ (1 + k))
                                            (EM∙ (πAb n X) (2 + n)))} (~ i)))
                  (inhProp→isContr
                  ∣ pt ((Ω^ (1 + k)) (EM∙ (πAb n X) (2 + n))) ∣ₕ
                  (isOfHLevel→isOfHLevelTrunc
                   (typ ((Ω^ (1 + k)) (EM∙ (πAb n X) (2 + n)))) 2 1
                  (isOfHLevel→isPropΩ^ (EM∙ (πAb n X) (2 + n)) (1 + k)
                    (isOfHLevelArith h k n p (hLevelEM (πAb n X) (2 + n)))))))))
  (sym (isContr→≡UnitGroup'
       (transport (λ i → isContr (propTrunc≡Trunc2
                                   {A = typ ((Ω^ (1 + k)) X)} (~ i)))
                  (inhProp→isContr
                  ∣ pt ((Ω^ (1 + k)) X) ∣ₕ
                  (isOfHLevel→isOfHLevelTrunc (typ ((Ω^ (1 + k)) X)) 2 1
                   (isOfHLevel→isPropΩ^ X (1 + k)
                    (isOfHLevelArith h k n p hX)))))))
  (πHom k (KGnWhiteheadFun X n hX))

KGnWhiteheadFunHypTrich : (X : Pointed ℓ) (n : ℕ)
  → isConnected (3 + n) (typ X) → (hX : isOfHLevel (4 + n) (typ X))
  → (k : ℕ) → Trichotomy k (1 + n)
  → isEquiv (fst (πHom k (KGnWhiteheadFun X n hX)))
KGnWhiteheadFunHypTrich X n cX hX k (lt T) = KGnWhthdFnHypTrLT X n cX hX k T
KGnWhiteheadFunHypTrich X n cX hX k (eq T) =
  transport (λ i → isEquiv (πFun (T (~ i)) (KGnWhiteheadFun X n hX)))
            (KGnWhthdFnHypTrEQ X n hX cX)
KGnWhiteheadFunHypTrich X n cX hX k (gt T) = KGnWhthdFnHypTrGT X n hX k T

KGnWhiteheadFunHyp : (X : Pointed ℓ) (n : ℕ) → isConnected (3 + n) (typ X)
  → (hX : isOfHLevel (4 + n) (typ X))
  → ∀ (k : ℕ) → isEquiv (fst (πHom k (KGnWhiteheadFun X n hX)))
KGnWhiteheadFunHyp X n cX hX k =
  KGnWhiteheadFunHypTrich X n cX hX k (k ≟ (suc n))

neededAssoc : (n : HLevel) → (3 + n) ≡ (1 + (2 + n))
neededAssoc n = refl

EMUniqueness' : (X : Pointed ℓ) (n : ℕ) → isConnected (3 + n) (typ X)
  → isOfHLevel (4 + n) (typ X) → (EM∙ (πAb n X) (2 + n)) ≡ X
EMUniqueness' X n cX hX =
  ua∙
  ( (fst (KGnWhiteheadFun X n hX))
  , WhiteheadsLemma {n = 4 + n}
      (hLevelEM (πAb n X) (2 + n))
      hX
      (fst (KGnWhiteheadFun X n hX))
      (ConnConnIsEquiv (EM (πAb n X) (2 + n)) (typ X) (suc n)
       (isConnectedEM (2 + n))
       cX
       (mapSetTrunc (fst (KGnWhiteheadFun X n hX))))
      (Homogeneity→WhiteheadHyp (EM∙ (πAb n X) (2 + n)) X
        (KGnWhiteheadFun X n hX)
        (isConnSubtr' _ (1 + n) 2 (isConnectedEM (2 + n)))
        (KGnWhiteheadFunHyp X n cX hX)))
  (snd (KGnWhiteheadFun X n hX))

EMUniqueness : (X : Pointed ℓ) (n : ℕ) → isConnected (3 + n) (typ X)
  → isOfHLevel (4 + n) (typ X) → X ≡ (EM∙ (πAb n X) (2 + n))
EMUniqueness X n cX hX = sym (EMUniqueness' X n cX hX)


EMAbGrpEq : (G G' : AbGroup ℓ) (n : ℕ) → AbGroupEquiv G G'
  → (EM∙ G n) ≡ (EM∙ G' n)
EMAbGrpEq G G' n e = ua∙ (isoToEquiv (Iso→EMIso e n)) (Iso→EMIso∙ e n)
