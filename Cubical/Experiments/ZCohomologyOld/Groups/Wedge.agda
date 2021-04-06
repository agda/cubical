{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.Experiments.ZCohomologyOld.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.Experiments.ZCohomologyOld.Properties
open import Cubical.Experiments.ZCohomologyOld.MayerVietorisUnreduced
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to pRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.Experiments.ZCohomologyOld.Groups.Unit
open import Cubical.Experiments.ZCohomologyOld.Groups.Sn

open import Cubical.HITs.Pushout
open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Equiv


module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where
  module I = MV (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  Hⁿ-⋁ zero = BijectionIsoToGroupIso bijIso
    where
    surj-helper : (x : coHom 0 Unit) → isInIm _ _ (I.Δ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
            λ f → ∣ (∣ (λ _ → f tt) ∣₂ , 0ₕ 0) , cong ∣_∣₂ (funExt λ _ → -rUnitₖ 0 (f tt)) ∣₁

    helper : (x : coHom 1 (A ⋁ B)) → isInIm _ _ (I.d 0) x → x ≡ 0ₕ 1
    helper x inim =
      pRec (setTruncIsSet _ _)
           (λ p → sym (snd p) ∙
                       MV.Im-Δ⊂Ker-d _ _ Unit (λ _ → pt A) (λ _ → pt B) 0 (fst p) (surj-helper (fst p)))
             inim

    bijIso : BijectionIso (coHomGr 1 (A ⋁ B)) (×coHomGr 1 (typ A) (typ B))
    BijectionIso.map' bijIso = I.i 1
    BijectionIso.inj bijIso =
      sElim (λ _ → isSetΠ λ _ → isProp→isSet (setTruncIsSet _ _))
            λ f inker → helper ∣ f ∣₂ (I.Ker-i⊂Im-d 0 ∣ f ∣₂ inker)
    BijectionIso.surj bijIso p = I.Ker-Δ⊂Im-i 1 p (isContr→isProp (isContrHⁿ-Unit 0) _ _)

  Hⁿ-⋁ (suc n) = Iso+Hom→GrIso mainIso
                                (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevel× 2 setTruncIsSet setTruncIsSet) _ _)
                                         λ _ _ → refl)
    where
    helpIso : ∀ {ℓ'''} {C : Type ℓ'''} → Iso (A ⋁ B → C) (Σ[ f ∈ (typ A → C) × (typ B → C) ] (fst f) (pt A) ≡ (snd f) (pt B))
    Iso.fun helpIso f = ((λ x → f (inl x)) , λ x → f (inr x)) , cong f (push tt)
    Iso.inv helpIso ((f , g) , p) (inl x) = f x
    Iso.inv helpIso ((f , g) , p) (inr x) = g x
    Iso.inv helpIso ((f , g) , p) (push a i) = p i
    Iso.rightInv helpIso ((f , g) , p) = ΣPathP (ΣPathP (refl , refl) , refl)
    Iso.leftInv helpIso f = funExt λ {(inl a) → refl ; (inr a) → refl ; (push a i) → refl}

    mainIso : Iso (coHom (2 + n) (A ⋁ B))
                  (coHom (2 + n) (typ A) × coHom (2 + n) (typ B))
    mainIso = compIso (setTruncIso helpIso) (compIso theIso setTruncOfProdIso)
      where
      forget :  ∥ (Σ[ f ∈ (typ A → coHomK (2 + n)) × (typ B → coHomK (2 + n)) ] (fst f) (pt A) ≡ (snd f) (pt B)) ∥₂
                     → ∥ (typ A → coHomK (2 + n)) × (typ B → coHomK (2 + n)) ∥₂
      forget = sMap (λ {((f , g) , _) → f , g})

      isEq :  (f :  ∥ (typ A → coHomK (2 + n)) × (typ B → coHomK (2 + n)) ∥₂) → isContr (fiber forget f)
      isEq = sElim (λ _ → isOfHLevelSuc 1 isPropIsContr) (uncurry λ f g → helper f g (f (pt A)) (g (pt B)) refl refl)
        where
        helper : (f : (typ A → coHomK (2 +  n))) (g : (typ B → coHomK (2 + n))) (x y : coHomK (2 + n))
               → f (pt A) ≡ x
               → g (pt B) ≡ y
               → isContr (fiber forget ∣ f , g ∣₂)
        helper f g = trElim2 (λ _ _ → isProp→isOfHLevelSuc (3 + n)
                               (isPropΠ2 λ _ _ → isPropIsContr))
                             (suspToPropElim2 (ptSn (suc n))
                                              (λ _ _ → isPropΠ2 λ _ _ → isPropIsContr)
                                              λ p q → (∣ (f , g) , (p ∙ sym q) ∣₂
                         , refl)
                         , uncurry (sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet λ _ → isOfHLevelPath 2 setTruncIsSet _ _) _ _)
                               λ { ((f' , g') , id1) y →
                                     Σ≡Prop (λ _ → setTruncIsSet _ _)
                                              (pRec (setTruncIsSet _ _)
                                                 (λ id2 → trRec (setTruncIsSet _ _)
                                                   (λ pathp → cong ∣_∣₂ (ΣPathP ((sym id2) , pathp)))
                                                   (isConnectedPathP 1
                                                     {A = λ i → (fst (id2 (~ i)) (pt A) ≡ snd (id2 (~ i)) (pt B))}
                                                       (isConnectedPath 2 (isConnectedSubtr 3 n
                                                                          (subst (λ m → isConnected m (coHomK (2 + n))) (+-comm 3 n)
                                                                                 (isConnectedKn (suc n)))) _ _)
                                                       (p ∙ sym q) id1 .fst))
                                                       (Iso.fun PathIdTrunc₀Iso y))}))
      theIso : Iso ∥ (Σ[ f ∈ (typ A → coHomK (2 + n)) × (typ B → coHomK (2 + n)) ] (fst f) (pt A) ≡ (snd f) (pt B)) ∥₂
                   ∥ (typ A → coHomK (2 + n)) × (typ B → coHomK (2 + n)) ∥₂
      theIso = equivToIso (forget , record { equiv-proof = isEq })

   {- Alternative, less direct proof :
       vSES→GroupIso _ _
         (ses (isOfHLevelSuc 0 (isContrHⁿ-Unit n))
              (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)))
              (I.d (suc n))
              (I.Δ (suc (suc n)))
              (I.i (suc (suc n)))
              (I.Ker-i⊂Im-d (suc n))
              (I.Ker-Δ⊂Im-i (suc (suc n))))
   -}

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥) → ((x : typ B) → ∥ pt B ≡ x ∥) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥
  wedgeConnected conA conB =
    PushoutToProp (λ _ → propTruncIsProp)
                  (λ a → pRec propTruncIsProp (λ p → ∣ cong inl p ∣₁) (conA a))
                   λ b → pRec propTruncIsProp (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b)
