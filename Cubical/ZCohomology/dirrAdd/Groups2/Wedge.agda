{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.pathComp.Groups2.Wedge where

open import Cubical.ZCohomology.pathComp.Base
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.MayerVietoris2
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to pRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.ZCohomology.pathComp.Groups2.Unit
open import Cubical.ZCohomology.pathComp.Groups2.Sn

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
    surj-helper : (x : coHom' 0 Unit) → isInIm _ _ (I.Δ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
            λ f → ∣ (∣ (λ _ → f tt) ∣₂ , (0ₕ 0)) , (cong ∣_∣₂ (funExt λ _ → sym (rUnit (f tt)))) ∣₁

    helper : (x : coHom' 1 (A ⋁ B)) → isInIm _ _ (I.d 0) x → x ≡ 0ₕ 1
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

  Hⁿ-⋁ (suc n) =
    vSES→GroupIso _ _
         (ses (isOfHLevelSuc 0 (isContrHⁿ-Unit n))
              (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)))
              (I.d (suc n))
              (I.Δ (suc (suc n)))
              (I.i (suc (suc n)))
              (I.Ker-i⊂Im-d (suc n))
              (I.Ker-Δ⊂Im-i (suc (suc n)))) {- Iso+Hom→GrIso mainIso
                                (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevel× 2 setTruncIsSet setTruncIsSet) _ _)
                                         λ _ _ → refl)-}
 {-   where
    helpIso : ∀ {ℓ'''} {C : Type ℓ'''} → Iso (A ⋁ B → C) (Σ[ f ∈ (typ A → C) × (typ B → C) ] (fst f) (pt A) ≡ (snd f) (pt B))
    Iso.fun helpIso f = ((λ x → f (inl x)) , λ x → f (inr x)) , cong f (push tt)
    Iso.inv helpIso ((f , g) , p) (inl x) = f x
    Iso.inv helpIso ((f , g) , p) (inr x) = g x
    Iso.inv helpIso ((f , g) , p) (push a i) = p i
    Iso.rightInv helpIso ((f , g) , p) = ΣPathP (ΣPathP (refl , refl) , refl)
    Iso.leftInv helpIso f = funExt λ {(inl a) → refl ; (inr a) → refl ; (push a i) → refl}

    mainIso : Iso (coHom' (2 + n) (A ⋁ B))
                  (coHom' (2 + n) (typ A) × coHom' (2 + n) (typ B))
    mainIso =  compIso (setTruncIso helpIso) (compIso theIso setTruncOfProdIso)
      where
      forget :  ∥ (Σ[ f ∈ (typ A → loopK (2 + n)) × (typ B → loopK (2 + n)) ] (fst f) (pt A) ≡ (snd f) (pt B)) ∥₂
                     → ∥ (typ A → loopK (2 + n)) × (typ B → loopK (2 + n)) ∥₂
      forget = sMap (λ {((f , g) , _) → f , g})

      isEq :  (f :  ∥ (typ A → loopK (2 + n)) × (typ B → loopK (2 + n)) ∥₂) → isContr (fiber forget f)
      isEq = sElim (λ _ → isOfHLevelSuc 1 isPropIsContr) (uncurry λ f g → helper f g (f (pt A)) (g (pt B)) refl refl)
        where
        helper : (f : (typ A → loopK (2 +  n))) (g : (typ B → loopK (2 + n))) (x y : loopK (2 + n))
               → f (pt A) ≡ x
               → g (pt B) ≡ y
               → isContr (fiber forget ∣ f , g ∣₂)
        helper f g =
          trElim2 (λ _ _ → isProp→isOfHLevelSuc (3 + n)
                            (isPropΠ2 λ _ _ → isPropIsContr))
                          (curry
                            (Iso.inv (elim.isIsoPrecompose {A = Unit}
                                     (λ _ → refl , refl)
                                     1
                                     (λ _ → _ , isPropΠ2 λ _ _ → isPropIsContr)
                                     (isConnectedPoint 1 (isOfHLevelRetractFromIso 0 (truncOfProdIso 2)
                                                         (isOfHLevelΣ 0 (isConnectedPath 2 (isConnectedSubtr 3 (suc n) (connSn n)) _ _)
                                                                        λ _ → isConnectedPath 2 (isConnectedSubtr 3 (suc n) (connSn n)) _ _)) _))
                                     λ _ fId gId → (∣ (f , g) , fId ∙ sym gId ∣₂ , refl)
                                                   , uncurry (sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 (isSetΣ setTruncIsSet (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)) _ _)
                                                              λ {((f' , g') , p) y
                                                              → Σ≡Prop (λ _ → setTruncIsSet _ _)
                                                                        (pRec (setTruncIsSet _ _)
                                                                              (λ q → trRec (setTruncIsSet _ _)
                                                                                           (λ sq → cong ∣_∣₂ (ΣPathP (sym q , sq)))
                                                                                           (oki (fId ∙ sym (gId))
                                                                                                p
                                                                                                (funExt⁻ (cong fst (sym q)) (pt A))
                                                                                                (funExt⁻ (cong snd (sym q)) (pt B))))
                                                                              (Iso.fun PathIdTrunc₀Iso y))})))
         where
         connSn : (n : ℕ) → isConnected (suc (n + 3)) (fst (S₊∙ (suc (suc (suc n)))))
         connSn n = subst (λ x → isConnected x (S₊ (3 + n))) (cong suc (+-comm 3 n)) (sphereConnected (3 + n))

         oki : {x y z w : loopK (suc (suc n))} (p : x ≡ y) (q : z ≡ w) (l : x ≡ z) (r : y ≡ w)
            → hLevelTrunc 1 (Square p q l r)
         oki p q l r = subst (hLevelTrunc 1)
                             (sym (PathP≡Path _ _ _))
                             (isConnectedPath _
                               (isConnectedPath _
                                 (isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso' 3 (suc n)))
                                   (isConnectedPath _ (isConnectedSubtr 4 n (subst (λ x → isConnected x (S₊ (3 + n)))
                                                                                   (+-comm 4 n)
                                                                                   (sphereConnected (3 + n))))
                                 _ _))  _ _) _ _ .fst)

      theIso : Iso ∥ (Σ[ f ∈ (typ A → loopK (2 + n)) × (typ B → loopK (2 + n)) ] (fst f) (pt A) ≡ (snd f) (pt B)) ∥₂
                   ∥ (typ A → loopK (2 + n)) × (typ B → loopK (2 + n)) ∥₂
      theIso = equivToIso (forget , record { equiv-proof = isEq })
-}
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

  wedgeConnected : isConnected 2 (typ A) → isConnected 2 (typ B) → isConnected 2 (A ⋁ B)
  wedgeConnected conA conB =
      ∣ inl (pt A) ∣
    , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                  (PushoutToProp (λ _ → isOfHLevelTrunc 2 _ _)
                  (λ a → trRec (isOfHLevelTrunc 2 _ _) (λ p i → ∣ inl (p i) ∣)
                                (Iso.fun (PathIdTruncIso 1) (isOfHLevelSuc 0 conA ∣ pt A ∣ ∣ a ∣)))
                  λ b → trRec (isOfHLevelTrunc 2 _ _) (λ p i → ∣ (push tt ∙ cong inr p) i ∣) (Iso.fun (PathIdTruncIso 1) (isOfHLevelSuc 0 conB ∣ pt B ∣ ∣ b ∣)))
