{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Prelims
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Algebra.Group

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2) hiding (map)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁) hiding (map)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)


open GroupHom
open GroupIso

{-
The following induction principle says that when proving any propositon about an element
x ∈ Hⁿ(T²) (where T² := S¹×S¹) we may assume it is on the form
∣ f ∣₂ where f : T² → Kₙ is defined by
f (base , base) = 0          (*)
cong (f (base ,_)) loop = p
cong (f (_ , base)) loop = q
cong² f (loop , loop) = p□q
where p□q is a filler of
     p
   ----->
  ∣̂       ∣̂
q ∣       ∣ q
  ∣       ∣
   ----->
     p
furthermore, (*) holds definitionally
-}

coHomPointedElimT² : ∀ {ℓ} (n : ℕ) {B : coHom (suc n) (S¹ × S¹) → Type ℓ}
                 → ((x : coHom (suc n) (S¹ × S¹)) → isProp (B x))
                 → ((p q : _) (P : _) → B ∣ elimFunT² n p q P ∣₂)
                 → (x : coHom (suc n) (S¹ × S¹)) → B x
coHomPointedElimT² n {B = B} isprop indp =
  coHomPointedElim _ (base , base) isprop
    λ f fId → subst B (cong ∣_∣₂ (funExt (λ { (base , base) → sym fId
                                           ; (base , loop i) j → helper f fId i1 i (~ j)
                                           ; (loop i , base) j → helper f fId i i1 (~ j)
                                           ; (loop i , loop j) k → helper f fId i j (~ k)})))
                       (indp (λ i → helper f fId i i1 i1)
                             (λ i → helper f fId i1 i i1)
                              λ i j → helper f fId i j i1)
    where
    helper : (f : S¹ × S¹ → coHomK (suc n)) → f (base , base) ≡ ∣ ptSn (suc n) ∣
           → I → I → I → coHomK (suc n)
    helper f fId i j k = 
      hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (i = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (j = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i
                     ; (j = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i})
            (inS (f ((loop i) , (loop j))))
            k

private
  module congLemma (key : Unit') where
    module K = lockedCohom key

    main : (n : ℕ) (p : Path (coHomK n) (0ₖ n) (0ₖ n))
              → Path (K.+K n (0ₖ n) (0ₖ n) ≡ K.+K n (0ₖ n) (0ₖ n))
                      (cong (K.+K n (0ₖ n)) p) (cong (λ x → K.+K n x (0ₖ n)) p)
    main n = congIdLeft≡congIdRight (K.+K n) (K.-K n) (0ₖ n) (K.rUnitK n) (K.lUnitK n) (sym (lUnitK≡rUnitK key n))

--------- H⁰(T²) ------------
H⁰-T²≅ℤ : GroupIso (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
H⁰-T²≅ℤ =
  H⁰-connected (base , base)
    λ (a , b) → pRec propTruncIsProp
                     (λ id1 → pRec propTruncIsProp
                                   (λ id2 → ∣ ΣPathP (id1 , id2) ∣₁)
                                   (Sn-connected 0 b) )
                     (Sn-connected 0 a)

--------- H¹(T²) -------------------------------

H¹-T²≅ℤ×ℤ : GroupIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
H¹-T²≅ℤ×ℤ = theIso □ dirProdGroupIso (invGroupIso (Hⁿ-Sⁿ≅ℤ 0)) (H⁰-Sⁿ≅ℤ 0)
  where
  helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ (S¹map x) ∣ ≡ x
  helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl

  typIso : Iso _ _
  typIso = setTruncIso (curryIso ⋄ codomainIso S1→K₁≡S1×Int ⋄ toProdIso)
                      ⋄ setTruncOfProdIso

  theIso : GroupIso _ _
  fun (map theIso) = Iso.fun (typIso)
  isHom (map theIso) =
    coHomPointedElimT² _ (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ pf qf Pf →
        coHomPointedElimT² _ (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
          λ pg qg Pg i → ∣ funExt (helper' pf qf pg qg Pg Pf) i  ∣₂
                        , ∣ funExt (helper'' pf qf pg qg Pg Pf) i ∣₂
     where
     helper' : (pf qf pg qg : _) → (Pg : Square qg qg pg pg) → (Pf : Square qf qf pf pf)
            → (x : S¹)
            → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst
            ≡ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst +ₖ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst
     helper' pf qf pg qg Pg Pf base = refl
     helper' pf qf pg qg Pg Pf (loop i) j = ok j i
       where
       ok : cong (λ x → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
          ≡ cong (λ x → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst +ₖ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
       ok = (λ i j → S¹map-id (pf j +ₖ pg j) i)
         ∙∙ {!!}
         ∙∙ {!!} -- (λ i j → (elimFunT² 0 pf qf Pf (loop j , base) +ₖ {!elimFunT² 0 pg qg  Pg (loop j , base)!}) ) ∙∙ {!!} ∙∙ {!!}

     helper'' : (pf qf pg qg : _) → (Pg : Square qg qg pg pg) → (Pf : Square qf qf pf pf)
            → (x : S¹)
            → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .snd
            ≡ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .snd +[ 0 ]ₖ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .snd
     helper'' pf qf pq gq Pg Pf = toPropElim (λ _ → isSetInt _ _) {!!}
  {-
    sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
            λ f g → ΣPathP ((cong ∣_∣₂
                             (funExt (λ x → helper (f (x , base) +ₖ g (x , base))
                                           ∙ sym (cong₂ (λ x y → x +ₖ y)
                                                        (helper (f (x , base)))
                                                        (helper (g (x , base))))))) ,
                           (cong ∣_∣₂
                              (funExt
                                (toPropElim
                                   (λ _ → isSetInt _ _)
                                   (cong winding
                                         (basechange-lemma2
                                           (λ x → f (base , x))
                                           (λ x → g (base , x))
                                           λ x → S¹map x)
                                  ∙∙ winding-hom
                                      (basechange2⁻
                                          (S¹map (f (base , base)))
                                          (λ i → S¹map (f (base , (loop i)))))
                                      (basechange2⁻
                                          (S¹map (g (base , base)))
                                          (λ i → S¹map (g (base , (loop i)))))
                                  ∙∙ sym (addLemma
                                          (winding
                                            (basechange2⁻
                                              (S¹map (f (base , base)))
                                              (λ i → S¹map (f (base , (loop i))))))
                                          (winding
                                            (basechange2⁻
                                              (S¹map  (g (base , base)))
                                              (λ i → S¹map (g (base , (loop i)))))))))))) -}
  inv theIso = Iso.inv typIso
  rightInv theIso = Iso.rightInv typIso
  leftInv theIso = Iso.leftInv typIso

----------------------- H²(T²) ------------------------------
open import Cubical.Foundations.Equiv
H²-T²≅ℤ : GroupIso (coHomGr 2 (S₊ 1 × S₊ 1)) intGroup
H²-T²≅ℤ = invGroupIso (ℤ≅H²-T² unlock)
  where
    module _ (key : Unit') where
      module K = lockedCohom key
      private
        _+K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
        _+K_ {n = n} = K.+K n

        -K_ : {n : ℕ} → coHomK n → coHomK n
        -K_ {n = n} = K.-K n

        -H_ : {A : Type₀} {n : ℕ} → coHom n A → coHom n A
        -H_ {n = n} = K.-H n

        _+H_ : {A : Type₀} {n : ℕ} → coHom n A → coHom n A → coHom n A
        _+H_ {n = n} = K.+H n

      typIso : Iso _ _
      typIso = helper
            ⋄ (invIso (prodIso (GroupIso→Iso (Hⁿ-S¹≅0 0))
                               (invIso (GroupIso→Iso (Hⁿ-Sⁿ≅ℤ 0))))
            ⋄ ((invIso setTruncOfProdIso)
            ⋄ (invIso (setTruncIso (curryIso
                                  ⋄ codomainIso (S1→K2≡K2×K1' key)
                                  ⋄ toProdIso)))))
        where
        helper : Iso Int (Unit × Int)
        Iso.inv helper = snd
        Iso.fun helper x = tt , x
        Iso.leftInv helper _ = refl
        Iso.rightInv helper _ = refl

      mapIsHom : (x y : Int)
              → Iso.fun typIso (x +ℤ y) ≡ ((Iso.fun typIso x) +H Iso.fun typIso y)
      mapIsHom a b = {!!}
      {-
          (cong f ((GroupHom.isHom (GroupIso.map (invGroupIso (dirProdGroupIso (Hⁿ-S¹≅0 0) (invGroupIso (Hⁿ-Sⁿ≅ℤ 0)))))
                                                              (_ , a) (_ , b))
                ∙ λ i → guyId i , +H≡+ₕ key _ (~ i) (g a) (g b)))
        ∙∙ helper (g a) (g b)
        ∙∙ cong₂ (_+H_) (λ i → f (guyId2 (~ i) , g a)) λ i → f (guyId2 (~ i) , g b)
        where
        f = Iso.fun (((invIso setTruncOfProdIso ⋄ invIso (setTruncIso (curryIso ⋄ codomainIso (S1→K2≡K2×K1' key) ⋄ toProdIso)))))
        g = GroupIso.inv (invGroupIso (Hⁿ-Sⁿ≅ℤ 0))

        isPropH²-S¹ : isProp (coHom 2 (S₊ 1))
        isPropH²-S¹ = isPropRetract (fun (map (Hⁿ-S¹≅0 0)))
                                    (inv (Hⁿ-S¹≅0 0))
                                    (leftInv (Hⁿ-S¹≅0 0))
                                    isPropUnit

        guyId : ∣ _ ∣₂ ≡ 0ₕ 2
        guyId = isPropH²-S¹ _ _

        guyId2 : ∣ _ ∣₂ ≡ 0ₕ 2
        guyId2 = isPropH²-S¹ _ _

        helper : (x y : ∥ ((S₊ 1) → (hLevelTrunc 3 (S₊ 1) )) ∥₂) →
                  f ((0ₕ 2) , (x +H y)) ≡ f ((0ₕ 2) , x) +H f (0ₕ 2 , y)
        helper =
          sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                 λ f g i → ∣ (λ x → helper2 (f (fst x)) (g (fst x)) (snd x) i) ∣₂
          where
          helper2 : (x y : coHomK 1) (s : S₊ 1)
                 → Iso.inv (S1→K2≡K2×K1' key) (0ₖ 2 , x +K y) s ≡ (Iso.inv (S1→K2≡K2×K1' key) (0ₖ 2 , x)) s +K (Iso.inv (S1→K2≡K2×K1' key) (0ₖ 2 , y)) s
          helper2 =
            trElim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 4 _ _)
                    λ a b → λ {base → cong₂ (_+K_) (sym (K.lUnitK _ 0₂)) (sym (K.lUnitK _ 0₂))
                            ; (loop i) j → hcomp (λ k → λ{ (i = i0) → cong₂ (_+K_) (sym (K.lUnitK _ 0₂)) (sym (K.lUnitK _ 0₂)) (j ∧ k)
                                                         ; (i = i1) → cong₂ (_+K_) (sym (K.lUnitK _ 0₂)) (sym (K.lUnitK _ 0₂)) (j ∧ k)
                                                         ; (j = i0) → 0₂ +K (Kn→ΩKn+1 1 (∣ a ∣ +K ∣ b ∣) i)
                                                         ; (j = i1) → cong₂ (_+K_) (sym (K.lUnitK _ (Kn→ΩKn+1 1 ∣ a ∣ i)))
                                                                            (sym (K.lUnitK _ (Kn→ΩKn+1 1 ∣ b ∣ i))) k})
                                               (helper3 ∣ a ∣ ∣ b ∣ j i)}
            where
            helper3 : (a b : coHomK 1) → cong (0₂ +K_) (Kn→ΩKn+1 1 (a +K b)) ≡ cong₂ (_+K_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b)
            helper3 a b = cong (cong (0₂ +K_)) (+K→∙ key 1 a b)
                        ∙ (congFunct (0₂ +K_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b)
                        ∙∙ (λ i → congLemma.main key 2 (Kn→ΩKn+1 1 a) i ∙ cong (_+K_ ∣ north ∣) (λ i → Kn→ΩKn+1 1 b i))
                        ∙∙ sym (cong₂Funct (_+K_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b))) -}

      ℤ≅H²-T² : GroupIso intGroup (coHomGr 2 (S₊ 1 × S₊ 1))
      fun (map ℤ≅H²-T²) = Iso.fun typIso
      isHom (map ℤ≅H²-T²) = pm key mapIsHom
        where
        pm : (t : Unit')
          → ((x y : Int)
                → Iso.fun typIso (x +ℤ y) ≡ (lockedCohom.+H t _ (Iso.fun typIso x) (Iso.fun typIso y)))
          → isGroupHom intGroup (coHomGr 2 (S₊ 1 × S₊ 1)) (Iso.fun typIso)
        pm unlock p = p
      inv ℤ≅H²-T² = Iso.inv typIso
      rightInv ℤ≅H²-T² = Iso.rightInv typIso
      leftInv ℤ≅H²-T² = Iso.leftInv typIso

private
  to₂ : coHom 2 (S₊ 1 × S₊ 1) → Int
  to₂ = fun (map H²-T²≅ℤ)

  from₂ : Int → coHom 2 (S₊ 1 × S₊ 1)
  from₂ = inv H²-T²≅ℤ

  to₁ : coHom 1 (S₊ 1 × S₊ 1) → Int × Int
  to₁ = fun (map H¹-T²≅ℤ×ℤ)

  from₁ : Int × Int → coHom 1 (S₊ 1 × S₊ 1)
  from₁ = inv H¹-T²≅ℤ×ℤ

  to₀ : coHom 0 (S₊ 1 × S₊ 1) → Int
  to₀ = fun (map H⁰-T²≅ℤ)

  from₀ : Int → coHom 0 (S₊ 1 × S₊ 1)
  from₀ = inv H⁰-T²≅ℤ

test3 : to₂ (from₂ 0 +ₕ from₂ 1) ≡ 1
test3 = refl

{-
-- Compute fast:
test : to₁ (from₁ (0 , 1) +ₕ from₁ (1 , 0)) ≡ (1 , 1)
test = refl

test2 : to₁ (from₁ (5 , 1) +ₕ from₁ (-2 , 3)) ≡ (3 , 4)
test2 = refl

-- Will not compute:

test3 : to₂ (from₂ 0) ≡ 0
test3 = refl

-}
