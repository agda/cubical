{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Prelims

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
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open GroupHom
open GroupIso


-- The following section contains stengthened induction principles for cohomology groups of T². They are particularly useful for showing that
-- that some Isos are morphisms. They make things type-check faster, but should probably not be used for computations.

-- We first need some functions
elimFunT² : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc n))))
                  → Square q q p p
                  → S¹ × S¹ → coHomK (suc n)
elimFunT² n p q P (base , base) = ∣ ptSn (suc n) ∣
elimFunT² n p q P (base , loop i) = q i
elimFunT² n p q P (loop i , base) = p i
elimFunT² n p q P (loop i , loop j) = P i j

elimFunT²' : (n : ℕ) → Square (refl {ℓ-zero} {coHomK (suc n)} {∣ ptSn (suc n) ∣}) refl refl refl
           → S¹ × S¹ → coHomK (suc n)
elimFunT²' n P (x , base) = ∣ ptSn (suc n) ∣
elimFunT²' n P (base , loop j) = ∣ ptSn (suc n) ∣
elimFunT²' n P (loop i , loop j) = P i j

elimFunT²'≡elimFunT² : (n : ℕ) → (P : _) → elimFunT²' n P ≡ elimFunT² n refl refl P
elimFunT²'≡elimFunT² n P i (base , base) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (base , loop k) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (loop j , base) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (loop j , loop k) = P j k

{-
The first induction principle says that when proving a proposition for some x : Hⁿ(T²), n ≥ 1, it suffices to show that it holds for
(elimFunT² p q P) for any paths p q : ΩKₙ, and square P : Square q q p p. This is useful because elimFunT² p q P (base , base) recudes to 0
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
  lem : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                   → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                   → (p : _) → (refl ≡ p)
                   → (q : _) → (refl ≡ q)
                   → (P : _)
                   → B ∣ elimFunT² (suc n) p q P ∣₂
  lem n {B = B} elimP p =
    J (λ p _ → (q : _) → (refl ≡ q)
             → (P : _)
             → B ∣ elimFunT² (suc n) p q P ∣₂)
      λ q →
        J (λ q _ → (P : _) → B ∣ elimFunT² (suc n) refl q P ∣₂)
           elimP

{- When working with Hⁿ(T²) , n ≥ 2, we are, in the case described above, allowed to assume that any f : Hⁿ(T²) is
   elimFunT² n refl refl P -}
coHomPointedElimT²' : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                 → ((x : coHom (2 + n) (S¹ × S¹)) → isProp (B x))
                 → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                 → (x : coHom (2 + n) (S¹ × S¹)) → B x
coHomPointedElimT²' n {B = B} prop ind =
  coHomPointedElimT² (suc n) prop
    λ p q P → trRec (isProp→isOfHLevelSuc n (prop _))
      (λ p-refl → trRec (isProp→isOfHLevelSuc n (prop _))
                         (λ q-refl → lem n {B = B} ind p (sym p-refl) q (sym q-refl) P)
      (isConnectedPath _ (isConnectedPathKn (suc n) _ _) q refl .fst))
      (isConnectedPath _ (isConnectedPathKn (suc n) _ _) p refl .fst)

{- A slight variation of the above which gives definitional equalities for all points (x , base) -}
private
  coHomPointedElimT²'' : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                   → ((x : coHom (2 + n) (S¹ × S¹)) → isProp (B x))
                   → ((P : _) → B ∣ elimFunT²' (suc n) P ∣₂)
                   → (x : coHom (2 + n) (S¹ × S¹)) → B x
  coHomPointedElimT²'' n {B = B} prop ind =
    coHomPointedElimT²' n prop λ P → subst (λ x → B ∣ x ∣₂)
                        (elimFunT²'≡elimFunT² (suc n) P) (ind P)

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
H¹-T²≅ℤ×ℤ = theIso □ dirProdGroupIso (Hⁿ-Sⁿ≅ℤ 0) (H⁰-Sⁿ≅ℤ 0)
  where
  typIso : Iso _ _
  typIso = setTruncIso (curryIso ⋄ codomainIso S1→K₁≡S1×Int ⋄ toProdIso)
                      ⋄ setTruncOfProdIso

  theIso : GroupIso _ _
  fun (map theIso) = Iso.fun (typIso)
  isHom (map theIso) =
    coHomPointedElimT² _ (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ pf qf Pf →
        coHomPointedElimT² _ (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
          λ pg qg Pg i → ∣ funExt (helperFst pf qf pg qg Pg Pf) i  ∣₂
                        , ∣ funExt (helperSnd pf qf pg qg Pg Pf) i ∣₂
     where
       module _ (pf qf pg qg : 0ₖ 1 ≡ 0ₖ 1) (Pg : Square qg qg pg pg) (Pf : Square qf qf pf pf) where
         helperFst : (x : S¹)
                → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst
                 ≡ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst
                +ₖ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst
         helperFst base = refl
         helperFst (loop i) j = loopLem j i
           where
           loopLem : cong (λ x → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
                   ≡ cong (λ x → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst
                               +ₖ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
           loopLem = (λ i j → S¹map-id (pf j +ₖ pg j) i)
                   ∙ (λ i j → S¹map-id (pf j) (~ i) +ₖ S¹map-id (pg j) (~ i))

         helperSnd : (x : S¹)
                → Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .snd
                ≡ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .snd +ℤ Iso.fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .snd
         helperSnd =
           toPropElim (λ _ → isSetInt _ _)
                      ((λ i → winding (basechange2⁻ base λ j → S¹map (∙≡+₁ qf qg (~ i) j)))
                    ∙∙ cong (winding ∘ basechange2⁻ base) (congFunct S¹map qf qg)
                    ∙∙ (cong winding (basechange2⁻-morph base (cong S¹map qf) (cong S¹map qg))
                      ∙ winding-hom (basechange2⁻ base (cong S¹map qf)) (basechange2⁻ base (cong S¹map qg))))
  inv theIso = Iso.inv typIso
  rightInv theIso = Iso.rightInv typIso
  leftInv theIso = Iso.leftInv typIso

----------------------- H²(T²) ------------------------------
open import Cubical.Foundations.Equiv
H²-T²≅ℤ : GroupIso (coHomGr 2 (S₊ 1 × S₊ 1)) intGroup
H²-T²≅ℤ = compGroupIso helper2 (Hⁿ-Sⁿ≅ℤ 0)
  where
  helper : Iso (∥ ((a : S¹) → coHomK 2) ∥₂ × ∥ ((a : S¹) → coHomK 1) ∥₂) (coHom 1 S¹)
  Iso.inv helper s = 0ₕ _ , s
  Iso.fun helper = snd
  Iso.leftInv helper _ =
    ΣPathP (isOfHLevelSuc 0 (isOfHLevelRetractFromIso 0 (GroupIso→Iso (Hⁿ-S¹≅0 0)) (isContrUnit)) _ _
          , refl)
  Iso.rightInv helper _ = refl
  theIso : Iso (coHom 2 (S¹ × S¹)) (coHom 1 S¹)
  theIso = setTruncIso (curryIso ⋄ codomainIso S1→K2≡K2×K1 ⋄ toProdIso)
         ⋄ setTruncOfProdIso
         ⋄ helper

  helper2 : GroupIso (coHomGr 2 (S¹ × S¹)) (coHomGr 1 S¹)
  helper2 = Iso+Hom→GrIso theIso (
    coHomPointedElimT²'' 0 (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
      λ P → coHomPointedElimT²'' 0 (λ _ → setTruncIsSet _ _)
      λ Q → (λ i → ∣ (λ a → ΩKn+1→Kn 1 (transportRefl refl i
                                            ∙∙ cong (λ x → (elimFunT²' 1 P (a , x) +ₖ elimFunT²' 1 Q (a , x)) -ₖ ∣ north ∣) loop
                                            ∙∙ transportRefl refl i)) ∣₂)
          ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 P (a , x) +ₖ elimFunT²' 1 Q (a , x)) i) loop) (~ i))) ∣₂)
          ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn 1 (∙≡+₂ 0 (cong (λ x → elimFunT²' 1 P (a , x)) loop) (cong (λ x → elimFunT²' 1 Q (a , x)) loop) (~ i))) ∣₂)
          ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn-hom 1 (cong (λ x → elimFunT²' 1 P (a , x)) loop) (cong (λ x → elimFunT²' 1 Q (a , x)) loop) i) ∣₂)
          ∙∙ (λ i → ∣ ((λ a → ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 P (a , x)) (~ i)) loop) i)
                                           +ₖ ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 Q (a , x)) (~ i)) loop) i))) ∣₂)
           ∙ (λ i → ∣ ((λ a → ΩKn+1→Kn 1 (transportRefl refl (~ i)
                                                         ∙∙ cong (λ x → elimFunT²' 1 P (a , x) +ₖ ∣ north ∣) loop
                                                         ∙∙ transportRefl refl (~ i))
                                           +ₖ ΩKn+1→Kn 1 (transportRefl refl (~ i)
                                                         ∙∙ cong (λ x → elimFunT²' 1 Q (a , x) +ₖ ∣ north ∣) loop
                                                         ∙∙ transportRefl refl (~ i)))) ∣₂))

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

{-
-- Compute fast:
test : to₁ (from₁ (0 , 1) +ₕ from₁ (1 , 0)) ≡ (1 , 1)
test = refl

test2 : to₁ (from₁ (5 , 1) +ₕ from₁ (-2 , 3)) ≡ (3 , 4)
test2 = refl

-- Compute pretty fast

test3 : to₂ (from₂ 1) ≡ 1
test3 = refl

test4 : to₂ (from₂ 2) ≡ 2
test4 = refl

test5 : to₂ (from₂ 3) ≡ 3
test5 = refl

-- Compute, but slower

test6 : to₂ (from₂ 0 +ₕ from₂ 0) ≡ 0
test6 = refl

test6 : to₂ (from₂ 0 +ₕ from₂ 1) ≡ 1
test6 = refl

-- Does not compute
test7 : to₂ (from₂ 1 +ₕ from₂ 0) ≡ 1
test7 = refl
-}
