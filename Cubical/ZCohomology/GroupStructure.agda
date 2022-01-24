{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.GroupStructure where

open import Cubical.ZCohomology.Base

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (id)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; isSetSetTrunc to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_ ; -_ to -ℤ_)
open import Cubical.Data.Nat renaming (+-assoc to +-assocℕ ; +-comm to +-commℕ)
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3 ; map2 to trMap2)
open import Cubical.Homotopy.Loopspace
open import Cubical.Algebra.Group renaming (ℤ to ℤGroup)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ

infixr 34 _+ₖ_
infixr 34 _+ₕ_
infixr 34 _+ₕ∙_

-- Addition in the Eilenberg-Maclane spaces is uniquely determined if we require it to have left- and right-unit laws,
-- such that these agree on 0. In particular, any h-structure (see http://ericfinster.github.io/files/emhott.pdf) is unique.
+ₖ-unique : (n : ℕ) → (comp1 comp2 : coHomK (suc n) → coHomK (suc n) → coHomK (suc n))
         → (rUnit1 : (x : _) → comp1 x (coHom-pt (suc n)) ≡ x)
         → (lUnit1 : (x : _) → comp1 (coHom-pt (suc n)) x ≡ x)
         → (rUnit2 : (x : _) → comp2 x (coHom-pt (suc n)) ≡ x)
         → (lUnit2 : (x : _) → comp2 (coHom-pt (suc n)) x ≡ x)
         → (unId1 : rUnit1 (coHom-pt (suc n)) ≡ lUnit1 (coHom-pt (suc n)))
         → (unId2 : rUnit2 (coHom-pt (suc n)) ≡ lUnit2 (coHom-pt (suc n)))
         → (x y : _) → comp1 x y ≡ comp2 x y
+ₖ-unique n comp1 comp2 rUnit1 lUnit1 rUnit2 lUnit2 unId1 unId2 =
  elim2 (λ _ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
        (wedgeconFun _ _
        (λ _ _ → help _ _)
        (λ x → lUnit1 ∣ x ∣ ∙ sym (lUnit2 ∣ x ∣))
        (λ x → rUnit1 ∣ x ∣ ∙ sym (rUnit2 ∣ x ∣))
        (cong₂ _∙_ unId1 (cong sym unId2)))
  where
  help : isOfHLevel (2 + (n + suc n)) (coHomK (suc n))
  help = subst (λ x → isOfHLevel x (coHomK (suc n))) (+-suc n (2 + n) ∙ +-suc (suc n) (suc n))
               (isOfHLevelPlus n (isOfHLevelTrunc (3 + n)))

wedgeConHLev : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (coHomK (2 + n))
wedgeConHLev n = subst (λ x → isOfHLevel x (coHomK (2 + n)))
                       (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                       (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (4 + n)))
wedgeConHLev' : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (typ (Ω (coHomK-ptd (3 + n))))
wedgeConHLev' n = subst (λ x → isOfHLevel x (typ (Ω (coHomK-ptd (3 + n)))))
                        (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                        (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (5 + n) _ _))

wedgeConHLevPath : (n : ℕ) → (x y : coHomK (suc n)) → isOfHLevel ((suc n) + (suc n)) (x ≡ y)
wedgeConHLevPath zero x y = isOfHLevelTrunc 3 _ _
wedgeConHLevPath (suc n) x y = isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _

-- addition for n ≥ 2 together with the left- and right-unit laws (modulo truncations)
preAdd : (n : ℕ) → (S₊ (2 + n) → S₊ (2 + n) → coHomK (2 + n))
preAdd n =
  wedgeconFun _ _
             (λ _ _ → wedgeConHLev n)
             ∣_∣
             ∣_∣
             refl

preAdd-l : (n : ℕ) → (x : (S₊ (2 + n))) → preAdd n north x ≡ ∣ x ∣
preAdd-l n _ = refl

preAdd-r : (n : ℕ) → (x : (S₊ (2 + n))) → preAdd n x north ≡ ∣ x ∣
preAdd-r n =
  wedgeconRight _ (suc n)
             (λ _ _ → wedgeConHLev n)
             ∣_∣
             ∣_∣
             refl

-- addition for n = 1
wedgeMapS¹ : S¹ → S¹ → S¹
wedgeMapS¹ base y = y
wedgeMapS¹ (loop i) base = loop i
wedgeMapS¹ (loop i) (loop j) =
  hcomp (λ k → λ { (i = i0) → loop j
                  ; (i = i1) → loop (j ∧ k)
                  ; (j = i0) → loop i
                  ; (j = i1) → loop (i ∧ k)})
        (loop (i ∨ j))

---------- Algebra/Group stuff --------
0ₖ : (n : ℕ) → coHomK n
0ₖ = coHom-pt

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = zero} x y = x ℤ+ y
_+ₖ_ {n = suc zero} = trMap2 wedgeMapS¹
_+ₖ_ {n = suc (suc n)} = trRec (isOfHLevelΠ (4 + n) λ _ → isOfHLevelTrunc (4 + n))
                            λ x → trRec (isOfHLevelTrunc (4 + n)) (preAdd n x)

private
  isEquiv+ : (n : ℕ) → (x : coHomK (suc n)) → isEquiv (_+ₖ_ {n = (suc n)} x)
  isEquiv+ zero =
    trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropIsEquiv _))
           (toPropElim (λ _ → isPropIsEquiv _)
                       (subst isEquiv (sym help) (idIsEquiv _)))
    where
    help : _+ₖ_ {n = 1} (coHom-pt 1) ≡ idfun _
    help = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ _ → refl)
  isEquiv+ (suc n) =
    trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropIsEquiv _))
           (suspToPropElim (ptSn (suc n)) (λ _ → isPropIsEquiv _)
           (subst isEquiv (sym help) (idIsEquiv _)))
    where
    help : _+ₖ_ {n = (2 + n)} (coHom-pt (2 + n)) ≡ idfun _
    help = funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _) λ _ → refl)


  Kₙ≃Kₙ : (n : ℕ) (x : coHomK (suc n)) → coHomK (suc n) ≃ coHomK (suc n)
  Kₙ≃Kₙ n x = _ , isEquiv+ n x

-ₖ_ : {n : ℕ} →  coHomK n → coHomK n
-ₖ_ {n = zero} x = 0 - x
-ₖ_ {n = suc zero} = trMap λ {base → base ; (loop i) → (loop (~ i))}
-ₖ_ {n = suc (suc n)} = trMap λ {north → north
                                ; south → north
                                ; (merid a i) → ((merid (ptSn (suc n)) ∙ sym (merid a))) i}

_-ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_-ₖ_ {n = n} x y = _+ₖ_ {n = n} x (-ₖ_ {n = n} y)

+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

-'ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
-'ₖ-syntax n = _-ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x
syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

-ₖ^2 : {n : ℕ} → (x : coHomK n) → (-ₖ (-ₖ x)) ≡ x
-ₖ^2 {n = zero} x =
  +Comm (pos zero) (-ℤ (pos zero ℤ+ (-ℤ x))) ∙∙ -Dist+  (pos zero) (-ℤ x)
     ∙∙ (+Comm (pos zero) (-ℤ (-ℤ x)) ∙ -Involutive x)
-ₖ^2 {n = suc zero} =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ { base → refl ; (loop i) → refl}
-ₖ^2 {n = suc (suc n)} =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
              λ { north → refl
                ; south j → ∣ merid (ptSn _) j ∣ₕ
                ; (merid a i) j
                  → hcomp (λ k → λ { (i = i0) → ∣ north ∣
                                     ; (i = i1) → ∣ compPath-filler' (merid a) (sym (merid (ptSn _))) (~ k) (~ j) ∣ₕ
                                     ; (j = i0) → help a (~ k) i
                                     ; (j = i1) → ∣ merid a (i ∧ k) ∣})
                            ∣ (merid a ∙ sym (merid (ptSn _))) (i ∧ ~ j) ∣ₕ}
  where
  help : (a : _) → cong (-ₖ_ ∘ (-ₖ_ {n = suc (suc n)})) (cong ∣_∣ₕ (merid a))
       ≡ cong ∣_∣ₕ (merid a ∙ sym (merid (ptSn _)))
  help a = cong (cong ((-ₖ_ {n = suc (suc n)}))) (cong-∙ ∣_∣ₕ (merid (ptSn (suc n))) (sym (merid a)))
        ∙∙ cong-∙ (-ₖ_ {n = suc (suc n)}) (cong ∣_∣ₕ (merid (ptSn (suc n)))) (cong ∣_∣ₕ (sym (merid a)))
        ∙∙ (λ i → (λ j → ∣ rCancel (merid (ptSn (suc n))) i j ∣ₕ)
                 ∙ λ j → ∣ symDistr (merid (ptSn (suc n))) (sym (merid a)) i j ∣ₕ)
         ∙ sym (lUnit _)


------- Groupoid Laws for Kₙ ---------
commₖ : (n : ℕ) → (x y : coHomK n) → x +[ n ]ₖ y ≡ y +[ n ]ₖ x
commₖ zero = +Comm
commₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeconFun _ _
          (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ {base → refl ; (loop i) → refl})
          (λ {base → refl ; (loop i) → refl})
          refl)
commₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeconFun _ _
                    (λ x y → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                    (λ x → preAdd-l n x ∙ sym (preAdd-r n x))
                    (λ x → preAdd-r n x ∙ sym (preAdd-l n x))
                    refl)

commₖ-base : (n : ℕ) → commₖ n (coHom-pt n) (coHom-pt n) ≡ refl
commₖ-base zero = refl
commₖ-base (suc zero) = refl
commₖ-base (suc (suc n)) = sym (rUnit _)

rUnitₖ : (n : ℕ) → (x : coHomK n) → x +[ n ]ₖ coHom-pt n ≡ x
rUnitₖ zero x = refl
rUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
rUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
         (preAdd-r n)

lUnitₖ : (n : ℕ) → (x : coHomK n) → coHom-pt n +[ n ]ₖ x ≡ x
lUnitₖ zero x = sym (pos0+ x)
lUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
lUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → refl

∙≡+₁ : (p q : typ (Ω (coHomK-ptd 1))) → p ∙ q ≡ cong₂ _+ₖ_ p q
∙≡+₁ p q = (λ i → (λ j → rUnitₖ 1 (p j) (~ i)) ∙ λ j → lUnitₖ 1 (q j) (~ i)) ∙  sym (cong₂Funct _+ₖ_ p q)

∙≡+₂ : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc (suc n))))) → p ∙ q ≡ cong₂ _+ₖ_ p q
∙≡+₂ n p q = (λ i → (λ j → rUnitₖ (2 + n) (p j) (~ i)) ∙ λ j → lUnitₖ (2 + n) (q j) (~ i)) ∙ sym (cong₂Funct _+ₖ_ p q)

lCancelₖ : (n : ℕ) → (x : coHomK n) → (-ₖ_ {n = n} x) +ₖ x ≡ coHom-pt n
lCancelₖ zero x = minusPlus x 0
lCancelₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl ; (loop i) j → help j i}
  where
  help : cong₂ _+ₖ_ (sym (cong ∣_∣ loop)) (cong ∣_∣ loop) ≡ refl
  help = sym (∙≡+₁ (sym (cong ∣_∣ loop)) (cong ∣_∣ loop)) ∙ lCancel _
lCancelₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
         λ {north → refl ; south → cong ∣_∣ (sym (merid (ptSn (suc n)))) ; (merid a i) → help a i }
  where
  s : (a : _) → _ ≡ _
  s x = cong₂ _+ₖ_ (sym (cong ∣_∣ (merid (ptSn (suc n)) ∙ sym (merid x)))) (cong ∣_∣ (sym (merid x)))

  help : (a : _) → PathP (λ i → (preAdd n ((merid (ptSn (suc n)) ∙ (λ i₁ → merid a (~ i₁))) i)
                                  (merid a i)) ≡ ∣ north ∣) refl λ i₁ → ∣ merid (ptSn (suc n)) (~ i₁) ∣
  help x =
    compPathR→PathP
      ((sym (lCancel _)
    ∙∙ (λ i → ∙≡+₂ _ (cong ∣_∣ (symDistr (merid x) (sym (merid (ptSn (suc n)))) i)) (cong ∣_∣ ((merid x) ∙ sym (merid (ptSn (suc n))))) i)
    ∙∙  rUnit _)
    ∙∙ (λ j → cong₂ _+ₖ_ ((cong ∣_∣ (merid (ptSn (suc n)) ∙ sym (merid x))))
                       (λ i → ∣ compPath-filler ((merid x)) ((sym (merid (ptSn (suc n))))) (~ j) i ∣)
              ∙ λ i → ∣ merid (ptSn (suc n)) (~ i ∧ j) ∣)
    ∙∙ λ i → sym (s x) ∙ rUnit (cong ∣_∣ (sym (merid (ptSn (suc n)))))  i)

rCancelₖ : (n : ℕ) → (x : coHomK n) → x +ₖ (-ₖ_ {n = n} x) ≡ coHom-pt n
rCancelₖ zero x = +Comm x (pos 0 - x) ∙ minusPlus x 0 -- +-comm x (pos 0 - x) ∙ minusPlus x 0
rCancelₖ (suc zero) = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                              λ {base → refl ; (loop i) j → help j i}
  where
  help : (λ i → ∣ loop i ∣ₕ +ₖ (-ₖ ∣ loop i ∣ₕ)) ≡ refl
  help = sym (∙≡+₁ (cong ∣_∣ₕ loop) (sym (cong ∣_∣ₕ loop))) ∙ rCancel _
rCancelₖ (suc (suc n)) x = commₖ _ x (-ₖ x) ∙ lCancelₖ _ x

rCancel≡refl : (n : ℕ) → rCancelₖ (2 + n) (0ₖ _) ≡ refl
rCancel≡refl n i = rUnit (rUnit refl (~ i)) (~ i)

assocₖ : (n : ℕ) → (x y z : coHomK n) → x +[ n ]ₖ (y +[ n ]ₖ z) ≡ (x +[ n ]ₖ y) +[ n ]ₖ z
assocₖ zero = +Assoc
assocₖ (suc zero) =
  trElim3 (λ _ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
          λ x → wedgeconFun _ _
                (λ _ _ → isOfHLevelTrunc 3 _ _)
                (λ y i → rUnitₖ 1 ∣ x ∣ (~ i) +ₖ ∣ y ∣)
                (λ z → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ z ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ z ∣)))
                (helper x)
  where
  helper : (x : S¹) → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ base ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ base ∣))
                    ≡ (cong (_+ₖ ∣ base ∣) (sym (rUnitₖ 1 ∣ x ∣)))
  helper = toPropElim (λ _ → isOfHLevelTrunc 3 _ _ _ _)
                      (sym (lUnit refl))

assocₖ (suc (suc n)) =
  trElim3 (λ _ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          (wedgeConSn-×3 _
            (λ x z i → preAdd-r n x (~ i) +ₖ ∣ z ∣)
            (λ x y → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ y ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ y ∣)))
            (lUnit (sym (rUnitₖ (2 + n) (∣ north ∣ +ₖ ∣ north ∣)))))
  where
  wedgeConSn-×3 : (n : ℕ)
          → (f : (x z : S₊ (2 + n))→ ∣ x ∣ +ₖ ((0ₖ _) +ₖ ∣ z ∣) ≡ (∣ x ∣ +ₖ (0ₖ _)) +ₖ ∣ z ∣)
          → (g : (x y : S₊ (2 + n)) → ∣ x ∣ +ₖ (∣ y ∣ +ₖ 0ₖ _) ≡ (∣ x ∣ +ₖ ∣ y ∣) +ₖ 0ₖ _)
          → (f (ptSn _) (ptSn _) ≡ g (ptSn _) (ptSn _))
          → (x y z : S₊ (2 + n)) → ∣ x ∣ +ₖ (∣ y ∣ +ₖ ∣ z ∣) ≡ (∣ x ∣ +ₖ ∣ y ∣) +ₖ ∣ z ∣
  wedgeConSn-×3 n f g d x =
    wedgeconFun _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
               (f x)
               (g x)
               (sphereElim _ {A = λ x → g x (ptSn (suc (suc n))) ≡ f x (ptSn (suc (suc n))) }
                             (λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
                             (sym d) x)
{-
This was the original proof for the case n ≥ 2:
For some reason it doesn't check in reasonable time anymore:
assocₖ (suc (suc n)) =
  trElim3 (λ _ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                           (λ z i → preAdd n .snd .snd x (~ i) +ₖ ∣ z ∣)
                           (λ y → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ y ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ y ∣)))
                           (helper x) .fst
  where
  helper : (x : S₊ (2 + n)) → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ north ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ north ∣))
                          ≡ cong (_+ₖ ∣ north ∣) (sym (preAdd n .snd .snd x))
  helper = sphereElim (suc n) (λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
                              (sym (lUnit (sym (rUnitₖ (2 + n) (∣ north ∣ +ₖ ∣ north ∣)))))
-}


lUnitₖ≡rUnitₖ : (n : ℕ) → lUnitₖ n (coHom-pt n) ≡ rUnitₖ n (coHom-pt n)
lUnitₖ≡rUnitₖ zero = isSetℤ _ _ _ _
lUnitₖ≡rUnitₖ (suc zero) = refl
lUnitₖ≡rUnitₖ (suc (suc n)) = refl

------ Commutativity of  ΩKₙ
-- We show that p ∙ q ≡ (λ i → (p i) +ₖ (q i)) for any p q : ΩKₙ₊₁. This allows us to prove that p ∙ q ≡ q ∙ p
-- without having to use the equivalence Kₙ ≃ ΩKₙ₊₁


cong+ₖ-comm : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc n)))) → cong₂ _+ₖ_ p q ≡ cong₂ _+ₖ_ q p
cong+ₖ-comm zero p q =
     rUnit (cong₂ _+ₖ_ p q)
  ∙∙ (λ i → (λ j → commₖ 1 ∣ base ∣ ∣ base ∣ (i ∧ j))
     ∙∙ (λ j → commₖ 1 (p j) (q j) i)
     ∙∙ λ j → commₖ 1 ∣ base ∣ ∣ base ∣ (i ∧ ~ j))
  ∙∙ ((λ i → commₖ-base 1 i ∙∙ cong₂ _+ₖ_ q p ∙∙ sym (commₖ-base 1 i))
    ∙ sym (rUnit (cong₂ _+ₖ_ q p)))
cong+ₖ-comm (suc n) p q =
     rUnit (cong₂ _+ₖ_ p q)
  ∙∙ (λ i → (λ j → commₖ (2 + n) ∣ north ∣ ∣ north ∣ (i ∧ j))
     ∙∙ (λ j → commₖ (2 + n) (p j) (q j) i )
     ∙∙ λ j → commₖ (2 + n) ∣ north ∣ ∣ north ∣ (i ∧ ~ j))
  ∙∙ ((λ i → commₖ-base (2 + n) i ∙∙ cong₂ _+ₖ_ q p ∙∙ sym (commₖ-base (2 + n) i))
    ∙ sym (rUnit (cong₂ _+ₖ_ q p)))

isCommΩK : (n : ℕ) → isComm∙ (coHomK-ptd n)
isCommΩK zero p q = isSetℤ _ _ (p ∙ q) (q ∙ p)
isCommΩK (suc zero) p q = ∙≡+₁ p q ∙∙ cong+ₖ-comm 0 p q ∙∙ sym (∙≡+₁ q p)
isCommΩK (suc (suc n)) p q = ∙≡+₂ n p q ∙∙ cong+ₖ-comm (suc n) p q ∙∙ sym (∙≡+₂ n q p)

----- some other useful lemmas about algebra in Kₙ
-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ {n = zero} = refl
-0ₖ {n = suc zero} = refl
-0ₖ {n = suc (suc n)} = refl

-distrₖ : (n : ℕ) (x y : coHomK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ zero x y = GroupTheory.invDistr ℤGroup x y ∙ +Comm (0 - y) (0 - x)
-distrₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ x → sym (lUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (λ x → cong (λ x → -[ 1 ]ₖ x) (rUnitₖ 1 ∣ x ∣) ∙ sym (rUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (sym (rUnit refl)))
-distrₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeconFun _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                        (λ x → sym (lUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (λ x → cong (λ x → -[ (2 + n) ]ₖ x) (rUnitₖ (2 + n) ∣ x ∣ ) ∙ sym (rUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (sym (rUnit refl)))

-cancelRₖ : (n : ℕ) (x y : coHomK n) → (y +[ n ]ₖ x) -[ n ]ₖ x ≡ y
-cancelRₖ zero x y = sym (+Assoc y x (0 - x))
                  ∙∙ cong (y ℤ+_) (+Comm x (0 - x))
                  ∙∙ cong (y ℤ+_) (minusPlus x (pos 0))
-cancelRₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeconFun _ _ (λ _ _ → wedgeConHLevPath 0 _ _)
                        (λ x → cong (_+ₖ ∣ base ∣) (rUnitₖ 1 ∣ x ∣) ∙ rUnitₖ 1 ∣ x ∣)
                        (λ x → rCancelₖ 1 ∣ x ∣)
                        (rUnit refl))
-cancelRₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeconFun _ _ (λ _ _ → wedgeConHLevPath (suc n) _ _)
                        (λ x → cong (_+ₖ ∣ north ∣) (rUnitₖ (2 + n) ∣ x ∣) ∙ rUnitₖ (2 + n) ∣ x ∣)
                        (λ x → rCancelₖ (2 + n) ∣ x ∣)
                        (sym (rUnit _)))

-cancelLₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ x ≡ y
-cancelLₖ n x y = cong (λ z → z -[ n ]ₖ x) (commₖ n x y) ∙ -cancelRₖ n x y

-+cancelₖ : (n : ℕ) (x y : coHomK n) → (x -[ n ]ₖ y) +[ n ]ₖ y ≡ x
-+cancelₖ zero x y = sym (+Assoc x (0 - y) y) ∙ cong (x ℤ+_) (minusPlus y (pos 0))
-+cancelₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeconFun _ _ (λ _ _ → wedgeConHLevPath 0 _ _)
          (λ x → cong (_+ₖ ∣ x ∣) (lUnitₖ 1 (-ₖ ∣ x ∣)) ∙ lCancelₖ 1 ∣ x ∣)
          (λ x → cong (_+ₖ ∣ base ∣) (rUnitₖ 1 ∣ x ∣) ∙ rUnitₖ 1 ∣ x ∣)
          refl)
-+cancelₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeconFun _ _ (λ _ _ → wedgeConHLevPath (suc n) _ _)
          (λ x → cong (_+ₖ ∣ x ∣) (lUnitₖ (2 + n) (-ₖ ∣ x ∣)) ∙ lCancelₖ (2 + n) ∣ x ∣)
          (λ x → cong (_+ₖ ∣ north ∣) (rUnitₖ (2 + n) ∣ x ∣) ∙ rUnitₖ (2 + n) ∣ x ∣)
          refl)

---- Group structure of cohomology groups
_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ {n = n} = sRec2 § λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom n A → coHom n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

_-ₕ_  : {n : ℕ} → coHom n A → coHom n A → coHom n A
_-ₕ_  {n = n} = sRec2 § λ a b → ∣ (λ x → a x -[ n ]ₖ b x) ∣₂

+ₕ-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom n A → coHom n A
-ₕ-syntax n = -ₕ_ {n = n}

-ₕ'-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
-ₕ'-syntax n = _-ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x
syntax -ₕ'-syntax n x y = x -[ n ]ₕ y

0ₕ : (n : ℕ) → coHom n A
0ₕ n = ∣ (λ _ → (0ₖ n)) ∣₂

_+'ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+'ₕ_ {n = n} x y = (x +ₕ 0ₕ _) +ₕ y +ₕ 0ₕ _

rUnitₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (0ₕ n) ≡ x
rUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ n (a x)) i ∣₂

lUnitₕ : (n : ℕ) (x : coHom n A) → (0ₕ n) +[ n ]ₕ x ≡ x
lUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → lUnitₖ n (a x)) i ∣₂

rCancelₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (-[ n ]ₕ x) ≡ 0ₕ n
rCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ n (a x)) i ∣₂

lCancelₕ : (n : ℕ) (x : coHom n A) → (-[ n ]ₕ x) +[ n ]ₕ x  ≡ 0ₕ n
lCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ n (a x)) i ∣₂

assocₕ : (n : ℕ) (x y z : coHom n A) →  (x +[ n ]ₕ (y +[ n ]ₕ z)) ≡ ((x +[ n ]ₕ y) +[ n ]ₕ z)
assocₕ n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ n (a x) (b x) (c x)) i ∣₂

commₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) ≡ (y +[ n ]ₕ x)
commₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ funExt (λ x → commₖ n (a x) (b x)) i ∣₂

-cancelLₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) -[ n ]ₕ x ≡ y
-cancelLₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelLₖ n (a x) (b x) i) ∣₂

-cancelRₕ : (n : ℕ) (x y : coHom n A) → (y +[ n ]ₕ x) -[ n ]ₕ x ≡ y
-cancelRₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelRₖ n (a x) (b x) i) ∣₂

-+cancelₕ : (n : ℕ) (x y : coHom n A) → (x -[ n ]ₕ y) +[ n ]ₕ y ≡ x
-+cancelₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -+cancelₖ n (a x) (b x) i) ∣₂

-- Group structure of reduced cohomology groups (in progress - might need K to compute properly first)
_+ₕ∙_ : {A : Pointed ℓ} {n : ℕ} → coHomRed n A → coHomRed n A → coHomRed n A
_+ₕ∙_ {n = zero} = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x)
                                            , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
_+ₕ∙_ {n = (suc zero)} = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ 1 ]ₖ b x)
                                                 , (λ i → pa i +[ 1 ]ₖ pb i) ∣₂ }
_+ₕ∙_ {n = (suc (suc n))} =
  sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (2 + n) ]ₖ b x)
                                  , (λ i → pa i +[ (2 + n) ]ₖ pb i) ∣₂ }

-ₕ∙_ : {A : Pointed ℓ} {n : ℕ} → coHomRed n A → coHomRed n A
-ₕ∙_ {n = zero} = sRec § λ {(f , p) → ∣ (λ x → -[ 0 ]ₖ (f x))
                                      , cong (λ x → -[ 0 ]ₖ x) p ∣₂}
-ₕ∙_ {n = suc zero} = sRec § λ {(f , p) → ∣ (λ x → -ₖ (f x))
                                           , cong -ₖ_ p ∣₂}
-ₕ∙_ {n = suc (suc n)} = sRec § λ {(f , p) → ∣ (λ x → -ₖ (f x))
                                             , cong -ₖ_ p ∣₂}

0ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A
0ₕ∙ n = ∣ (λ _ → 0ₖ n) , refl ∣₂

+ₕ∙-syntax : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙-syntax n = _+ₕ∙_ {n = n}

-ₕ∙-syntax : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A
-ₕ∙-syntax n = -ₕ∙_ {n = n}

-'ₕ∙-syntax : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
-'ₕ∙-syntax n x y = _+ₕ∙_ {n = n} x (-ₕ∙_ {n = n} y)

syntax +ₕ∙-syntax n x y = x +[ n ]ₕ∙ y
syntax -ₕ∙-syntax n x = -[ n ]ₕ∙ x
syntax -'ₕ∙-syntax n x y = x -[ n ]ₕ∙ y

commₕ∙ : {A : Pointed ℓ} (n : ℕ) (x y : coHomRed n A) → x +[ n ]ₕ∙ y ≡ y +[ n ]ₕ∙ x
commₕ∙ zero =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) (g , q)
           → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) λ i x → commₖ 0 (f x) (g x) i)}
commₕ∙ (suc zero) =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) (g , q)
           → cong ∣_∣₂ (ΣPathP ((λ i x → commₖ 1 (f x) (g x) i)
                             , λ i j → commₖ 1 (p j) (q j) i))}
commₕ∙ {A = A} (suc (suc n)) =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) (g , q)
           → cong ∣_∣₂ (ΣPathP ((λ i x → commₖ (2 + n) (f x) (g x) i)
                              , λ i j → hcomp (λ k → λ {(i = i0) → p j +ₖ q j
                                                        ; (i = i1) → q j +ₖ p j
                                                        ; (j = i0) → commₖ (2 + n) (f (pt A)) (g (pt A)) i
                                                        ; (j = i1) → rUnit (refl {x = 0ₖ (2 + n)}) (~ k) i})
                                               (commₖ (2 + n) (p j) (q j) i)))}

rUnitₕ∙ : {A : Pointed ℓ} (n : ℕ) (x : coHomRed n A) → x +[ n ]ₕ∙ 0ₕ∙ n ≡ x
rUnitₕ∙ zero =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) λ i x → rUnitₖ zero (f x) i)}
rUnitₕ∙ (suc zero) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (ΣPathP ((λ i x → rUnitₖ 1 (f x) i) , λ i j → rUnitₖ 1 (p j) i))}
rUnitₕ∙ (suc (suc n)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (ΣPathP ((λ i x → rUnitₖ (2 + n) (f x) i) , λ i j → rUnitₖ (2 + n) (p j) i))}

lUnitₕ∙ : {A : Pointed ℓ} (n : ℕ) (x : coHomRed n A) → 0ₕ∙ n +[ n ]ₕ∙ x ≡ x
lUnitₕ∙ zero =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) λ i x → lUnitₖ zero (f x) i)}
lUnitₕ∙ (suc zero) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (ΣPathP ((λ i x → lUnitₖ 1 (f x) i) , λ i j → lUnitₖ 1 (p j) i))}
lUnitₕ∙ (suc (suc n)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (ΣPathP ((λ i x → lUnitₖ (2 + n) (f x) i) , λ i j → lUnitₖ (2 + n) (p j) i))}


private
  pp : {A : Pointed ℓ}  (n : ℕ) → (f : fst A → coHomK (suc (suc n)))
      → (p : f (snd A) ≡ snd (coHomK-ptd (suc (suc n))))
      → PathP (λ i → rCancelₖ (2 + n) (f (snd A)) i ≡ 0ₖ (suc (suc n)))
        (λ i → (p i) +ₖ (-ₖ p i)) (λ _ → 0ₖ (suc (suc n)))
  pp {A = A} n f p i j =
    hcomp (λ k → λ {(i = i0) → rCancelₖ (suc (suc n)) (p j) (~ k)
                  ; (i = i1) → 0ₖ (suc (suc n))
                  ; (j = i0) → rCancelₖ (2 + n) (f (snd A)) (i ∨ ~ k)
                  ; (j = i1) → rUnit (rUnit (λ _ → 0ₖ (suc (suc n))) (~ i)) (~ i) k})
         (0ₖ (suc (suc n)))

rCancelₕ∙ : {A : Pointed ℓ} (n : ℕ) (x : coHomRed n A) → x +[ n ]ₕ∙ (-[ n ]ₕ∙ x) ≡ 0ₕ∙ n
rCancelₕ∙ zero =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) λ i x → rCancelₖ zero (f x) i)}
rCancelₕ∙ {A = A} (suc zero) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (ΣPathP ((λ i x → rCancelₖ 1 (f x) i) , λ i j → rCancelₖ 1 (p j) i))}
rCancelₕ∙ {A = A} (suc (suc n)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p)
           → cong ∣_∣₂ (ΣPathP ((λ i x → rCancelₖ (2 + n) (f x) i)
                               , pp n f p))}

lCancelₕ∙ : {A : Pointed ℓ} (n : ℕ) (x : coHomRed n A) → (-[ n ]ₕ∙ x) +[ n ]ₕ∙ x ≡ 0ₕ∙ n
lCancelₕ∙ zero =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) λ i x → lCancelₖ zero (f x) i)}
lCancelₕ∙ {A = A} (suc zero) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p)
           → cong ∣_∣₂ (ΣPathP ((λ i x → lCancelₖ 1 (f x) i)
                               , λ i j → (lCancelₖ 1 (p j) i)))}
lCancelₕ∙ {A = A} (suc (suc n)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ {(f , p)
           → cong ∣_∣₂ (ΣPathP ((λ i x → lCancelₖ (2 + n) (f x) i)
                               , λ i j → lCancelₖ (2 + n) (p j) i))}

assocₕ∙ : {A : Pointed ℓ} (n : ℕ) (x y z : coHomRed n A)
       → (x +[ n ]ₕ∙ (y +[ n ]ₕ∙ z)) ≡ ((x +[ n ]ₕ∙ y) +[ n ]ₕ∙ z)
assocₕ∙ zero =
  elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) (g , q) (h , r)
          → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _)
                              (λ i x → assocₖ zero (f x) (g x) (h x) i))}
assocₕ∙ (suc zero) =
  elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) (g , q) (h , r)
          → cong ∣_∣₂ (ΣPathP ((λ i x → assocₖ 1 (f x) (g x) (h x) i)
                             , λ i j → assocₖ 1 (p j) (q j) (r j) i))}
assocₕ∙ (suc (suc n)) =
  elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) (g , q) (h , r)
          → cong ∣_∣₂ (ΣPathP ((λ i x → assocₖ (2 + n) (f x) (g x) (h x) i)
                             , λ i j → assocₖ (2 + n) (p j) (q j) (r j) i))}

open IsSemigroup
open IsMonoid
open GroupStr
open IsGroupHom

coHomGr : (n : ℕ) (A : Type ℓ) → Group ℓ
coHomGr n A = coHom n A , coHomGrnA
  where
  coHomGrnA : GroupStr (coHom n A)
  1g coHomGrnA = 0ₕ n
  GroupStr._·_ coHomGrnA = λ x y → x +[ n ]ₕ y
  inv coHomGrnA = λ x → -[ n ]ₕ x
  isGroup coHomGrnA = helper
    where
    abstract
      helper : IsGroup {G = coHom n A} (0ₕ n) (λ x y → x +[ n ]ₕ y) (λ x → -[ n ]ₕ x)
      helper = makeIsGroup § (assocₕ n) (rUnitₕ n) (lUnitₕ n) (rCancelₕ n) (lCancelₕ n)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group _
×coHomGr n A B = DirProd (coHomGr n A) (coHomGr n B)

coHomGroup : (n : ℕ) (A : Type ℓ) → AbGroup ℓ
fst (coHomGroup n A) = coHom n A
AbGroupStr.0g (snd (coHomGroup n A)) = 0ₕ n
AbGroupStr._+_ (snd (coHomGroup n A)) = _+ₕ_ {n = n}
AbGroupStr.- snd (coHomGroup n A) = -ₕ_ {n = n}
IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd (coHomGroup n A))) = isGroup (snd (coHomGr n A))
IsAbGroup.comm (AbGroupStr.isAbGroup (snd (coHomGroup n A))) = commₕ n

-- Reduced cohomology group (direct def)

coHomRedGroupDir : (n : ℕ) (A : Pointed ℓ) → AbGroup ℓ
fst (coHomRedGroupDir n A) = coHomRed n A
AbGroupStr.0g (snd (coHomRedGroupDir n A)) = 0ₕ∙ n
AbGroupStr._+_ (snd (coHomRedGroupDir n A)) = _+ₕ∙_ {n = n}
AbGroupStr.- snd (coHomRedGroupDir n A) = -ₕ∙_ {n = n}
IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd (coHomRedGroupDir n A))) = helper
  where
  abstract
    helper : IsGroup {G = coHomRed n A} (0ₕ∙ n) (_+ₕ∙_ {n = n}) (-ₕ∙_ {n = n})
    helper = makeIsGroup § (assocₕ∙ n) (rUnitₕ∙ n) (lUnitₕ∙ n) (rCancelₕ∙ n) (lCancelₕ∙ n)
IsAbGroup.comm (AbGroupStr.isAbGroup (snd (coHomRedGroupDir n A))) = commₕ∙ n

coHomRedGrDir : (n : ℕ) (A : Pointed ℓ) → Group ℓ
coHomRedGrDir n A = AbGroup→Group (coHomRedGroupDir n A)

-- Induced map
coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

coHomMorph : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → GroupHom (coHomGr n B) (coHomGr n A)
fst (coHomMorph n f) = coHomFun n f
snd (coHomMorph n f) = makeIsGroupHom (helper n)
  where
  helper : ℕ → _
  helper zero = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl
  helper (suc zero) = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl
  helper (suc (suc n)) = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl

-- Alternative definition of cohomology using ΩKₙ instead. Useful for breaking proofs of group isos
-- up into smaller parts
coHomGrΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group ℓ
coHomGrΩ n A = ∥ (A → typ (Ω (coHomK-ptd (suc n)))) ∥₂ , coHomGrnA
  where
  coHomGrnA : GroupStr ∥ (A → typ (Ω (coHomK-ptd (suc n)))) ∥₂
  1g coHomGrnA = ∣ (λ _ → refl) ∣₂
  GroupStr._·_ coHomGrnA = sRec2 § λ p q → ∣ (λ x → p x ∙ q x) ∣₂
  inv coHomGrnA = map λ f x → sym (f x)
  isGroup coHomGrnA = helper
    where
    abstract
      helper :
        IsGroup {G = ∥ (A → typ (Ω (coHomK-ptd (suc n)))) ∥₂}
          (∣ (λ _ → refl) ∣₂) (sRec2 § λ p q → ∣ (λ x → p x ∙ q x) ∣₂) (map λ f x → sym (f x))
      helper = makeIsGroup § (elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _)
                                    (λ p q r → cong ∣_∣₂ (funExt λ x → assoc∙ (p x) (q x) (r x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → sym (rUnit (p x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → sym (lUnit (p x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → rCancel (p x)))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → lCancel (p x)))

--- the loopspace of Kₙ is commutative regardless of base
addIso : (n : ℕ) (x : coHomK n) → Iso (coHomK n) (coHomK n)
fun (addIso n x) y = y +[ n ]ₖ x
inv' (addIso n x) y = y -[ n ]ₖ x
rightInv (addIso n x) y = -+cancelₖ n y x
leftInv (addIso n x) y = -cancelRₖ n x y

baseChange : (n : ℕ) (x : coHomK (suc n)) → (0ₖ (suc n) ≡ 0ₖ (suc n)) ≃ (x ≡ x)
baseChange n x = isoToEquiv is
  where
  f : (n : ℕ) (x : coHomK (suc n)) → (0ₖ (suc n) ≡ 0ₖ (suc n)) → (x ≡ x)
  f n x p = sym (rUnitₖ _ x) ∙∙ cong (x +ₖ_) p ∙∙ rUnitₖ _ x

  g : (n : ℕ) (x : coHomK (suc n)) → (x ≡ x) → (0ₖ (suc n) ≡ 0ₖ (suc n))
  g n x p = sym (rCancelₖ _ x) ∙∙ cong (λ y → y -ₖ x) p ∙∙ rCancelₖ _ x

  f-g : (n : ℕ) (x : coHomK (suc n)) (p : x ≡ x) → f n x (g n x p) ≡ p
  f-g n =
    trElim (λ _ → isOfHLevelΠ (3 + n) λ _ → isOfHLevelPath (3 + n)
      (isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _) _ _)
        (ind n)
    where
    ind : (n : ℕ) (a : S₊ (suc n)) (p : ∣ a ∣ₕ ≡ ∣ a ∣ₕ) → f n ∣ a ∣ₕ (g n ∣ a ∣ₕ p) ≡ p
    ind zero =
      toPropElim (λ _ → isPropΠ λ _ → isOfHLevelTrunc 3 _ _ _ _)
        λ p → cong (f zero (0ₖ 1)) (sym (rUnit _) ∙ (λ k i → rUnitₖ _ (p i) k))
            ∙∙ sym (rUnit _)
            ∙∙ λ k i → lUnitₖ _ (p i) k
    ind (suc n) =
      sphereElim (suc n) (λ _ → isOfHLevelΠ (2 + n) λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
        λ p → cong (f (suc n) (0ₖ (2 + n)))
                ((λ k → (sym (rUnit (refl ∙ refl)) ∙ sym (rUnit refl)) k
                     ∙∙ (λ i → p i +ₖ 0ₖ (2 + n)) ∙∙ (sym (rUnit (refl ∙ refl)) ∙ sym (rUnit refl)) k)
              ∙ (λ k → rUnit (λ i → rUnitₖ _ (p i) k) (~ k)))
              ∙ λ k → rUnit (λ i → lUnitₖ _ (p i) k) (~ k)

  g-f : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ 0ₖ _) → g n x (f n x p) ≡ p
  g-f n =
    trElim (λ _ → isOfHLevelΠ (3 + n) λ _ → isOfHLevelPath (3 + n)
      (isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _) _ _)
        (ind n)
    where
    ind : (n : ℕ) (a : S₊ (suc n)) (p : 0ₖ (suc n) ≡ 0ₖ (suc n)) → g n ∣ a ∣ₕ (f n ∣ a ∣ₕ p) ≡ p
    ind zero =
      toPropElim (λ _ → isPropΠ λ _ → isOfHLevelTrunc 3 _ _ _ _)
        λ p → cong (g zero (0ₖ 1)) (λ k → rUnit (λ i → lUnitₖ _ (p i) k) (~ k))
            ∙ (λ k → rUnit (λ i → rUnitₖ _ (p i) k) (~ k))
    ind (suc n) =
      sphereElim (suc n) (λ _ → isOfHLevelΠ (2 + n) λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
        λ p → cong (g (suc n) (0ₖ (2 + n)))
                (λ k → rUnit (λ i → lUnitₖ _ (p i) k) (~ k))
            ∙∙ (λ k → (sym (rUnit (refl ∙ refl)) ∙ sym (rUnit refl)) k
                    ∙∙ (λ i → p i +ₖ 0ₖ (2 + n))
                    ∙∙ (sym (rUnit (refl ∙ refl)) ∙ sym (rUnit refl)) k)
            ∙∙ λ k → rUnit (λ i → rUnitₖ _ (p i) k) (~ k)

  is : Iso _ _
  fun is = f n x
  inv' is = g n x
  rightInv is = f-g n x
  leftInv is = g-f n x

isCommΩK-based : (n : ℕ) (x : coHomK n) → isComm∙ (coHomK n , x)
isCommΩK-based zero x p q = isSetℤ _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc zero) x =
  subst isComm∙ (λ i → coHomK 1 , lUnitₖ 1 x i)
                (ptdIso→comm {A = (_ , 0ₖ 1)} (addIso 1 x)
                              (isCommΩK 1))
isCommΩK-based (suc (suc n)) x =
  subst isComm∙ (λ i → coHomK (suc (suc n)) , lUnitₖ (suc (suc n)) x i)
                (ptdIso→comm {A = (_ , 0ₖ (suc (suc n)))} (addIso (suc (suc n)) x)
                              (isCommΩK (suc (suc n))))

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
  -Kbin n x y = +K n x (-K n y)

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
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) y x) (lock t (-ₖ_ {n = n}) x) ≡ y
    pm unlock = -cancelRₖ n x y

  -cancelLK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n x y) x ≡ y
  -cancelLK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) (lock t (-ₖ_ {n = n}) x) ≡ y
    pm unlock = -cancelLₖ n x y

  -+cancelK : (n : ℕ) (x y : coHomK n) → +K n (-Kbin n x y) y ≡ x
  -+cancelK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n})  x (lock t (-ₖ_ {n = n}) y)) y ≡ x
    pm unlock = -+cancelₖ n x y

  assocK : (n : ℕ) (x y z : coHomK n) → +K n x (+K n y z) ≡ +K n (+K n x y) z
  assocK n x y z = pm key
    where
    pm : (t : Unit') →  lock t (_+ₖ_ {n = n}) x (lock t (_+ₖ_ {n = n}) y z)
                       ≡ lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) z
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

  assocH : (n : ℕ) (x y z : coHom n A) → (+H n x (+H n y z)) ≡ (+H n (+H n x y) z)
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

lUnitK≡rUnitK : (key : Unit') (n : ℕ) → lockedCohom.lUnitK key n (0ₖ n) ≡ lockedCohom.rUnitK key n (0ₖ n)
lUnitK≡rUnitK unlock = lUnitₖ≡rUnitₖ

open GroupStr renaming (_·_ to _+gr_)
open IsGroupHom

-- inducedCoHom : ∀ {ℓ ℓ'} {A : Type ℓ} {G : Group {ℓ'}} {n : ℕ}
--   → GroupIso (coHomGr n A) G
--   → Group
-- inducedCoHom {A = A} {G = G} {n = n} e =
--   InducedGroup (coHomGr n A)
--                (coHom n A , λ x y → Iso.inv (isom e) (_+gr_ (snd G) (fun (isom e) x)
--                                                          (fun (isom e) y)))
--                (idEquiv _)
--                λ x y → sym (leftInv (isom e) _)
--                       ∙ cong (Iso.inv (isom e)) (isHom e x y)

-- induced+ : ∀ {ℓ ℓ'} {A : Type ℓ} {G : Group {ℓ'}} {n : ℕ}
--   → (e : GroupIso (coHomGr n A) G)
--   → fst (inducedCoHom e) → fst (inducedCoHom e) → fst (inducedCoHom e)
-- induced+ e = _+gr_ (snd (inducedCoHom e))

-- inducedCoHomIso : ∀ {ℓ ℓ'} {A : Type ℓ} {G : Group {ℓ'}} {n : ℕ}
--                → (e : GroupIso (coHomGr n A) G)
--                → GroupIso (coHomGr n A) (inducedCoHom e)
-- isom (inducedCoHomIso e) = idIso
-- isHom (inducedCoHomIso e) x y = sym (leftInv (isom e) _)
--                               ∙ cong (Iso.inv (isom e)) (isHom e x y)

-- inducedCoHomPath : ∀ {ℓ ℓ'} {A : Type ℓ} {G : Group {ℓ'}} {n : ℕ}
--                → (e : GroupIso (coHomGr n A) G)
--                → coHomGr n A ≡ inducedCoHom e
-- inducedCoHomPath e = InducedGroupPath _ _ _ _
