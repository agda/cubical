{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to pRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.HITs.Pushout
open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Equiv

open GroupIso renaming (map to map')
open GroupHom

{-
This module proves that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B) for n ≥ 1 directly (rather than by means of Mayer-Vietoris).

Proof sketch:

Any ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) is uniquely characterised by a pair of functions
  f₁ : A → Kₙ
  f₂ : B → Kₙ
together with a path
  p : f₁ (pt A) ≡ f₂ (pt B)

The map F : Hⁿ(A ⋁ B) → Hⁿ(A) × Hⁿ(B) simply forgets about p, i.e.:
  F(∣ f ∣₂) := (∣ f₁ ∣₂ , ∣ f₂ ∣₂)

The construction of its inverse is defined by
  F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂) := ∣ f₁∨f₂ ∣₂
  where
  f₁∨f₂ : A ⋁ B → Kₙ is defined inductively by
  f₁∨f₂ (inl x) := f₁ x + f₂ (pt B)
  f₁∨f₂ (inr x) := f₂ x + f₁ (pt B)
  cong f₁∨f₂ (push tt) := "f₁ (pt A) + f₂ (pt B) =(commutativity) f₂ (pt B) + f₁ (pt A)"
  (this is the map wedgeFun⁻ below)
  Note that the cong-case above reduces to refl when f₁ (pt A) := f₂ (pt B) := 0

The fact that F and F⁻ cancel out is a proposition and we may thus assume for any
  ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) and its corresponding f₁ that
  f₁ (pt A) = f₂ (pt B) = 0                (*)
  and
  f (inl (pt A)) = 0                       (**)

The fact that F(F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂)) = ∣ f₁ ∣₂ , ∣ f₂ ∣₂) follows immediately from (*)

The other way is slightly trickier. We need to construct paths
  Pₗ : f (inl (x)) + f (inr (pt B)) ---> f (inl (x))
  Pᵣ  : f (inr (x)) + f (inl (pt A)) ---> f (inr (x))

Together with a filler of the following square

     cong f (push tt)
    ----------------->
   ^                  ^
   |                  |
   |                  |
Pₗ |                  | Pᵣ
   |                  |
   |                  |
   |                  |
    ----------------->
            Q
where Q is commutativity proof f (inl (pt A)) + f (inr (pt B)) = f (inr (pt B)) + f (inl (pt A))

The square is filled by first constructing Pₗ by
  f (inl (x)) + f (inr (pt B))    ---[cong f (push tt)⁻¹]--->
  f (inl (x)) + f (inl (pt A))    ---[(**)]--->
  f (inl (x)) + 0                 ---[right-unit]--->
  f (inl (x))

and then Pᵣ by
  f (inr (x)) + f (inl (pt A))    ---[(**)]--->
  f (inr (x)) + 0                 ---[right-unit]--->
  f (inr (x))

and finally by using the fact that the group laws for Kₙ are refl at its base point.
-}

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where

  private
    wedgeFun⁻ : ∀ n → (f : typ A → coHomK (suc n)) (g : typ B → coHomK (suc n))
            → ((A ⋁ B) → coHomK (suc n))
    wedgeFun⁻ n f g (inl x) = f x +ₖ g (pt B)
    wedgeFun⁻ n f g (inr x) = g x +ₖ f (pt A)
    wedgeFun⁻ n f g (push a i) = commₖ (suc n) (f (pt A)) (g (pt B)) i

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  fun (map' (Hⁿ-⋁ zero)) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ zero)) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ zero) = uncurry (sElim2 (λ _ _ → setTruncIsSet)
                             λ f g → ∣ wedgeFun⁻ 0 f g ∣₂)
  rightInv (Hⁿ-⋁ zero) =
    uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP (cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ 1 (f x))) ,
                           cong ∣_∣₂ (funExt (λ x → cong (g x +ₖ_) fId ∙ rUnitₖ 1 (g x)))))
  leftInv (Hⁿ-⋁ zero) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK 1) (x : coHomK 1)
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ 0 (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropΠ λ _ → propTruncIsProp))
        (sphereElim 0 (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ 1 (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (rUnitₖ 1 (f (inr x)))
                                            ∙ cong ((f (inr x)) +ₖ_) (sym inlId)
                                 ; (push tt i) j → cheating (f (inl (pt A))) (sym (inlId))
                                                             (f (inr (pt B)))
                                                             (cong f (push tt)) j i}) ∣₁))
      where
      cheating : (x : coHomK 1) (r : ∣ base ∣ ≡ x) (y : coHomK 1) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (rUnitₖ 1 y) ∙ cong (y +ₖ_) r) j)
                       p (commₖ 1 x y)
      cheating x = J (λ x r → (y : coHomK 1) (p : x ≡ y)
                            → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                            ≡ (sym (rUnitₖ 1 y) ∙ cong (y +ₖ_) r) j)
                                     p (commₖ 1 x y))
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ 1 ∣ base ∣) ∙∙ refl ∙∙ cong (∣ base ∣ +ₖ_) p)) j
                                                     ≡ (sym (rUnitₖ 1 y) ∙ refl) j)
                                              p (commₖ 1 ∣ base ∣ y))
                             λ i j → comp (λ _ → hLevelTrunc 3 S¹)
                                           (λ k → λ {(i = i0) → ∣ base ∣
                                                    ; (i = i1) → ∣ base ∣
                                                    ; (j = i0) → (rUnit (λ _ → ∣ base ∣) k) i
                                                    ; (j = i1) → (rUnit (λ _ → ∣ base ∣) k) i})
                                           ∣ base ∣
  fun (map' (Hⁿ-⋁ (suc n))) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ (suc n))) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ (suc n)) =
    uncurry (sElim2 (λ _ _ → setTruncIsSet)
                     λ f g → ∣ wedgeFun⁻ (suc n) f g ∣₂)
  rightInv (Hⁿ-⋁ (suc n)) =
   uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP (cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ (2 + n) (f x))) ,
                           cong ∣_∣₂ (funExt (λ x → cong (g x +ₖ_) fId ∙ rUnitₖ (2 + n) (g x)))))
  leftInv (Hⁿ-⋁ (suc n)) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK (2 + n)) (x : coHomK (2 + n))
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ (suc n) (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropΠ λ _ → propTruncIsProp))
        (sphereToPropElim (suc n) (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ (2 + n) (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (rUnitₖ (2 + n) (f (inr x)))
                                            ∙ cong ((f (inr x)) +ₖ_) (sym inlId)
                                 ; (push tt i) j → cheating (f (inl (pt A))) (sym (inlId))
                                                             (f (inr (pt B))) (cong f (push tt)) j i}) ∣₁))
      where
      cheating : (x : coHomK (2 + n)) (r : ∣ north ∣ ≡ x) (y : coHomK (2 + n)) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (rUnitₖ (2 + n) y) ∙ cong (y +ₖ_) r) j)
                       p (commₖ (2 + n) x y)
      cheating x =
         J (λ x r → (y : coHomK (2 + n)) (p : x ≡ y)
                            → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                            ≡ (sym (rUnitₖ (2 + n) y) ∙ cong (y +ₖ_) r) j)
                                     p (commₖ (2 + n) x y))
                     doubleCheating
        where
        doubleCheating : (y : coHomK (2 + n)) → (p : ∣ north ∣ ≡ y)
                      → PathP (λ j → ((refl ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                      ≡ (sym (rUnitₖ (2 + n) y) ∙ refl) j)
                               p
                               (commₖ (2 + n) ∣ north ∣ y)
        doubleCheating y =
          J (λ y p → PathP (λ j → ((refl ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                      ≡ (sym (rUnitₖ (2 + n) y) ∙ refl) j)
                               p
                               (commₖ (2 + n) ∣ north ∣ y))
            λ i j → comp (λ _ → coHomK (2 + n))
                          (λ k → λ {(i = i0) → ∣ north ∣
                                   ; (i = i1) → commₖ-base (2 + n) (~ k) j
                                   ; (j = i0) → rUnit (λ _ → ∣ north ∣) k i
                                   ; (j = i1) → rUnit (λ _ → ∣ north ∣) k i})
                          ∣ north ∣

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥) → ((x : typ B) → ∥ pt B ≡ x ∥) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥
  wedgeConnected conA conB =
    PushoutToProp (λ _ → propTruncIsProp)
                  (λ a → pRec propTruncIsProp (λ p → ∣ cong inl p ∣₁) (conA a))
                   λ b → pRec propTruncIsProp (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b)


open import Cubical.Data.Int
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Int renaming (+-comm to +-commℤ ; _+_ to _+ℤ_)

even : Int → Bool
even (pos zero) = true
even (pos (suc zero)) = false
even (pos (suc (suc n))) = even (pos n)
even (negsuc zero) = false
even (negsuc (suc n)) = even (pos n)

open import Cubical.Data.Sum

even-2 : (x : Int) → even (-2 +ℤ x) ≡ even x
even-2 (pos zero) = refl
even-2 (pos (suc zero)) = refl
even-2 (pos (suc (suc n))) =
    cong even (cong sucInt (sucInt+pos _ _)
            ∙∙ sucInt+pos _ _
            ∙∙ +-commℤ 0 (pos n))
  ∙ noClueWhy n
  where
  noClueWhy : (n : ℕ) → even (pos n) ≡ even (pos n)
  noClueWhy n = refl
even-2 (negsuc zero) = refl
even-2 (negsuc (suc n)) =
    cong even (predInt+negsuc n _
             ∙ +-commℤ -3 (negsuc n))
  ∙ noClueWhy n
  where
  noClueWhy : (n : ℕ) → even (negsuc (suc (suc (suc n)))) ≡ even (pos n)
  noClueWhy n = refl

test3 : (p : 0ₖ 1 ≡ 0ₖ 1) → even (ΩKn+1→Kn 0 (transport (λ i → ∣ (loop ∙ loop) i ∣ ≡ 0ₖ 1) p)) ≡ even (ΩKn+1→Kn 0 p)
test3 p = cong even (cong (ΩKn+1→Kn 0) (cong (transport (λ i → ∣ (loop ∙ loop) i ∣ ≡ 0ₖ 1)) (lUnit p)))
      ∙∙ cong even (cong (ΩKn+1→Kn 0) λ j → transp (λ i → ∣ (loop ∙ loop) (i ∨ j) ∣ ≡ 0ₖ 1) j ((λ i → ∣ (loop ∙ loop) (~ i ∧ j) ∣) ∙ p))
      ∙∙ cong even (ΩKn+1→Kn-hom 0 (sym (cong ∣_∣ (loop ∙ loop))) p)
       ∙ even-2 (ΩKn+1→Kn 0 p)

test2 :  Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 → Bool
test2 = uncurry (trElim (λ _ → isGroupoidΠ λ _ → isOfHLevelSuc 2 isSetBool)
                        λ {base p → even (ΩKn+1→Kn 0 p)
                        ; (loop i) p → hcomp (λ k → λ { (i = i0) → test3 p k
                                                        ; (i = i1) → even (ΩKn+1→Kn 0 p)})
                        (even (ΩKn+1→Kn 0 (transp (λ j → ∣ (loop ∙ loop) (i ∨ j) ∣ ≡ 0ₖ 1) i
                                                      p)))})

*' : (x y : coHomK 1) (p : x +ₖ x ≡ 0ₖ 1) (q : y +ₖ y ≡ 0ₖ 1) → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
*' =
  trElim2 (λ _ _ → isGroupoidΠ2 λ _ _ → isOfHLevelSuc 2 setTruncIsSet)
          (wedgeConSn _ _
            (λ _ _ → isSetΠ2 λ _ _ → setTruncIsSet)
            (λ x p q → ∣ ∣ x ∣ , cong₂ _+ₖ_ p q ∣₂)
            (λ y p q → ∣ ∣ y ∣ , sym (rUnitₖ 1 (∣ y ∣ +ₖ ∣ y ∣)) ∙ cong₂ _+ₖ_ p q ∣₂)
            (funExt λ p → funExt λ q → cong ∣_∣₂ (ΣPathP (refl , (sym (lUnit _))))) .fst)



_*_ : ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
_*_ = sRec (isSetΠ (λ _ → setTruncIsSet)) λ a → sRec setTruncIsSet λ b → *' (fst a) (fst b) (snd a) (snd b)
*=∙ : (p q : 0ₖ 1 ≡ 0ₖ 1) → ∣ 0ₖ 1 , p ∣₂ * ∣ 0ₖ 1 , q ∣₂ ≡ ∣ 0ₖ 1 , p ∙ q ∣₂
*=∙ p q = cong ∣_∣₂ (ΣPathP (refl , sym (∙≡+₁ p q)))

help : (n : ℕ) → even (pos (suc n)) ≡ true → even (negsuc n) ≡ true
help zero p = ⊥-rec (true≢false (sym p))
help (suc n) p = p

help2 : (n : ℕ) → even (pos (suc n)) ≡ false → even (negsuc n) ≡ false
help2 zero p = refl
help2 (suc n) p = p


evenCharac : (x : Int) → even x ≡ true
    → Path ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
            ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂
            ∣ (0ₖ 1 , refl) ∣₂
evenCharac (pos zero) iseven i = ∣ (0ₖ 1) , (rUnit refl (~ i)) ∣₂
evenCharac (pos (suc zero)) iseven = ⊥-rec (true≢false (sym iseven))
evenCharac (pos (suc (suc zero))) iseven = cong ∣_∣₂ ((λ i → 0ₖ 1 , rUnit (cong ∣_∣ ((lUnit loop (~ i)) ∙ loop)) (~ i))
                                           ∙  (ΣPathP (cong ∣_∣ loop , λ i j → ∣ (loop ∙ loop) (i ∨ j) ∣)))
evenCharac (pos (suc (suc (suc n)))) iseven =
     (λ i → ∣ 0ₖ 1 , Kn→ΩKn+1-hom 0 (pos (suc n)) 2 i ∣₂)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (pos (suc n))) (Kn→ΩKn+1 0 (pos 2)))
  ∙∙ (cong₂ _*_ (evenCharac (pos (suc n)) iseven) (evenCharac 2 refl))

evenCharac (negsuc zero) iseven = ⊥-rec (true≢false (sym iseven))
evenCharac (negsuc (suc zero)) iseven =
  cong ∣_∣₂ ((λ i → 0ₖ 1 , λ i₁ → hfill (doubleComp-faces (λ i₂ → ∣ base ∣) (λ _ → ∣ base ∣) i₁)
                                         (inS ∣ compPath≡compPath' (sym loop) (sym loop) i i₁ ∣) (~ i))
                                ∙ ΣPathP ((cong ∣_∣ (sym loop)) , λ i j → ∣ (sym loop ∙' sym loop) (i ∨ j) ∣))
evenCharac (negsuc (suc (suc n))) iseven =
     cong ∣_∣₂ (λ i → 0ₖ 1 , Kn→ΩKn+1-hom 0 (negsuc n) -2 i)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (negsuc n)) (Kn→ΩKn+1 0 -2))
  ∙∙ cong₂ _*_ (evenCharac (negsuc n) (help n iseven)) (evenCharac -2 refl) -- i

oddCharac : (x : Int) → even x ≡ false
    → Path ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
            ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂
            ∣ (0ₖ 1 , cong ∣_∣ loop) ∣₂
oddCharac (pos zero) isOdd = ⊥-rec (true≢false isOdd)
oddCharac (pos (suc zero)) isOdd i =
  ∣ (0ₖ 1 , λ j → hfill (doubleComp-faces (λ i₂ → ∣ base ∣) (λ _ → ∣ base ∣) j)
                         (inS ∣ lUnit loop (~ i) j ∣) (~ i)) ∣₂
oddCharac (pos (suc (suc n))) isOdd =
  (λ i → ∣ 0ₖ 1 , Kn→ΩKn+1-hom 0 (pos n) 2 i ∣₂)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (pos n)) (Kn→ΩKn+1 0 2))
  ∙∙ cong₂ _*_ (oddCharac (pos n) isOdd) (evenCharac 2 refl)
oddCharac (negsuc zero) isOdd =
    cong ∣_∣₂ ((λ i → 0ₖ 1 , rUnit (sym (cong ∣_∣ loop)) (~ i))
  ∙ ΣPathP (cong ∣_∣ (sym loop) , λ i j → ∣ hcomp (λ k → λ { (i = i0) → loop (~ j ∧ k)
                                                           ; (i = i1) → loop j
                                                           ; (j = i1) → base})
                                                 (loop (j ∨ ~ i)) ∣))
oddCharac (negsuc (suc zero)) isOdd = ⊥-rec (true≢false isOdd)
oddCharac (negsuc (suc (suc n))) isOdd =
     cong ∣_∣₂ (λ i → 0ₖ 1 , Kn→ΩKn+1-hom 0 (negsuc n) -2 i)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (negsuc n)) (Kn→ΩKn+1 0 -2))
  ∙∙ cong₂ _*_ (oddCharac (negsuc n) (help2 n isOdd)) (evenCharac (negsuc 1) refl)

map⁻ : Bool → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
map⁻ false = ∣ 0ₖ 1 , cong ∣_∣ loop ∣₂
map⁻ true = ∣ 0ₖ 1 , refl ∣₂

testIso : Iso ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ Bool
Iso.fun testIso = sRec isSetBool test2
Iso.inv testIso = map⁻
Iso.rightInv testIso false = refl
Iso.rightInv testIso true = refl
Iso.leftInv testIso =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        (uncurry (trElim
          (λ _ → isGroupoidΠ λ _ → isOfHLevelPlus {n = 1} 2 (setTruncIsSet _ _))
          (toPropElim (λ _ → isPropΠ (λ _ → setTruncIsSet _ _))
          (λ p → path p (even (ΩKn+1→Kn 0 p)) refl))))
  where
  path : (p : 0ₖ 1 ≡ 0ₖ 1) (b : Bool) → (even (ΩKn+1→Kn 0 p) ≡ b) → map⁻ (test2 (∣ base ∣ , p)) ≡ ∣ ∣ base ∣ , p ∣₂
  path p false q =
       (cong map⁻ q)
    ∙∙ sym (oddCharac (ΩKn+1→Kn 0 p) q)
    ∙∙ cong ∣_∣₂ λ i → 0ₖ 1 , Iso.rightInv (Iso-Kn-ΩKn+1 0) p i
  path p true q =
       cong map⁻ q
    ∙∙ sym (evenCharac (ΩKn+1→Kn 0 p) q)
    ∙∙ cong ∣_∣₂ λ i → 0ₖ 1 , Iso.rightInv (Iso-Kn-ΩKn+1 0) p i
