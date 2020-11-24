{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.KleinBottle where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
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

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Int renaming (+-comm to +-commℤ ; _+_ to _+ℤ_)

open import Cubical.HITs.KleinBottle
open import Cubical.Data.Empty
open import Cubical.Foundations.Path

movePathLem : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) → isComm∙ (A , x) → (p ∙∙ q ∙∙ p ≡ q) ≡ ((p ∙ p) ∙ q ≡ q)
movePathLem p q comm = cong (_≡ q) (doubleCompPath-elim' p q p ∙∙ cong (p ∙_) (comm q p) ∙∙ assoc _ _ _)

movePathLem2 : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) → (((p ∙ p) ∙ q) ∙ sym q ≡ q ∙ sym q) ≡ (p ∙ p ≡ refl)
movePathLem2 p q = cong₂ _≡_ (sym (assoc (p ∙ p) q (sym q)) ∙∙ cong ((p ∙ p) ∙_) (rCancel q) ∙∙ sym (rUnit (p ∙ p)))
                             (rCancel q)

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Transport
helpIso : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) → isComm∙ (A , x) → Iso (p ∙∙ q ∙∙ p ≡ q) (p ∙ p ≡ refl)
helpIso {x = x} p q comm =
  compIso (pathToIso (movePathLem p q comm))
    (compIso (helper (p ∙ p))
             (pathToIso (movePathLem2 p q)))
  where
  helper : (p : x ≡ x) → Iso (p ∙ q ≡ q) ((p ∙ q) ∙ sym q ≡ q ∙ sym q)
  helper p = congIso (equivToIso (_ , compPathr-isEquiv (sym q)))

Iso-Klein₂ : Iso ∥ Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ∥₂ ∥ (Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ∙ p ≡ refl) ∥₂
Iso.fun Iso-Klein₂ = 
  sRec setTruncIsSet
    (uncurry (trElim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 2} 2 setTruncIsSet)
                     (sphereElim _ (λ _ → isSetΠ λ _ → setTruncIsSet)
                                 λ y → ∣ fst y , snd (snd y) ∣₂)))
Iso.inv Iso-Klein₂ =
  sMap λ p → (0ₖ 2) , ((fst p) , (refl , (snd p)))
Iso.rightInv Iso-Klein₂ =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ p → refl
Iso.leftInv Iso-Klein₂ =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        (uncurry (trElim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 1} 3 (setTruncIsSet _ _))
                 (sphereToPropElim _
                   (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
                   λ {(p , (q , sq)) → trRec (setTruncIsSet _ _)
                                              (λ qid → cong ∣_∣₂ (ΣPathP (refl , (ΣPathP (refl , (ΣPathP (sym qid  , refl)))))))
                                              (Iso.fun (PathIdTruncIso _)
                                                       (isContr→isProp (isConnectedPathKn 1 (0ₖ 2) (0ₖ 2)) ∣ q ∣ ∣ refl ∣))})))


Test : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (x₀ : A) (y₀ : B) (_+A_ : A → A → A) (_+B_ : B → B → B) 
  → (e : Iso A B)
  → Iso.fun e x₀ ≡ y₀
  → ((x y : B) → Iso.inv e (x +B y) ≡ (Iso.inv e x +A Iso.inv e y))
  → (Σ A λ a → a +A a ≡ x₀) ≡ (Σ B λ a → a +B a ≡ y₀)
Test x₀ y₀ _+A_ _+B_ is x₀→y₀ hom⁻ = 
    (λ i → Σ (isoToPath is i) λ p → transp (λ j →  (isoToPath is (i ∧ j)) → (isoToPath is (i ∧ j)) → (isoToPath is (i ∧ j))) (~ i) _+A_ p p ≡ transp (λ j →  (isoToPath is (i ∧ j))) (~ i) x₀)
  ∙ (λ i → Σ _ λ p → transportRefl (Iso.fun is (Iso.inv is (transportRefl p i) +A Iso.inv is (transportRefl p i))) i ≡ transportRefl (Iso.fun is x₀) i)
  ∙ (λ i → Σ _ λ p → Iso.fun is (hom⁻ p p (~ i)) ≡ x₀→y₀ i)
  ∙ λ i → Σ _ λ p → Iso.rightInv is (p +B p) i ≡ y₀

Iso-Klein₃ : Iso ∥ (Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ∙ p ≡ refl) ∥₂ ∥ (Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1) ∥₂
Iso-Klein₃ = setTruncIso (pathToIso (Test refl (0ₖ 1) _∙_ _+ₖ_ (invIso (Iso-Kn-ΩKn+1 1)) refl (Kn→ΩKn+1-hom 1)))


even : Int → Bool
even (pos zero) = true
even (pos (suc zero)) = false
even (pos (suc (suc n))) = even (pos n)
even (negsuc zero) = false
even (negsuc (suc n)) = even (pos n)

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


open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

discreteBool : Discrete Bool
discreteBool false false = yes refl
discreteBool false true = no λ p → true≢false (sym p)
discreteBool true false = no true≢false
discreteBool true true = yes refl

IsoPresDiscrete : ∀ {ℓ ℓ'}{A : Type ℓ} {B : Type ℓ'} → Iso A B
               → Discrete A → Discrete B
IsoPresDiscrete e dA x y with dA (Iso.inv e x) (Iso.inv e y)
... | yes p = subst Dec (λ i → Iso.rightInv e x i ≡ Iso.rightInv e y i)
                        (yes (cong (Iso.fun e) p))
... | no p = subst Dec (λ i → Iso.rightInv e x i ≡ Iso.rightInv e y i)
                   (no λ q → p (sym (Iso.leftInv e (Iso.inv e x))
                     ∙∙ cong (Iso.inv e) q
                     ∙∙ Iso.leftInv e (Iso.inv e y)))

BoolGroup : Group₀
open GroupStr renaming (assoc to assocG)
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open IsGroup  hiding (rid ; lid)
open IsMonoid hiding (rid ; lid)
open IsSemigroup renaming (assoc to assoc')
fst BoolGroup = Bool
0g (snd BoolGroup) = true
(snd BoolGroup GroupStr.+ false) false = true
(snd BoolGroup GroupStr.+ false) true = false
(snd BoolGroup GroupStr.+ true) y = y
(- snd BoolGroup) false = false
(- snd BoolGroup) true = true

is-set (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) = isSetBool
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true true = refl
identity (IsGroup.isMonoid (isGroup (snd BoolGroup))) false = refl , refl
identity (IsGroup.isMonoid (isGroup (snd BoolGroup))) true = refl , refl
inverse (isGroup (snd BoolGroup)) false = refl , refl
inverse (isGroup (snd BoolGroup)) true = refl , refl

data twoPoint {ℓ : Level} (A : Type ℓ) : Type ℓ where
  point1 : twoPoint A
  point2 : twoPoint A


open import Cubical.Data.Sum
module _ {ℓ : Level} {A : Group {ℓ}} (e : Iso (fst A) Bool) where
  discreteA : Discrete (typ A)
  discreteA = IsoPresDiscrete (invIso e) discreteBool

  _+A_ = GroupStr._+_ (snd A)
  -A_ = GroupStr.-_ (snd A)

  notIso : Iso Bool Bool
  Iso.fun notIso = not
  Iso.inv notIso = not
  Iso.rightInv notIso = notnot
  Iso.leftInv notIso = notnot

  ¬true→false : (x : Bool) → ¬ x ≡ true → x ≡ false
  ¬true→false false _ = refl
  ¬true→false true p = ⊥-rec (p refl)

  ¬false→true : (x : Bool) → ¬ x ≡ false → x ≡ true
  ¬false→true false p = ⊥-rec (p refl)
  ¬false→true true _ = refl

  IsoABool : Iso Bool (typ A)
  IsoABool with discreteBool (Iso.fun e (0g (snd A))) true
  ... | yes p = invIso e
  ... | no p = compIso notIso (invIso e)

  test : Iso.fun IsoABool true ≡ 0g (snd A)
  test with discreteBool (Iso.fun e (0g (snd A))) true
  ... | yes p = sym (cong (Iso.inv e) p) ∙ Iso.leftInv e _
  ... | no p = sym (cong (Iso.inv e) (¬true→false (Iso.fun e (0g (snd A))) p)) ∙ Iso.leftInv e (0g (snd A))

  decA : (x : typ A) → (x ≡ 0g (snd A)) ⊎ (x ≡ Iso.fun IsoABool false)
  decA x with discreteBool (Iso.inv IsoABool x) false | discreteA x (0g (snd A))
  ... | yes p | yes q = inl q
  ... | yes p | no q  = inr (sym (Iso.rightInv IsoABool x) ∙ cong (Iso.fun (IsoABool)) p)
  ... | no p  | no q  = inr (⊥-rec (q (sym (Iso.rightInv IsoABool x) ∙∙ cong (Iso.fun IsoABool) (¬false→true _ p) ∙∙ test)))
  ... | no p  | yes q = inl q

  ≅Bool : GroupIso BoolGroup A
  ≅Bool = Iso+Hom→GrIso IsoABool homHelp
    where
    homHelp : isGroupHom BoolGroup A (Iso.fun IsoABool)
    homHelp false false with discreteA (Iso.fun IsoABool false) (0g (snd A)) | (decA ((Iso.fun IsoABool false) +A Iso.fun IsoABool false))
    ... | yes p | _     = test ∙∙ sym (rid (snd A) (0g (snd A))) ∙∙ cong₂ (_+A_) (sym p) (sym p)
    ... | no p  | inl x = test ∙ sym x
    ... | no p  | inr x = test ∙∙ sym (helper _ x) ∙∙ sym x
      where
      helper : (x : typ A) → x +A x ≡ x → x ≡ (0g (snd A))
      helper x p = sym (GroupStr.rid (snd A) x)
                ∙∙ cong (x +A_) (sym (inverse (snd A) x .fst))
                ∙∙ assocG (snd A) x x (-A x) ∙∙ cong (_+A (-A x)) p
                ∙∙ inverse (snd A) x .fst
    homHelp false true = sym (rid (snd A) _) ∙ cong (Iso.fun IsoABool false +A_) (sym test)
    homHelp true y = sym (lid (snd A) _) ∙ cong (_+A (Iso.fun IsoABool y)) (sym test)


Iso-Klein₁ : Iso (KleinBottle → coHomK 2) (Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q)
Iso.fun Iso-Klein₁ f =
  (f point) ,
  ((cong f line1) ,
   (cong f line2 ,
   fst (Square≃doubleComp
         (cong f line2) (cong f line2)
         (sym (cong f line1)) (cong f line1))
         (λ i j → f (square i j))))
Iso.inv Iso-Klein₁ (x , p , q , sq) point = x
Iso.inv Iso-Klein₁ (x , p , q , sq) (line1 i) = p i
Iso.inv Iso-Klein₁ (x , p , q , sq) (line2 i) = q i
Iso.inv Iso-Klein₁ (x , p , q , sq) (square i j) = invEq (Square≃doubleComp q q (sym p) p) sq i j
Iso.rightInv Iso-Klein₁ (x , (p , (q , sq))) =
  ΣPathP (refl , (ΣPathP (refl , (ΣPathP (refl , retEq (Square≃doubleComp q q (sym p) p) sq)))))
Iso.leftInv Iso-Klein₁ f _ point = f point
Iso.leftInv Iso-Klein₁ f _ (line1 i) = f (line1 i)
Iso.leftInv Iso-Klein₁ f _ (line2 i) = f (line2 i)
Iso.leftInv Iso-Klein₁ f z (square i j) = 
  secEq (Square≃doubleComp
          (cong f line2) (cong f line2)
          (sym (cong f line1)) (cong f line1))
          (λ i j → f (square i j)) z i j


Klein₂≅Bool : GroupIso BoolGroup (coHomGr 2 KleinBottle)
Klein₂≅Bool = ≅Bool theIso
  where
  theIso : Iso _ _
  theIso =
    compIso (setTruncIso
               (compIso Iso-Klein₁
                          (Σ-cong-iso-snd
                            λ x → Σ-cong-iso-snd
                              λ p → Σ-cong-iso-snd
                                λ q → (helpIso p q (isCommΩK-based 2 x)))))
      (compIso Iso-Klein₂
        (compIso
          Iso-Klein₃
          testIso))
