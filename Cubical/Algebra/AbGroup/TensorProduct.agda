{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.AbGroup.TensorProduct where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function hiding (flip)
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary

open import Cubical.Data.Sigma

open import Cubical.Data.List
open import Cubical.Data.Nat as ℕ
open import Cubical.Foundations.HLevels
open import Cubical.Data.Int
open import Cubical.Data.Sum hiding (map)

open import Cubical.HITs.PropositionalTruncation renaming (map to pMap ; rec to pRec ; elim to pElim ; elim2 to pElim2)

open import Cubical.Algebra.Group hiding (ℤ)

-- open import Cubical.HITs.SetQuotients

private
  variable
    ℓ ℓ' : Level


module _ (AGr : AbGroup ℓ) (BGr : AbGroup ℓ') where
  private
    open AbGroupStr renaming (_+_ to _+G_ ; -_ to -G_)

    strA = snd AGr
    strB = snd BGr

    A = fst AGr
    B = fst BGr

    0A = 0g strA
    0B = 0g strB

    _+A_ = _+G_ strA
    _+B_ = _+G_ strB

    -A_ = -G_ strA
    -B_ = -G_ strB

  data _⨂₁_ : Type (ℓ-max ℓ ℓ') where
   _⊗_ : (a : A) → (b : B) → _⨂₁_
   _+⊗_ : (w : _⨂₁_) → (u : _⨂₁_) → _⨂₁_

   ⊗comm : (x y : _) → x +⊗ y ≡ y +⊗ x
   ⊗assoc : (x y z : _) → x +⊗ (y +⊗ z) ≡ (x +⊗ y) +⊗ z
   ⊗lUnit : (x : _) → (0A ⊗ 0B) +⊗ x ≡ x

   linl : (x y : A) (z : B) → (x +A y) ⊗ z ≡ ((x ⊗ z) +⊗ (y ⊗ z))
   linr : (x : A) (y z : B) → x ⊗ (y +B z) ≡ ((x ⊗ y) +⊗ (x ⊗ z))

   flip : (x : A) (b : B) → x ⊗ (-B b) ≡ ((-A x) ⊗ b) -- needed ?

   ⊗squash : isSet _⨂₁_


move4 : ∀ {ℓ} {A : Type ℓ} (x y z w : A) (_+_ : A → A → A)
       → ((x y z : A) → x + (y + z) ≡ (x + y) + z)
       → ((x y : A) → x + y ≡ y + x)
      → (x + y) + (z + w) ≡ ((x + z) + (y + w)) 
move4 x y z w _+_ assoc comm =
     sym (assoc x y (z + w))
  ∙∙ cong (x +_) (assoc y z w ∙∙ cong (_+ w) (comm y z) ∙∙ sym (assoc z y w))
  ∙∙ assoc x z (y + w)

module _ {AGr : AbGroup ℓ} {BGr : AbGroup ℓ'} where
  private
    open AbGroupStr renaming (_+_ to _+G_ ; -_ to -G_)

    strA = snd AGr
    strB = snd BGr

    A = fst AGr
    B = fst BGr

    0A = 0g strA
    0B = 0g strB

    _+A_ = _+G_ strA
    _+B_ = _+G_ strB

    -A_ = -G_ strA
    -B_ = -G_ strB

  A⊗B = AGr ⨂₁ BGr

  0⊗ : AGr ⨂₁ BGr
  0⊗ = 0A ⊗ 0B

  ⊗elimProp : ∀ {ℓ} {C : AGr ⨂₁ BGr → Type ℓ}
           → ((x : _) → isProp (C x))
           → (f : (x : A) (b : B) → C (x ⊗ b))
           → (g : ((x y : _) → C x → C y → C (x +⊗ y)))
           → (x : _) → C x
  ⊗elimProp p f g (a ⊗ b) = f a b
  ⊗elimProp p f g (x +⊗ y) = g x y (⊗elimProp p f g x) (⊗elimProp p f g y)
  ⊗elimProp  {C = C} p f g (⊗comm x y j) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g x y (⊗elimProp p f g x) (⊗elimProp p f g y))
      (g y x (⊗elimProp p f g y) (⊗elimProp p f g x)) (⊗comm x y) j
  ⊗elimProp {C = C} p f g (⊗assoc x y z j) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g x (y +⊗ z) (⊗elimProp p f g x)
         (g y z (⊗elimProp p f g y) (⊗elimProp p f g z)))
         (g (x +⊗ y) z (g x y (⊗elimProp p f g x)
           (⊗elimProp p f g y)) (⊗elimProp p f g z)) (⊗assoc x y z) j
  ⊗elimProp {C = C} p f g (⊗lUnit x i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g (0A ⊗ 0B) x (f 0A 0B) (⊗elimProp p f g x))
      (⊗elimProp p f g x)
      (⊗lUnit x) i
  ⊗elimProp {C = C} p f g (linl x y z i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (f (x +A y) z) (g (x ⊗ z) (y ⊗ z) (f x z) (f y z)) (linl x y z) i
  ⊗elimProp {C = C} p f g (linr x y z i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (f x (y +B z)) (g (x ⊗ y) (x ⊗ z) (f x y) (f x z)) (linr x y z) i
  ⊗elimProp {C = C} p f g (flip x b i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (f x (-B b)) (f (-A x) b) (flip x b) i
  ⊗elimProp {C = C} p f g (⊗squash x y q r i j) =
    isOfHLevel→isOfHLevelDep 2 {B = C} (λ x → isProp→isSet (p x))
      _ _ (λ j → ⊗elimProp p f g (q j)) (λ j → ⊗elimProp p f g (r j)) (⊗squash x y q r) i j

  -⊗ : AGr ⨂₁ BGr → AGr ⨂₁ BGr
  -⊗ (a ⊗ b) = (-A a) ⊗ b
  -⊗ (x +⊗ x₁) = -⊗ x +⊗ -⊗ x₁
  -⊗ (⊗comm x y i) = ⊗comm (-⊗ x) (-⊗ y) i
  -⊗ (⊗assoc x y z i) = ⊗assoc (-⊗ x) (-⊗ y) (-⊗ z) i
  -⊗ (⊗lUnit x i) =
    ((λ i → (GroupTheory.inv1g (AbGroup→Group AGr) i ⊗ 0B) +⊗ -⊗ x)
       ∙ ⊗lUnit (-⊗ x)) i
  -⊗ (linl x y z i) =
     ((λ i → (GroupTheory.invDistr (AbGroup→Group AGr) x y
             ∙ comm strA (-A y) (-A x)) i ⊗ z)
    ∙ linl (-A x) (-A y) z) i
  -⊗ (linr x y z i) = linr (-A x) y z i
  -⊗ (flip x b i) = flip (-A x) b i
  -⊗ (⊗squash x y p q i j) =
    ⊗squash _ _ (λ j → -⊗ (p j)) (λ j → -⊗ (q j)) i j

  ⊗rUnit : (x : A⊗B) → x +⊗ 0⊗ ≡ x
  ⊗rUnit x = ⊗comm x 0⊗ ∙ ⊗lUnit x

  listify : List (A × B) → AGr ⨂₁ BGr
  listify [] = 0A ⊗ 0B
  listify (x ∷ x₁) = (fst x ⊗ snd x) +⊗ listify x₁

  listify++ : (x y : List (A × B)) → listify (x ++ y) ≡ (listify x +⊗ listify y)
  listify++ [] y = sym (⊗lUnit (listify y))
  listify++ (x ∷ x₁) y =
       (λ i → (fst x ⊗ snd x) +⊗ (listify++ x₁ y i))
     ∙ ⊗assoc (fst x ⊗ snd x) (listify x₁) (listify y)

  slick : (x : AGr ⨂₁ BGr) → ∃[ l ∈ List (A × B) ] listify l ≡ x
  slick =
    ⊗elimProp (λ _ → squash)
      (λ a b → ∣ [ a , b ] , ⊗rUnit (a ⊗ b) ∣)
      λ x y → rec2 squash λ {(l1 , p) (l2 , q) → ∣ (l1 ++ l2) , listify++ l1 l2 ∙ cong₂ _+⊗_ p q ∣}


  ⊗elimPropCool : ∀ {ℓ} {C : AGr ⨂₁ BGr → Type ℓ}
           → ((x : _) → isProp (C x))
           → ((x : _) → C (listify x))
           → (x : _) → C x
  ⊗elimPropCool {C = C} p f =
    ⊗elimProp p (λ x y → subst C (⊗rUnit (x ⊗ y)) (f [ x , y ]))
      λ x y → pRec (isPropΠ2 λ _ _ → p _)
                    (pRec (isPropΠ3 λ _ _ _ → p _)
                      (λ {(l1 , p) (l2 , q) ind1 ind2 → subst C (listify++ l2 l1 ∙ cong₂ _+⊗_ q p) (f (l2 ++ l1))})
                      (slick y))
                    (slick x)

  rCancelPrim : (x : B) → (0A ⊗ x) ≡ 0⊗
  rCancelPrim x =
       (λ i → rid strA 0A (~ i) ⊗ x)
    ∙∙ linl 0A 0A x
    ∙∙ cong ((0A ⊗ x) +⊗_) (cong (_⊗ x) (sym (GroupTheory.inv1g (AbGroup→Group AGr)))
                          ∙ sym (flip 0A x))
    ∙∙ sym (linr 0A x (-B x))
    ∙∙ (λ i → 0A ⊗ (invr strB x i))

  ⊗rCancel : (x : AGr ⨂₁ BGr) → (x +⊗ -⊗ x) ≡ 0⊗
  ⊗rCancel =
    ⊗elimPropCool (λ _ → ⊗squash _ _) h
    where
    h : (x : List (A × B)) → (listify x +⊗ -⊗ (listify x)) ≡ 0⊗
    h [] = sym (linl 0A (-A 0A) (0B))
         ∙ cong (λ x →  _⊗_ {AGr = AGr} {BGr = BGr} x 0B) (invr strA 0A)
    h (x ∷ x₁) =
      move4 (fst x ⊗ snd x) (listify x₁) ((-A fst x) ⊗ snd x) (-⊗ (listify x₁))
            _+⊗_ ⊗assoc ⊗comm
      ∙∙ cong₂ _+⊗_ (sym (linl (fst x) (-A (fst x)) (snd x))
                   ∙∙ (λ i → invr strA (fst x) i ⊗ (snd x))
                   ∙∙ rCancelPrim (snd x))
                    (h x₁)
      ∙∙ ⊗rUnit 0⊗

  ⊗lCancel : (x : AGr ⨂₁ BGr) → (-⊗ x +⊗ x) ≡ 0⊗
  ⊗lCancel x = ⊗comm _ _ ∙ ⊗rCancel x

module _ where
  open import Cubical.Algebra.Monoid
  open import Cubical.Algebra.Semigroup
  open AbGroupStr
  open IsAbGroup
  open IsGroup
  open IsMonoid
  open IsSemigroup
  _⨂_ : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')
  fst (A ⨂ B) = A ⨂₁ B
  0g (snd (A ⨂ B)) = 0⊗
  AbGroupStr._+_ (snd (A ⨂ B)) = _+⊗_
  AbGroupStr.- snd (A ⨂ B) = -⊗
  is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd (A ⨂ B)))))) = ⊗squash
  assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd (A ⨂ B)))))) = ⊗assoc
  fst (identity (isMonoid (isGroup (isAbGroup (snd (A ⨂ B))))) x) = ⊗rUnit x
  snd (identity (isMonoid (isGroup (isAbGroup (snd (A ⨂ B))))) x) = ⊗lUnit x
  fst (inverse (isGroup (isAbGroup (snd (A ⨂ B)))) x) = ⊗rCancel x
  snd (inverse (isGroup (isAbGroup (snd (A ⨂ B)))) x) = ⊗lCancel x
  comm (isAbGroup (snd (A ⨂ B))) = ⊗comm

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

_* : AbGroup ℓ → Group ℓ
_* = AbGroup→Group

module _ (AGr : Group ℓ) (BGr : AbGroup ℓ') where
  private
    strA = snd AGr
    strB = snd BGr

    A = fst AGr
    B = fst BGr
    open IsGroupHom

    open AbGroupStr strB renaming (_+_ to _+B_ ; -_ to -B_ ; 0g to 0B ; rid to ridB ; lid to lidB ; assoc to assocB ; comm to commB ; invr to invrB ; invl to invlB)
    open GroupStr strA renaming (_·_ to _∙A_ ; inv to -A_ ; 1g to 1A ; rid to ridA)

  trivGroupHom : GroupHom AGr (BGr *)
  fst trivGroupHom x = 0B
  snd trivGroupHom = makeIsGroupHom λ _ _ → sym (ridB 0B)

  compHom : GroupHom AGr (BGr *) → GroupHom AGr (BGr *) → GroupHom AGr (BGr *)
  fst (compHom f g) x = fst f x +B fst g x
  snd (compHom f g) =
      makeIsGroupHom λ x y
      → cong₂ _+B_ (pres· (snd f) x y) (pres· (snd g) x y)
      ∙ move4 (fst f x) (fst f y) (fst g x) (fst g y)
              _+B_ assocB commB

  invHom : GroupHom AGr (BGr *) → GroupHom AGr (BGr *)
  fst (invHom (f , p)) x = -B f x
  snd (invHom (f , p)) =
    makeIsGroupHom
      λ x y → cong -B_ (pres· p x y)
            ∙∙ GroupTheory.invDistr (BGr *) (f x) (f y)
            ∙∙ commB _ _

  open import Cubical.Algebra.Monoid
  open import Cubical.Algebra.Semigroup
  open AbGroupStr
  open IsAbGroup
  open IsGroup
  open IsMonoid
  open IsSemigroup

  HomGroup : AbGroup (ℓ-max ℓ ℓ')
  fst HomGroup = GroupHom AGr (BGr *)
  0g (snd HomGroup) = trivGroupHom
  AbGroupStr._+_ (snd HomGroup) = compHom
  AbGroupStr.- snd HomGroup = invHom
  is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd HomGroup))))) =
    isSetGroupHom
  assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd HomGroup))))) (f , p) (g , q) (h , r) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ x → assocB _ _ _)
  fst (identity (isMonoid (isGroup (isAbGroup (snd HomGroup)))) (f , p)) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ y → ridB _)
  snd (identity (isMonoid (isGroup (isAbGroup (snd HomGroup)))) (f , p)) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x → lidB _)
  fst (inverse (isGroup (isAbGroup (snd HomGroup))) (f , p)) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x → invrB (f x))
  snd (inverse (isGroup (isAbGroup (snd HomGroup))) (f , p)) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x → invlB (f x))
  comm (isAbGroup (snd HomGroup)) (f , p) (g , q) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ x → commB _ _)

tensorFun : (A : Group ℓ) (B : Group ℓ') (T C : AbGroup (ℓ-max ℓ ℓ'))
    (f : GroupHom A (HomGroup B T *))
  → GroupHom (T *) (C *)
  → GroupHom A (HomGroup B C *)
fst (fst (tensorFun A B T C (f , p) (g , q)) a) b = g (fst (f a) b)
snd (fst (tensorFun A B T C (f , p) (g , q)) a) =
    makeIsGroupHom λ x y
      → cong g (IsGroupHom.pres· (snd (f a)) x y)
       ∙ IsGroupHom.pres· q _ _
snd (tensorFun A B T C (f , p) (g , q)) =
     makeIsGroupHom λ x y
      → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
           (funExt λ b
             → cong g (funExt⁻ (cong fst (IsGroupHom.pres· p x y)) b)
              ∙ IsGroupHom.pres· q _ _) 
{-
  makeIsGroupHom λ x y
      → cong g (IsGroupHom.pres· (snd (f a)) x y)
       ∙ IsGroupHom.pres· q _ _
snd (tensorFun A B T C (f , p) (g , q)) =
    makeIsGroupHom λ x y
      → cong g (IsGroupHom.pres· (snd (f a)) x y)
       ∙ IsGroupHom.pres· q _ _
snd (h (f , p) C (g , q)) =
    makeIsGroupHom λ x y
      → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
           (funExt λ b
             → cong g (funExt⁻ (cong fst (IsGroupHom.pres· p x y)) b)
              ∙ IsGroupHom.pres· q _ _)  -}

isTensorProductOf_and_ : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')→ Type _
isTensorProductOf_and_ {ℓ} {ℓ'} A B T =
  Σ[ f ∈ GroupHom (A *) ((HomGroup (B *) T) *) ]
    ((C : AbGroup (ℓ-max ℓ ℓ'))
      → isEquiv {A = GroupHom (T *) (C *)}
                 {B = GroupHom (A *) ((HomGroup (B *) C) *)}
          (tensorFun (A *) (B *) T C f))

module UP (AGr : AbGroup ℓ) (BGr : AbGroup ℓ') where
  private
    open AbGroupStr renaming (_+_ to _+G_ ; -_ to -G_)

    strA = snd AGr
    strB = snd BGr

    A = fst AGr
    B = fst BGr

    0A = 0g strA
    0B = 0g strB

    _+A_ = _+G_ strA
    _+B_ = _+G_ strB

    -A_ = -G_ strA
    -B_ = -G_ strB

  mainF : GroupHom (AGr *) (HomGroup (BGr *) (AGr ⨂ BGr) *)
  fst (fst mainF a) b = a ⊗ b
  snd (fst mainF a) =
    makeIsGroupHom (linr a)
  snd mainF =
    makeIsGroupHom λ x y → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (linl x y))

  isTensorProduct⨂ : (isTensorProductOf AGr and BGr) (AGr ⨂ BGr)
  fst isTensorProduct⨂ = mainF
  snd isTensorProduct⨂ C =
    isoToIsEquiv mainIso
    where
    invF : GroupHom (AGr *) (HomGroup (BGr *) C *) → GroupHom ((AGr ⨂ BGr) *) (C *)
    fst (invF (f , p)) = F
      where
      lem : f (0g (snd AGr)) .fst (0g (snd BGr)) ≡ 0g (snd C)
      lem = funExt⁻ (cong fst (IsGroupHom.pres1 p)) (0g (snd BGr))
      F : ((AGr ⨂ BGr) *) .fst → (C *) .fst
      F (a ⊗ b) = f a .fst b
      F (x +⊗ x₁) = _+G_ (snd C) (F x) (F x₁)
      F (⊗comm x x₁ i) = comm (snd C) (F x) (F x₁) i
      F (⊗assoc x y z i) = assoc (snd C) (F x) (F y) (F z) i
      F (⊗lUnit x i) = (cong (λ y → _+G_ (snd C) y (F x)) lem ∙ lid (snd C) (F x)) i
      F (linl x y z i) = fst (IsGroupHom.pres· p x y i) z
      F (linr x y z i) = IsGroupHom.pres· (f x .snd) y z i
      F (flip x b i) = (IsGroupHom.presinv (f x .snd) b
                      ∙ sym (funExt⁻ (cong fst (IsGroupHom.presinv p x)) b)) i
      F (⊗squash x x₁ x₂ y i i₁) =
        is-set (snd C) (F x) (F x₁)
          (λ i → F (x₂ i)) (λ i → F (y i)) i i₁
    snd (invF (f , p)) =
      makeIsGroupHom λ x y → refl

    mainIso : Iso (GroupHom ((AGr ⨂ BGr) *) (C *))
                  (GroupHom (AGr *) (HomGroup (BGr *) C *))
    Iso.fun mainIso = _
    Iso.inv mainIso = invF
    Iso.rightInv mainIso (f , p) =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
             (funExt λ a → Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl)
    Iso.leftInv mainIso (f , p) =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
             (funExt (⊗elimProp (λ _ → is-set (snd C) _ _)
               (λ _ _ → refl)
               λ x y ind1 ind2 → cong₂ (_+G_ (snd C)) ind1 ind2 ∙ sym (IsGroupHom.pres· p x y)))
  
--   CODE : (z x : FMSet (A × B)) (y : _⨂₁_) → TypeOfHLevel (ℓ-max ℓ ℓ') 1
--   JFun : (z x : {!!}) → {!!} → {!!}
--   JFun = {!!}
--   CODE z x (inc x₁) = Path _⨂₁_ (inc (z ++ x)) (inc (z ++ x₁)) , ⊗squash _ _
--   CODE z x (unit i) = {!!}
--   CODE z x (lin-l x₁ y b i) = {!!}
--     where
--     h : (z : _) → Path (TypeOfHLevel (ℓ-max ℓ ℓ') 1)
--              (Path _⨂₁_ (inc (z ++ x)) (inc (z ++ [ (x₁ +A y) , b ])) ,
--                ⊗squash (inc (z ++ x)) (inc (z ++ [ (x₁ +A y) , b ])))
--              (Path _⨂₁_ (inc (z ++ x))
--          (inc (z ++ ((x₁ , b) ∷ [ y , b ])))
--          , ⊗squash (inc (z ++ x)) (inc (z ++ ((x₁ , b) ∷ [ y , b ]))))
--     h = ElimProp.f {!λ xs → ?!}
--           (Σ≡Prop {!!} {!!})
--           λ m {xs} p → Σ≡Prop {!!} (cong (Path _⨂₁_ (inc ((m ∷ xs) ++ x))) {!p!}) -- λ m xss → Σ≡Prop {!!} (cong (Path _⨂₁_ (inc ((m ∷ xs) ++ x))) {!!}) -- Σ≡Prop {!!} {!!}
--   CODE z x (lin-r x₁ y z₁ i) = {!!}
--   CODE z x (⊗squash y y₁ x₁ y₂ i i₁) = {!!}
  

--   inclem : (x y z : FMSet (A × B)) → Path _⨂₁_ (inc x) (inc y) → Path _⨂₁_ (inc (z ++ x)) (inc (z ++ y))
--   inclem x y z = {!!}

--   _+⊗_ : _⨂₁_ → _⨂₁_ → _⨂₁_
--   inc x +⊗ inc x₁ = inc (x ++ x₁)
--   inc x +⊗ unit i = {!!}
--   inc x +⊗ lin-l y z b i = {!!}
--     where
--     lem : (x : _) → inc (x ++ [ (y +A z) , b ]) ≡ inc (x ++ ((y , b) ∷ [ z , b ]))
--     lem =
--       ElimProp.f {!!}
--         (lin-l y z b)
--         λ x {xs} p → inclem _ _ [ x ] p -- inclem _ _ {!x ∷ xs!} p 
--   inc x +⊗ lin-r x₁ y z i = {!!}
--   inc x +⊗ ⊗squash y y₁ x₁ y₂ i i₁ = {!!}
--   unit i +⊗ y = {!!}
--   lin-l x y₁ b i +⊗ y = {!!}
--   lin-r x y₁ z i +⊗ y = {!!}
--   ⊗squash x x₁ x₂ y₁ i i₁ +⊗ y = {!!}

-- -- Word : (A : Type ℓ) → Type ℓ
-- -- Word A = List (A ⊎ A)

-- -- module _ {A : Type ℓ} where
-- --   pm = A ⊎ A

-- --   flip : pm → pm
-- --   flip (inl x) = inr x
-- --   flip (inr x) = inl x

-- --   flip-flip : (x : pm) → flip (flip x) ≡ x
-- --   flip-flip (inl x) = refl
-- --   flip-flip (inr x) = refl

-- --   wordFlip : Word A → Word A
-- --   wordFlip = map flip

-- --   wordInverse : Word A → Word A
-- --   wordInverse = rev ∘ wordFlip

-- --   map++ : {B : Type ℓ} (v w : Word A)
-- --        → (f : _ → B) → map f (v ++ w)
-- --        ≡ map f v ++ map f w
-- --   map++ [] w f = refl
-- --   map++ (x ∷ v) w f = cong (f x ∷_) (map++ v w f)

-- --   wordInverseInverse : (x : Word A) → wordInverse (wordInverse x) ≡ x
-- --   wordInverseInverse [] = refl
-- --   wordInverseInverse (x ∷ x₁) =
-- --        cong rev (map++ (rev (map flip x₁)) (flip x ∷ []) flip)
-- --     ∙∙ rev-++ (map flip (rev (map flip x₁))) (flip (flip x) ∷ [])
-- --     ∙∙ cong₂ _∷_ (flip-flip x) (wordInverseInverse x₁)

-- --   wordExp : A → ℤ → Word A
-- --   wordExp a (pos zero) = []
-- --   wordExp a (pos (suc n)) = inl a ∷ wordExp a (pos n)
-- --   wordExp a (negsuc zero) = [ inr a ]
-- --   wordExp a (negsuc (suc n)) = inr a ∷ wordExp a (negsuc n)

-- -- module _ {A : Type ℓ} (G : Group ℓ') (f : A → fst G) where
-- --   private
-- --     str = snd G
-- --   open GroupStr str renaming (_·_ to _·G_)

-- --   PlusMinus-extendᴳ : A ⊎ A → fst G
-- --   PlusMinus-extendᴳ (inl x) = f x
-- --   PlusMinus-extendᴳ (inr x) = inv (f x)

-- --   PlusMinus-extendᴳ-flip : ∀ x → PlusMinus-extendᴳ (flip x)
-- --                                 ≡ inv (PlusMinus-extendᴳ x)
-- --   PlusMinus-extendᴳ-flip (inl x) = refl
-- --   PlusMinus-extendᴳ-flip (inr x) = sym (GroupTheory.invInv G (f x))

-- --   Word-extendᴳ : Word A → fst G
-- --   Word-extendᴳ = foldr _·G_ 1g ∘ map PlusMinus-extendᴳ

-- --   Word-extendᴳ-++ : ∀ x y → Word-extendᴳ (x ++ y)
-- --                           ≡ (Word-extendᴳ x ·G Word-extendᴳ y)
-- --   Word-extendᴳ-++ [] y = sym (lid (Word-extendᴳ y))
-- --   Word-extendᴳ-++ (x ∷ x₁) y =
-- --        cong (PlusMinus-extendᴳ x ·G_) (Word-extendᴳ-++ x₁ y)
-- --     ∙∙ assoc _ _ _
-- --     ∙∙ cong (_·G Word-extendᴳ y) (help x x₁)
-- --     where
-- --     help : (x : _) (y : _)
-- --       → PlusMinus-extendᴳ x ·G Word-extendᴳ y ≡ Word-extendᴳ (x ∷ y)
-- --     help x [] = refl
-- --     help x (z ∷ y) = refl


-- -- module _ {A : Type ℓ} (G : AbGroup ℓ') where
-- --   private
-- --     str = snd G
-- --     open AbGroupStr str renaming (_+_ to _+G_ ; -_ to -G_)
-- --   G' = AbGroup→Group G

-- --   PlusMinus-extendᴳ-comp :  (f g : A → fst G) (x : _)
-- --     → PlusMinus-extendᴳ G' (λ a → f a +G g a) x
-- --     ≡ (PlusMinus-extendᴳ G' f x +G PlusMinus-extendᴳ G' g x)
-- --   PlusMinus-extendᴳ-comp f g (inl x) = refl
-- --   PlusMinus-extendᴳ-comp f g (inr x) =
-- --     GroupTheory.invDistr G' (f x) (g x) ∙ comm _ _

-- --   Word-extendᴳ-comp :  (f g : A → fst G) (x : _) → Word-extendᴳ G' (λ a → f a +G g a) x
-- --                               ≡ (Word-extendᴳ G' f x +G Word-extendᴳ G' g x)
-- --   Word-extendᴳ-comp f g [] = sym (lid 0g)
-- --   Word-extendᴳ-comp f g (x ∷ x₁) =
-- --     cong₂ _+G_ (PlusMinus-extendᴳ-comp f g x)
-- --                (Word-extendᴳ-comp f g x₁)
-- --        ∙∙ sym (assoc pm-fx pm-gx _)
-- --        ∙∙ cong (pm-fx +G_) (assoc _ _ _
-- --                         ∙∙ cong (_+G we-gx) (comm _ _)
-- --                         ∙∙ sym (assoc _ _ _))
-- --        ∙∙ assoc pm-fx we-fx _
-- --        ∙∙ cong₂ _+G_ (main x x₁ f) (main x x₁ g)
-- --      where
-- --      main : (x : _) (y : _) (f : _)
-- --          → (PlusMinus-extendᴳ G' f x +G Word-extendᴳ G' f y)
-- --          ≡ Word-extendᴳ G' f (x ∷ y)
-- --      main x [] f = refl
-- --      main x (x₁ ∷ y) f = refl

-- --      pm-fx = PlusMinus-extendᴳ G' f x
-- --      pm-gx = PlusMinus-extendᴳ G' g x
-- --      we-fx = Word-extendᴳ G' f x₁
-- --      we-gx = Word-extendᴳ G' g x₁

-- -- module GeneratedGroup (A : Type ℓ) (R : Rel (Word A) (Word A) ℓ') where
-- --   data QuotWordRel : Word A → Word A → Type (ℓ-max ℓ ℓ') where
-- --     qwr-refl : ∀ {x} → QuotWordRel x x
-- --     qwr-trans : ∀ {x y z} → QuotWordRel x y → QuotWordRel y z → QuotWordRel x z
-- --     qwr-sym : ∀ {x y} → QuotWordRel x y → QuotWordRel y x
-- --     qwr-cong : ∀ {x y z w} → QuotWordRel x y → QuotWordRel z w → QuotWordRel (x ++ z) (y ++ w)
-- --     qwr-flip-r : ∀ x → QuotWordRel (x ∷ flip x ∷ []) []
-- --     qwr-rel : ∀ {x y} → R x y → QuotWordRel x y

-- --   qwr-cong-refl : {!!}
-- --   qwr-cong-refl = {!!}

-- --   qwr-cong-l : {!!}
-- --   qwr-cong-l = {!!}





-- -- {-
-- -- module _ {ℓ : Level} where
-- --   ℤmult : {A : Type ℓ} (_+_ : A → A → A) (-A_ : A → A) (0A : A) (n : ℤ) → A → A
-- --   ℤmult _+_ -A_ 0A (pos zero) a = 0A
-- --   ℤmult _+_ -A_ 0A (pos (suc n)) a = a + ℤmult _+_ -A_ 0A (pos n) a
-- --   ℤmult _+_ -A_ 0A (negsuc zero) a = -A a
-- --   ℤmult _+_ -A_ 0A (negsuc (suc n)) a = (-A a) + ℤmult _+_ -A_ 0A (negsuc n) a

-- --   data commList (A : Type ℓ) : Type ℓ where
-- --     [] : commList A
-- --     _∷_ : A → commList A → commList A
-- --     isComm : (a b : A) (w : commList A) → a ∷ b ∷ w ≡ b ∷ a ∷ w
-- --     squashCommList : isSet (commList A)

-- --   _++'_ : {A : Type ℓ} → commList A → commList A → commList A
-- --   [] ++' y = y
-- --   (x ∷ x₁) ++' y = x ∷ (x₁ ++' y)
-- --   isComm a b w i ++' y = isComm a b (w ++' y) i
-- --   squashCommList x y p q i j ++' z =
-- --     squashCommList _ _ (λ j → p j ++' z) (λ j → q j ++' z) i j

-- --   propElimCommList : ∀ {ℓ'} {A : Type ℓ} {B : (x : commList A) → Type ℓ'}
-- --                   → ((x : _) → isProp (B x))
-- --                   → B []
-- --                   → ((x : A) (y : commList A) → B y → B (x ∷ y))
-- --                   → (x : _) → B x
-- --   propElimCommList {B = B} prop c l [] = c
-- --   propElimCommList {B = B} prop c l (x ∷ x₁) = l x x₁ (propElimCommList {B = B} prop c l x₁)
-- --   propElimCommList {B = B} prop c l (isComm a b x i) =
-- --     isOfHLevel→isOfHLevelDep 1 prop
-- --       (l a (b ∷ x) (l b x (propElimCommList prop c l x))) (l b (a ∷ x) (l a x (propElimCommList prop c l x)))
-- --       (isComm a b x) i
-- --   propElimCommList {B = B} prop c l (squashCommList x y p q i j) =
-- --     isOfHLevel→isOfHLevelDep 2 {B = B} (λ _ → isProp→isSet (prop _))
-- --       _ _ (λ j → propElimCommList prop c l (p j))
-- --           (λ j → propElimCommList prop c l (q j))
-- --           (squashCommList x y p q) i j

-- --   propElimCommList' :
-- --     ∀ {ℓ'} {A : Type ℓ} {B : (x : commList A) → Type ℓ'}
-- --                   → ((x : _) → isProp (B x))
-- --                   → B []
-- --                   → ((x : A) → B (x ∷ []))
-- --                   → ((x : A) (y : commList A) → B (x ∷ []) → B y → B (x ∷ y))
-- --                   → (x : _) → B x
-- --   propElimCommList' {B = B} prop b ind1 ind2 =
-- --     propElimCommList prop b h
-- --     where
-- --     h : (x : _) (y : commList _) → B y → B (x ∷ y)
-- --     h x [] _ = ind1 x
-- --     h x (x₁ ∷ y) l = ind2 x (x₁ ∷ y) (h x [] b) l
-- --     h x (isComm a b y i) = K i
-- --       where
-- --       K : PathP (λ i → B (isComm a b y i) → B (x ∷ isComm a b y i))
-- --                 (ind2 x (a ∷ (b ∷ y)) (ind1 x)) (ind2 x (b ∷ (a ∷ y)) (ind1 x))
-- --       K = isProp→PathP (λ _ → isPropΠ λ _ → prop _) _ _
-- --     h x (squashCommList w z p q i j) = K i j
-- --       where
-- --       K : SquareP (λ i j → B (squashCommList w z p q i j) → B (x ∷ squashCommList w z p q i j))
-- --                   (λ j → h x (p j))
-- --                   (λ j → h x (q j))
-- --                   (λ _ → h x w)
-- --                   λ _ → h x z
-- --       K = toPathP (isOfHLevelPathP' 1 (isProp→isSet (isPropΠ (λ _ → prop _))) _ _ _ _)

-- --   ++'-assoc : {A : Type ℓ} → (x y z : commList A) → x ++' (y ++' z) ≡ ((x ++' y) ++' z)
-- --   ++'-assoc =
-- --     propElimCommList'
-- --       (λ _ → isPropΠ2 λ _ _ → squashCommList _ _)
-- --       (λ _ _ → refl)
-- --       (λ x → propElimCommList' (λ _ → isPropΠ λ _ → squashCommList _ _)
-- --                  (λ _ → refl)
-- --                  (λ _ _ → refl)
-- --                  λ x y p q → propElimCommList' (λ _ → squashCommList _ _)
-- --                        refl
-- --                        (λ _ → refl)
-- --                        λ z w P Q → refl)
-- --       λ x y p q z w → cong (x ∷_) (q z w)

-- --   ++'-comm : {A : Type ℓ} → (x y : commList A) → x ++' y ≡ y ++' x
-- --   ++'-comm =
-- --     propElimCommList' (λ _ → isPropΠ λ _ → squashCommList _ _)
-- --       (propElimCommList' (λ _ → squashCommList _ _)
-- --         refl
-- --         (λ _ → refl)
-- --         (λ x y p q → cong (x ∷_) q))
-- --       (λ x → propElimCommList'
-- --                (λ _ → squashCommList _ _)
-- --                refl
-- --                (λ _ → isComm _ _ _)
-- --                λ y w p q → isComm x y w ∙ cong (y ∷_) q)
-- --       λ x y p q r → p (y ++' r)
-- --       ∙∙ cong (_++' (x ∷ [])) (q r)
-- --       ∙∙ (sym (++'-assoc r y (x ∷ [])) ∙ cong (r ++'_) (q (x ∷ [])))

-- --   len : {A : Type ℓ} → (x : commList A) → ℕ
-- --   len [] = 0
-- --   len (x ∷ x₁) = ℕ._+_ 1 (len x₁)
-- --   len (isComm a b x i) = suc (suc (len x))
-- --   len (squashCommList x x₁ x₂ y i i₁) =
-- --     isSetℕ (len x) (len x₁) (λ i → len (x₂ i)) (λ i → len (y i)) i i₁

-- -- module _ (A : AbGroup ℓ) (B : AbGroup ℓ') where
-- --   private
-- --     strA = snd A
-- --     strB = snd B
-- --   open AbGroupStr renaming (_+_ to +G ; -_ to -G)

-- --   _⨂₁-raw2_ : Type _
-- --   _⨂₁-raw2_ = List (fst A × fst B)

-- --   A' = fst A
-- --   B' = fst B

-- --   data _⨂₁_  : Type (ℓ-max ℓ ℓ') where
-- --     inc : commList (A' × B') → _⨂₁_
-- --     bilinl : (x y : A') (b : B') (w : _)
-- --       → inc ((+G strA x y , b) ∷ w) ≡ inc (((x , b) ∷ w) ++' ((y , b) ∷ w))
-- --     bilinr : (x : A') (y z : B') (w : _)
-- --       → inc ((x , +G strB y z) ∷ w) ≡ inc (((x , y) ∷ w) ++' ((x , z) ∷ w))
-- --     l : (x : A') (y : B') → inc ((x , y) ∷ []) ≡ inc []
-- --     ⊗squash : isSet _⨂₁_

-- --   +⊗ : _⨂₁_ → _⨂₁_ → _⨂₁_
-- --   +⊗ x y = {!!}
  
-- -- --   (inc x) (inc y) = inc (x ++' y)
-- -- --   +⊗ (inc x) (bilinl y z w r i) = commListInd x i
-- -- --     where
-- -- --     commListInd : (x : _) → inc (x ++' ((+G strA y z , w) ∷ r)) ≡ inc (x ++' ((y , w) ∷ (r ++' ((z , w) ∷ r))))
-- -- --     commListInd =
-- -- --       propElimCommList' (λ _ → ⊗squash _ _)
-- -- --         (bilinl y z w r)
-- -- --         (λ l → (λ i → inc ((l ∷ []) ++' (((+G strA y z , w) ∷ []) ++' r))) ∙∙ {!((+G strA y z , w₁) ∷ r)!} ∙∙ {!!})
-- -- --         λ x y p q → {!!}
-- -- --                   ∙∙ {!!}
-- -- --                   ∙∙ {!!}

-- -- --     lem : ((r ++' x) ++' ((z , w) ∷ (r ++' x))) ≡ ((r ++' ((z , w) ∷ r)) ++' x)
-- -- --     lem = {!!}
-- -- --        ∙∙ {!!}
-- -- --        ∙∙ ++'-assoc r ((z , w) ∷ r) x
-- -- --     help : inc (x ++' ((+G strA y z , w) ∷ r)) ≡ inc (x ++' ((y , w) ∷ (r ++' ((z , w) ∷ r))))
-- -- --     help = cong inc (++'-comm x _)
-- -- --         ∙∙ bilinl y z w (r ++' x)
-- -- --         ∙∙ (λ i → inc (((y , w) ∷ []) ++' ((r ++' x) ++' (((z , w) ∷ []) ++' (r ++' x)))))
-- -- --         ∙∙ cong inc (cong (((y , w) ∷ []) ++'_) {!!})
-- -- --         ∙∙ {!!}
-- -- --         ∙∙ {!!}
-- -- --         ∙∙ cong inc (cong (((y , w) ∷ []) ++'_) {!!})
-- -- --         ∙∙ (λ i → inc (((y , w) ∷ []) ++' ((r ++' (((z , w) ∷ []) ++' r)) ++' x)))
-- -- --         ∙∙ cong inc (sym (++'-comm x ((y , w) ∷ (r ++' ((z , w) ∷ r)))))
-- -- --   +⊗ (inc x) (bilinr y z w r i) = {!!}
-- -- --   +⊗ (inc x) (⊗squash y y₁ x₁ y₂ i i₁) = {!!}
-- -- --   +⊗ (bilinl x y z w i) r = {!!}
-- -- --   +⊗ (bilinr x y₁ z w i) y = {!!}
-- -- --   +⊗ (⊗squash x x₁ x₂ y₁ i i₁) y = {!!}
  
    

-- -- -- --   _⊗_ : A' → B' → _⨂₁-raw_ 
-- -- -- --   a ⊗ b = inc [ a , b ]

-- -- -- --   invList : _⨂₁-raw2_ → _⨂₁-raw2_
-- -- -- --   invList [] = []
-- -- -- --   invList (x ∷ x₁) =
-- -- -- --     ((-G strA (fst x)) , (snd x)) ∷ invList x₁



-- -- -- --   _ℤ∙_ : ℤ → _⨂₁-raw2_ → _⨂₁-raw2_
-- -- -- --   pos zero ℤ∙ y = []
-- -- -- --   pos (suc n) ℤ∙ y = y ++ (pos n ℤ∙ y)
-- -- -- --   negsuc zero ℤ∙ y = invList y
-- -- -- --   negsuc (suc n) ℤ∙ y = (invList y) ++ (negsuc n ℤ∙ y)

-- -- -- --   0⊗ₗ : (b : B') → 0g strA ⊗ b ≡ (0g strA ⊗ 0g strB)
-- -- -- --   0⊗ₗ b = {!!}
-- -- -- --     where
-- -- -- --     lem : (0g strA ⊗ b) ≡ inc ([ 0g strA , b ] ++ [ 0g strA , b ])
-- -- -- --     lem = cong (_⊗ b) (sym (rid strA (0g strA))) ∙ bilinl (0g strA) (0g strA) b

-- -- -- -- module _ {A : AbGroup ℓ} {B : AbGroup ℓ'} where
-- -- -- --   private
-- -- -- --     strA = snd A
-- -- -- --     strB = snd B
-- -- -- --     open AbGroupStr renaming (_+_ to +G ; -_ to -G)

-- -- -- --   rec⨂₁ : ∀ {ℓ'} {C : Type ℓ'}
-- -- -- --        → isSet C
-- -- -- --        → (c : C)
-- -- -- --        → (f : fst A → fst B → C → C)
-- -- -- --        → (((x y : fst A) (z : fst B) → f (+G strA x y) z c ≡ f x z (f y z c)))
-- -- -- --        → ((x : fst A) (y z : fst B) → f x (+G strB y z) c ≡ f x y (f x z c))
-- -- -- --        → (x : A ⨂₁-raw B) → C
-- -- -- --   rec⨂₁ {ℓ'} {C} set c f bil bir x = {!!}
-- -- -- --     -- set _ _ (λ j → rec⨂₁ set c f bil bir (p j)) (λ j → rec⨂₁ set c f bil bir (q j)) i j

-- -- -- --   elimProp : ∀ {ℓ'} {C : A ⨂₁-raw B → Type ℓ'}
-- -- -- --           → ((x : _) → isProp (C x))
-- -- -- --           → ((x : A ⨂₁-raw2 B) → C (inc x))
-- -- -- --           → (x : _) → C x
-- -- -- --   elimProp {C = C} prop ind (inc x) = ind x
-- -- -- --   elimProp {C = C} prop ind (bilinl x y z i) =
-- -- -- --     isOfHLevel→isOfHLevelDep 1 {B = C} prop
-- -- -- --       (ind (((+G strA x y) , z) ∷ []))
-- -- -- --       (ind ((x , z) ∷ (y , z) ∷ [])) (bilinl x y z) i
-- -- -- --   elimProp {C = C} prop ind (bilinr x y z i) =
-- -- -- --     isOfHLevel→isOfHLevelDep 1 {B = C} prop
-- -- -- --       (ind ((x , (+G strB y z)) ∷ []))
-- -- -- --       (ind ((x , y) ∷ (x , z) ∷ [])) (bilinr x y z) i
-- -- -- --   elimProp {C = C} prop ind (⊗squash x y p q i j) =
-- -- -- --     isOfHLevel→isOfHLevelDep 2 {B = C} (λ x → isProp→isSet (prop x)) _ _
-- -- -- --       (λ j → elimProp prop ind (p j))
-- -- -- --       (λ j → elimProp prop ind (q j))
-- -- -- --       (⊗squash x y p q) i j

-- -- -- --   AA = fst A
-- -- -- --   BB = fst B

-- -- -- --   bilinRGen : (x : fst A) (y z : fst B) (w : _) → Path (A ⨂₁-raw B) (inc ((x , +G strB y z) ∷ w)) (inc ((x , y) ∷ (x , z) ∷ w))
-- -- -- --   bilinRGen x y z [] = bilinr x y z
-- -- -- --   bilinRGen x y z (x₁ ∷ w) = {!bilinRGen x y z w!}

-- -- -- --   pre-comm : (x y : A ⨂₁-raw2 B) → Path (A ⨂₁-raw B) (inc (x ++ y)) (inc (y ++ x))
-- -- -- --   pre-comm [] [] = refl
-- -- -- --   pre-comm [] (x ∷ y) = {!!} -- cong inc (cong (x ∷_) {!pre-comm [] y!})
-- -- -- --   pre-comm (x ∷ x₁) y = {!!}

-- -- -- --   +⊗-mere : (x y : A ⨂₁-raw2 B) (z : _) → Path (A ⨂₁-raw B) (inc x) (inc y) → Path (A ⨂₁-raw B) (inc (z ∷ x)) (inc (z ∷ y))
-- -- -- --   +⊗-mere [] [] z p = refl
-- -- -- --   +⊗-mere [] (x ∷ y) z p = {!!}
-- -- -- --   +⊗-mere (x ∷ x₁) y z = {!!}

-- -- -- --   +⊗-merecomm' : (x y : fst A × fst B) → Path (A ⨂₁-raw B) (inc ([ x ] ++ [ y ])) (inc ([ y ] ++ [ x ])) 
-- -- -- --   +⊗-merecomm' (a , b) (c , d) =
-- -- -- --        cong inc (cong (_∷ (c , d) ∷ []) (cong (_, b) (sym (rid strA a)
-- -- -- --                                                    ∙∙ cong (+G strA a) (sym (invr strA c))
-- -- -- --                                                    ∙∙ {!!})))
-- -- -- --     ∙∙ {!!}
-- -- -- --     ∙∙ {!!}
  

-- -- -- --   _+⊗_ : A ⨂₁-raw B → A ⨂₁-raw B → A ⨂₁-raw B
-- -- -- --   inc x +⊗ inc x₁ = inc (x ++ x₁)
-- -- -- --   inc [] +⊗ bilinl x₁ y z i = bilinl x₁ y z i
-- -- -- --   inc ((a , b) ∷ []) +⊗ bilinl x₁ y z i = {!!} -- help i
-- -- -- --     where
-- -- -- --     help : inc
-- -- -- --          ((a , b) ∷
-- -- -- --           (+G strA x₁ y , z) ∷
-- -- -- --           []) ≡ inc ((a , b) ∷ (x₁ , z) ∷ (y , z) ∷ [])
-- -- -- --     help = {!sym (bilinl a _ b)!} ∙ {!!}
-- -- -- --   inc (x ∷ y ∷ z) +⊗ bilinl a b c i = {!!} -- inc (x ∷ x₃) +⊗ {!!}
-- -- -- --   inc x +⊗ bilinr x₁ y z i = {!!}
-- -- -- --   inc x +⊗ ⊗squash y y₁ x₁ y₂ i i₁ = {!!}
-- -- -- --   bilinl x y₁ z i +⊗ y = {!!}
-- -- -- --   bilinr x y₁ z i +⊗ y = {!!}
-- -- -- --   ⊗squash x x₁ x₂ y₁ i i₁ +⊗ y = {!!}

-- -- -- -- -- module _ (A : Type ℓ) (R : Rel (Word A) (Word A) ℓ') where
-- -- -- -- --   data AbGroupRel : Word A → Word A → Type (ℓ-max ℓ ℓ') where
-- -- -- -- --     agr-commutes : ∀ x y → AbGroupRel (x ++ y) (y ++ x)
-- -- -- -- --     agr-refl : ∀ {x y} → R x y → AbGroupRel x y

-- -- -- -- --   agr-rev : (w : Word A) → {!⨂₁!} -- QuotWordRel (rev w) w
-- -- -- -- --   agr-rev = {!!}

-- -- -- -- -- module _ (G H : AbGroup ℓ) where
-- -- -- -- --   TensorCarrier : Type _
-- -- -- -- --   TensorCarrier =
-- -- -- -- --     Σ[ T ∈ AbGroup ℓ ]
-- -- -- -- --      (Σ[ t ∈ (fst G → fst H → fst T) ]
-- -- -- -- --        ((C : AbGroup ℓ)
-- -- -- -- --          → isEquiv {A = fst T → fst C} {B = fst G → fst H → fst C}
-- -- -- -- --                     λ f a b → f (t a b)))
-- -- -- -- --   anIso : {!!}
-- -- -- -- --   anIso = {!!}

-- -- -- -- --   -- 0⊗ : TensorCarrier
-- -- -- -- --   -- fst 0⊗ = dirProdAb G H
-- -- -- -- --   -- fst (snd 0⊗) x y = x , y
-- -- -- -- --   -- snd (snd 0⊗) C = isoToIsEquiv {!0⊗!}
-- -- -}
