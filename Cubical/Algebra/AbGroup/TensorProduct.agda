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

open import Cubical.HITs.PropositionalTruncation
  renaming (map to pMap ; rec to pRec ; elim to pElim ; elim2 to pElim2)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

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

   ⊗squash : isSet _⨂₁_

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
  ⊗elimProp {C = C} p f g (⊗squash x y q r i j) =
    isOfHLevel→isOfHLevelDep 2 {B = C} (λ x → isProp→isSet (p x))
      _ _ (λ j → ⊗elimProp p f g (q j)) (λ j → ⊗elimProp p f g (r j))
          (⊗squash x y q r) i j

  -- Group structure
  0⊗ : AGr ⨂₁ BGr
  0⊗ = 0A ⊗ 0B

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
  -⊗ (⊗squash x y p q i j) =
    ⊗squash _ _ (λ j → -⊗ (p j)) (λ j → -⊗ (q j)) i j

  ⊗rUnit : (x : A⊗B) → x +⊗ 0⊗ ≡ x
  ⊗rUnit x = ⊗comm x 0⊗ ∙ ⊗lUnit x

  -------------------------------------------------------------------------------
  -- Useful induction principle, which lets us view elements of A ⨂ B as lists
  -- over (A × B). Used for the right cancellation law
  unlist : List (A × B) → AGr ⨂₁ BGr
  unlist [] = 0A ⊗ 0B
  unlist (x ∷ x₁) = (fst x ⊗ snd x) +⊗ unlist x₁

  unlist++ : (x y : List (A × B))
            → unlist (x ++ y) ≡ (unlist x +⊗ unlist y)
  unlist++ [] y = sym (⊗lUnit (unlist y))
  unlist++ (x ∷ x₁) y =
       (λ i → (fst x ⊗ snd x) +⊗ (unlist++ x₁ y i))
     ∙ ⊗assoc (fst x ⊗ snd x) (unlist x₁) (unlist y)

  ∃List : (x : AGr ⨂₁ BGr) → ∃[ l ∈ List (A × B) ] (unlist l ≡ x)
  ∃List =
    ⊗elimProp (λ _ → squash₁)
      (λ a b → ∣ [ a , b ] , ⊗rUnit (a ⊗ b) ∣₁)
      λ x y → rec2 squash₁ λ {(l1 , p) (l2 , q)
                          → ∣ (l1 ++ l2) , unlist++ l1 l2 ∙ cong₂ _+⊗_ p q ∣₁}

  ⊗elimPropUnlist : ∀ {ℓ} {C : AGr ⨂₁ BGr → Type ℓ}
           → ((x : _) → isProp (C x))
           → ((x : _) → C (unlist x))
           → (x : _) → C x
  ⊗elimPropUnlist {C = C} p f =
    ⊗elimProp p (λ x y → subst C (⊗rUnit (x ⊗ y)) (f [ x , y ]))
      λ x y → pRec (isPropΠ2 λ _ _ → p _)
                    (pRec (isPropΠ3 λ _ _ _ → p _)
                      (λ {(l1 , p) (l2 , q) ind1 ind2
                        → subst C (unlist++ l2 l1 ∙ cong₂ _+⊗_ q p) (f (l2 ++ l1))})
                      (∃List y))
                    (∃List x)
  -----------------------------------------------------------------------------------

  lCancelPrim : (x : B) → (0A ⊗ x) ≡ 0⊗
  lCancelPrim x =
    sym (⊗rUnit _)
    ∙∙ cong ((0A ⊗ x) +⊗_) (sym cancelLem)
    ∙∙ ⊗assoc (0A ⊗ x) (0A ⊗ x) (0A ⊗ (-B x))
    ∙∙ cong (_+⊗ (0A ⊗ (-B x))) inner
    ∙∙ cancelLem
    where
    cancelLem : (0A ⊗ x) +⊗ (0A ⊗ (-B x)) ≡ 0⊗
    cancelLem = sym (linr 0A x (-B x)) ∙ (λ i → 0A ⊗ invr strB x i)

    inner : (0A ⊗ x) +⊗ (0A ⊗ x) ≡ 0A ⊗ x
    inner = sym (linl 0A 0A x) ∙ (λ i → rid strA 0A i ⊗ x)

  rCancelPrim : (x : A) → (x ⊗ 0B) ≡ 0⊗
  rCancelPrim x =
    sym (⊗rUnit _)
    ∙∙ cong ((x ⊗ 0B) +⊗_) (sym cancelLem)
    ∙∙ ⊗assoc (x ⊗ 0B) (x ⊗ 0B) ((-A x) ⊗ 0B)
    ∙∙ cong (_+⊗ ((-A x) ⊗ 0B)) inner
    ∙∙ cancelLem
    where
    cancelLem : (x ⊗ 0B) +⊗ ((-A x) ⊗ 0B) ≡ 0⊗
    cancelLem = sym (linl x (-A x) 0B) ∙ (λ i → invr strA x i ⊗ 0B)

    inner : (x ⊗ 0B) +⊗ (x ⊗ 0B) ≡ x ⊗ 0B
    inner = sym (linr x 0B 0B) ∙ (λ i → x ⊗ rid strB 0B i)

  flip : (x : A) (b : B) → x ⊗ (-B b) ≡ ((-A x) ⊗ b)
  flip x b =
    sym (⊗rUnit _)
    ∙ cong ((x ⊗ (-B b)) +⊗_) (sym cancelLemA)
    ∙ ⊗assoc (x ⊗ (-B b)) (x ⊗ b) ((-A x) ⊗ b)
    ∙ cong (_+⊗ ((-A x) ⊗ b)) cancelLemB
    ∙ ⊗lUnit _
    where
    cancelLemA : (x ⊗ b) +⊗ ((-A x) ⊗ b) ≡ 0⊗
    cancelLemA = sym (linl x (-A x) b) ∙ (λ i → invr strA x i ⊗ b) ∙ lCancelPrim b

    cancelLemB : (x ⊗ (-B b)) +⊗ (x ⊗ b) ≡ 0⊗
    cancelLemB = sym (linr x (-B b) b) ∙ (λ i → x ⊗ invl strB b i) ∙ rCancelPrim x

  ⊗rCancel : (x : AGr ⨂₁ BGr) → (x +⊗ -⊗ x) ≡ 0⊗
  ⊗rCancel =
    ⊗elimPropUnlist (λ _ → ⊗squash _ _) h
    where
    h : (x : List (A × B)) → (unlist x +⊗ -⊗ (unlist x)) ≡ 0⊗
    h [] = sym (linl 0A (-A 0A) (0B))
         ∙ cong (λ x →  _⊗_ {AGr = AGr} {BGr = BGr} x 0B) (invr strA 0A)
    h (x ∷ x₁) =
      move4 (fst x ⊗ snd x) (unlist x₁) ((-A fst x) ⊗ snd x) (-⊗ (unlist x₁))
            _+⊗_ ⊗assoc ⊗comm
      ∙∙ cong₂ _+⊗_ (sym (linl (fst x) (-A (fst x)) (snd x))
                   ∙∙ (λ i → invr strA (fst x) i ⊗ (snd x))
                   ∙∙ lCancelPrim (snd x))
                    (h x₁)
      ∙∙ ⊗rUnit 0⊗

  ⊗lCancel : (x : AGr ⨂₁ BGr) → (-⊗ x +⊗ x) ≡ 0⊗
  ⊗lCancel x = ⊗comm _ _ ∙ ⊗rCancel x

module _ where
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

-------------- Elimination principle into AbGroups --------------
module _ {ℓ ℓ' : Level} {A : AbGroup ℓ}  {B : AbGroup ℓ'} where
  private
    open AbGroupStr renaming (_+_ to _+G_ ; -_ to -G)
    _+A_ = _+G_ (snd A)
    _+B_ = _+G_ (snd B)

    0A = 0g (snd A)
    0B = 0g (snd B)

  ⨂→AbGroup-elim : ∀ {ℓ} (C : AbGroup ℓ)
         → (f : (fst A × fst B) → fst C)
         → (f (0A , 0B) ≡ 0g (snd C))
         → (linL : (x y : fst A) (b : fst B)
                 → f (x +A y , b) ≡ _+G_ (snd C) (f (x , b)) (f (y , b)))
         → (linR : (a : fst A) (x y : fst B)
                 → f (a , x +B y) ≡ _+G_ (snd C) (f (a , x)) (f (a , y)))
         → A ⨂₁ B → fst C
  ⨂→AbGroup-elim C f p linL linR (a ⊗ b) = f (a , b)
  ⨂→AbGroup-elim C f p linL linR (x +⊗ x₁) =
    _+G_ (snd C) (⨂→AbGroup-elim C f p linL linR x)
                 (⨂→AbGroup-elim C f p linL linR x₁)
  ⨂→AbGroup-elim C f p linL linR (⊗comm x x₁ i) =
    comm (snd C) (⨂→AbGroup-elim C f p linL linR x)
                 (⨂→AbGroup-elim C f p linL linR x₁) i
  ⨂→AbGroup-elim C f p linL linR (⊗assoc x x₁ x₂ i) =
    assoc (snd C) (⨂→AbGroup-elim C f p linL linR x)
                  (⨂→AbGroup-elim C f p linL linR x₁)
                  (⨂→AbGroup-elim C f p linL linR x₂) i
  ⨂→AbGroup-elim C f p linL linR (⊗lUnit x i) =
    (cong (λ y → (snd C +G y) (⨂→AbGroup-elim C f p linL linR x)) p
                     ∙ (lid (snd C) (⨂→AbGroup-elim C f p linL linR x))) i
  ⨂→AbGroup-elim C f p linL linR (linl x y z i) = linL x y z i
  ⨂→AbGroup-elim C f p linL linR (linr x y z i) = linR x y z i
  ⨂→AbGroup-elim C f p linL linR (⊗squash x x₁ x₂ y i i₁) =
    is-set (snd C) _ _
           (λ i → ⨂→AbGroup-elim C f p linL linR (x₂ i))
           (λ i → ⨂→AbGroup-elim C f p linL linR (y i)) i i₁

  ⨂→AbGroup-elim-hom : ∀ {ℓ} (C : AbGroup ℓ)
        → (f : (fst A × fst B) → fst C) (linL : _) (linR : _) (p : _)
        → AbGroupHom (A ⨂ B) C
  fst (⨂→AbGroup-elim-hom C f linL linR p) = ⨂→AbGroup-elim C f p linL linR
  snd (⨂→AbGroup-elim-hom C f linL linR p) =
    makeIsGroupHom
      (λ x y → refl)

private
  _* = AbGroup→Group


----------- Definition of universal property ------------
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

isTensorProductOf_and_ : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')→ Type _
isTensorProductOf_and_ {ℓ} {ℓ'} A B T =
  Σ[ f ∈ GroupHom (A *) ((HomGroup (B *) T) *) ]
    ((C : AbGroup (ℓ-max ℓ ℓ'))
      → isEquiv {A = GroupHom (T *) (C *)}
                 {B = GroupHom (A *) ((HomGroup (B *) C) *)}
          (tensorFun (A *) (B *) T C f))

------ _⨂_ satisfies the universal property --------
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
  snd isTensorProduct⨂ C = isoToIsEquiv mainIso
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

-------------------- Commutativity ------------------------
commFun : ∀ {ℓ ℓ'} {A : AbGroup ℓ}  {B : AbGroup ℓ'} → A ⨂₁ B → B ⨂₁ A
commFun (a ⊗ b) = b ⊗ a
commFun (x +⊗ x₁) = commFun x +⊗ commFun x₁
commFun (⊗comm x x₁ i) = ⊗comm (commFun x) (commFun x₁) i
commFun (⊗assoc x x₁ x₂ i) = ⊗assoc (commFun x) (commFun x₁) (commFun x₂) i
commFun (⊗lUnit x i) = ⊗lUnit (commFun x) i
commFun (linl x y z i) = linr z x y i
commFun (linr x y z i) = linl y z x i
commFun (⊗squash x x₁ x₂ y i i₁) =
  ⊗squash (commFun x) (commFun x₁)
          (λ i → commFun (x₂ i)) (λ i → commFun (y i)) i i₁

commFun²≡id : ∀ {ℓ ℓ'} {A : AbGroup ℓ}  {B : AbGroup ℓ'} (x : A ⨂₁ B)
          → commFun (commFun x) ≡ x
commFun²≡id =
  ⊗elimProp (λ _ → ⊗squash _ _)
    (λ _ _ → refl)
    λ _ _ p q → cong₂ _+⊗_ p q

⨂-commIso : ∀ {ℓ ℓ'} {A : AbGroup ℓ} {B : AbGroup ℓ'}
          → GroupIso ((A ⨂ B) *) ((B ⨂ A) *)
Iso.fun (fst ⨂-commIso) = commFun
Iso.inv (fst ⨂-commIso) = commFun
Iso.rightInv (fst ⨂-commIso) = commFun²≡id
Iso.leftInv (fst ⨂-commIso) = commFun²≡id
snd ⨂-commIso = makeIsGroupHom λ x y → refl

⨂-comm : ∀ {ℓ ℓ'} {A : AbGroup ℓ} {B : AbGroup ℓ'} → AbGroupEquiv (A ⨂ B) (B ⨂ A)
fst ⨂-comm = isoToEquiv (fst (⨂-commIso))
snd ⨂-comm = snd ⨂-commIso

open AbGroupStr

-------------------- Associativity ------------------------
module _ {ℓ ℓ' ℓ'' : Level} {A : AbGroup ℓ} {B : AbGroup ℓ'} {C : AbGroup ℓ''} where
  private
    f : (c : fst C) → AbGroupHom (A ⨂ B) (A ⨂ (B ⨂ C))
    f c = ⨂→AbGroup-elim-hom (A ⨂ (B ⨂ C)) ((λ ab → fst ab ⊗ (snd ab ⊗ c)))
                  (λ x y b → linl x y (b ⊗ c))
                  (λ x y b → (λ i → x ⊗ (linl y b c i)) ∙ linr x (y ⊗ c) (b ⊗ c))
                  (λ i → 0g (snd A) ⊗ (lCancelPrim c i))

  assocHom : AbGroupHom ((A ⨂ B) ⨂ C) (A ⨂ (B ⨂ C))
  assocHom =
    ⨂→AbGroup-elim-hom _ (λ x → f (snd x) .fst (fst x))
      (λ x y b → IsGroupHom.pres· (snd (f b)) x y)
      (⊗elimProp (λ _ → isPropΠ2 λ _ _ → ⊗squash _ _)
                 (λ a b x y → (λ i → a ⊗ (linr b x y i))
                            ∙∙ linr a (b ⊗ x) (b ⊗ y)
                            ∙∙ refl)
                 λ a b ind1 ind2 x y → cong₂ _+⊗_ (ind1 x y) (ind2 x y)
                       ∙∙ move4 (f x .fst a) (f y .fst a) (f x .fst b) (f y .fst b)
                                _+⊗_ ⊗assoc ⊗comm
                       ∙∙ cong₂ _+⊗_ (sym (IsGroupHom.pres· (snd (f x)) a b))
                                     (IsGroupHom.pres· (snd (f y)) a b))
      refl

module _ {ℓ ℓ' ℓ'' : Level} {A : AbGroup ℓ} {B : AbGroup ℓ'} {C : AbGroup ℓ''} where
  private
    f' : (a : fst A) → AbGroupHom (B ⨂ C) ((A ⨂ B) ⨂ C)
    f' a =
      ⨂→AbGroup-elim-hom ((A ⨂ B) ⨂ C)
         (λ bc → (a ⊗ fst bc) ⊗ snd bc)
         (λ x y b → (λ i → (linr a x y i) ⊗ b) ∙ linl (a ⊗ x) (a ⊗ y) b)
         (λ x y b → linr (a ⊗ x) y b)
         λ i → rCancelPrim a i ⊗ (0g (snd C))

  assocHom⁻ : AbGroupHom (A ⨂ (B ⨂ C)) ((A ⨂ B) ⨂ C)
  assocHom⁻ =
    ⨂→AbGroup-elim-hom _ (λ abc → f' (fst abc) .fst (snd abc))
       (λ x y → ⊗elimProp (λ _ → ⊗squash _ _)
                   (λ b c → (λ i → linl x y b i ⊗ c) ∙ linl (x ⊗ b) (y ⊗ b) c)
                   λ a b ind1 ind2 → cong₂ _+⊗_ ind1 ind2
                                  ∙∙ move4 _ _ _ _ _+⊗_ ⊗assoc ⊗comm
                                  ∙∙ cong₂ _+⊗_ (IsGroupHom.pres· (snd (f' x)) a b)
                                                (IsGroupHom.pres· (snd (f' y)) a b))
       (λ a → IsGroupHom.pres· (snd (f' a)))
       refl

  ⨂assocIso : Iso (A ⨂₁ (B ⨂ C)) ((A ⨂ B) ⨂₁ C)
  Iso.fun ⨂assocIso = fst assocHom⁻
  Iso.inv ⨂assocIso = fst assocHom
  Iso.rightInv ⨂assocIso =
    ⊗elimProp (λ _ → ⊗squash _ _)
      (⊗elimProp (λ _ → isPropΠ (λ _ → ⊗squash _ _))
        (λ a b c → refl)
        λ a b ind1 ind2 c → cong₂ _+⊗_ (ind1 c) (ind2 c) ∙ sym (linl a b c))
      λ x y p q → cong (fst assocHom⁻) (IsGroupHom.pres· (snd assocHom) x y)
               ∙∙ IsGroupHom.pres· (snd assocHom⁻) (fst assocHom x) (fst assocHom y)
               ∙∙ cong₂ _+⊗_ p q
  Iso.leftInv ⨂assocIso =
    ⊗elimProp (λ _ → ⊗squash _ _)
      (λ a → ⊗elimProp (λ _ → ⊗squash _ _)
              (λ b c → refl)
              λ x y ind1 ind2 →
                   cong (fst assocHom ∘ fst assocHom⁻) (linr a x y)
                ∙∙ cong (fst assocHom) (IsGroupHom.pres· (snd assocHom⁻) (a ⊗ x) (a ⊗ y))
                ∙∙ IsGroupHom.pres· (snd assocHom) (fst assocHom⁻ (a ⊗ x)) (fst assocHom⁻ (a ⊗ y))
                ∙∙ cong₂ _+⊗_ ind1 ind2
                ∙∙ sym (linr a x y))
      λ x y p q → cong (fst assocHom) (IsGroupHom.pres· (snd assocHom⁻) x y)
               ∙∙ IsGroupHom.pres· (snd assocHom) (fst assocHom⁻ x) (fst assocHom⁻ y)
               ∙∙ cong₂ _+⊗_ p q

  ⨂assoc : AbGroupEquiv (A ⨂ (B ⨂ C)) ((A ⨂ B) ⨂ C)
  fst ⨂assoc = isoToEquiv ⨂assocIso
  snd ⨂assoc = snd assocHom⁻
