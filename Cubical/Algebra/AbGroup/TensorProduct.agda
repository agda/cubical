{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.AbGroup.TensorProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring


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
   _⊗_     : (a : A) → (b : B) → _⨂₁_
   _+⊗_    : (w : _⨂₁_) → (u : _⨂₁_) → _⨂₁_

   +⊗Comm   : (x y : _) → x +⊗ y ≡ y +⊗ x
   +⊗Assoc  : (x y z : _) → x +⊗ (y +⊗ z) ≡ (x +⊗ y) +⊗ z
   +⊗IdL    : (x : _) → (0A ⊗ 0B) +⊗ x ≡ x

   ⊗DistR+⊗ : (x : A) (y z : B) → x ⊗ (y +B z) ≡ ((x ⊗ y) +⊗ (x ⊗ z))
   ⊗DistL+⊗ : (x y : A) (z : B) → (x +A y) ⊗ z ≡ ((x ⊗ z) +⊗ (y ⊗ z))

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
  ⊗elimProp {C = C} p f g (+⊗Comm x y j) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g x y (⊗elimProp p f g x) (⊗elimProp p f g y))
      (g y x (⊗elimProp p f g y) (⊗elimProp p f g x)) (+⊗Comm x y) j
  ⊗elimProp {C = C} p f g (+⊗Assoc x y z j) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g x (y +⊗ z) (⊗elimProp p f g x)
         (g y z (⊗elimProp p f g y) (⊗elimProp p f g z)))
         (g (x +⊗ y) z (g x y (⊗elimProp p f g x)
           (⊗elimProp p f g y)) (⊗elimProp p f g z)) (+⊗Assoc x y z) j
  ⊗elimProp {C = C} p f g (+⊗IdL x i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (g (0A ⊗ 0B) x (f 0A 0B) (⊗elimProp p f g x))
      (⊗elimProp p f g x)
      (+⊗IdL x) i
  ⊗elimProp {C = C} p f g (⊗DistR+⊗ x y z i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (f x (y +B z)) (g (x ⊗ y) (x ⊗ z) (f x y) (f x z)) (⊗DistR+⊗ x y z) i
  ⊗elimProp {C = C} p f g (⊗DistL+⊗ x y z i) =
    isOfHLevel→isOfHLevelDep 1 {B = C} p
      (f (x +A y) z) (g (x ⊗ z) (y ⊗ z) (f x z) (f y z)) (⊗DistL+⊗ x y z) i
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
  -⊗ (+⊗Comm x y i) = +⊗Comm (-⊗ x) (-⊗ y) i
  -⊗ (+⊗Assoc x y z i) = +⊗Assoc (-⊗ x) (-⊗ y) (-⊗ z) i
  -⊗ (+⊗IdL x i) = ((λ i → (GroupTheory.inv1g (AbGroup→Group AGr) i ⊗ 0B) +⊗ -⊗ x)
                   ∙ +⊗IdL (-⊗ x)) i
  -⊗ (⊗DistR+⊗ x y z i) = ⊗DistR+⊗ (-A x) y z i
  -⊗ (⊗DistL+⊗ x y z i) = ((λ i → (GroupTheory.invDistr (AbGroup→Group AGr) x y
                           ∙ +Comm strA (-A y) (-A x)) i ⊗ z)
                           ∙ ⊗DistL+⊗ (-A x) (-A y) z) i
  -⊗ (⊗squash x y p q i j) = ⊗squash _ _ (λ j → -⊗ (p j)) (λ j → -⊗ (q j)) i j

  +⊗IdR : (x : A⊗B) → x +⊗ 0⊗ ≡ x
  +⊗IdR x = +⊗Comm x 0⊗ ∙ +⊗IdL x


  -------------------------------------------------------------------------------
  -- Useful induction principle, which lets us view elements of A ⨂ B as lists
  -- over (A × B). Used for the right cancellation law
  unlist : List (A × B) → AGr ⨂₁ BGr
  unlist [] = 0A ⊗ 0B
  unlist (x ∷ x₁) = (fst x ⊗ snd x) +⊗ unlist x₁

  unlist++ : (x y : List (A × B))  → unlist (x ++ y) ≡ (unlist x +⊗ unlist y)
  unlist++ [] y = sym (+⊗IdL (unlist y))
  unlist++ (x ∷ x₁) y = (λ i → (fst x ⊗ snd x) +⊗ (unlist++ x₁ y i))
                        ∙ +⊗Assoc (fst x ⊗ snd x) (unlist x₁) (unlist y)

  ∃List : (x : AGr ⨂₁ BGr) → ∃[ l ∈ List (A × B) ] (unlist l ≡ x)
  ∃List = ⊗elimProp (λ _ → squash₁)
          (λ a b → ∣ [ a , b ] , +⊗IdR (a ⊗ b) ∣₁)
          λ x y → rec2 squash₁ λ {(l1 , p) (l2 , q) →
                  ∣ (l1 ++ l2) , unlist++ l1 l2 ∙ cong₂ _+⊗_ p q ∣₁}

  ⊗elimPropUnlist : ∀ {ℓ} {C : AGr ⨂₁ BGr → Type ℓ}
           → ((x : _) → isProp (C x))
           → ((x : _) → C (unlist x))
           → (x : _) → C x
  ⊗elimPropUnlist {C = C} p f =
    ⊗elimProp p (λ x y → subst C (+⊗IdR (x ⊗ y)) (f [ x , y ]))
      λ x y → PT.rec (isPropΠ2 λ _ _ → p _)
                    (PT.rec (isPropΠ3 λ _ _ _ → p _)
                      (λ {(l1 , p) (l2 , q) ind1 ind2
                        → subst C (unlist++ l2 l1 ∙ cong₂ _+⊗_ q p) (f (l2 ++ l1))})
                      (∃List y))
                    (∃List x)
  -----------------------------------------------------------------------------------

  ⊗AnnihilL : (x : B) → (0A ⊗ x) ≡ 0⊗
  ⊗AnnihilL x = sym (+⊗IdR _)
                 ∙∙ cong ((0A ⊗ x) +⊗_) (sym cancelLem)
                 ∙∙ +⊗Assoc (0A ⊗ x) (0A ⊗ x) (0A ⊗ (-B x))
                 ∙∙ cong (_+⊗ (0A ⊗ (-B x))) inner
                 ∙∙ cancelLem
    where
    cancelLem : (0A ⊗ x) +⊗ (0A ⊗ (-B x)) ≡ 0⊗
    cancelLem = sym (⊗DistR+⊗ 0A x (-B x)) ∙ (λ i → 0A ⊗ +InvR strB x i)

    inner : (0A ⊗ x) +⊗ (0A ⊗ x) ≡ 0A ⊗ x
    inner = sym (⊗DistL+⊗ 0A 0A x) ∙ (λ i → +IdR strA 0A i ⊗ x)

  ⊗AnnihilR : (x : A) → (x ⊗ 0B) ≡ 0⊗
  ⊗AnnihilR x = sym (+⊗IdR _)
                ∙∙ cong ((x ⊗ 0B) +⊗_) (sym cancelLem)
                ∙∙ +⊗Assoc (x ⊗ 0B) (x ⊗ 0B) ((-A x) ⊗ 0B)
                ∙∙ cong (_+⊗ ((-A x) ⊗ 0B)) inner
                ∙∙ cancelLem
    where
    cancelLem : (x ⊗ 0B) +⊗ ((-A x) ⊗ 0B) ≡ 0⊗
    cancelLem = sym (⊗DistL+⊗ x (-A x) 0B) ∙ (λ i → +InvR strA x i ⊗ 0B)

    inner : (x ⊗ 0B) +⊗ (x ⊗ 0B) ≡ x ⊗ 0B
    inner = sym (⊗DistR+⊗ x 0B 0B) ∙ (λ i → x ⊗ +IdR strB 0B i)

  flip : (x : A) (b : B) → x ⊗ (-B b) ≡ ((-A x) ⊗ b)
  flip x b = sym (+⊗IdR _)
             ∙ cong ((x ⊗ (-B b)) +⊗_) (sym cancelLemA)
             ∙ +⊗Assoc (x ⊗ (-B b)) (x ⊗ b) ((-A x) ⊗ b)
             ∙ cong (_+⊗ ((-A x) ⊗ b)) cancelLemB
             ∙ +⊗IdL _
    where
    cancelLemA : (x ⊗ b) +⊗ ((-A x) ⊗ b) ≡ 0⊗
    cancelLemA = sym (⊗DistL+⊗ x (-A x) b) ∙ (λ i → +InvR strA x i ⊗ b) ∙ ⊗AnnihilL b

    cancelLemB : (x ⊗ (-B b)) +⊗ (x ⊗ b) ≡ 0⊗
    cancelLemB = sym (⊗DistR+⊗ x (-B b) b) ∙ (λ i → x ⊗ +InvL strB b i) ∙ ⊗AnnihilR x

  +⊗InvR : (x : AGr ⨂₁ BGr) → (x +⊗ -⊗ x) ≡ 0⊗
  +⊗InvR =
    ⊗elimPropUnlist (λ _ → ⊗squash _ _) h
    where
    h : (x : List (A × B)) → (unlist x +⊗ -⊗ (unlist x)) ≡ 0⊗
    h [] = sym (⊗DistL+⊗ 0A (-A 0A) (0B))
            ∙ cong (λ x →  _⊗_ {AGr = AGr} {BGr = BGr} x 0B) (+InvR strA 0A)
    h (x ∷ x₁) = move4 (fst x ⊗ snd x) (unlist x₁) ((-A fst x) ⊗ snd x) (-⊗ (unlist x₁))
                       _+⊗_ +⊗Assoc +⊗Comm
                 ∙∙ cong₂ _+⊗_ (sym (⊗DistL+⊗ (fst x) (-A (fst x)) (snd x))
                               ∙∙ (λ i → +InvR strA (fst x) i ⊗ (snd x))
                               ∙∙ ⊗AnnihilL (snd x))
                               (h x₁)
                 ∙∙ +⊗IdR 0⊗

  +⊗InvL : (x : AGr ⨂₁ BGr) → (-⊗ x +⊗ x) ≡ 0⊗
  +⊗InvL x = +⊗Comm _ _ ∙ +⊗InvR x

module _ where
  open AbGroupStr

  _⨂_ : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')
  fst (A ⨂ B) = A ⨂₁ B
  0g (snd (A ⨂ B)) = 0⊗
  AbGroupStr._+_ (snd (A ⨂ B)) = _+⊗_
  AbGroupStr.- snd (A ⨂ B) = -⊗
  isAbGroup (snd (A ⨂ B)) = makeIsAbGroup ⊗squash +⊗Assoc +⊗IdR +⊗InvR +⊗Comm


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
         → (linR : (a : fst A) (x y : fst B)
                 → f (a , x +B y) ≡ _+G_ (snd C) (f (a , x)) (f (a , y)))
         → (linL : (x y : fst A) (b : fst B)
                 → f (x +A y , b) ≡ _+G_ (snd C) (f (x , b)) (f (y , b)))
         → A ⨂₁ B → fst C
  ⨂→AbGroup-elim C f p linR linL (a ⊗ b) = f (a , b)
  ⨂→AbGroup-elim C f p linR linL (x +⊗ x₁) =
    _+G_ (snd C) (⨂→AbGroup-elim C f p linR linL x)
                 (⨂→AbGroup-elim C f p linR linL x₁)
  ⨂→AbGroup-elim C f p linR linL (+⊗Comm x x₁ i) =
    +Comm (snd C) (⨂→AbGroup-elim C f p linR linL x)
                  (⨂→AbGroup-elim C f p linR linL x₁) i
  ⨂→AbGroup-elim C f p linR linL (+⊗Assoc x x₁ x₂ i) =
    +Assoc (snd C) (⨂→AbGroup-elim C f p linR linL x)
                   (⨂→AbGroup-elim C f p linR linL x₁)
                   (⨂→AbGroup-elim C f p linR linL x₂) i
  ⨂→AbGroup-elim C f p linR linL (+⊗IdL x i) =
    (cong (λ y → (snd C +G y) (⨂→AbGroup-elim C f p linR linL x)) p
                     ∙ (+IdL (snd C) (⨂→AbGroup-elim C f p linR linL x))) i
  ⨂→AbGroup-elim C f p linR linL (⊗DistR+⊗ x y z i) = linR x y z i
  ⨂→AbGroup-elim C f p linR linL (⊗DistL+⊗ x y z i) = linL x y z i
  ⨂→AbGroup-elim C f p linR linL (⊗squash x x₁ x₂ y i i₁) =
    is-set (snd C) _ _
           (λ i → ⨂→AbGroup-elim C f p linR linL (x₂ i))
           (λ i → ⨂→AbGroup-elim C f p linR linL (y i)) i i₁

  ⨂→AbGroup-elim-hom : ∀ {ℓ} (C : AbGroup ℓ)
        → (f : (fst A × fst B) → fst C) (linR : _) (linL : _) (p : _)
        → AbGroupHom (A ⨂ B) C
  fst (⨂→AbGroup-elim-hom C f linR linL p) = ⨂→AbGroup-elim C f p linR linL
  snd (⨂→AbGroup-elim-hom C f linR linL p) = makeIsGroupHom (λ x y → refl)

private
  _* = AbGroup→Group


----------- Definition of universal property ------------
tensorFun : (A : Group ℓ) (B : Group ℓ') (T C : AbGroup (ℓ-max ℓ ℓ'))
            (f : GroupHom A (HomGroup B T *))
            → GroupHom (T *) (C *)
            → GroupHom A (HomGroup B C *)
fst (fst (tensorFun A B T C (f , p) (g , q)) a) b = g (fst (f a) b)
snd (fst (tensorFun A B T C (f , p) (g , q)) a) =
     makeIsGroupHom
     λ x y → cong g (IsGroupHom.pres· (snd (f a)) x y)
              ∙ IsGroupHom.pres· q _ _
snd (tensorFun A B T C (f , p) (g , q)) =
     makeIsGroupHom
     λ x y → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                     (funExt λ b → cong g (funExt⁻ (cong fst (IsGroupHom.pres· p x y)) b)
                                    ∙ IsGroupHom.pres· q _ _)

isTensorProductOf_and_ : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')→ Type _
isTensorProductOf_and_ {ℓ} {ℓ'} A B T =
  Σ[ f ∈ GroupHom (A *) ((HomGroup (B *) T) *) ]
    ((C : AbGroup (ℓ-max ℓ ℓ')) → isEquiv {A = GroupHom (T *) (C *)}
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
  snd (fst mainF a) = makeIsGroupHom (⊗DistR+⊗ a)
  snd mainF = makeIsGroupHom
              λ x y → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                              (funExt (⊗DistL+⊗ x y))

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
      F (+⊗Comm x x₁ i) = +Comm (snd C) (F x) (F x₁) i
      F (+⊗Assoc x y z i) = +Assoc (snd C) (F x) (F y) (F z) i
      F (+⊗IdL x i) = (cong (λ y → _+G_ (snd C) y (F x)) lem ∙ +IdL (snd C) (F x)) i
      F (⊗DistR+⊗ x y z i) = IsGroupHom.pres· (f x .snd) y z i
      F (⊗DistL+⊗ x y z i) = fst (IsGroupHom.pres· p x y i) z
      F (⊗squash x x₁ x₂ y i i₁) = is-set (snd C) (F x) (F x₁)
                                   (λ i → F (x₂ i)) (λ i → F (y i)) i i₁
    snd (invF (f , p)) = makeIsGroupHom λ x y → refl

    mainIso : Iso (GroupHom ((AGr ⨂ BGr) *) (C *))
                  (GroupHom (AGr *) (HomGroup (BGr *) C *))
    Iso.fun mainIso = _
    Iso.inv mainIso = invF
    Iso.rightInv mainIso (f , p) = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                                   (funExt λ a → Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl)
    Iso.leftInv mainIso (f , p) =
        Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                (funExt (⊗elimProp (λ _ → is-set (snd C) _ _)
                                   (λ _ _ → refl)
                                    λ x y ind1 ind2 → cong₂ (_+G_ (snd C)) ind1 ind2
                                                       ∙ sym (IsGroupHom.pres· p x y)))

module _ {ℓ'' ℓ''' : Level} {A : AbGroup ℓ}
         {B : AbGroup ℓ'} {C : AbGroup ℓ''} {D : AbGroup ℓ'''}
         (ϕ : AbGroupHom A C) (ψ : AbGroupHom B D) where
  inducedFun⨂ : A ⨂₁ B → C ⨂₁ D
  inducedFun⨂ =
    ⨂→AbGroup-elim (C ⨂ D)
      (λ x → fst ϕ (fst x) ⊗ fst ψ (snd x))
      (cong (_⊗ fst ψ _) (IsGroupHom.pres1 (snd ϕ)) ∙ ⊗AnnihilL _)
      (λ x y z → cong (fst ϕ x ⊗_) (IsGroupHom.pres· (snd ψ) y z) ∙ ⊗DistR+⊗ _ _ _)
      λ x y z → cong (_⊗ fst ψ z) (IsGroupHom.pres· (snd ϕ) x y) ∙ ⊗DistL+⊗ _ _ _

  inducedHom⨂ : AbGroupHom (A ⨂ B) (C ⨂ D)
  fst inducedHom⨂ = inducedFun⨂
  snd inducedHom⨂ =
    makeIsGroupHom λ _ _ → refl

-------------------- Commutativity ------------------------
commFun : ∀ {ℓ ℓ'} {A : AbGroup ℓ}  {B : AbGroup ℓ'} → A ⨂₁ B → B ⨂₁ A
commFun (a ⊗ b) = b ⊗ a
commFun (x +⊗ x₁) = commFun x +⊗ commFun x₁
commFun (+⊗Comm x x₁ i) = +⊗Comm (commFun x) (commFun x₁) i
commFun (+⊗Assoc x x₁ x₂ i) = +⊗Assoc (commFun x) (commFun x₁) (commFun x₂) i
commFun (+⊗IdL x i) = +⊗IdL (commFun x) i
commFun (⊗DistR+⊗ x y z i) = ⊗DistL+⊗ y z x i
commFun (⊗DistL+⊗ x y z i) = ⊗DistR+⊗ z x y i
commFun (⊗squash x x₁ x₂ y i i₁) = ⊗squash (commFun x) (commFun x₁)
                                           (λ i → commFun (x₂ i)) (λ i → commFun (y i)) i i₁

commFun²≡id : ∀ {ℓ ℓ'} {A : AbGroup ℓ}  {B : AbGroup ℓ'} (x : A ⨂₁ B)
               → commFun (commFun x) ≡ x
commFun²≡id = ⊗elimProp (λ _ → ⊗squash _ _)
                        (λ _ _ → refl)
                        (λ _ _ p q → cong₂ _+⊗_ p q)

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
    f c = ⨂→AbGroup-elim-hom (A ⨂ (B ⨂ C))
                               (λ ab → (fst ab) ⊗ ((snd ab) ⊗ c))
                               (λ a b b' → (λ i → a ⊗ (⊗DistL+⊗ b b' c i)) ∙ ⊗DistR+⊗ a (b ⊗ c) (b' ⊗ c))
                               (λ a a' b → ⊗DistL+⊗ a a' (b ⊗ c))
                               (⊗AnnihilL _ ∙ sym (⊗AnnihilL _))

  assocHom : AbGroupHom ((A ⨂ B) ⨂ C) (A ⨂ (B ⨂ C))
  assocHom = ⨂→AbGroup-elim-hom (A ⨂ (B ⨂ C))
                                  (λ x → f (snd x) .fst (fst x))
                                  helper
                                  (λ x y b → IsGroupHom.pres· (snd (f b)) x y)
                                  refl
    where
    helper : _
    helper = ⊗elimProp (λ _ → isPropΠ2 λ _ _ → ⊗squash _ _)
                       (λ a b x y → (λ i → a ⊗ (⊗DistR+⊗ b x y i))
                                     ∙∙ ⊗DistR+⊗ a (b ⊗ x) (b ⊗ y)
                                     ∙∙ refl)
                       λ a b ind1 ind2 x y → cong₂ _+⊗_ (ind1 x y) (ind2 x y)
                                              ∙∙ move4 (f x .fst a) (f y .fst a) (f x .fst b) (f y .fst b)
                                                       _+⊗_ +⊗Assoc +⊗Comm
                                              ∙∙ cong₂ _+⊗_
                                                       (sym (IsGroupHom.pres· (snd (f x)) a b))
                                                       (IsGroupHom.pres· (snd (f y)) a b)

module _ {ℓ ℓ' ℓ'' : Level} {A : AbGroup ℓ} {B : AbGroup ℓ'} {C : AbGroup ℓ''} where
  private
    f' : (a : fst A) → AbGroupHom (B ⨂ C) ((A ⨂ B) ⨂ C)
    f' a = ⨂→AbGroup-elim-hom
               ((A ⨂ B) ⨂ C)
               (λ bc → (a ⊗ fst bc) ⊗ snd bc)
               (λ x y b → ⊗DistR+⊗ (a ⊗ x) y b)
               (λ x y b → (λ i → (⊗DistR+⊗ a x y i) ⊗ b)
                           ∙ ⊗DistL+⊗ (a ⊗ x) (a ⊗ y) b)
               λ i → ⊗AnnihilR a i ⊗ (0g (snd C))

  assocHom⁻ : AbGroupHom (A ⨂ (B ⨂ C)) ((A ⨂ B) ⨂ C)
  assocHom⁻ = ⨂→AbGroup-elim-hom
                  ((A ⨂ B) ⨂ C)
                  (λ abc → f' (fst abc) .fst (snd abc))
                  (λ a → IsGroupHom.pres· (snd (f' a)))
                  helper
                  refl
       where
       helper : _
       helper = λ x y → ⊗elimProp
                         (λ _ → ⊗squash _ _)
                         (λ b c → (λ i → ⊗DistL+⊗ x y b i ⊗ c)
                                           ∙ ⊗DistL+⊗ (x ⊗ b) (y ⊗ b) c)
                          λ a b ind1 ind2 → cong₂ _+⊗_ ind1 ind2
                                             ∙∙ move4 _ _ _ _ _+⊗_ +⊗Assoc +⊗Comm
                                             ∙∙ cong₂ _+⊗_ (IsGroupHom.pres· (snd (f' x)) a b)
                                                (IsGroupHom.pres· (snd (f' y)) a b)

  ⨂assocIso : Iso (A ⨂₁ (B ⨂ C)) ((A ⨂ B) ⨂₁ C)
  Iso.fun ⨂assocIso = fst assocHom⁻
  Iso.inv ⨂assocIso = fst assocHom
  Iso.rightInv ⨂assocIso =
    ⊗elimProp (λ _ → ⊗squash _ _)
               (⊗elimProp (λ _ → isPropΠ (λ _ → ⊗squash _ _))
                           (λ a b c → refl)
                           λ a b ind1 ind2 c → cong₂ _+⊗_ (ind1 c) (ind2 c)
                                                ∙ sym (⊗DistL+⊗ a b c))
                λ x y p q → cong (fst assocHom⁻) (IsGroupHom.pres· (snd assocHom) x y)
                             ∙∙ IsGroupHom.pres· (snd assocHom⁻) (fst assocHom x) (fst assocHom y)
                             ∙∙ cong₂ _+⊗_ p q
  Iso.leftInv ⨂assocIso =
    ⊗elimProp (λ _ → ⊗squash _ _)
               (λ a → ⊗elimProp (λ _ → ⊗squash _ _)
                                  (λ b c → refl)
                                   λ x y ind1 ind2 →
                                        cong (fst assocHom ∘ fst assocHom⁻) (⊗DistR+⊗ a x y)
                                     ∙∙ cong (fst assocHom) (IsGroupHom.pres· (snd assocHom⁻) (a ⊗ x) (a ⊗ y))
                                     ∙∙ IsGroupHom.pres· (snd assocHom) (fst assocHom⁻ (a ⊗ x)) (fst assocHom⁻ (a ⊗ y))
                                     ∙∙ cong₂ _+⊗_ ind1 ind2
                                     ∙∙ sym (⊗DistR+⊗ a x y))
                λ x y p q → cong (fst assocHom) (IsGroupHom.pres· (snd assocHom⁻) x y)
                             ∙∙ IsGroupHom.pres· (snd assocHom) (fst assocHom⁻ x) (fst assocHom⁻ y)
                             ∙∙ cong₂ _+⊗_ p q

  ⨂assoc : AbGroupEquiv (A ⨂ (B ⨂ C)) ((A ⨂ B) ⨂ C)
  fst ⨂assoc = isoToEquiv ⨂assocIso
  snd ⨂assoc = snd assocHom⁻

module _ {G' : Ring ℓ} where
  private
    G = Ring→AbGroup G'
    _·G_ = RingStr._·_ (snd G')

  TensorMult : fst (G ⨂ G) → fst G
  TensorMult =
    ⨂→AbGroup-elim G
      (λ x → fst x ·G snd x)
       (RingTheory.0LeftAnnihilates G' _)
       (IsRing.·DistR+ (RingStr.isRing (snd G')))
       (IsRing.·DistL+ (RingStr.isRing (snd G')))

  TensorMultHom : AbGroupHom (G ⨂ G) G
  fst TensorMultHom = TensorMult
  snd TensorMultHom =
    makeIsGroupHom λ x y → refl

lIncl⨂ : {G : AbGroup ℓ} {H : AbGroup ℓ'} → (h : fst H) → AbGroupHom G (G ⨂ H)
fst (lIncl⨂ h) g = g ⊗ h
snd (lIncl⨂ h) = makeIsGroupHom λ x y → ⊗DistL+⊗ x y h

rIncl⨂ : {G : AbGroup ℓ} {H : AbGroup ℓ'} → (g : fst G) → AbGroupHom H (G ⨂ H)
fst (rIncl⨂ g) h = g ⊗ h
snd (rIncl⨂ g) = makeIsGroupHom (⊗DistR+⊗ g)

G→G⨂G→Gₗ : {G : Ring ℓ}
  → Path (AbGroupHom (Ring→AbGroup G) (Ring→AbGroup G))
          ((compGroupHom (lIncl⨂ (RingStr.1r (snd G))) TensorMultHom))
          idGroupHom
G→G⨂G→Gₗ {G = G} =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (RingStr.·IdR (snd G)))

G→G⨂G→Gᵣ : {G : Ring ℓ}
  → Path (AbGroupHom (Ring→AbGroup G) (Ring→AbGroup G))
          ((compGroupHom (rIncl⨂ (RingStr.1r (snd G))) TensorMultHom))
          idGroupHom
G→G⨂G→Gᵣ {G = G} =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (RingStr.·IdL (snd G)))
