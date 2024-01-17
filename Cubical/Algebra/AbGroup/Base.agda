{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsAbGroup {A : Type ℓ}
                 (0g : A) (_+_ : A → A → A) (-_ : A → A) : Type ℓ where

  constructor isabgroup

  field
    isGroup : IsGroup 0g _+_ -_
    +Comm    : (x y : A) → x + y ≡ y + x

  open IsGroup isGroup public
    renaming
      ( ·Assoc      to +Assoc
      ; ·IdL        to +IdL
      ; ·IdR        to +IdR
      ; ·InvL       to +InvL
      ; ·InvR       to +InvR)

  infixl 6 _-_

  -- Useful notation for additive groups
  _-_ : A → A → A
  x - y = x + (- y)

unquoteDecl IsAbGroupIsoΣ = declareRecordIsoΣ IsAbGroupIsoΣ (quote IsAbGroup)

record AbGroupStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor abgroupstr

  field
    0g        : A
    _+_       : A → A → A
    -_        : A → A
    isAbGroup : IsAbGroup 0g _+_ -_


  infixr 7 _+_
  infix  8 -_

  open IsAbGroup isAbGroup public

AbGroup : ∀ ℓ → Type (ℓ-suc ℓ)
AbGroup ℓ = TypeWithStr ℓ AbGroupStr

module _ {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
         (is-setG : isSet G)
         (+Assoc   : (x y z : G) → x + (y + z) ≡ (x + y) + z)
         (+IdR     : (x : G) → x + 0g ≡ x)
         (+InvR    : (x : G) → x + (- x) ≡ 0g)
         (+Comm    : (x y : G) → x + y ≡ y + x)
  where

  makeIsAbGroup : IsAbGroup 0g _+_ -_
  makeIsAbGroup .IsAbGroup.isGroup =
    makeIsGroup is-setG +Assoc +IdR
                (λ x → +Comm _ _ ∙ +IdR x)
                +InvR
                (λ x → +Comm _ _ ∙ +InvR x)
  makeIsAbGroup .IsAbGroup.+Comm = +Comm

module _ {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
         (is-setG : isSet G)
         (+Assoc  : (x y z : G) → x + (y + z) ≡ (x + y) + z)
         (+IdR    : (x : G) → x + 0g ≡ x)
         (+InvR   : (x : G) → x + (- x) ≡ 0g)
         (+Comm   : (x y : G) → x + y ≡ y + x)
  where

  makeAbGroup : AbGroup ℓ
  makeAbGroup .fst = G
  makeAbGroup .snd .AbGroupStr.0g = 0g
  makeAbGroup .snd .AbGroupStr._+_ = _+_
  makeAbGroup .snd .AbGroupStr.-_ = -_
  makeAbGroup .snd .AbGroupStr.isAbGroup = makeIsAbGroup is-setG +Assoc +IdR +InvR +Comm

open GroupStr
open AbGroupStr
open IsAbGroup

AbGroupStr→GroupStr : {G : Type ℓ} → AbGroupStr G → GroupStr G
AbGroupStr→GroupStr A .1g = A .0g
AbGroupStr→GroupStr A ._·_ = A ._+_
AbGroupStr→GroupStr A .inv = A .-_
AbGroupStr→GroupStr A .isGroup = A .isAbGroup .isGroup

AbGroup→Group : AbGroup ℓ → Group ℓ
fst (AbGroup→Group A) = fst A
snd (AbGroup→Group A) = AbGroupStr→GroupStr (snd A)

Group→AbGroup : (G : Group ℓ) → ((x y : fst G) → _·_ (snd G) x y ≡ _·_ (snd G) y x) → AbGroup ℓ
fst (Group→AbGroup G +Comm) = fst G
AbGroupStr.0g (snd (Group→AbGroup G +Comm)) = 1g (snd G)
AbGroupStr._+_ (snd (Group→AbGroup G +Comm)) = _·_ (snd G)
AbGroupStr.- snd (Group→AbGroup G +Comm) = inv (snd G)
IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd (Group→AbGroup G +Comm))) = isGroup (snd G)
IsAbGroup.+Comm (AbGroupStr.isAbGroup (snd (Group→AbGroup G +Comm))) = +Comm

module _ ((G , abgroupstr _ _ _ GisGroup) : AbGroup ℓ) where
  AbGroup→CommMonoid : CommMonoid ℓ
  AbGroup→CommMonoid .fst = G
  AbGroup→CommMonoid .snd .CommMonoidStr.ε = _
  AbGroup→CommMonoid .snd .CommMonoidStr._·_ = _
  AbGroup→CommMonoid .snd .CommMonoidStr.isCommMonoid .IsCommMonoid.isMonoid = IsAbGroup.isMonoid GisGroup
  AbGroup→CommMonoid .snd .CommMonoidStr.isCommMonoid .IsCommMonoid.·Comm = IsAbGroup.+Comm GisGroup

AbGroupHom : (G : AbGroup ℓ) (H : AbGroup ℓ') → Type (ℓ-max ℓ ℓ')
AbGroupHom G H = GroupHom (AbGroup→Group G) (AbGroup→Group H)

AbGroupIso : (G : AbGroup ℓ) (H : AbGroup ℓ') → Type (ℓ-max ℓ ℓ')
AbGroupIso G H = GroupIso (AbGroup→Group G) (AbGroup→Group H)

IsAbGroupEquiv : {A : Type ℓ} {B : Type ℓ'}
  (G : AbGroupStr A) (e : A ≃ B) (H : AbGroupStr B) → Type (ℓ-max ℓ ℓ')
IsAbGroupEquiv G e H = IsGroupHom (AbGroupStr→GroupStr G) (e .fst) (AbGroupStr→GroupStr H)

AbGroupEquiv : (G : AbGroup ℓ) (H : AbGroup ℓ') → Type (ℓ-max ℓ ℓ')
AbGroupEquiv G H = Σ[ e ∈ (G .fst ≃ H .fst) ] IsAbGroupEquiv (G .snd) e (H .snd)

isPropIsAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
                → isProp (IsAbGroup 0g _+_ (-_))
isPropIsAbGroup 0g _+_ -_ =
  isOfHLevelRetractFromIso 1 IsAbGroupIsoΣ
    (isPropΣ (isPropIsGroup 0g _+_ (-_))
             (λ grp → isPropΠ2 (λ _ _ → grp .is-set _ _)))
  where
  open IsGroup


𝒮ᴰ-AbGroup : DUARel (𝒮-Univ ℓ) AbGroupStr ℓ
𝒮ᴰ-AbGroup =
  𝒮ᴰ-Record (𝒮-Univ _) IsAbGroupEquiv
    (fields:
      data[ _+_ ∣ autoDUARel _ _ ∣ pres· ]
      data[ 0g ∣ autoDUARel _ _ ∣ pres1 ]
      data[ -_ ∣ autoDUARel _ _ ∣ presinv ]
      prop[ isAbGroup ∣ (λ _ _ → isPropIsAbGroup _ _ _) ])
  where
  open AbGroupStr
  open IsGroupHom

-- Extract the characterization of equality of groups
AbGroupPath : (G H : AbGroup ℓ) → (AbGroupEquiv G H) ≃ (G ≡ H)
AbGroupPath = ∫ 𝒮ᴰ-AbGroup .UARel.ua


-- The module below defines an abelian group induced from an
-- equivalence between an abelian group G and a type A which preserves
-- the full raw group structure from G to A. This version is useful
-- when proving that some type equivalent to an abelian group is an
-- abelian group while also specifying the binary operation, unit and
-- inverse. For an example of this see Algebra.Matrix
module _ (G : AbGroup ℓ) {A : Type ℓ}
  (m : A → A → A)
  (u : A)
  (inverse : A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p+ : ∀ x y → e .fst (G .snd ._+_ x y) ≡ m (e .fst x) (e .fst y))
  (pu : e .fst (G .snd .0g) ≡ u)
  (pinv : ∀ x → e .fst (G .snd .-_ x) ≡ inverse (e .fst x))
  where

  private
    module G = AbGroupStr (G .snd)

    BaseΣ : Type (ℓ-suc ℓ)
    BaseΣ = Σ[ B ∈ Type ℓ ] (B → B → B) × B × (B → B)

    FamilyΣ : BaseΣ → Type ℓ
    FamilyΣ (B , m , u , i) = IsAbGroup u m i

    inducedΣ : FamilyΣ (A , m , u , inverse)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel BaseΣ) (e , p+ , pu , pinv))
        G.isAbGroup

  InducedAbGroup : AbGroup ℓ
  InducedAbGroup .fst = A
  InducedAbGroup .snd ._+_ = m
  InducedAbGroup .snd .0g = u
  InducedAbGroup .snd .-_ = inverse
  InducedAbGroup .snd .isAbGroup = inducedΣ

  InducedAbGroupEquiv : AbGroupEquiv G InducedAbGroup
  fst InducedAbGroupEquiv = e
  snd InducedAbGroupEquiv = makeIsGroupHom p+

  InducedAbGroupPath : G ≡ InducedAbGroup
  InducedAbGroupPath = AbGroupPath _ _ .fst InducedAbGroupEquiv



-- The module below defines an abelian group induced from an
-- equivalence which preserves the binary operation (i.e. a group
-- isomorphism). This version is useful when proving that some type
-- equivalent to an abelian group G is an abelian group when one
-- doesn't care about what the unit and inverse are. When using this
-- version the unit and inverse will both be defined by transporting
-- over the unit and inverse from G to A.
module _ (G : AbGroup ℓ) {A : Type ℓ}
  (m : A → A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p· : ∀ x y → e .fst (G .snd ._+_ x y) ≡ m (e .fst x) (e .fst y))
  where

  private
    module G = AbGroupStr (G .snd)

    FamilyΣ : Σ[ B ∈ Type ℓ ] (B → B → B) → Type ℓ
    FamilyΣ (B , n) = Σ[ e ∈ B ] Σ[ i ∈ (B → B) ] IsAbGroup e n i

    inducedΣ : FamilyΣ (A , m)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel (Σ[ B ∈ Type ℓ ] (B → B → B))) (e , p·))
        (G.0g , G.-_ , G.isAbGroup)

  InducedAbGroupFromPres· : AbGroup ℓ
  InducedAbGroupFromPres· .fst = A
  InducedAbGroupFromPres· .snd ._+_ = m
  InducedAbGroupFromPres· .snd .0g = inducedΣ .fst
  InducedAbGroupFromPres· .snd .-_ = inducedΣ .snd .fst
  InducedAbGroupFromPres· .snd .isAbGroup = inducedΣ .snd .snd

  InducedAbGroupEquivFromPres· : AbGroupEquiv G InducedAbGroupFromPres·
  fst InducedAbGroupEquivFromPres· = e
  snd InducedAbGroupEquivFromPres· = makeIsGroupHom p·

  InducedAbGroupPathFromPres· : G ≡ InducedAbGroupFromPres·
  InducedAbGroupPathFromPres· = AbGroupPath _ _ .fst InducedAbGroupEquivFromPres·


dirProdAb : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')
dirProdAb A B =
  Group→AbGroup (DirProd (AbGroup→Group A) (AbGroup→Group B))
                 λ p q → ΣPathP (+Comm (isAbGroup (snd A)) _ _
                                , +Comm (isAbGroup (snd B)) _ _)

trivialAbGroup : ∀ {ℓ} → AbGroup ℓ
fst trivialAbGroup = Unit*
0g (snd trivialAbGroup) = tt*
_+_ (snd trivialAbGroup) _ _ = tt*
(- snd trivialAbGroup) _ = tt*
isAbGroup (snd trivialAbGroup) = makeIsAbGroup
                                 (isProp→isSet isPropUnit*)
                                 (λ _ _ _ → refl)
                                 (λ _ → refl)
                                 (λ _ → refl)
                                 (λ _ _ → refl)

-- useful lemma
-- duplicate propeerties => this file should be split !
move4 : ∀ {ℓ} {A : Type ℓ} (x y z w : A) (_+_ : A → A → A)
       → ((x y z : A) → x + (y + z) ≡ (x + y) + z)
       → ((x y : A) → x + y ≡ y + x)
      → (x + y) + (z + w) ≡ ((x + z) + (y + w))
move4 x y z w _+_ assoc +Comm =
     sym (assoc x y (z + w))
  ∙∙ cong (x +_) (assoc y z w ∙∙ cong (_+ w) (+Comm y z) ∙∙ sym (assoc z y w))
  ∙∙ assoc x z (y + w)

---- The type of homomorphisms A → B is an AbGroup if B is -----
module _ {ℓ ℓ' : Level} (AGr : Group ℓ) (BGr : AbGroup ℓ') where
  private
    strA = snd AGr
    strB = snd BGr

    _* = AbGroup→Group

    A = fst AGr
    B = fst BGr
    open IsGroupHom

    open AbGroupStr strB
      renaming (_+_ to _+B_ ; -_ to -B_ ; 0g to 0B
              ; +IdR to +IdRB ; +IdL to +IdLB
              ; +Assoc to +AssocB ; +Comm to +CommB
              ; +InvR to +InvRB ; +InvL to +InvLB)
    open GroupStr strA
      renaming (_·_ to _∙A_ ; inv to -A_
                ; 1g to 1A ; ·IdR to ·IdRA)

  compHom : GroupHom AGr (BGr *) → GroupHom AGr (BGr *) → GroupHom AGr (BGr *)
  fst (compHom f g) x = fst f x +B fst g x
  snd (compHom f g) =
      makeIsGroupHom λ x y
      → cong₂ _+B_ (pres· (snd f) x y) (pres· (snd g) x y)
      ∙ move4 (fst f x) (fst f y) (fst g x) (fst g y)
              _+B_ +AssocB +CommB

  invHom : GroupHom AGr (BGr *) → GroupHom AGr (BGr *)
  fst (invHom (f , p)) x = -B f x
  snd (invHom (f , p)) =
    makeIsGroupHom
      λ x y → cong -B_ (pres· p x y)
            ∙∙ GroupTheory.invDistr (BGr *) (f x) (f y)
            ∙∙ +CommB _ _

  open AbGroupStr

  HomGroup : AbGroup (ℓ-max ℓ ℓ')
  fst HomGroup = GroupHom AGr (BGr *)
  0g (snd HomGroup) = trivGroupHom
  _+_ (snd HomGroup) = compHom
  - snd HomGroup = invHom
  isAbGroup (snd HomGroup) =
    makeIsAbGroup
    isSetGroupHom
    (λ { (f , p) (g , q) (h , r) → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                                             (funExt λ x → +AssocB _ _ _) })
    (λ { (f , p) → Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ y → +IdRB _)})
    ((λ { (f , p) → Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ y → +InvRB _)}))
    (λ { (f , p) (g , q) → Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x → +CommB _ _)})
