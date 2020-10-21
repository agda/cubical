{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Talks.DURG where

open import Cubical.Algebra.Group
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Relation.Binary

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.XModule

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓA' ℓ≅A' ℓB ℓB' ℓ≅B' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓP : Level

-- NOTES
-- Top-Level presentation possible, but code is going to be used
-- interrupt any time, especially when I'm going too fast
-- split screen so URGStr always visible

{-
  Goals of the project:
  - define strict 2-groups
  - define crossed modules
  - prove their equivalence
  - do something with the classifying space
    perspective on groups

  Problems:
  - performance
  - the maps going back and forth were fine,
    but the identity types stating that these maps
    are inverse to each other were too complex

  How did we solve this?
  - Copatterns
  - Ulrik's idea: displayed univalent reflexive graphs
    - Provide a fiberwise characterization of the identity types
      of a type family to obtain a characterization of the
      identity types of the total space
    - Avoid equality on objects in proofs
    - Modular and abstract
-}





-- DEFINITION
-- - URG structure
-- - alternative constructors

record URGStr' (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor urgstr'

  field
    _≅_ : Rel A A ℓ≅A
    ρ : isRefl _≅_
    uni : isUnivalent _≅_ ρ

-- substituted version
record URGStr'' (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  field
    -- a binary relation
    _≅_ : A → A → Type ℓ≅A
    -- a witness of reflexivity
    ρ : (a : A) → a ≅ a
  -- these two fields induce a map that turns
  -- a path into a proof the endpoints are related
  ≡→≅ : {a a' : A} → a ≡ a' → a ≅ a'
  ≡→≅ {a} {a'} p = subst (λ z → a ≅ z) p (ρ a)
  field
    -- that natural map is a fiberwise equivalence
    uni : (a a' : A) → isEquiv (≡→≅ {a} {a'})


  -- alternatively, we could ask for any fiberwise equivalence
  uni' = (a a' : A) → (a ≡ a') ≃ (a ≅ a')
  -- another alternative: all ≅-singletons should be contractible
  contrRelSingl' = (a : A) → isContr (Σ[ a' ∈ A ] (a ≅ a'))

  -- We can prove that these are equivalent:
  -- uni ↔ uni' ↔ contrRelSingl'

  -- This gives rise to alternative constructors for URGs:

make-𝒮' : {A : Type ℓA}
         {_≅_ : Rel A A ℓ≅A}
         (ρ : isRefl _≅_)
         (contrTotal : contrRelSingl _≅_)
         → URGStr A ℓ≅A
make-𝒮' {_≅_ = _≅_} ρ contrTotal =
  urgstr _≅_
         ρ
         (contrRelSingl→isUnivalent _≅_ ρ contrTotal)








-- EXAMPLES
-- - groups
-- - univalent categories
-- - observational equality on ℕ
-- - universe
-- - identity types

-- The SIP for groups produces a URG structure on the type of groups
𝒮-group' : (ℓ : Level) → URGStr (Group {ℓ}) ℓ
𝒮-group' ℓ .URGStr._≅_ = GroupEquiv
𝒮-group' ℓ .URGStr.ρ = idGroupEquiv
𝒮-group' ℓ .URGStr.uni =
  isUnivalent'→isUnivalent GroupEquiv
                            idGroupEquiv
                            λ G H → invEquiv (GroupPath G H)

-- Every univalent Category induces a URG on its type of objects
open import Cubical.Categories.Category renaming (isUnivalent to isUnivalentCat)
Cat→𝒮 : (𝒞 : Precategory ℓ ℓ')
         → (uni : isUnivalentCat 𝒞)
         → URGStr (𝒞 .ob) ℓ'
Cat→𝒮 𝒞 uni
  = urgstr (CatIso {𝒞 = 𝒞})
           idCatIso
           λ x y → isUnivalentCat.univ uni x y

-- observational equality on ℕ
ℕ-≅ : ℕ → ℕ → Type ℓ-zero
ℕ-≅ 0 0 = Unit
ℕ-≅ 0 (suc _) = ⊥
ℕ-≅ (suc _) 0 = ⊥
ℕ-≅ (suc n) (suc m) = ℕ-≅ n m
-- observational equality on ℕ is a URG
𝒮-Nat' : URGStr ℕ ℓ-zero
𝒮-Nat' = {!!}
  where
    import Cubical.DStructures.Structures.Nat using (𝒮-Nat)

-- equivalences determine a URG on any universe
𝒮-universe : URGStr (Type ℓ) ℓ
𝒮-universe
  = make-𝒮 {_≅_ = _≃_}
            idEquiv
            λ A → isContrRespectEquiv (Σ-cong-equiv-snd (λ A' → isoToEquiv (equivInv A' A)))
                                       (equivContr' A)
  where
    module _ (A : Type ℓ) where
      equivInv : (A' : Type ℓ) → Iso (A ≃ A') (A' ≃ A)
      Iso.fun (equivInv A') = invEquiv
      Iso.inv (equivInv A') = invEquiv
      Iso.leftInv (equivInv A') = λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl))
      Iso.rightInv (equivInv A') = λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl))
      equivContr' : isContr (Σ[ A' ∈ Type ℓ ] A' ≃ A)
      equivContr' = EquivContr A

-- trivially, a type is a URGStr with the relation given by its identity type
𝒮-type : (A : Type ℓ) → URGStr A ℓ
𝒮-type A = make-𝒮 {_≅_ = _≡_}
                  (λ _ → refl)
                  isContrSingl






-- THEOREM:
-- - uniqueness of small URGs

𝒮-uniqueness' : (A : Type ℓA) → isContr (URGStr A ℓA)
𝒮-uniqueness' = {!!}
  where
    import Cubical.DStructures.Structures.Type using (𝒮-uniqueness)






-- DEFINITION
-- - displayed URG

record URGStrᴰ' {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                (B : A → Type ℓB) (ℓ≅ᴰ : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓB) ℓ≅A) (ℓ-suc ℓ≅ᴰ)) where
  no-eta-equality
  constructor urgstrᴰ'
  open URGStr 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅ᴰ
    ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_
    uniᴰ : {a : A} → isUnivalent _≅ᴰ⟨ ρ a ⟩_ ρᴰ

  -- Of course, this also has the alternative constructor make-𝒮ᴰ
  -- using that the uniᴰ field follows from
  uniᴰ' = {a : A} → (b : B a) → isContr (Σ[ b' ∈ B a ] b ≅ᴰ⟨ ρ a ⟩ b')


-- EXAMPLE
-- - pointedness displayed over the universe
𝒮ᴰ-pointed : {ℓ : Level} → URGStrᴰ (𝒮-universe {ℓ}) (λ A → A) ℓ
𝒮ᴰ-pointed {ℓ} =
  make-𝒮ᴰ (λ a e b → equivFun e a ≡ b)
          (λ _ → refl)
          p
          where
            p : (A : Type ℓ) (a : A) → isContr (Σ[ b ∈ A ] a ≡ b)
            p _ a = isContrSingl a



-- THEOREM
-- Every DURG on a type family B induces
-- a URG on the total space Σ[ a ∈ A ] B a

∫⟨_⟩'_ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
        {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
        → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
∫⟨_⟩'_ = {!!}

{-
  B   ∫
  |   ↦   A × B
  A
-}

-- EXAMPLE
-- A characterization of the identity types of pointed types
𝒮-pointed : {ℓ : Level} → URGStr (Σ[ A ∈ Type ℓ ] A) ℓ
𝒮-pointed = ∫⟨ 𝒮-universe ⟩ 𝒮ᴰ-pointed


-- EXAMPLE
-- - constant DURG
-- - URG product
-- - URG structure on pairs of groups

𝒮ᴰ-const : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
           {B : Type ℓB} (𝒮-B : URGStr B ℓ≅B)
           → URGStrᴰ 𝒮-A (λ _ → B) ℓ≅B
𝒮ᴰ-const {A = A} 𝒮-A {B} 𝒮-B
  = urgstrᴰ (λ b _ b' → b ≅ b') ρ uni
    where
      open URGStr 𝒮-B

_×𝒮_ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
        {B : Type ℓB} (𝒮-B : URGStr B ℓ≅B)
        → URGStr (A × B) (ℓ-max ℓ≅A ℓ≅B)
_×𝒮_ 𝒮-A 𝒮-B = ∫⟨ 𝒮-A ⟩ (𝒮ᴰ-const 𝒮-A 𝒮-B)


{-
        const   B    ∫
  A, B   ↦     |    ↦ A × B
                A
-}

-- EXAMPLE
-- Group Homomorphisms displayed over pairs of groups

𝒮ᴰ-G²\F' : URGStrᴰ (𝒮-group' ℓ ×𝒮 𝒮-group' ℓ')
                  (λ (G , H) → GroupHom G H)
                  (ℓ-max ℓ ℓ')
𝒮ᴰ-G²\F' =
    make-𝒮ᴰ (λ {(G , H)} {(G' , H')} f (eG , eH) f'
               → (g : ⟨ G ⟩)
               → GroupEquiv.eq eH .fst ((f .fun) g) ≡ (f' .fun) (GroupEquiv.eq eG .fst g))
            (λ _ _ → refl)
            λ (G , H) f → isContrRespectEquiv (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                              (isContrSingl f)
    where open GroupHom

{-
The displayed relation is defined as

  f ≅⟨ eG , eH ⟩ f = commutativity of

         f
   G --------> H
   |           |
eG |           | eH
   |           |
   G'--------> H'
        f'

Reflexivity is trivial

Univalence follows from contractibility of
Σ[ (f' , _) ∈ GroupHom G H ] (f ∼ f')
for all (f , _) ∈ GroupHom G H
-}




{-
  Overview of Crossed Modules and Strict 2-Groups

  Definition: Crossed module
    - group action α of G₀ on H
    - homomorphism φ : H → G₀
    - equivariance condition
      (g : G₀) → (h : H) → φ (g α h) ≡ g + (φ h) - g
    - peiffer condition
      (h h' : ⟨ H ⟩) → (φ h) α h' ≡ h + h' - h

  Definition: Strict 2-Group
    - internal category in the category of groups
    This means
    - split mono ι with two retractions
      ι : G₀ ↔ G : σ τ₁
    - vertical composition operation which satisfies the interchange law
      _∘⟨_⟩_ : (g f : G₁) → isComposable g f → G₁
    - equivalent to type of vertical compositions on internal reflexive graph: PFG
      (a b :  G₁) → ι(σ b) + a - ι(τ a) - ι(σ b) + b + ι(τ a) ≡ b + a

  Produce this tree of displayed structures:

  PFXM                    PFG     VertComp
  |                       |      /
  |                       |     /
  isEquivar               isSecRet
  |                       |
  |                       |
  B                       B
  |                       |
  |                       |
  isAction                isSecRet
  |                       |
  |                       |
  LAS       F      B      F×B
  \         |      |      /
    \       |      |    /
      \     |      /   /
        \   |     /  /
            Grp
            |
            |
             Grp


use the next result to display propositions like isAction, isEquivariant and isSecRet
-}

-- THEOREM
-- Subtypes have a simple DURG structure given by 𝟙
-- This makes it easy to impose axioms on a structure
Subtype→Sub-𝒮ᴰ : {A : Type ℓA}
                 → (P : A → hProp ℓP)
                 → (𝒮-A : URGStr A ℓ≅A)
                 → URGStrᴰ 𝒮-A (λ a → P a .fst) ℓ-zero
Subtype→Sub-𝒮ᴰ P 𝒮-A =
  make-𝒮ᴰ (λ _ _ _ → Unit)
          (λ _ → tt)
          (λ a p → isContrRespectEquiv (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                        (inhProp→isContr p (P a .snd)))

-- EXAMPLE
-- isAction axioms on pairs of groups together with a left action structure
module _ (ℓ ℓ' : Level) where
  ℓℓ' = ℓ-max ℓ ℓ'

  open import Cubical.DStructures.Structures.Action
  𝒮ᴰ-G²Las\Action' : URGStrᴰ (𝒮-G²Las ℓ ℓ')
                     (λ ((G , H) , _α_) → IsGroupAction G H _α_)
                     ℓ-zero
  𝒮ᴰ-G²Las\Action' = Subtype→Sub-𝒮ᴰ (λ ((G , H) , _α_) → IsGroupAction G H _α_ , isPropIsGroupAction G H _α_)
                                    (𝒮-G²Las ℓ ℓ')
  𝒮-G²LasAction' : URGStr (Action ℓ ℓ') (ℓ-max ℓ ℓ')
  𝒮-G²LasAction' = ∫⟨ 𝒮-G²Las ℓ ℓ' ⟩ 𝒮ᴰ-G²Las\Action'


{-
-- THEOREM
-- DURGs can be lifted to be displayed over the total space of
-- another DURG on the same base URG

                 B
                 |
  B   C   Lift   C
   \ /     ↦    |
    A            A
-}


VerticalLift-𝒮ᴰ' : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                   {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                   {C : A → Type ℓC} (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
                   → URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
VerticalLift-𝒮ᴰ' {ℓ≅B = ℓ≅B} 𝒮-A {B = B} 𝒮ᴰ-B 𝒮ᴰ-C =
  urgstrᴰ (λ b (pA , _) b' → b ≅ᴰ⟨ pA ⟩ b')
          ρᴰ
          uniᴰ
  where open URGStrᴰ 𝒮ᴰ-B

{-
-- THEOREM
-- A tower of two DURGs can be reassociated

   C
   |
   B  split  B × C
   |   ↦      |
   A           A
(but C depends on B)


-}
splitTotal-𝒮ᴰ' : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                {C : Σ A B → Type ℓC} (𝒮ᴰ-C : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) C ℓ≅C)
                → URGStrᴰ 𝒮-A
                          (λ a → Σ[ b ∈ B a ] C (a , b))
                          (ℓ-max ℓ≅B ℓ≅C)
splitTotal-𝒮ᴰ' {A = A} 𝒮-A {B} 𝒮ᴰ-B {C} 𝒮ᴰ-C
  = make-𝒮ᴰ (λ (b , c) eA (b' , c') → Σ[ eB ∈ b B≅ᴰ⟨ eA ⟩ b' ] c ≅ᴰ⟨ eA , eB ⟩ c')
            (λ (b , c) → Bρᴰ b , ρᴰ c)
            {!!}
  where
    open URGStrᴰ 𝒮ᴰ-C
    open URGStr 𝒮-A
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B
    Bρᴰ = URGStrᴰ.ρᴰ 𝒮ᴰ-B
    Buniᴰ = URGStrᴰ.uniᴰ 𝒮ᴰ-B

{-
-- THEOREM
-- two DURGs over the same URGs can be combined

                 B
                 |
  B   C   Lift   C   split  B × C
   \ /     ↦    |     ↦     |
    A            A           A
-}
combine-𝒮ᴰ' : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
             {B : A → Type ℓB} {C : A → Type ℓC}
             (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
             (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
             → URGStrᴰ 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combine-𝒮ᴰ' {𝒮-A = 𝒮-A} 𝒮ᴰ-B 𝒮ᴰ-C = splitTotal-𝒮ᴰ 𝒮-A 𝒮ᴰ-B (VerticalLift-𝒮ᴰ 𝒮-A 𝒮ᴰ-C 𝒮ᴰ-B)


-- REMARK: DURG is equivalent to URG + morphism of URG via fibrant replacement

module _ (C : Type ℓ) where
  dispTypeIso :  Iso (C → Type ℓ) (Σ[ X ∈ Type ℓ ] (X → C))
  Iso.fun dispTypeIso D = (Σ[ c ∈ C ] D c) , fst
  Iso.inv dispTypeIso (X , F) c = Σ[ x ∈ X ] F x ≡ c
  Iso.leftInv dispTypeIso = {!!}
  Iso.rightInv dispTypeIso = {!!}

-- → combine is pullback in the (∞,1)-topos of DURGs

{-
With these operations we can construct the entire tree, but how
to get equivalences?


  PFXM                    PFG     VertComp
  |                       |      /
  |                       |     /
  isEquivar               isSecRet
  |                       |
  |                       |
  B                       B
  |                       |
  |                       |
  isAction                isSecRet
  |                       |
  |                       |
  LAS       F      B      F×B
  \         |      |      /
    \       |      |    /
      \     |      /   /
        \   |     /  /
            Grp
            |
            |
            Grp

-- For URGs: relational isomorphisms
-}

record RelIso' {A : Type ℓA} (_≅_ : Rel A A ℓ≅A)
              {A' : Type ℓA'} (_≅'_ : Rel A' A' ℓ≅A') : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A')) where
  constructor reliso'
  field
    fun : A → A'
    inv : A' → A
    rightInv : (a' : A') → fun (inv a') ≅' a'
    leftInv : (a : A) → inv (fun a) ≅ a

RelIso→Iso' : {A : Type ℓA} {A' : Type ℓA'}
             (_≅_ : Rel A A ℓ≅A) (_≅'_ : Rel A' A' ℓ≅A')
             {ρ : isRefl _≅_} {ρ' : isRefl _≅'_}
             (uni : isUnivalent _≅_ ρ) (uni' : isUnivalent _≅'_ ρ')
             (f : RelIso _≅_ _≅'_)
             → Iso A A'
Iso.fun (RelIso→Iso' _ _ _ _ f) = RelIso.fun f
Iso.inv (RelIso→Iso' _ _ _ _ f) = RelIso.inv f
Iso.rightInv (RelIso→Iso' _ _≅'_ {ρ' = ρ'} _ uni' f) a'
  = invEquiv (≡→R _≅'_ ρ' , uni' (RelIso.fun f (RelIso.inv f a')) a') .fst (RelIso.rightInv f a')
Iso.leftInv (RelIso→Iso' _≅_ _ {ρ = ρ} uni _ f) a
  = invEquiv (≡→R _≅_ ρ , uni (RelIso.inv f (RelIso.fun f a)) a) .fst (RelIso.leftInv f a)

{-
  For DURGs:
  pull back one of the DURGs
  along an equivalence and show that
  there is a fiberwise relational isomorphism
  between B and f*B'

  B   f*B' B'
  |  /     |
  | /      |
  A   ≃   A'
      f
-}
𝒮ᴰ-*-Iso-Over→TotalIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                         {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                         (ℱ : Iso A A')
                         {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                         {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                         (𝒢 : 𝒮ᴰ-♭PIso (Iso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                         → Iso (Σ A B) (Σ A' B')
𝒮ᴰ-*-Iso-Over→TotalIso  ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢
  = RelFiberIsoOver→Iso ℱ
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ-B .uniᴰ)
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B') (𝒮ᴰ-B' .uniᴰ)
                        𝒢
  where open URGStrᴰ



{-
  Let's apply this machinery to our tower of DURGs.
-}

import Cubical.DStructures.Equivalences.GroupSplitEpiAction
import Cubical.DStructures.Equivalences.PreXModReflGraph
import Cubical.DStructures.Equivalences.XModPeifferGraph
import Cubical.DStructures.Equivalences.PeifferGraphS2G

{-
 Grp × LAS × isAction   Grp × (F × B) × isSecRet
                 |     |
                  \    /
                   Grp



-}


