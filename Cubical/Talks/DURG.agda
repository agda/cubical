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

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓP : Level

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
  B
  |  ↦ A × B
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
            B
  A, B  ↦  |   ↦ A × B
            A
-}

-- EXAMPLE
-- Group Homomorphisms displayed over pairs of groups

𝒮ᴰ-G²\F' : URGStrᴰ (𝒮-group' ℓ ×𝒮 𝒮-group' ℓ')
                  (λ (G , H) → GroupHom G H)
                  (ℓ-max ℓ ℓ')
𝒮ᴰ-G²\F' =
    make-𝒮ᴰ (λ {(G , H)} {(G' , H')} f (eG , eH) f' → (g : ⟨ G ⟩) → GroupEquiv.eq eH .fst ((f .fun) g) ≡ (f' .fun) (GroupEquiv.eq eG .fst g))
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

  Crossed module

  α : Action G₀ H
  φ : G₀ ← H

  Strict 2-Group
  internal category in the category of groups

  diagrams
  maps
  levels



  PFXM
  |
  |
  Equivar.
  |
  |
  B
  |
  |
  isAction
  |
  |
  LAS       F      B      F×B


              Grp
               |
               |
               Grp






































-}
















-- THEOREM
-- Subtypes have a simple DURG structure given by 𝟙
-- This makes it easy to impose axioms on a structure
Subtype→Sub-𝒮ᴰ : {A : Type ℓA}
                 → (P : A → hProp ℓP)
                 → (𝒮-A : URGStr A ℓ≅A)
                 → URGStrᴰ 𝒮-A (λ a → P a .fst) ℓ-zero
Subtype→Sub-𝒮ᴰ P StrA =
  make-𝒮ᴰ (λ _ _ _ → Unit)
          (λ _ → tt)
          (λ a p → isContrRespectEquiv (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                        (inhProp→isContr p (P a .snd)))
