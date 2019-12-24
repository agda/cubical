{-# OPTIONS --cubical --postfix-projections #-}

module Cubical.Experiments.Category where

open import Cubical.CategoryTheory.Category
open import Cubical.CategoryTheory.Functor

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation


module _ {ℓ𝒞 ℓ𝒟 : Level} {𝒞 : Precategory ℓ𝒞} {𝒟 : Precategory ℓ𝒟} where
  record NatTrans (F G : Functor 𝒞 𝒟) : Type (ℓ-max ℓ𝒞 ℓ𝒟) where
    open Precategory
    open Functor

    field
      N-ob : (x : 𝒞 .ob) → 𝒟 .hom (F .F-ob x) (G .F-ob x)
      N-hom : {x y : 𝒞 .ob} (f : 𝒞 .hom x y) → 𝒟 .seq (F .F-hom f) (N-ob y) ≡ 𝒟 .seq (N-ob x) (G .F-hom f)


  open Precategory
  open Functor
  open NatTrans

  id-trans : (F : Functor 𝒞 𝒟) → NatTrans F F
  id-trans F .N-ob x = 𝒟 .idn (F .F-ob x)
  id-trans F .N-hom f =
     𝒟 .seq (F .F-hom f) (id-trans F .N-ob _)
       ≡⟨ 𝒟 .seq-ρ _ ⟩
     F .F-hom f
       ≡⟨ sym (𝒟 .seq-λ _) ⟩
     𝒟 .seq (𝒟 .idn (F .F-ob _)) (F .F-hom f)
       ∎


  seq-trans : {F G H : Functor 𝒞 𝒟} (α : NatTrans F G) (β : NatTrans G H) → NatTrans F H
  seq-trans α β .N-ob x = 𝒟 .seq (α .N-ob x) (β .N-ob x)
  seq-trans {F} {G} {H} α β .N-hom f =
    𝒟 .seq (F .F-hom f) (𝒟 .seq (α .N-ob _) (β .N-ob _))
      ≡⟨ sym (𝒟 .seq-α _ _ _) ⟩
    𝒟 .seq (𝒟 .seq (F .F-hom f) (α .N-ob _)) (β .N-ob _)
      ≡[ i ]⟨ 𝒟 .seq (α .N-hom f i) (β .N-ob _) ⟩
    𝒟 .seq (𝒟 .seq (α .N-ob _) (G .F-hom f)) (β .N-ob _)
      ≡⟨ 𝒟 .seq-α _ _ _ ⟩
    𝒟 .seq (α .N-ob _) (𝒟 .seq (G .F-hom f) (β .N-ob _))
      ≡[ i ]⟨ 𝒟 .seq (α .N-ob _) (β .N-hom f i) ⟩
    𝒟 .seq (α .N-ob _) (𝒟 .seq (β .N-ob _) (H .F-hom f))
      ≡⟨ sym (𝒟 .seq-α _ _ _) ⟩
    𝒟 .seq (𝒟 .seq (α .N-ob _) (β .N-ob _)) (H .F-hom f)
      ∎


module _ {ℓ𝒞 ℓ𝒟} (𝒞 : Precategory ℓ𝒞) (𝒟 : Precategory ℓ𝒟) ⦃ 𝒟-category : isCategory 𝒟 ⦄ where
  open Precategory
  open Functor
  open NatTrans

  module _ {F G : Functor 𝒞 𝒟} {α β : NatTrans F G} where
    build-nat-trans-path : α .N-ob ≡ β .N-ob → α ≡ β
    build-nat-trans-path p i .N-ob = p i
    build-nat-trans-path p i .N-hom f = rem i
      where
        rem : PathP (λ i → 𝒟 .seq (F .F-hom f) (p i _) ≡ 𝒟 .seq (p i _) (G .F-hom f)) (α .N-hom f) (β .N-hom f)
        rem = toPathP (𝒟-category .homIsSet _ _ _ _)


  FTR : Precategory (ℓ-max ℓ𝒞 ℓ𝒟)
  FTR .ob = Functor 𝒞 𝒟
  FTR .hom = NatTrans
  FTR .idn = id-trans
  FTR .seq = seq-trans
  FTR .seq-λ α = build-nat-trans-path λ i x → 𝒟 .seq-λ (α .N-ob x) i
  FTR .seq-ρ α = build-nat-trans-path λ i x → 𝒟 .seq-ρ (α .N-ob x) i
  FTR .seq-α α β γ = build-nat-trans-path λ i x → 𝒟 .seq-α (α .N-ob x) (β .N-ob x) (γ .N-ob x) i



module _ (ℓ : Level) where

  TYPE : Precategory (ℓ-suc ℓ)
  TYPE .ob = Type ℓ
  TYPE .hom A B = Lift (A → B)
  TYPE .idn A .lower x = x
  TYPE .seq (lift f) (lift g) .lower x = g (f x)
  TYPE .seq-λ f = refl
  TYPE .seq-ρ f = refl
  TYPE .seq-α f g h = refl

  SET : Precategory (ℓ-suc ℓ)
  SET .ob = Σ (Type ℓ) isSet
  SET .hom (A , _) (B , _) = Lift (A → B)
  SET .idn _ .lower x = x
  SET .seq (lift f) (lift g) .lower x = g (f x)
  SET .seq-λ f = refl
  SET .seq-ρ f = refl
  SET .seq-α f g h = refl

  isSetExpIdeal : {A B : Type ℓ} → isSet B → isSet (A → B)
  isSetExpIdeal B/set = hLevelPi 2 λ _ → B/set

  isSetLift : {A : Type ℓ} → isSet A → isSet (Lift {ℓ} {ℓ-suc ℓ} A)
  isSetLift = isOfHLevelLift 2

  instance
    SET-category : isCategory SET
    SET-category .homIsSet {_} {B , B/set} = isSetLift (isSetExpIdeal B/set)


  PSH : Precategory ℓ → Precategory (ℓ-suc ℓ)
  PSH 𝒞 = FTR (𝒞 ^op) SET

  liftExt : ∀ {ℓ'} {A : Type ℓ} {a b : Lift {ℓ} {ℓ'} A} → (lower a ≡ lower b) → a ≡ b
  liftExt x i = lift (x i)

  pairExt : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} (α : x .fst ≡ y .fst) (β : PathP (λ i → B (α i)) (x .snd) (y .snd)) → x ≡ y
  pairExt α β i .fst = α i
  pairExt α β i .snd = β i

  module YonedaEmbedding (𝒞 : Precategory ℓ) ⦃ 𝒞-cat : isCategory 𝒞 ⦄ where
    open Functor
    open NatTrans

    yo : 𝒞 .ob → Functor (𝒞 ^op) SET
    yo x .F-ob y .fst = 𝒞 .hom y x
    yo x .F-ob y .snd = 𝒞-cat .homIsSet
    yo x .F-hom f .lower g = 𝒞 .seq f g
    yo x .F-idn i .lower f = 𝒞 .seq-λ f i
    yo x .F-seq f g i .lower h = 𝒞 .seq-α g f h i

    YO : Functor 𝒞 (PSH 𝒞)
    YO .F-ob = yo
    YO .F-hom f .N-ob z .lower g = 𝒞 .seq g f
    YO .F-hom f .N-hom g i .lower h = 𝒞 .seq-α g h f i
    YO .F-idn = build-nat-trans-path _ _ λ i _ → lift λ f → 𝒞 .seq-ρ f i
    YO .F-seq f g = build-nat-trans-path _ _ λ i _ → lift λ h → 𝒞 .seq-α h f g (~ i)


    module _ {x} (F : Functor (𝒞 ^op) SET) where
      yo-yo-yo : NatTrans (yo x) F → F .F-ob x .fst
      yo-yo-yo α = α .N-ob _ .lower (𝒞 .idn _)

      no-no-no : F .F-ob x .fst → NatTrans (yo x) F
      no-no-no a .N-ob y .lower f = F .F-hom f .lower a
      no-no-no a .N-hom f = liftExt (funExt λ g i → F .F-seq g f i .lower a)

    module YonedaLemma {x} (F : Functor (𝒞 ^op) SET) where

      yo-iso : Iso (NatTrans (yo x) F) (F .F-ob x .fst)
      yo-iso .Iso.fun = yo-yo-yo F
      yo-iso .Iso.inv = no-no-no F
      yo-iso .Iso.rightInv b i = F .F-idn i .lower b
      yo-iso .Iso.leftInv a = build-nat-trans-path _ _ (funExt λ _ → liftExt (funExt rem))
        where
          rem : ∀ {z} (x₁ : 𝒞 .hom z x) → F .F-hom x₁ .lower (yo-yo-yo _ a) ≡ lower (a .N-ob z) x₁
          rem g =
            F .F-hom g .lower (yo-yo-yo _ a)
              ≡[ i ]⟨ a .N-hom g (~ i) .lower (𝒞 .idn x) ⟩
            a .N-hom g i0 .lower (𝒞 .idn x)
              ≡[ i ]⟨ a .N-ob _ .lower (𝒞 .seq-ρ g i) ⟩
            lower (a .N-ob _) g
              ∎


    YO-full : is-full YO
    YO-full x y F[f] = ∣ yo-yo-yo _ F[f] , YonedaLemma.yo-iso {x} (yo y) .Iso.leftInv F[f] ∣

    YO-faithful : is-faithful YO
    YO-faithful x y f g p i =
      hcomp
        (λ j → λ{ (i = i0) → 𝒞 .seq-λ f j; (i = i1) → 𝒞 .seq-λ g j})
        (yo-yo-yo _ (p i))
