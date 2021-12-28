{-# OPTIONS --safe #-}
module Cubical.Categories.Yoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Function renaming (_∘_ to _◍_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

private
  variable
    ℓ ℓ' ℓ'' : Level

-- THE YONEDA LEMMA

open NatTrans
open NatTransP
open Functor
open Iso

module _ {C : Category ℓ ℓ'} where
  open Category

  yoneda : (F : Functor C (SET ℓ'))
         → (c : C .ob)
         → Iso ((FUNCTOR C (SET ℓ')) [ C [ c ,-] , F ]) (fst (F ⟅ c ⟆))
  yoneda F c = theIso
    where
      natType = (FUNCTOR C (SET ℓ')) [ C [ c ,-] , F ]
      setType = fst (F ⟅ c ⟆)

      -- takes a natural transformation to what it does on id
      ϕ : natType → setType
      ϕ α = (α ⟦ _ ⟧) (C .id)

      -- takes an element x of F c and sends it to the (only) natural transformation
      -- which takes the identity to x
      Ψ : setType → natType
      Ψ x .N-ob c = λ f → (F ⟪ f ⟫) x
      Ψ x .N-hom g
        = funExt (λ f → (F ⟪ f ⋆⟨ C ⟩ g ⟫) x
                      ≡[ i ]⟨ (F .F-seq f g) i x ⟩
                        (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
                      ∎)

      theIso : Iso natType setType
      theIso .fun = ϕ
      theIso .inv = Ψ
      theIso .rightInv x i = F .F-id i x
      theIso .leftInv α@(natTrans αo αh) = NatTrans-≡-intro (sym αo≡βo) (symP αh≡βh)
        where
          β = Ψ (ϕ α)
          βo = β .N-ob
          βh = β .N-hom

          -- equivalence of action on objects follows
          -- from simple equational reasoning using naturality
          αo≡βo : αo ≡ βo
          αo≡βo = funExt λ x → funExt λ f
                → αo x f
                ≡[ i ]⟨ αo x (C .⋆IdL f (~ i)) ⟩ -- expand into the bottom left of the naturality diagram
                  αo x (C .id ⋆⟨ C ⟩ f)
                ≡[ i ]⟨ αh f i (C .id) ⟩ -- apply naturality
                  (F ⟪ f ⟫) ((αo _) (C .id))
                ∎

          -- type aliases for natural transformation
          NOType = N-ob-Type (C [ c ,-]) F
          NHType = N-hom-Type (C [ c ,-]) F

          -- equivalence of commutative squares follows from SET being a Category
          αh≡βh : PathP (λ i → NHType (αo≡βo i)) αh βh -- αh βh
          αh≡βh = isPropHomP αh βh αo≡βo
            where
              isProp-hom : (ϕ : NOType) → isProp (NHType ϕ)
              isProp-hom γ = isPropImplicitΠ2 λ x y → isPropΠ λ f → isSetHom (SET _) {x = (C [ c , x ]) , C .isSetHom } {F ⟅ y ⟆} _ _

              isPropHomP : isOfHLevelDep 1 (λ ηo → NHType ηo)
              isPropHomP = isOfHLevel→isOfHLevelDep 1 λ a → isProp-hom a

  -- Naturality of the bijection

  -- in the functor
  -- it's equivalent to apply ϕ to α then do β ⟦ c ⟧
  -- or apply ϕ the the composite nat trans α ◍ β
  -- where ϕ takes a natural transformation to its representing element
  yonedaIsNaturalInFunctor : ∀ {F G : Functor C (SET ℓ')} (c : C .ob)
                     → (β : F ⇒ G)
                     → (fun (yoneda G c) ◍ compTrans β) ≡ (β ⟦ c ⟧ ◍ fun (yoneda F c))
  yonedaIsNaturalInFunctor {F = F} {G} c β = funExt λ α → refl

  -- in the object
  -- it's equivalent to apply ϕ and then F ⟪ f ⟫
  -- or to apply ϕ to the natural transformation obtained by precomposing with f
  yonedaIsNaturalInOb : ∀ {F : Functor C (SET ℓ')}
                      → (c c' : C .ob)
                      → (f : C [ c , c' ])
                      → yoneda F c' .fun ◍ preComp f ≡ F ⟪ f ⟫ ◍ yoneda F c .fun
  yonedaIsNaturalInOb {F = F} c c' f = funExt (λ α
                             → (yoneda F c' .fun ◍ preComp f) α
                             ≡⟨ refl ⟩
                               (α ⟦ c' ⟧) (f ⋆⟨ C ⟩ C .id)
                             ≡[ i ]⟨ (α ⟦ c' ⟧) (C .⋆IdR f i) ⟩
                               (α ⟦ c' ⟧) f
                             ≡[ i ]⟨ (α ⟦ c' ⟧) (C .⋆IdL f (~ i)) ⟩
                               (α ⟦ c' ⟧) (C .id ⋆⟨ C ⟩ f)
                             ≡[ i ]⟨ (α .N-hom f i) (C .id) ⟩
                               (F ⟪ f ⟫) ((α ⟦ c ⟧) (C .id))
                             ≡⟨ refl ⟩
                               ((F ⟪ f ⟫) ◍ yoneda F c .fun) α
                             ∎)

-- Yoneda embedding
-- TODO: probably want to rename/refactor
module _ {C : Category ℓ ℓ} where
  open Functor
  open NatTrans
  open Category C

  yo : ob → Functor (C ^op) (SET ℓ)
  yo x .F-ob y .fst = C [ y , x ]
  yo x .F-ob y .snd = isSetHom
  yo x .F-hom f g = f ⋆⟨ C ⟩ g
  yo x .F-id i f = ⋆IdL f i
  yo x .F-seq f g i h = ⋆Assoc g f h i

  YO : Functor C (PreShv C ℓ)
  YO .F-ob = yo
  YO .F-hom f .N-ob z g = g ⋆⟨ C ⟩ f
  YO .F-hom f .N-hom g i h = ⋆Assoc g h f i
  YO .F-id = makeNatTransPath λ i _ → λ f → ⋆IdR f i
  YO .F-seq f g = makeNatTransPath λ i _ → λ h → ⋆Assoc h f g (~ i)


  module _ {x} (F : Functor (C ^op) (SET ℓ)) where
    yo-yo-yo : NatTrans (yo x) F → F .F-ob x .fst
    yo-yo-yo α = α .N-ob _ id

    no-no-no : F .F-ob x .fst → NatTrans (yo x) F
    no-no-no a .N-ob y f = F .F-hom f a
    no-no-no a .N-hom f = funExt λ g i → F .F-seq g f i a

    yoIso : Iso (NatTrans (yo x) F) (F .F-ob x .fst)
    yoIso .Iso.fun = yo-yo-yo
    yoIso .Iso.inv = no-no-no
    yoIso .Iso.rightInv b i = F .F-id i b
    yoIso .Iso.leftInv a = makeNatTransPath (funExt λ _ → funExt rem)
      where
        rem : ∀ {z} (x₁ : C [ z , x ]) → F .F-hom x₁ (yo-yo-yo a) ≡ (a .N-ob z) x₁
        rem g =
          F .F-hom g (yo-yo-yo a)
            ≡[ i ]⟨ a .N-hom g (~ i) id ⟩
          a .N-hom g i0 id
            ≡[ i ]⟨ a .N-ob _ (⋆IdR g i) ⟩
          (a .N-ob _) g
            ∎

    yoEquiv : NatTrans (yo x) F ≃ F .F-ob x .fst
    yoEquiv = isoToEquiv yoIso


  isFullYO : isFull YO
  isFullYO x y F[f] = ∣ yo-yo-yo _ F[f] , yoIso {x} (yo y) .Iso.leftInv F[f] ∣

  isFaithfulYO : isFaithful YO
  isFaithfulYO x y f g p i =
    hcomp
      (λ j → λ{ (i = i0) → ⋆IdL f j; (i = i1) → ⋆IdL g j})
      (yo-yo-yo _ (p i))
