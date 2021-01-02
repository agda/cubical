{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Yoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' ℓ'' : Level

-- THE YONEDA LEMMA

open Precategory
open NatTrans
open NatTransP
open Functor
open Iso

-- question: is Functor a category? because we need the Type of natural transforms to be a Set
-- answer: yes indeed

-- function composition??
_●_ : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → (A → C)
(g ● f) x = g (f x)


module _ (A B : Type ℓ) (f : A → B) where

  isInj = ∀ (x y : A) → (f x ≡ f y) → x ≡ y
  isSurj = ∀ (b : B) → Σ[ a ∈ A ] f a ≡ b

  bijectionToIso : isInj × isSurj
                 → isIso f
  bijectionToIso (i , s) = (λ b → fst (s b)) , (λ b → snd (s b)) , λ a → i (fst (s (f a))) a (snd (s (f a)))

module _ {C : Precategory ℓ ℓ'} ⦃ isCatC : isCategory C ⦄ where
  yoneda : (F : Functor C (SET ℓ'))
         → (c : C .ob)
         → Iso ((FUNCTOR C (SET ℓ')) [ C [ c ,-] , F ]) (fst (F ⟅ c ⟆)) -- (Lift {ℓ'} {ℓ} (fst (F ⟅ c ⟆)))
  yoneda F c = theIso
    where
      natType = (FUNCTOR C (SET ℓ')) [ C [ c ,-] , F ]
      setType = fst (F ⟅ c ⟆)

      -- takes a natural transformation to what it does on id
      ϕ : natType → setType
      ϕ α = (α ⟦ _ ⟧) (C .id c)

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
                  αo x (C .id c ⋆⟨ C ⟩ f)
                ≡[ i ]⟨ αh f i (C .id c) ⟩ -- apply naturality
                  (F ⟪ f ⟫) ((αo _) (C .id c))
                ∎

          -- type aliases for natural transformation
          NOType = N-ob-Type (C [ c ,-]) F
          NHType = N-hom-Type (C [ c ,-]) F

          -- equivalence of commutative squares follows from SET being a Category
          αh≡βh : PathP (λ i → NHType (αo≡βo i)) αh βh -- αh βh
          αh≡βh = isPropHomP αh βh αo≡βo
            where
              isProp-hom : ⦃ isCatSET : isCategory (SET ℓ') ⦄ → (ϕ : NOType) → isProp (NHType ϕ)
              isProp-hom ⦃ isCatSET ⦄ γ = isPropImplicitΠ λ x
                                        → isPropImplicitΠ λ y
                                        → isPropΠ λ f
                                        → isCatSET .isSetHom {x = (C [ c , x ]) , (isCatC .isSetHom)} {F ⟅ y ⟆} _ _

              isPropHomP : isOfHLevelDep 1 (λ ηo → NHType ηo)
              isPropHomP = isOfHLevel→isOfHLevelDep 1 λ a → isProp-hom a

  -- Naturality of the bijection

  -- in the functor
  -- it's equivalent to apply ϕ to α then do β ⟦ c ⟧
  -- or apply ϕ the the composite nat trans α ● β
  -- where ϕ takes a natural transformation to its representing element
  yonedaIsNaturalInFunctor : ∀ {F G : Functor C (SET ℓ')} (c : C .ob)
                     → (β : F ⇒ G)
                     → (fun (yoneda G c) ● compTrans β) ≡ (β ⟦ c ⟧ ● fun (yoneda F c))
  yonedaIsNaturalInFunctor {F = F} {G} c β = funExt λ α → refl

  -- in the object
  -- it's equivalent to apply ϕ and then F ⟪ f ⟫
  -- or to apply ϕ to the natural transformation obtained by precomposing with f
  yonedaIsNaturalInOb : ∀ {F : Functor C (SET ℓ')}
                      → (c c' : C .ob)
                      → (f : C [ c , c' ])
                      → yoneda F c' .fun ● preComp f ≡ F ⟪ f ⟫ ● yoneda F c .fun
  yonedaIsNaturalInOb {F = F} c c' f = funExt (λ α
                             → (yoneda F c' .fun ● preComp f) α
                             ≡⟨ refl ⟩
                               (α ⟦ c' ⟧) (f ⋆⟨ C ⟩ C .id c')
                             ≡[ i ]⟨ (α ⟦ c' ⟧) (C .⋆IdR f i) ⟩
                               (α ⟦ c' ⟧) f
                             ≡[ i ]⟨ (α ⟦ c' ⟧) (C .⋆IdL f (~ i)) ⟩
                               (α ⟦ c' ⟧) (C .id c ⋆⟨ C ⟩ f)
                             ≡[ i ]⟨ (α .N-hom f i) (C .id c) ⟩
                               (F ⟪ f ⟫) ((α ⟦ c ⟧) (C .id c))
                             ≡⟨ refl ⟩
                               ((F ⟪ f ⟫) ● yoneda F c .fun) α
                             ∎)
