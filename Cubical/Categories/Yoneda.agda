module Cubical.Categories.Yoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Function renaming (_∘_ to _◍_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Lift
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor

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

      -- takes an element x of F c and sends it to the (only) natural
      -- transformation which takes the identity to x
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
      theIso .sec x i = F .F-id i x
      theIso .ret α@(natTrans αo αh) =
        NatTrans-≡-intro (sym αo≡βo) (symP αh≡βh)
        where
          β = Ψ (ϕ α)
          βo = β .N-ob
          βh = β .N-hom

          -- equivalence of action on objects follows
          -- from simple equational reasoning using naturality
          αo≡βo : αo ≡ βo
          αo≡βo = funExt λ x → funExt λ f
                → αo x f
                -- expand into the bottom left of the naturality diagram
                ≡[ i ]⟨ αo x (C .⋆IdL f (~ i)) ⟩
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
              isProp-hom γ = isPropImplicitΠ2 λ x y → isPropΠ λ f →
                isSetHom (SET _)
                         {x = (C [ c , x ]) , C .isSetHom } {F ⟅ y ⟆} _ _

              isPropHomP : isOfHLevelDep 1 (λ ηo → NHType ηo)
              isPropHomP = isOfHLevel→isOfHLevelDep 1 λ a → isProp-hom a

  -- Naturality of the bijection

  -- in the functor
  -- it's equivalent to apply ϕ to α then do β ⟦ c ⟧
  -- or apply ϕ the the composite nat trans α ◍ β
  -- where ϕ takes a natural transformation to its representing element
  yonedaIsNaturalInFunctor : ∀ {F G : Functor C (SET ℓ')} (c : C .ob)
                     → (β : F ⇒ G)
                     → (fun (yoneda G c) ◍ compTrans β)
                       ≡ (β ⟦ c ⟧ ◍ fun (yoneda F c))
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

-- Yoneda for contravariant functors
module _ {C : Category ℓ ℓ'} where
  open Category
  import Cubical.Categories.NaturalTransformation
  open NatTrans
  yonedaᴾ : (F : Functor (C ^op) (SET ℓ'))
          → (c : C .ob)
          → Iso ((FUNCTOR (C ^op) (SET ℓ')) [ C [-, c ] , F ]) (fst (F ⟅ c ⟆))
  yonedaᴾ F c =
    ((FUNCTOR (C ^op) (SET ℓ')) [ C [-, c ] , F ]) Iso⟨ the-iso ⟩
    FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ] Iso⟨ yoneda F c ⟩
    (fst (F ⟅ c ⟆)) ∎Iso where

    to : FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ]
       → FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ]
    to α = natTrans (α .N-ob) (α .N-hom)

    fro : FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ]
        → FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ]
    fro β = natTrans (β .N-ob) (β .N-hom)

    the-iso : Iso (FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ])
              (FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ])
    the-iso = iso to fro (λ b → refl) λ a → refl

-- A more universe-polymorphic Yoneda lemma
yoneda* : {C : Category ℓ ℓ'}(F : Functor C (SET ℓ''))
        → (c : Category.ob C)
        → Iso ((FUNCTOR C (SET (ℓ-max ℓ' ℓ''))) [ LiftF ℓ'' ∘F (C [ c ,-])
                                                , LiftF ℓ'  ∘F F ])
              (fst (F ⟅ c ⟆))
yoneda* {ℓ}{ℓ'}{ℓ''}{C} F c =
  ((FUNCTOR C (SET (ℓ-max ℓ' ℓ''))) [ LiftF ℓ'' ∘F (C [ c ,-])
                                    , LiftF ℓ'  ∘F F ])
    Iso⟨ the-iso ⟩
  ((FUNCTOR (LiftHoms C ℓ'')
            (SET (ℓ-max ℓ' ℓ''))) [ (LiftHoms C ℓ'' [ c ,-])
                                  , LiftF ℓ' ∘F (F ∘F lowerHoms C ℓ'') ])
    Iso⟨ yoneda (LiftF ℓ' ∘F (F ∘F lowerHoms C ℓ'')) c ⟩
  Lift ℓ' (fst (F ⟅ c ⟆))
    Iso⟨ invIso LiftIso ⟩
  (fst (F ⟅ c ⟆)) ∎Iso where

  the-iso : Iso ((FUNCTOR C (SET (ℓ-max ℓ' ℓ'')))
                  [ LiftF ℓ'' ∘F (C [ c ,-])
                  , LiftF ℓ' ∘F F ])
                ((FUNCTOR (LiftHoms C ℓ'') (SET (ℓ-max ℓ' ℓ'')))
                  [ (LiftHoms C ℓ'' [ c ,-])
                  , LiftF ℓ' ∘F (F ∘F lowerHoms C ℓ'') ])
  the-iso .fun α .N-ob d f = α .N-ob d f
  the-iso .fun α .N-hom g = α .N-hom (g .lower)
  the-iso .inv β .N-ob d f = β .N-ob d f
  the-iso .inv β .N-hom g = β .N-hom (lift g)
  the-iso .sec β = refl
  the-iso .ret α = refl

yonedaᴾ* : {C : Category ℓ ℓ'}(F : Functor (C ^op) (SET ℓ''))
            → (c : Category.ob C)
            → Iso (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ''))
                    [ LiftF ℓ'' ∘F (C [-, c ])
                    , LiftF ℓ'  ∘F F ])
                  (fst (F ⟅ c ⟆))
yonedaᴾ* {ℓ}{ℓ'}{ℓ''}{C} F c =
  (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ''))
    [ LiftF ℓ'' ∘F (C [-, c ]) , LiftF ℓ' ∘F F ]) Iso⟨ the-iso ⟩
  (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ''))
    [ LiftF ℓ'' ∘F ((C ^op) [ c ,-])
    , LiftF  ℓ' ∘F F ]) Iso⟨ yoneda* F c ⟩
  fst (F ⟅ c ⟆) ∎Iso where

  the-iso :
    Iso (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ''))
          [ LiftF ℓ'' ∘F (C [-, c ]) , LiftF ℓ' ∘F F ])
        (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ''))
          [ LiftF ℓ'' ∘F ((C ^op) [ c ,-]) , LiftF ℓ' ∘F F ])
  the-iso .fun α .N-ob = α .N-ob
  the-iso .fun α .N-hom = α .N-hom
  the-iso .inv β .N-ob = β .N-ob
  the-iso .inv β .N-hom = β .N-hom
  the-iso .sec = λ b → refl
  the-iso .ret = λ a → refl
