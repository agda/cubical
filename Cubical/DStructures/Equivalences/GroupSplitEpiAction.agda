{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Equivalences.GroupSplitEpiAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary


open import Cubical.Structures.Subtype
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Group.Semidirect

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level

private
  -- this private module contains, over a group G₀ the definition of
  -- the types of split epis over G₀ and of the type of group actions
  -- of G₀ on groups G₁,
  -- as well as maps between those types
  module _ {ℓ : Level} (G₀ : Group {ℓ}) (ℓ' : Level) where
    private
      ℓℓ' = ℓ-max ℓ ℓ'

    GroupSplitEpi : Type (ℓ-suc ℓℓ')
    GroupSplitEpi = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ ι ∈ GroupHom G₀ G₁ ] Σ[ σ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι σ

    GroupAct : Type (ℓ-suc ℓℓ')
    GroupAct = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ _α_ ∈ LeftActionStructure ⟨ G₀ ⟩ ⟨ G₁ ⟩ ] (IsGroupAction G₀ G₁ _α_)

    GroupSplitEpi→GroupAct : GroupSplitEpi → GroupAct
    GroupSplitEpi→GroupAct (G₁ , ι , σ , isSplit) = ker-σ , _α_ , isAct
      where
        open GroupNotation₀ G₀
        open GroupNotation₁ G₁
        open IsGroupAction

        ker-σ : Group {ℓℓ'}
        ker-σ = ker σ

        _+ₖ_ = ker-σ ._+_

        _α_ : LeftActionStructure ⟨ G₀ ⟩ ⟨ ker-σ ⟩
        _α_ g (h , p) = (ig +₁ h) +₁ (-₁ ig) , q
          where
            ig = ι .fun g
            s = σ .fun
            abstract
              q = s ((ig +₁ h) +₁ (-₁ ig))
                    ≡⟨ σ .isHom (ig +₁ h) (-₁ ig) ⟩
                  (s (ig +₁ h)) +₀ s (-₁ ig)
                     ≡⟨ cong (s (ig +₁ h) +₀_) (mapInv σ ig) ⟩
                  (s (ig +₁ h)) +₀ (-₀ (s ig))
                     ≡⟨ cong (_+₀ -₀ (s ig)) (σ .isHom ig h) ⟩
                  ((s ig) +₀ (s h)) +₀ (-₀ (s ig))
                      ≡⟨ cong (λ z → ((s ig) +₀ z) +₀ (-₀ (s ig))) p ⟩
                  ((s ig) +₀ 0₀) +₀ (-₀ (s ig))
                      ≡⟨ cong (_+₀ -₀ (s ig)) (rId₀ (s ig)) ⟩
                  (s ig) +₀ (-₀ (s ig))
                     ≡⟨ rCancel₀ (s ig) ⟩
                  0₀ ∎

        isAct : IsGroupAction G₀ ker-σ _α_
        abstract
          -- (g α (ker-σ Group.+ h) h') ≡ (ker-σ Group.+ (g α h)) (g α h')
          isAct .isHom g (h , p) (h' , p') = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              ig = ι .fun g
              -ig = -₁ ig
              s = σ .fun
              abstract
                q = fst (g α ((h , p) +ₖ (h' , p')))
                        ≡⟨ refl ⟩
                    (ig +₁ (h +₁ h')) +₁ (-₁ ig)
                        ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) +₁ (-₁ ig)) ((sym (rId₁ h)) ∙ (cong (h +₁_) (sym (lCancel₁ ig)))) ⟩
                    (ig +₁ ((h +₁ (-ig +₁ ig)) +₁ h')) +₁ -ig
                        ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) +₁ -ig) (assoc₁ h -ig ig) ⟩
                    (ig +₁ (((h +₁ -ig) +₁ ig) +₁ h')) +₁ -ig
                        ≡⟨ cong (λ z → (ig +₁ z) +₁ -ig) (sym (assoc₁ (h +₁ -ig) ig h')) ⟩
                    (ig +₁ ((h +₁ -ig) +₁ (ig +₁ h'))) +₁ -ig
                        ≡⟨ cong (_+₁ -ig) (assoc₁ ig (h +₁ -ig) (ig +₁ h')) ⟩
                    ((ig +₁ (h +₁ -ig)) +₁ (ig +₁ h')) +₁ -ig
                        ≡⟨ cong (λ z → (z +₁ (ig +₁ h')) +₁ -ig) (assoc₁ ig h -ig) ⟩
                    (((ig +₁ h) +₁ -ig) +₁ (ig +₁ h')) +₁ -ig
                        ≡⟨ sym (assoc₁ ((ig +₁ h) +₁ -ig) (ig +₁ h') -ig) ⟩
                    ((ig +₁ h) +₁ -ig) +₁ ((ig +₁ h') +₁ -ig)
                        ≡⟨ refl ⟩
                    fst ((g α (h , p)) +ₖ (g α (h' , p'))) ∎
          isAct .identity (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              abstract
                q = fst (0₀ α (h , p))
                      ≡⟨ cong (λ z → (z +₁ h) +₁ (-₁ z)) (mapId ι) ⟩
                    (0₁ +₁ h) +₁ (-₁ 0₁)
                      ≡⟨ (cong ((0₁ +₁ h) +₁_) (invId G₁)) ∙∙ rId₁ (0₁ +₁ h) ∙∙ lId₁ h ⟩
                    h ∎
          -- (g +₀ g') α h ≡ g α (g' α h)
          isAct .assoc g g' (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              ig = ι .fun g
              ig' = ι .fun g'
              -ig = -₁ ig
              -ig' = -₁ ig'
              abstract
                q = (ι .fun (g +₀ g') +₁ h) +₁ (-₁ (ι .fun (g +₀ g')))
                       ≡⟨ cong (λ z → (z +₁ h) +₁ (-₁ z)) (ι .isHom g g') ⟩
                    ((ig +₁ ig') +₁ h) +₁ (-₁ (ig +₁ ig'))
                       ≡⟨ cong (((ig +₁ ig') +₁ h) +₁_) (invDistr G₁ ig ig') ⟩
                    ((ig +₁ ig') +₁ h) +₁ (-ig' +₁ -ig)
                      ≡⟨ cong (_+₁ (-ig' +₁ -ig)) (sym (assoc₁ ig ig' h)) ⟩
                    (ig +₁ (ig' +₁ h)) +₁ (-ig' +₁ -ig)
                      ≡⟨ assoc₁ (ig +₁ (ig' +₁ h)) -ig' -ig ⟩
                    ((ig +₁ (ig' +₁ h)) +₁ -ig') +₁ -ig
                      ≡⟨ cong (_+₁ -ig) (sym (assoc₁ ig (ig' +₁ h) -ig')) ⟩
                    fst (g α (g' α (h , p))) ∎

    GroupAct→GroupSplitEpi : GroupAct → GroupSplitEpi
    GroupAct→GroupSplitEpi (G₁ , _α_ , isAct) = G₁⋊G₀ , ι₂ α , π₂ α , π₂-hasSec α
      where
        α = groupaction _α_ isAct
        G₁⋊G₀ : Group {ℓℓ'}
        G₁⋊G₀ = G₁ ⋊⟨ α ⟩ G₀

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  -- the 𝒮-iso of the 𝒮-structures on the total space of split epis
  -- and that of group actions
  𝒮-Iso-GroupAct-SplitEpi : 𝒮-iso (𝒮-Action ℓ (ℓ-max ℓ ℓ')) (𝒮-SplitEpi ℓ (ℓ-max ℓ ℓ'))

  RelIso.fun 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , _α_) , isAct) =
    ((G₀ , fst se) , (fst (snd se)) , (fst (snd (snd se)))) , snd (snd (snd se))
    where
      se = GroupAct→GroupSplitEpi G₀ ℓ' (G₁ , _α_ , isAct)

  RelIso.inv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit) =
    ((G₀ , fst ga) , fst (snd ga)) , snd (snd ga)
    where
      ga = GroupSplitEpi→GroupAct G₀ ℓ' (G₁ , ι , σ , isSplit)

  RelIso.rightInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit) = ((G₀-≅ , G₁-≅) , ι-≅ , σ-≅) , isSplit-≅
    where
      -- get our hands dirty with shameless reference to what we're constructing
      -- TODO: Maybe, just maybe, define a ton of separate maps instead of GroupAct→GroupSplitEpi
      -- and the reverse map
      ga = RelIso.inv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit)
      se' = RelIso.fun 𝒮-Iso-GroupAct-SplitEpi ga

      -- get specific parts of the above
      kσ⋊G₀ = snd (fst (fst se'))
      _α_ = snd (fst ga)
      isAct = snd ga

      -- import notation
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁

      -- notational convention:
      -- g : ⟨ G₀ ⟩
      -- h : ⟨ G₁ ⟩
      -- p : witness that g is in ker σ

      𝓈 = σ .fun
      𝒾 = ι .fun

      -- G₀ ≃ G₀
      G₀-≅ = idGroupEquiv G₀

      -- (ker σ) ⋊⟨ Adᵢ ⟩ G₀ ≃ G₁
      G₁-≅ : GroupEquiv kσ⋊G₀ G₁
      GroupEquiv.eq G₁-≅ = isoToEquiv isom
        where

          isom : Iso ⟨ kσ⋊G₀ ⟩ ⟨ G₁ ⟩
          -- map forth is straight forward
          Iso.fun isom ((h , p) , g) = h +₁ 𝒾 g

          -- map back
          -- G₁ part of the map
          fst (fst (Iso.inv isom h)) = h +₁ 𝒾 (𝓈 (-₁ h))
          -- proof that G₁ part is in ker σ
          snd (fst (Iso.inv isom h)) = q
            where
              abstract
                q = 𝓈 (h +₁ 𝒾 (𝓈 (-₁ h)))
                      ≡⟨ σ .isHom h (𝒾 (𝓈 (-₁ h))) ⟩
                    𝓈 h +₀ 𝓈 (𝒾 (𝓈 (-₁ h)))
                      ≡⟨ cong (𝓈 h +₀_) (funExt⁻ (cong GroupHom.fun isSplit) (𝓈 (-₁ h))) ⟩
                    𝓈 h +₀ (𝓈 (-₁ h))
                      ≡⟨ cong (𝓈 h +₀_) (mapInv σ h) ⟩
                    𝓈 h +₀ (-₀ (𝓈 h))
                      ≡⟨ rCancel₀ (𝓈 h) ⟩
                    0₀ ∎
          -- G₀ part of the map
          snd (Iso.inv isom h) = 𝓈 h

          Iso.leftInv isom ((h , p) , g) = ΣPathP (subtypeWitnessIrrelevance (sg-typeProp σ) q , q')
            where
              abstract
                q = (h +₁ 𝒾 g) +₁ 𝒾 (𝓈 (-₁ (h +₁ 𝒾 g)))
                       ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 (𝓈 z)) (invDistr G₁ h (𝒾 g)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 (𝓈 ((-₁ (𝒾 g)) +₁ (-₁ h)))
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z) (σ .isHom (-₁ (𝒾 g)) (-₁ h)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 ((𝓈 (-₁ (𝒾 g))) +₀ (𝓈 (-₁ h)))
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 ((𝓈 (-₁ (𝒾 g))) +₀ z)) (mapInv σ h ∙∙ cong -₀_ p ∙∙ invId G₀) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 ((𝓈 (-₁ (𝒾 g))) +₀ 0₀)
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z) (rId₀ (𝓈 (-₁ (𝒾 g)))) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 (𝓈 (-₁ (𝒾 g)))
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z ) (mapInv σ (𝒾 g)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 (-₀ (𝓈 (𝒾 g)))
                      ≡⟨ cong ((h +₁ 𝒾 g) +₁_) (mapInv ι (𝓈 (𝒾 g))) ⟩
                    (h +₁ 𝒾 g) +₁ (-₁ (𝒾 (𝓈 (𝒾 g))))
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ (-₁ (𝒾 z))) (funExt⁻ (cong GroupHom.fun isSplit) g ) ⟩
                    (h +₁ 𝒾 g) +₁ (-₁ (𝒾 g))
                      ≡⟨ sym (assoc₁ h (𝒾 g) (-₁ (𝒾 g))) ⟩
                    h +₁ (𝒾 g +₁ (-₁ (𝒾 g)))
                      ≡⟨ cong (h +₁_) (rCancel₁ (𝒾 g)) ⟩
                    h +₁ 0₁
                      ≡⟨ rId₁ h ⟩
                    h ∎

                q' = 𝓈 (h +₁ 𝒾 g)
                       ≡⟨ σ .isHom h (𝒾 g) ⟩
                     𝓈 h +₀ 𝓈 (𝒾 g)
                       ≡⟨ cong (_+₀ 𝓈 (𝒾 g)) p ⟩
                     0₀ +₀ 𝓈 (𝒾 g)
                       ≡⟨ lId₀ (𝓈 (𝒾 g)) ⟩
                     𝓈 (𝒾 g)
                       ≡⟨ funExt⁻ (cong GroupHom.fun isSplit) g ⟩
                     g ∎

          Iso.rightInv isom h = q
            where
              ish = 𝒾 (𝓈 h)
              abstract
                q = (h +₁ 𝒾 (𝓈 (-₁ h))) +₁ ish
                       ≡⟨ cong (λ z → (h +₁ z) +₁ ish) (cong 𝒾 (mapInv σ h) ∙ mapInv ι (𝓈 h)) ⟩
                    (h +₁ (-₁ ish)) +₁ ish
                       ≡⟨ sym (assoc₁ h (-₁ ish) ish) ⟩
                    h +₁ ((-₁ ish) +₁ ish)
                       ≡⟨ (cong (h +₁_) (lCancel₁ ish)) ∙ (rId₁ h) ⟩
                    h ∎

      GroupEquiv.isHom G₁-≅ ((h , p) , g) ((h' , p') , g') = q
        where
          abstract
            q = (h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁ 𝒾 (g +₀ g')
                   ≡⟨ cong ((h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁_) (ι .isHom g g') ⟩
                (h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁ (𝒾 g +₁ 𝒾 g')
                   ≡⟨ sym (assoc₁ h ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g)) (𝒾 g +₁ 𝒾 g')) ⟩
                h +₁ (((𝒾 g +₁ h') +₁ (-₁ 𝒾 g)) +₁ (𝒾 g +₁ 𝒾 g'))
                   ≡⟨ cong (h +₁_) (sym (assoc₁ (𝒾 g +₁ h') (-₁ 𝒾 g) (𝒾 g +₁ 𝒾 g'))) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ ((-₁ 𝒾 g) +₁ (𝒾 g +₁ 𝒾 g')))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ z)) (assoc₁ (-₁ 𝒾 g) (𝒾 g) (𝒾 g')) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ (((-₁ 𝒾 g) +₁ 𝒾 g) +₁ 𝒾 g'))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ (z +₁ 𝒾 g'))) (lCancel₁ (𝒾 g)) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ (0₁ +₁ 𝒾 g'))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ z)) (lId₁ (𝒾 g')) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ 𝒾 g')
                   ≡⟨ cong (h +₁_) (sym (assoc₁ (𝒾 g) h' (𝒾 g'))) ⟩
                h +₁ (𝒾 g +₁ (h' +₁ 𝒾 g'))
                   ≡⟨ assoc₁ h (𝒾 g) (h' +₁ 𝒾 g') ⟩
                (h +₁ 𝒾 g) +₁ (h' +₁ 𝒾 g') ∎

      ι-≅ : (g : ⟨ G₀ ⟩) → 0₁ +₁ (𝒾 g) ≡ 𝒾 g
      ι-≅ g = lId₁ (𝒾 g)

      σ-≅ : (((h , _) , g) : ⟨ kσ⋊G₀ ⟩) → g ≡ 𝓈 (h +₁ 𝒾 g)
      σ-≅ ((h , p) , g) = q
        where
          abstract
            q = g
                  ≡⟨ funExt⁻ (cong fun (sym isSplit)) g ⟩
                𝓈 (𝒾 g)
                  ≡⟨ sym (lId₀ (𝓈 (𝒾 g))) ⟩
                0₀ +₀ 𝓈 (𝒾 g)
                  ≡⟨ cong (_+₀ 𝓈 (𝒾 g)) (sym p) ⟩
                𝓈 h +₀ 𝓈 (𝒾 g)
                  ≡⟨ sym (σ .isHom h (𝒾 g)) ⟩
                𝓈 (h +₁ 𝒾 g) ∎

      isSplit-≅ : Unit
      isSplit-≅ = tt

  RelIso.leftInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , _α_) , isAct) = ((G₀-≅ , G₁-≅) , α-≅) , isAct-≅
    where
      -- import notation
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      open ActionNotationα (groupaction _α_ isAct) using (α-id)

      se = RelIso.fun 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , _α_) , isAct)
      ga' = RelIso.inv 𝒮-Iso-GroupAct-SplitEpi se

      -- G₁ under fun and then inv
      ker-π₂ = snd (fst (fst ga'))
      -- the adjoint action w.t.r. ι₂
      _β_ = snd (fst ga')
      β-isAct = snd ga'
      -- inclusion of G₀ into G₁ ⋊⟨ α ⟩ G₀
      ι = ι₂ (groupaction _α_ isAct)
      𝒾 = ι .fun


      G₀-≅ : GroupEquiv G₀ G₀
      G₀-≅ = idGroupEquiv G₀

      G₁-≅ : GroupEquiv ker-π₂ G₁
      GroupEquiv.eq G₁-≅ = isoToEquiv isom
        where
          isom : Iso ⟨ ker-π₂ ⟩ ⟨ G₁ ⟩
          Iso.fun isom ((h , g) , p) = h
          Iso.inv isom h = (h , 0₀) , refl
          Iso.leftInv isom ((h , g) , p) = q
            where
              abstract
                r = ΣPathP (refl , sym p)
                q = ΣPathP (r , isProp→PathP (λ i → set₀ (snd (r i)) 0₀) refl p)
                -- q = subtypeWitnessIrrelevance (sg-typeProp {!π₂ (groupaction _α_ isAct)!}) {!!}
                -- q = Σ≡Prop (λ (h , g) → {!set₀g 0₀ !}) {!!}
          Iso.rightInv isom h = refl

      GroupEquiv.isHom G₁-≅ ((h , g) , p) ((h' , g') , p') = q
        where
          abstract
            q : h +₁ (g α h') ≡ h +₁ h'
            q = h +₁ (g α h')
                  ≡⟨ cong (λ z → h +₁ (z α h')) p ⟩
                h +₁ (0₀ α h')
                  ≡⟨ cong (h +₁_) (α-id h') ⟩
                h +₁ h' ∎

      α-≅ : (g : ⟨ G₀ ⟩) (((h , g') , p) : ⟨ ker-π₂ ⟩)
            → GroupEquiv.eq G₁-≅ .fst (g β ((h , g') , p)) ≡ g α h
      α-≅ g ((h , g') , p) = q
        where
          open ActionLemmas (groupaction _α_ isAct)
          abstract
            q = (0₁ +₁ (g α h)) +₁ ((g +₀ g') α ((-₀ g) α (-₁ 0₁)))
                  ≡⟨ cong (_+₁ ((g +₀ g') α ((-₀ g) α (-₁ 0₁)))) (lId₁ (g α h)) ⟩
                (g α h) +₁ ((g +₀ g') α ((-₀ g) α (-₁ 0₁)))
                  ≡⟨ cong (λ z → (g α h) +₁ ((g +₀ g') α ((-₀ g) α z))) (invId G₁) ⟩
                (g α h) +₁ ((g +₀ g') α ((-₀ g) α 0₁))
                  ≡⟨ cong (λ z → (g α h) +₁ ((g +₀ g') α z)) (actOnUnit (-₀ g)) ⟩
                (g α h) +₁ ((g +₀ g') α 0₁)
                  ≡⟨ cong ((g α h) +₁_) (actOnUnit (g +₀ g')) ⟩
                (g α h) +₁ 0₁
                  ≡⟨ rId₁ (g α h) ⟩
                g α h ∎

      isAct-≅ : Unit
      isAct-≅ = tt

  IsoActionSplitEpi : Iso (Action ℓ ℓℓ') (SplitEpi ℓ ℓℓ')
  IsoActionSplitEpi = 𝒮-iso→Iso (𝒮-Action ℓ ℓℓ') (𝒮-SplitEpi ℓ ℓℓ') 𝒮-Iso-GroupAct-SplitEpi
