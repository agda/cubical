{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Equivalences.GroupSplitEpiAction where

open import Cubical.Foundations.Prelude
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

module _ (ℓ ℓ' : Level) where
  -- the 𝒮-iso of the 𝒮-structures on the type of
  -- group actions and that of split epis
  𝒮-Iso-GroupAct-SplitEpi : 𝒮-iso (𝒮-Action ℓ (ℓ-max ℓ ℓ')) (𝒮-SplitEpi ℓ (ℓ-max ℓ ℓ'))

  -- GroupAction → Split Epimorphism
  -- Given the action α, form the semidirect product attached to α,
  -- and show that the second projection out of H ⋊⟨ α ⟩ G₀
  -- is a split epi with section the right inclusion of G₀
  RelIso.fun 𝒮-Iso-GroupAct-SplitEpi (((G₀ , H) , _α_) , isAct) = ((G₀ , H⋊G₀) , (ι₂ α , π₂ α)) , π₂-hasSec α
      where
        -- combine the action structure and axioms
        α = groupaction _α_ isAct
        -- semidirect product induced by the action α
        H⋊G₀ : Group {ℓ-max ℓ ℓ'}
        H⋊G₀ = H ⋊⟨ α ⟩ G₀
  -- end of RelIso.fun 𝒮-Iso-GroupAct-SplitEpi (((G₀ , H) , _α_) , isAct)

  -- split epimorphism → group action
  RelIso.inv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit) = ((G₀ , ker-σ) , _α_) , isAct
      where
        open GroupNotation₀ G₀
        open GroupNotation₁ G₁
        open SplitEpiNotation ι σ isSplit
        open IsGroupAction

        -- G₀ will act on ker σ
        ker-σ : Group {ℓ-max ℓ ℓ'}
        ker-σ = ker σ

        -- notation: group operation of ker σ
        _+ₖ_ = ker-σ ._+_

        -- the left action structure of G₀ on ker σ
        -- is given by
        -- g α h := ιg + h - ιg
        _α_ : LeftActionStructure ⟨ G₀ ⟩ ⟨ ker-σ ⟩
        g α (h , p) = (ig +₁ h) -₁ ig , q
          where
            ig = 𝒾 g
            abstract
              -- proof that (ig +₁ h) -₁ ig
              -- lies in ker-σ
              q = s ((ig +₁ h) -₁ ig)
                    ≡⟨ σ .isHom (ig +₁ h) (-₁ ig) ⟩
                  s (ig +₁ h) +₀ s (-₁ ig)
                     ≡⟨ cong (s (ig +₁ h) +₀_)
                             (mapInv σ ig) ⟩
                  s (ig +₁ h) -₀ si g
                     ≡⟨ cong (_+₀ -₀ (s ig))
                             (σ .isHom ig h) ⟩
                  (si g +₀ s h) -₀ si g
                      ≡⟨ cong (λ z → ((si g) +₀ z) -₀ (si g))
                              p ⟩
                  ((si g) +₀ 0₀) -₀ (si g)
                      ≡⟨ cong (_+₀ -₀ (s ig))
                              (rId₀ (s ig)) ⟩
                  (si g) -₀ (si g)
                     ≡⟨ rCancel₀ (si g) ⟩
                  0₀ ∎

        -- proof that the left action structure α
        -- satisfies the group action axioms
        abstract
          isAct : IsGroupAction G₀ ker-σ _α_
          -- at every g, g α_ is a homomorphism, that is
          -- g α (h + h') ≡ g α h + g α h'
          isAct .isHom g (h , p) (h' , p') = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              ig = ι .fun g
              -ig = -₁ ig
              q = fst (g α ((h , p) +ₖ (h' , p')))
                      ≡⟨ refl ⟩
                  (ig +₁ (h +₁ h')) -₁ ig
                      ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) +₁ (-₁ ig))
                              (sym (rId₁ h)
                                ∙ cong (h +₁_) (sym (lCancel₁ ig))) ⟩
                  (ig +₁ ((h +₁ (-ig +₁ ig)) +₁ h')) -₁ ig
                      ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) -₁ ig)
                              (assoc₁ h -ig ig) ⟩
                  (ig +₁ (((h +₁ -ig) +₁ ig) +₁ h')) -₁ ig
                      ≡⟨ cong (λ z → (ig +₁ z) -₁ ig)
                              (sym (assoc₁ (h -₁ ig) ig h')) ⟩
                  (ig +₁ ((h +₁ -ig) +₁ (ig +₁ h'))) -₁ ig
                      ≡⟨ cong (_+₁ -ig)
                              (assoc₁ ig (h -₁ ig) (ig +₁ h')) ⟩
                  ((ig +₁ (h +₁ -ig)) +₁ (ig +₁ h')) -₁ ig
                       ≡⟨ cong (λ z → (z +₁ (ig +₁ h')) -₁ ig)
                               (assoc₁ ig h -ig) ⟩
                  (((ig +₁ h) +₁ -ig) +₁ (ig +₁ h')) -₁ ig
                    ≡⟨ sym (assoc₁ ((ig +₁ h) -₁ ig) (ig +₁ h') -ig) ⟩
                  ((ig +₁ h) +₁ -ig) +₁ ((ig +₁ h') +₁ -ig)
                       ≡⟨ refl ⟩
                  fst ((g α (h , p)) +ₖ (g α (h' , p'))) ∎
          -- α satisfies the identity law, that is
          -- 0 α h = h for every h
          isAct .identity (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              q = fst (0₀ α (h , p))
                      ≡⟨ cong (λ z → (z +₁ h) +₁ (-₁ z))
                              (mapId ι) ⟩
                  (0₁ +₁ h) +₁ (-₁ 0₁)
                    ≡⟨ cong ((0₁ +₁ h) +₁_)
                            (invId G₁) ∙∙
                       rId₁ (0₁ +₁ h) ∙∙
                       lId₁ h ⟩
                  h ∎
          -- α is associative in the sense that
          -- (g +₀ g') α h = g α (g' α h)
          isAct .assoc g g' (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
            where
              ig = ι .fun g
              ig' = ι .fun g'
              -ig = -₁ ig
              -ig' = -₁ ig'
              q = (ι .fun (g +₀ g') +₁ h) -₁ (ι .fun (g +₀ g'))
                     ≡⟨ cong (λ z → (z +₁ h) -₁ z)
                             (ι .isHom g g') ⟩
                  ((ig +₁ ig') +₁ h) -₁ (ig +₁ ig')
                    ≡⟨ cong (((ig +₁ ig') +₁ h) +₁_)
                            (invDistr G₁ ig ig') ⟩
                  ((ig +₁ ig') +₁ h) +₁ (-ig' -₁ ig)
                    ≡⟨ cong (_+₁ (-ig' +₁ -ig))
                            (sym (assoc₁ ig ig' h)) ⟩
                  (ig +₁ (ig' +₁ h)) +₁ (-ig' -₁ ig)
                    ≡⟨ assoc₁ (ig +₁ (ig' +₁ h)) -ig' -ig ⟩
                  ((ig +₁ (ig' +₁ h)) -₁ ig') -₁ ig
                    ≡⟨ cong (_+₁ -ig)
                            (sym (assoc₁ ig (ig' +₁ h) -ig')) ⟩
                  fst (g α (g' α (h , p))) ∎
        -- end of abstract
  -- end of RelIso.inv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit)

  RelIso.rightInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit) = ((G₀-≅ , G₁-≅) , ι-≅ , σ-≅) , isSplit-≅
    where
      -- get our hands dirty with shameless reference to what we're constructing,
      -- such is the power of copatterns!
      -- back: turn the given split epi into the group action tuple ga
      ga = RelIso.inv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit)
      -- map ga forth to the split epi tuple se'
      se' = RelIso.fun 𝒮-Iso-GroupAct-SplitEpi ga

      -- notation

      -- short for (ker σ) ⋊⟨ Adᵢ ⟩ G₀
      kσ⋊G₀ = snd (fst (fst se'))
      -- the group action ga
      _α_ = snd (fst ga)
      isAct = snd ga

      open GroupNotation₀ G₀
      open GroupNotation₁ G₁

      -- notational convention:
      -- g : ⟨ G₀ ⟩
      -- h : ⟨ G₁ ⟩
      -- p : witness that g is in ker σ

      open SplitEpiNotation ι σ isSplit

      -- G₀ ≃ G₀
      G₀-≅ = idGroupEquiv G₀

      -- (ker σ) ⋊⟨ Adᵢ ⟩ G₀ ≃ G₁
      G₁-≅ : GroupEquiv kσ⋊G₀ G₁
      GroupEquiv.eq G₁-≅ = isoToEquiv isom
        where
          isom : Iso ⟨ kσ⋊G₀ ⟩ ⟨ G₁ ⟩
          -- map forth is straight forward
          Iso.fun isom ((h , p) , g) = h +₁ 𝒾 g

          -- beginning of Iso.inv isom h

          -- G₁ part of the map
          fst (fst (Iso.inv isom h)) = h +₁ (is- h)
          -- proof that G₁ part is in ker σ
          snd (fst (Iso.inv isom h)) = q
            where
              abstract
                q = s (h +₁ is- h)
                      ≡⟨ σ .isHom h (is- h) ⟩
                    s h +₀ s (is- h)
                      ≡⟨ cong (s h +₀_)
                              (funExt⁻ (cong GroupHom.fun isSplit) (s- h)) ⟩
                    s h +₀ (s- h)
                      ≡⟨ cong (s h +₀_)
                              (mapInv σ h) ⟩
                    s h -₀ (s h)
                      ≡⟨ rCancel₀ (s h) ⟩
                    0₀ ∎
          -- G₀ part of the map
          snd (Iso.inv isom h) = s h

          -- end of Iso.inv isom h

          -- beginning of Iso.leftInv isom ((h , p) , g)

          Iso.leftInv isom ((h , p) , g) = ΣPathP (subtypeWitnessIrrelevance (sg-typeProp σ) q , q')
            where
              abstract
                q = (h +₁ 𝒾 g) +₁ is- (h +₁ 𝒾 g)
                       ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ is z)
                               (invDistr G₁ h (𝒾 g)) ⟩
                    (h +₁ 𝒾 g) +₁ is ((-i g) -₁ h)
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z)
                              (σ .isHom (-i g) (-₁ h)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 ((s-i g) +₀ (s- h))
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 ((s-i g) +₀ z))
                              (mapInv σ h ∙∙
                               cong -₀_ p ∙∙
                               invId G₀) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 ((s-i g) +₀ 0₀)
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z)
                              (rId₀ (s-i g)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 (s-i g)
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) +₁ 𝒾 z )
                              (mapInv σ (𝒾 g)) ⟩
                    (h +₁ 𝒾 g) +₁ 𝒾 (-si g)
                      ≡⟨ cong ((h +₁ 𝒾 g) +₁_)
                              (mapInv ι (si g)) ⟩
                    (h +₁ 𝒾 g) -₁ (isi g)
                      ≡⟨ cong (λ z → (h +₁ 𝒾 g) -₁ (𝒾 z))
                              (funExt⁻ (cong GroupHom.fun isSplit) g ) ⟩
                    (h +₁ 𝒾 g) -₁ (𝒾 g)
                      ≡⟨ sym (assoc₁ h (𝒾 g) (-i g)) ⟩
                    h +₁ (𝒾 g -₁ (𝒾 g))
                      ≡⟨ cong (h +₁_)
                              (rCancel₁ (𝒾 g)) ⟩
                    h +₁ 0₁
                      ≡⟨ rId₁ h ⟩
                    h ∎

                q' = s (h +₁ 𝒾 g)
                       ≡⟨ σ .isHom h (𝒾 g) ⟩
                     s h +₀ si g
                       ≡⟨ cong (_+₀ si g) p ⟩
                     0₀ +₀ si g
                       ≡⟨ lId₀ (si g) ⟩
                     si g
                       ≡⟨ funExt⁻ (cong GroupHom.fun isSplit) g ⟩
                     g ∎

          -- end of Iso.leftInv isom ((h , p) , g)

          Iso.rightInv isom h = q
            where
              ish = 𝒾 (s h)
              abstract
                q = (h +₁ 𝒾 (s (-₁ h))) +₁ ish
                       ≡⟨ cong (λ z → (h +₁ z) +₁ ish) (cong 𝒾 (mapInv σ h) ∙ mapInv ι (s h)) ⟩
                    (h +₁ (-₁ ish)) +₁ ish
                       ≡⟨ sym (assoc₁ h (-₁ ish) ish) ⟩
                    h +₁ ((-₁ ish) +₁ ish)
                       ≡⟨ (cong (h +₁_) (lCancel₁ ish)) ∙ (rId₁ h) ⟩
                    h ∎

          -- end of Iso.rightInv isom h

          -- end of Iso ⟨ kσ⋊G₀ ⟩ ⟨ G₁ ⟩

      GroupEquiv.isHom G₁-≅ ((h , p) , g) ((h' , p') , g') = q
        where
          abstract
            q = (h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁ 𝒾 (g +₀ g')
                   ≡⟨ cong ((h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁_)
                           (ι .isHom g g') ⟩
                (h +₁ ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g))) +₁ (𝒾 g +₁ 𝒾 g')
                   ≡⟨ sym (assoc₁ h ((𝒾 g +₁ h') +₁ (-₁ 𝒾 g)) (𝒾 g +₁ 𝒾 g')) ⟩
                h +₁ (((𝒾 g +₁ h') +₁ (-₁ 𝒾 g)) +₁ (𝒾 g +₁ 𝒾 g'))
                   ≡⟨ cong (h +₁_)
                           (sym (assoc₁ (𝒾 g +₁ h') (-₁ 𝒾 g) (𝒾 g +₁ 𝒾 g'))) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ ((-₁ 𝒾 g) +₁ (𝒾 g +₁ 𝒾 g')))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ z))
                           (assoc₁ (-₁ 𝒾 g) (𝒾 g) (𝒾 g')) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ (((-₁ 𝒾 g) +₁ 𝒾 g) +₁ 𝒾 g'))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ (z +₁ 𝒾 g')))
                           (lCancel₁ (𝒾 g)) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ (0₁ +₁ 𝒾 g'))
                   ≡⟨ cong (λ z → h +₁ ((𝒾 g +₁ h') +₁ z))
                           (lId₁ (𝒾 g')) ⟩
                h +₁ ((𝒾 g +₁ h') +₁ 𝒾 g')
                   ≡⟨ cong (h +₁_)
                           (sym (assoc₁ (𝒾 g) h' (𝒾 g'))) ⟩
                h +₁ (𝒾 g +₁ (h' +₁ 𝒾 g'))
                   ≡⟨ assoc₁ h (𝒾 g) (h' +₁ 𝒾 g') ⟩
                (h +₁ 𝒾 g) +₁ (h' +₁ 𝒾 g') ∎

      -- end of GroupEquiv kσ⋊G₀ G₁

      ι-≅ : (g : ⟨ G₀ ⟩) → 0₁ +₁ (𝒾 g) ≡ 𝒾 g
      ι-≅ g = lId₁ (𝒾 g)

      σ-≅ : (((h , _) , g) : ⟨ kσ⋊G₀ ⟩) → g ≡ s (h +₁ 𝒾 g)
      σ-≅ ((h , p) , g) = q
        where
          abstract
            q = g
                  ≡⟨ funExt⁻ (cong fun (sym isSplit)) g ⟩
                s (𝒾 g)
                  ≡⟨ sym (lId₀ (s (𝒾 g))) ⟩
                0₀ +₀ s (𝒾 g)
                  ≡⟨ cong (_+₀ s (𝒾 g)) (sym p) ⟩
                s h +₀ s (𝒾 g)
                  ≡⟨ sym (σ .isHom h (𝒾 g)) ⟩
                s (h +₁ 𝒾 g) ∎

      isSplit-≅ : Unit
      isSplit-≅ = tt

  -- end of RelIso.rightInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , G₁) , (ι , σ)) , isSplit)


  RelIso.leftInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , H) , _α_) , isAct) = ((G₀-≅ , H-≅) , α-≅) , isAct-≅
    where
      -- import notation
      open GroupNotation₀ G₀
      open GroupNotationH H
      open ActionNotationα (groupaction _α_ isAct) using (α-id)

      se = RelIso.fun 𝒮-Iso-GroupAct-SplitEpi (((G₀ , H) , _α_) , isAct)
      ga' = RelIso.inv 𝒮-Iso-GroupAct-SplitEpi se

      -- H under fun and then inv
      ker-π₂ = snd (fst (fst ga'))
      -- the adjoint action w.t.r. ι₂
      _β_ = snd (fst ga')
      β-isAct = snd ga'
      -- inclusion of G₀ into H ⋊⟨ α ⟩ G₀
      ι = ι₂ (groupaction _α_ isAct)
      𝒾 = ι .fun

      G₀-≅ : GroupEquiv G₀ G₀
      G₀-≅ = idGroupEquiv G₀

      H-≅ : GroupEquiv ker-π₂ H
      GroupEquiv.eq H-≅ = isoToEquiv isom
        where
          isom : Iso ⟨ ker-π₂ ⟩ ⟨ H ⟩
          Iso.fun isom ((h , g) , p) = h
          Iso.inv isom h = (h , 0₀) , refl
          Iso.leftInv isom ((h , g) , p) = q
            where
              abstract
                r : (h , 0₀) ≡ (h , g)
                r = ΣPathP (refl , sym p)
                q : ((h , 0₀) , refl) ≡ ((h , g) , p)
                q = ΣPathP (r , isProp→PathP (λ i → set₀ (snd (r i)) 0₀) refl p)
          Iso.rightInv isom h = refl

      GroupEquiv.isHom H-≅ ((h , g) , p) ((h' , g') , p') = q
        where
          abstract
            q : h +ᴴ (g α h') ≡ h +ᴴ h'
            q = h +ᴴ (g α h')
                  ≡⟨ cong (λ z → h +ᴴ (z α h')) p ⟩
                h +ᴴ (0₀ α h')
                  ≡⟨ cong (h +ᴴ_) (α-id h') ⟩
                h +ᴴ h' ∎

      α-≅ : (g : ⟨ G₀ ⟩) (((h , g') , p) : ⟨ ker-π₂ ⟩)
            → GroupEquiv.eq H-≅ .fst (g β ((h , g') , p)) ≡ g α h
      α-≅ g ((h , g') , p) = q
        where
          open ActionLemmas (groupaction _α_ isAct)
          abstract
            q = (0ᴴ +ᴴ (g α h)) +ᴴ ((g +₀ g') α ((-₀ g) α (-ᴴ 0ᴴ)))
                  ≡⟨ cong (_+ᴴ ((g +₀ g') α ((-₀ g) α (-ᴴ 0ᴴ))))
                          (lIdᴴ (g α h)) ⟩
                (g α h) +ᴴ ((g +₀ g') α ((-₀ g) α (-ᴴ 0ᴴ)))
                  ≡⟨ cong (λ z → (g α h) +ᴴ ((g +₀ g') α ((-₀ g) α z)))
                          (invId H) ⟩
                (g α h) +ᴴ ((g +₀ g') α ((-₀ g) α 0ᴴ))
                  ≡⟨ cong (λ z → (g α h) +ᴴ ((g +₀ g') α z))
                          (actOnUnit (-₀ g)) ⟩
                (g α h) +ᴴ ((g +₀ g') α 0ᴴ)
                  ≡⟨ cong ((g α h) +ᴴ_)
                          (actOnUnit (g +₀ g')) ⟩
                (g α h) +ᴴ 0ᴴ
                  ≡⟨ rIdᴴ (g α h) ⟩
                g α h ∎

      isAct-≅ : Unit
      isAct-≅ = tt
  -- end of RelIso.leftInv 𝒮-Iso-GroupAct-SplitEpi (((G₀ , H) , _α_) , isAct)

  IsoActionSplitEpi : Iso (Action ℓ (ℓ-max ℓ ℓ')) (SplitEpi ℓ (ℓ-max ℓ ℓ'))
  IsoActionSplitEpi = 𝒮-iso→Iso (𝒮-Action ℓ (ℓ-max ℓ ℓ')) (𝒮-SplitEpi ℓ (ℓ-max ℓ ℓ')) 𝒮-Iso-GroupAct-SplitEpi
