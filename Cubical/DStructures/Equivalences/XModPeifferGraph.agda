{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Equivalences.XModPeifferGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary


open import Cubical.Structures.Subtype
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Group.Semidirect

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Structures.PeifferGraph
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction
open import Cubical.DStructures.Equivalences.PreXModReflGraph


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas
open ActionLemmas

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

    ℱ = IsoPreXModuleReflGraph ℓ ℓℓ'
    F = Iso.fun ℱ

    𝒮ᴰ-S2G = 𝒮ᴰ-ReflGraph\Peiffer

    𝒮ᴰ-♭iso-XModule-Strict2Group : 𝒮ᴰ-♭iso F (𝒮ᴰ-XModule ℓ ℓℓ') (𝒮ᴰ-S2G ℓ ℓℓ')
    RelIso.fun (𝒮ᴰ-♭iso-XModule-Strict2Group (((((G₀ , H) , _α_) , isAct) , φ) , isEqui)) isPeif a b = q
      where
        open GroupNotationH H
        open GroupNotation₀ G₀
        f = GroupHom.fun φ
        A = groupaction _α_ isAct
        open ActionNotationα A using (α-assoc ; α-hom)

        SG = F (((((G₀ , H) , _α_) , isAct) , φ) , isEqui)
        -- H⋊G : Group {ℓℓ'}
        H⋊G = snd (fst (fst (fst (fst SG))))
        open GroupNotation₁ H⋊G
        -- σ : GroupHom H⋊G G₀
        σ = snd (snd (fst (fst (fst SG))))
        -- ι : GroupHom G₀ H⋊G
        ι = fst (snd (fst (fst (fst SG))))
        -- τ : GroupHom H⋊G G₀
        τ = snd (fst SG)
        t = GroupHom.fun τ
        s = GroupHom.fun σ
        𝒾 = GroupHom.fun ι
        is = λ (h : ⟨ H⋊G ⟩) → 𝒾 (s h)
        -is = λ (h : ⟨ H⋊G ⟩) → -₁ 𝒾 (s h)
        it = λ (h : ⟨ H⋊G ⟩) → 𝒾 (t h)
        -it = λ (h : ⟨ H⋊G ⟩) → -₁ 𝒾 (t h)
        u = fst a
        v = snd a
        x = fst b
        y = snd b
        abstract
          -- alright folks, let's do some simple arithmetic with a `twist`, that is Peiffer identities and equivariance
          r = ((0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) +ᴴ (((y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ ((-₀ y) +₀ y)) α 0ᴴ)
                ≡⟨ cong (((0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) +ᴴ_) (actOnUnit A ((y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ ((-₀ y) +₀ y))) ⟩
              ((0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) +ᴴ 0ᴴ
                ≡⟨ rIdᴴ ((0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) ⟩
              (0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))
                ≡⟨ cong (_+ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) (lIdᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) ⟩
              (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))
                ≡⟨ cong (λ z → (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (z +ᴴ ((-₀ y) α x)))) (actOn-Unit A (-₀ y)) ⟩
              (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (0ᴴ +ᴴ ((-₀ y) α x)))
                ≡⟨ cong (λ z → (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α z)) (lIdᴴ ((-₀ y) α x)) ⟩
              (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))
                ≡⟨ cong (λ z → (y α (u +ᴴ (v α z))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))) (actOn-Unit A (-₀ ((f u) +₀ v))) ⟩
              (y α (u +ᴴ (v α 0ᴴ))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))
                ≡⟨ cong (λ z → (y α (u +ᴴ z)) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))) (actOnUnit A v) ⟩
              (y α (u +ᴴ 0ᴴ)) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))
                ≡⟨ cong (λ z → (y α z) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))) (rIdᴴ u) ⟩
              (y α u) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α ((-₀ y) α x))
                ≡⟨ cong (λ z → (y α u) +ᴴ ((y +₀ (v +₀ z)) α ((-₀ y) α x))) (invDistr G₀ (f u) v) ⟩
              (y α u) +ᴴ ((y +₀ (v +₀ ((-₀ v) +₀ (-₀ (f u))))) α ((-₀ y) α x))
                ≡⟨ cong (λ z → (y α u) +ᴴ ((y +₀ z) α ((-₀ y) α x))) (assoc-rCancel G₀ v (-₀ f u)) ⟩
              (y α u) +ᴴ ((y +₀ (-₀ (f u))) α ((-₀ y) α x))
                ≡⟨ cong ((y α u) +ᴴ_) (sym (α-assoc (y +₀ (-₀ f u)) (-₀ y) x)) ⟩
              (y α u) +ᴴ (((y +₀ (-₀ (f u))) +₀ (-₀ y)) α x)
                ≡⟨ cong (λ z → (y α u) +ᴴ (((y +₀ z) +₀ (-₀ y)) α x)) (sym (mapInv φ u)) ⟩
              (y α u) +ᴴ (((y +₀ (f (-ᴴ u))) +₀ (-₀ y)) α x)
                ≡⟨ cong (λ z → (y α u) +ᴴ (z α x)) (sym (isEqui y (-ᴴ u))) ⟩
              (y α u) +ᴴ ((f (y α (-ᴴ u))) α x)
                ≡⟨ cong ((y α u) +ᴴ_) (isPeif (y α (-ᴴ u)) x) ⟩
              (y α u) +ᴴ (((y α (-ᴴ u)) +ᴴ x) +ᴴ (-ᴴ (y α (-ᴴ u))))
                ≡⟨ cong (λ z → (y α u) +ᴴ ((z +ᴴ x) +ᴴ (-ᴴ z))) (actOn- A y u) ⟩
              (y α u) +ᴴ (((-ᴴ (y α u)) +ᴴ x) +ᴴ (-ᴴ (-ᴴ (y α u))))
                ≡⟨ cong (λ z → (y α u) +ᴴ (((-ᴴ (y α u)) +ᴴ x) +ᴴ z)) (invInvo H (y α u)) ⟩
              (y α u) +ᴴ (((-ᴴ (y α u)) +ᴴ x) +ᴴ (y α u))
                ≡⟨ assoc-assoc H (y α u) (-ᴴ (y α u)) x (y α u) ⟩
              (((y α u) +ᴴ (-ᴴ (y α u))) +ᴴ x) +ᴴ (y α u)
                ≡⟨ cong (_+ᴴ (y α u)) (rCancel-lId H (y α u) x) ⟩
              x +ᴴ (y α u) ∎

          r' = ((y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ ((-₀ y) +₀ y)) +₀ (f u +₀ v)
                 ≡⟨ cong (_+₀ (f u +₀ v)) (lCancel-rId G₀ (y +₀ (v +₀ (-₀ (f u +₀ v)))) y) ⟩
               (y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ (f u +₀ v)
                 ≡⟨ cong (λ z → (y +₀ (v +₀ z)) +₀ (f u +₀ v)) (invDistr G₀ (f u) v) ⟩
               (y +₀ (v +₀ ((-₀ v) +₀ (-₀ f u)))) +₀ (f u +₀ v)
                 ≡⟨ cong (λ z → (y +₀ z) +₀ (f u +₀ v)) (assoc-rCancel G₀ v (-₀ f u)) ⟩
               (y +₀ (-₀ f u)) +₀ (f u +₀ v)
                 ≡⟨ assoc⁻-assocr-lCancel-lId G₀ y (f u) v ⟩
               y +₀ v ∎

          q = ((is b +₁ (a +₁ -it a)) +₁ (-is b +₁ b)) +₁ it a
                ≡⟨ refl ⟩
              ((0ᴴ +ᴴ (y α (u +ᴴ (v α ((-₀ ((f u) +₀ v)) α (-ᴴ 0ᴴ)))))) +ᴴ ((y +₀ (v +₀ (-₀ (f u +₀ v)))) α (((-₀ y) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ y) α x)))) +ᴴ (((y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ ((-₀ y) +₀ y)) α 0ᴴ)
              , ((y +₀ (v +₀ (-₀ (f u +₀ v)))) +₀ ((-₀ y) +₀ y)) +₀ (f u +₀ v)
                ≡⟨ ΣPathP (r , r') ⟩
              x +ᴴ (y α u) , y +₀ v
                ≡⟨ refl ⟩
              b +₁ a ∎
    RelIso.inv (𝒮ᴰ-♭iso-XModule-Strict2Group (((((G₀ , H) , _α_) , isAct) , φ) , isEqui)) ♭isPeif h h' = q
      where
        open GroupNotationH H
        open GroupNotation₀ G₀
        f = GroupHom.fun φ
        A = groupaction _α_ isAct
        open ActionNotationα A using (α-assoc ; α-hom ; α-id)

        SG = F (((((G₀ , H) , _α_) , isAct) , φ) , isEqui)
        -- H⋊G : Group {ℓℓ'}
        H⋊G = snd (fst (fst (fst (fst SG))))
        open GroupNotation₁ H⋊G
        -- σ : GroupHom H⋊G G₀
        σ = snd (snd (fst (fst (fst SG))))
        -- ι : GroupHom G₀ H⋊G
        ι = fst (snd (fst (fst (fst SG))))
        -- τ : GroupHom H⋊G G₀
        τ = snd (fst SG)
        t = GroupHom.fun τ
        s = GroupHom.fun σ
        𝒾 = GroupHom.fun ι
        is = λ (h : ⟨ H⋊G ⟩) → 𝒾 (s h)
        -is = λ (h : ⟨ H⋊G ⟩) → -₁ 𝒾 (s h)
        it = λ (h : ⟨ H⋊G ⟩) → 𝒾 (t h)
        -it = λ (h : ⟨ H⋊G ⟩) → -₁ 𝒾 (t h)
        -h = -ᴴ h
        abstract
          r₁ = ((0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α ((-₀ ((f -h) +₀ 0₀)) α (-ᴴ 0ᴴ)))))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))) +ᴴ (((0₀ +₀ (0₀ +₀ (-₀ ((f -h) +₀ 0₀)))) +₀ ((-₀ 0₀) +₀ 0₀)) α 0ᴴ)
                 ≡⟨ cong fst (♭isPeif (-h , 0₀) (h' , 0₀)) ⟩
               h' +ᴴ (0₀ α -h)
                 ≡⟨ cong (h' +ᴴ_) (α-id -h) ⟩
               h' +ᴴ -h ∎

          r₂ = ((0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α ((-₀ ((f -h) +₀ 0₀)) α (-ᴴ 0ᴴ)))))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                  +ᴴ (((0₀ +₀ (0₀ +₀ (-₀ ((f -h) +₀ 0₀)))) +₀ ((-₀ 0₀) +₀ 0₀)) α 0ᴴ)
                  ≡⟨ cong (((0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α ((-₀ ((f -h) +₀ 0₀)) α (-ᴴ 0ᴴ)))))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))) +ᴴ_)
                          (actOnUnit A (((0₀ +₀ (0₀ +₀ (-₀ ((f -h) +₀ 0₀)))) +₀ ((-₀ 0₀) +₀ 0₀))))
                     ∙ rIdᴴ _ ⟩
                (0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α ((-₀ ((f -h) +₀ 0₀)) α (-ᴴ 0ᴴ)))))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → (0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α z)))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (actOn-Unit A (-₀ ((f -h) +₀ 0₀))) ⟩
                (0ᴴ +ᴴ (0₀ α (-h +ᴴ (0₀ α 0ᴴ)))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → (0ᴴ +ᴴ (0₀ α (-h +ᴴ z))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (actOnUnit A 0₀) ⟩
                (0ᴴ +ᴴ (0₀ α (-h +ᴴ 0ᴴ))) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → (0ᴴ +ᴴ (0₀ α z)) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (rIdᴴ -h) ⟩
                (0ᴴ +ᴴ (0₀ α -h)) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → (0ᴴ +ᴴ z) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (α-id -h) ⟩
                (0ᴴ +ᴴ -h) +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (_+ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (lIdᴴ -h) ⟩
                -h +ᴴ ((0₀ +₀ (0₀ +₀ (-₀ (f -h +₀ 0₀)))) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → -h +ᴴ (z α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h'))))
                          (lId-lId G₀ (-₀ (f -h +₀ 0₀))) ⟩
                -h +ᴴ ((-₀ (f -h +₀ 0₀)) α (((-₀ 0₀) α (-ᴴ 0ᴴ)) +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → -h +ᴴ ((-₀ (f -h +₀ 0₀)) α (z +ᴴ ((-₀ 0₀) α h'))))
                          (actOn-Unit A (-₀ 0₀)) ⟩
                -h +ᴴ ((-₀ (f -h +₀ 0₀)) α (0ᴴ +ᴴ ((-₀ 0₀) α h')))
                  ≡⟨ cong (λ z → -h +ᴴ ((-₀ (f -h +₀ 0₀)) α z))
                          (lIdᴴ ((-₀ 0₀) α h')) ⟩
                -h +ᴴ ((-₀ (f -h +₀ 0₀)) α ((-₀ 0₀) α h'))
                  ≡⟨ cong (λ z → -h +ᴴ ((-₀ (f -h +₀ 0₀)) α z))
                          (-idAct A h') ⟩
                -h +ᴴ ((-₀ (f -h +₀ 0₀)) α h')
                  ≡⟨ cong (λ z → -h +ᴴ ((-₀ z) α h'))
                          (rId₀ (f -h)) ⟩
                -h +ᴴ ((-₀ (f -h)) α h')
                  ≡⟨ cong (λ z → -h +ᴴ (z α h'))
                          (cong -₀_ (mapInv φ h) ∙ invInvo G₀ (f h)) ⟩
                -h +ᴴ (f h α h') ∎

          q = f h α h'
                ≡⟨ sym (lIdᴴ (f h α h'))
                   ∙∙ sym (cong (_+ᴴ (f h α h')) (rCancelᴴ h))
                   ∙∙ sym (assocᴴ h -h (f h α h')) ⟩
              h +ᴴ (-h +ᴴ (f h α h'))
                ≡⟨ cong (h +ᴴ_)
                        (sym r₂ ∙ r₁) ⟩
              h +ᴴ (h' +ᴴ -h)
                ≡⟨ assocᴴ h h' -h ⟩
              (h +ᴴ h') +ᴴ (-ᴴ h) ∎

    RelIso.leftInv (𝒮ᴰ-♭iso-XModule-Strict2Group _) _ = tt
    RelIso.rightInv (𝒮ᴰ-♭iso-XModule-Strict2Group _) _ = tt


  IsoXModulePeifferGraph : Iso (XModule ℓ ℓℓ') (PeifferGraph ℓ ℓℓ')
  IsoXModulePeifferGraph = Iso→TotalIso ℱ (𝒮ᴰ-XModule ℓ ℓℓ') (𝒮ᴰ-S2G ℓ ℓℓ') 𝒮ᴰ-♭iso-XModule-Strict2Group
