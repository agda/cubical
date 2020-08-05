{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Experiments where

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
open BinaryRelation

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
-- open import Cubical.DStructures.Structures.Strict2Group
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas
open MorphismTree

module _ {ℓ ℓ' : Level} where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  -- give more suitable names
  SplitEpi = G²SecRet ℓ ℓℓ'
  𝒮-SplitEpi = 𝒮-G²FBSplit ℓ ℓℓ'

  Act = G²Act ℓ ℓℓ'
  𝒮-Act = 𝒮-Action ℓ ℓℓ'

  -- ReflGraph = Σ[ (((G₀ , G₁) , (ι , σ)) , split-σ) ∈ SplitEpi ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ
  -- this is on a different Σ type
  𝒮-ReflGraph = 𝒮-G²FBSplitBSplit ℓ ℓℓ'


  -- PreXMod = Σ[ (((G₀ , G₁) , _α_) , isAct) ∈ Act ] Σ[ φ ∈ GroupHom G₁ G₀ ] (isEquivariant _α_ φ)
  𝒮-PreXMod = 𝒮-PreXModule ℓ ℓℓ'
  ℱ-RelIso : 𝒮-iso 𝒮-Act 𝒮-SplitEpi
  ℱ-RelIso = 𝒮-Iso-GroupAct-SplitEpi ℓ ℓℓ'

  𝒮ᴰ-ReflGraph' : URGStrᴰ 𝒮-SplitEpi (λ (((G₀ , G₁) , (ι , σ)) , split-σ) → Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ) ℓℓ'
--  𝒮ᴰ-ReflGraph' = splitTotal-𝒮ᴰ 𝒮-SplitEpi (𝒮ᴰ-G²FBSplit\B ℓ ℓℓ') {!𝒮ᴰ-G²FBSplitB\Split ℓ ℓℓ'!}
  𝒮ᴰ-ReflGraph' = {!!}


  𝒮ᴰ-PreXMod' : URGStrᴰ 𝒮-Act (λ (((G₀ , G₁) , _α_) , isAct) → Σ[ φ ∈ GroupHom G₁ G₀ ] (isEquivariant _α_ φ)) ℓℓ'
  -- 𝒮ᴰ-PreXMod' = splitTotal-𝒮ᴰ 𝒮-Act (𝒮ᴰ-Action\PreXModuleStr ℓ ℓℓ') (𝒮ᴰ-PreXModule ℓ ℓℓ')
  𝒮ᴰ-PreXMod' = {!!}

  𝒢 : 𝒮ᴰ-♭iso (RelIso.fun ℱ-RelIso) 𝒮ᴰ-PreXMod' 𝒮ᴰ-ReflGraph'
  RelIso.fun (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .fst = τ
    where
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      open MorphismLemmas
      𝒻 = GroupHom.fun φ
      τ = grouphom (λ (h , g) → GroupHom.fun φ h +₀ g) q
          where
            abstract
              q = λ (h , g) (h' , g') → 𝒻 (h +₁ (g α h')) +₀ (g +₀ g')
                                          ≡⟨ cong (_+₀ (g +₀ g')) (φ .isHom h (g α h')) ⟩
                                        (𝒻 h +₀ 𝒻 (g α h')) +₀ (g +₀ g')
                                          ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g')) (isEqui g h') ⟩
                                        (𝒻 h +₀ ((g +₀ (𝒻 h')) +₀ (-₀ g))) +₀ (g +₀ g')
                                          ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g') ) (sym (assoc₀ g (𝒻 h') (-₀ g))) ⟩
                                        (𝒻 h +₀ (g +₀ (𝒻 h' +₀ (-₀ g)))) +₀ (g +₀ g')
                                          ≡⟨ cong (_+₀ (g +₀ g')) (assoc₀ (𝒻 h) g (𝒻 h' +₀ (-₀ g))) ⟩
                                        ((𝒻 h +₀ g) +₀ (𝒻 h' +₀ (-₀ g))) +₀ (g +₀ g')
                                          ≡⟨ sym (assoc₀ (𝒻 h +₀ g) (𝒻 h' +₀ (-₀ g)) (g +₀ g')) ⟩
                                        (𝒻 h +₀ g) +₀ ((𝒻 h' +₀ (-₀ g)) +₀ (g +₀ g'))
                                          ≡⟨ cong ((𝒻 h +₀ g) +₀_)
                                                  (sym (assoc₀ (𝒻 h') (-₀ g) (g +₀ g'))
                                                  ∙ (cong (𝒻 h' +₀_)
                                                          (assoc₀ (-₀ g) g g'
                                                          ∙∙ cong (_+₀ g') (lCancel₀ g)
                                                          ∙∙ lId₀ g')))⟩
                                        (𝒻 h +₀ g) +₀ (𝒻  h' +₀ g') ∎

  RelIso.fun (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .snd = q
    where
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      open MorphismLemmas
      𝒻 = GroupHom.fun φ
      abstract
        q = GroupMorphismExt λ g → 𝒻 0₁ +₀ g
                                             ≡⟨ cong (_+₀ g) (mapId φ) ⟩
                                           0₀ +₀ g
                                             ≡⟨ lId₀ g ⟩
                                           g ∎
  RelIso.inv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (τ , split-τ) = φ , isEqui
    where
      ℬ = RelIso.fun ℱ-RelIso (((G₀ , G₁) , _α_) , isAct)
      σ = snd (snd (fst ℬ))

      φ' = restrictToKer σ τ

      φ = {!φ'!}
      isEqui = {!!}

  RelIso.leftInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) = {!!}
  RelIso.rightInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) = {!!}

{-


  module _ (((((G₀ , G₁) , (ι , σ)) , split-σ) , τ , split-τ) : ReflGraph) where
    𝒜 : Act
    𝒜 = RelIso.inv ℱ-RelIso (((G₀ , G₁) , (ι , σ)) , split-σ)
    _α_ =  snd (fst 𝒜)

    get-φ : GroupHom (snd (fst (fst 𝒜))) G₀
    get-φ = restrictToKer σ τ

    abstract
      get-isEquivariant : isEquivariant _α_ get-φ
      get-isEquivariant g (h , p) = 𝓉 ((𝒾 g +₁ h) +₁ (-₁ (𝒾 g)))
                                      ≡⟨ τ .isHom (𝒾 g +₁ h) (-₁ (𝒾 g)) ⟩
                                    𝓉 (𝒾 g +₁ h) +₀ (𝓉 (-₁ (𝒾 g)))
                                      ≡⟨ cong (_+₀ 𝓉 (-₁ (𝒾 g))) (τ .isHom (𝒾 g) h) ⟩
                                    (𝓉 (𝒾 g) +₀ 𝓉 h) +₀ 𝓉 (-₁ (𝒾 g))
                                      ≡⟨ cong ((𝓉 (𝒾 g) +₀ 𝓉 h) +₀_) (mapInv τ (𝒾 g)) ⟩
                                    (𝓉 (𝒾 g) +₀ 𝓉 h) +₀ (-₀ (𝓉 (𝒾 g)))
                                      ≡⟨ cong (λ z → (z +₀ 𝓉 h) +₀ (-₀ z)) (funExt⁻ (cong fun split-τ) g) ⟩
                                    (g +₀ (𝓉 h)) +₀ (-₀ g) ∎
        where
          𝒾 = ι .fun
          𝓉 = τ .fun
          open GroupNotation₁ G₁
          open GroupNotation₀ G₀
          open MorphismLemmas


  module _ (((((G₀ , G₁) , _α_) , isAct) , φ , isEqui) : PreXMod) where
    ℬ : SplitEpi
    ℬ = RelIso.fun ℱ-RelIso (((G₀ , G₁) , _α_) , isAct)

    open GroupNotation₀ G₀
    open GroupNotation₁ G₁
    open MorphismLemmas
    𝒻 = GroupHom.fun φ

    get-τ : GroupHom (snd (fst (fst ℬ))) G₀
    GroupHom.fun get-τ (h , g) = GroupHom.fun φ h +₀ g
    GroupHom.isHom get-τ (h , g) (h' , g') = q
      where
        abstract
          q = 𝒻 (h +₁ (g α h')) +₀ (g +₀ g')
                ≡⟨ cong (_+₀ (g +₀ g')) (φ .isHom h (g α h')) ⟩
              (𝒻 h +₀ 𝒻 (g α h')) +₀ (g +₀ g')
                ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g')) (isEqui g h') ⟩
              (𝒻 h +₀ ((g +₀ (𝒻 h')) +₀ (-₀ g))) +₀ (g +₀ g')
                ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g') ) (sym (assoc₀ g (𝒻 h') (-₀ g))) ⟩
              (𝒻 h +₀ (g +₀ (𝒻 h' +₀ (-₀ g)))) +₀ (g +₀ g')
                ≡⟨ cong (_+₀ (g +₀ g')) (assoc₀ (𝒻 h) g (𝒻 h' +₀ (-₀ g))) ⟩
              ((𝒻 h +₀ g) +₀ (𝒻 h' +₀ (-₀ g))) +₀ (g +₀ g')
                ≡⟨ sym (assoc₀ (𝒻 h +₀ g) (𝒻 h' +₀ (-₀ g)) (g +₀ g')) ⟩
              (𝒻 h +₀ g) +₀ ((𝒻 h' +₀ (-₀ g)) +₀ (g +₀ g'))
                ≡⟨ cong ((𝒻 h +₀ g) +₀_)
                        (sym (assoc₀ (𝒻 h') (-₀ g) (g +₀ g'))
                        ∙ (cong (𝒻 h' +₀_)
                          (assoc₀ (-₀ g) g g'
                          ∙∙ cong (_+₀ g') (lCancel₀ g)
                          ∙∙ lId₀ g')))⟩
              (𝒻 h +₀ g) +₀ (𝒻  h' +₀ g') ∎


    abstract
      get-split-τ : isGroupSplitEpi (fst (snd (fst ℬ))) get-τ
      get-split-τ = GroupMorphismExt λ g → 𝒻 0₁ +₀ g
                                             ≡⟨ cong (_+₀ g) (mapId φ) ⟩
                                           0₀ +₀ g
                                             ≡⟨ lId₀ g ⟩
                                           g ∎


-}

  

{-
  ℱ : Act ≃ SplitEpi
  ℱ = isoToEquiv (𝒮-iso→Iso 𝒮-Act 𝒮-SplitEpi ℱ-RelIso)

  ReflGraph→PreXMod : ReflGraph → PreXMod
  ReflGraph→PreXMod = {!!}

  PreXMod→ReflGraph : PreXMod → ReflGraph
  PreXMod→ReflGraph  = {!!}

 --  𝒢 : 𝒮-iso 𝒮-ReflGraph 𝒮-PreXMod
 --  𝒢 = RelFiberIsoOver→RelFiberIso ℱ {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
-}

{-
module _ where

  𝒮ᴰ-isoOver→𝒮-♭iso-1 : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                      {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                      (ℱ : Iso A A')
                      {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                      → Iso (Σ[ a ∈ A ] B' (Iso.fun ℱ a)) (Σ A' B')
  𝒮ᴰ-isoOver→𝒮-♭iso-1 {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ {B' = B'} 𝒮ᴰ-B' =
    iso (λ (a , b') → ℱ .fun a , b')
        (λ (a' , b') → ℱ .inv a' , subst B' (sym (ℱ .rightInv a')) b')
        (λ (a' , b') → ΣPathP (ℱ .rightInv a' , J (λ y p → PathP (λ i → B' (p (~ i))) (subst B' p b') b')
                                                  (subst B' refl b' ≡⟨  substRefl b'  ⟩ b' ∎)
                                                  (sym (ℱ .rightInv a'))))
        λ (a , b) → ΣPathP (ℱ .leftInv a , {!J!})
    where
      open Iso

  𝒮ᴰ-isoOver→𝒮-♭iso-2 : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                      {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                      (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                      {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                      → RelIso {A = Σ[ a ∈ A ] B' (RelIso.fun ℱ a)}
                               (λ (a , b) (a' , b') → Σ[ e ∈ URGStr._≅_ 𝒮-A' (RelIso.fun ℱ a) (RelIso.fun ℱ a') ] URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B' b e b')
                               {A' = Σ A' B'} (URGStr._≅_ (∫⟨ 𝒮-A' ⟩ 𝒮ᴰ-B'))
  𝒮ᴰ-isoOver→𝒮-♭iso-2 {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ {B' = B'} 𝒮ᴰ-B' =
    reliso (λ (a , b') → ℱ .fun a , b')
           (λ (a' , b') → ℱ .inv a' , subst (λ x → B' x) (sym (𝒮-≅≃≡ 𝒮-A' (ℱ .fun (ℱ .inv a')) a' .fst (ℱ .rightInv a'))) b')
           (λ (a' , b') → {!!} , {!!})
           {!!}
      where
        open RelIso
        open URGStr

-}



-- Older Experiments --

{-
-- needs --guardedness flag

module _ where
  open import Cubical.Data.Maybe
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Maybe (Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
-}
