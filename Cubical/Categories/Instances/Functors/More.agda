{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors.More where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Category

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Categories.Equivalence
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓC ℓC' ℓD ℓD' ℓΓ ℓΓ' ℓ ℓ' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open Functor
  open NatTrans

  module _ {Γ : Category ℓΓ ℓΓ'} where
    -- The action of currying out the right argument of a Functor (Γ ×C C) D
    λFr : Functor (Γ ×C C) D → Functor Γ (FUNCTOR C D)
    λFr F .F-ob a .F-ob b = F ⟅ a , b ⟆
    λFr F .F-ob a .F-hom f = F .F-hom (Γ .id , f)
    λFr F .F-ob a .F-id = F .F-id
    λFr F .F-ob a .F-seq f g =
      F .F-hom (Γ .id , f ⋆⟨ C ⟩ g)
        ≡⟨ (λ i → F .F-hom ((Γ .⋆IdL (Γ .id) (~ i)) , f ⋆⟨ C ⟩ g)) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ Γ .id , f ⋆⟨ C ⟩ g)
        ≡⟨ F .F-seq (Γ .id , f) (Γ .id , g) ⟩
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (Γ .id , g ) ∎
    λFr F .F-hom γ .N-ob b = F .F-hom (γ , C .id)
    λFr F .F-hom γ .N-hom f =
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (γ , C .id)
        ≡⟨ sym (F .F-seq (Γ .id , f) (γ , C .id)) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ γ , f ⋆⟨ C ⟩ C .id)
        ≡⟨ (λ i → F .F-hom ((idTrans (Id {C = Γ}) .N-hom γ (~ i)) ,
                             idTrans (Id {C = C}) .N-hom f i)) ⟩
      F .F-hom (γ ⋆⟨ Γ ⟩ Γ .id , C .id ⋆⟨ C ⟩ f)
        ≡⟨ F .F-seq (γ , C .id) (Γ .id , f) ⟩
      F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (Γ .id , f)  ∎
    λFr F .F-id = makeNatTransPath (funExt (λ a → F .F-id))
    λFr F .F-seq γ δ = makeNatTransPath (funExt (λ a →
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id)
          ≡⟨ (λ i → F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .⋆IdL (C .id) (~ i))) ⟩
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id ⋆⟨ C ⟩ C .id)
          ≡⟨ F .F-seq (γ , C .id) (δ , C .id) ⟩
        F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (δ , C .id) ∎))

    -- Functorially extend the currying action from a
    -- function on objects to a functor between
    -- the relevant functor categories
    -- Here "currying" pulls out the right argument.
    -- We will define a similar left-sided version
    -- under the name curryFl
    curryF : Functor (FUNCTOR (Γ ×C C) D) (FUNCTOR Γ (FUNCTOR C D))
    curryF .F-ob = λFr
    curryF .F-hom η .N-ob γ .N-ob c = η .N-ob (γ , c)
    curryF .F-hom η .N-ob γ .N-hom ϕ = η .N-hom (Γ .id , ϕ)
    curryF .F-hom η .N-hom f =
      makeNatTransPath (funExt (λ (c : C .ob) → η .N-hom (f , C .id)))
    curryF .F-id = makeNatTransPath (funExt λ (γ : Γ .ob) → refl)
    curryF .F-seq η η' = makeNatTransPath (funExt λ (γ : Γ .ob) → refl)

    -- Preimage for the ESO proof
    -- i.e. an object in (FUNCTOR Γ (FUNCTOR C D)) that maps to λF
    curryF-ESO-object-preimage : (FUNCTOR Γ (FUNCTOR C D)) .ob →
                                 (FUNCTOR (Γ ×C C) D) .ob
    curryF-ESO-object-preimage λF .F-ob (γ , c) =  λF .F-ob γ .F-ob c
    curryF-ESO-object-preimage λF .F-hom
      {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} (ϕ , ψ) =
        λF .F-hom ϕ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom ψ
    curryF-ESO-object-preimage λF .F-seq
      {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} {z = (γ₃ , c₃)} (ϕ₁ , ψ₁) (ϕ₂ , ψ₂) = (
      curryF-ESO-object-preimage λF .F-hom ((ϕ₁ , ψ₁) ⋆⟨ Γ ×C C ⟩ (ϕ₂ , ψ₂))
        ≡⟨ ((λ i → ( (λF .F-seq ϕ₁ ϕ₂ (i) ) .N-ob c₁ ⋆⟨ D ⟩
          λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)))) ⟩
      (λF .F-hom ϕ₁ ⋆⟨ FUNCTOR C D ⟩ λF .F-hom ϕ₂) .N-ob c₁ ⋆⟨ D ⟩
        λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)
        ≡⟨ (λ i → (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
           λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-seq ψ₁ ψ₂ i)) ⟩
      (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
        λF .F-hom ϕ₂ .N-ob c₁) ⋆⟨ D ⟩
          (λF .F-ob γ₃ .F-hom ψ₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂)
        ≡⟨ solveCat! D ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩
        λF .F-ob γ₃ .F-hom ψ₁) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ ((λ i → ( λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
          (λF .F-hom ϕ₂ .N-hom ψ₁ (~ i) ) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂ ))) ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-ob γ₂ .F-hom ψ₁ ⋆⟨ D ⟩
        λF .F-hom ϕ₂ .N-ob c₂) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ solveCat! D ⟩
      curryF-ESO-object-preimage λF .F-hom (ϕ₁ , ψ₁) ⋆⟨ D ⟩
        curryF-ESO-object-preimage λF .F-hom (ϕ₂ , ψ₂) ∎)
    curryF-ESO-object-preimage λF .F-id  {x = (γ , c)} = (
      curryF-ESO-object-preimage λF .F-hom (Γ .id , C .id)
        ≡⟨ ((λ i → (λF .F-id i .N-ob c ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)
        ≡⟨ ((λ i → (D .id ⋆⟨ D ⟩ (λF .F-ob γ .F-id i)))) ⟩
      D .id ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdL (D .id) ⟩
      D .id
      ∎ )
    -- Half of the isomorphism between (curryF-ESO-object-preimage λF) and λF
    curryF-ESO-morphism-preimage : (λF : (FUNCTOR Γ (FUNCTOR C D)) .ob) →
                                   NatTrans
                                     (curryF .F-ob
                                       (curryF-ESO-object-preimage λF))
                                     λF
    curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c = D .id
    curryF-ESO-morphism-preimage λF .N-ob γ .N-hom {x = c₁} {y = c₂} ψ =
      ((λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩ (λF .F-ob γ .F-hom ψ)) ⋆⟨ D ⟩ D .id
        ≡⟨ (λ i → (D .⋆IdR ((λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩
          (λF .F-ob γ .F-hom ψ)) (i) )) ⟩
      (λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → ((λF .F-id i) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ∎
    curryF-ESO-morphism-preimage λF .N-hom {x = γ₁} {y = γ₂} ϕ =
      makeNatTransPath (funExt (λ (c : C .ob) →
      curryF .F-ob (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c ⋆⟨ D ⟩
        (curryF-ESO-morphism-preimage λF) .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR
          (curryF .F-ob (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom (C .id)
        ≡⟨ ((λ i → (λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id i))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdL (λF .F-hom ϕ .N-ob c) (~ i) ))) ⟩
      (curryF-ESO-morphism-preimage λF) .N-ob γ₁ .N-ob c ⋆⟨ D ⟩
        λF .F-hom ϕ .N-ob c ∎))

    open isIso

    -- Show that curryF-ESO-morphism-preimage is indeed an isomorphism in
    -- FUNCTOR Γ (FUNCTOR C D)
    curryF-ESO-morphism-preimage-isIso : (λF : (FUNCTOR Γ (FUNCTOR C D)) .ob) →
                                         isIsoC
                                           (FUNCTOR Γ (FUNCTOR C D))
                                           (curryF-ESO-morphism-preimage λF)
    curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c =  D .id
    curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-hom
      {x = c₁} {y = c₂} ψ =
      λF .F-ob γ .F-hom ψ ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-ob γ .F-hom ψ) ⟩
      λF .F-ob γ .F-hom ψ
        ≡⟨ (λ i → (D .⋆IdL (λF .F-ob γ .F-hom ψ) (~ i))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (λF .F-id (~ i)) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ) ) ⟩
     curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (D .⋆IdL
          (curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ )
            (~ i) ))) ⟩
      D .id ⋆⟨ D ⟩
        curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ ∎
    curryF-ESO-morphism-preimage-isIso λF .inv .N-hom {x = γ₁} {y = γ₂} ϕ =
      makeNatTransPath (funExt (λ (c : C .ob ) →
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩
        curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdR (λF .F-hom ϕ .N-ob c) (~ i)))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ ((λ i → ( λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id (~ i )))) ⟩
      λFr (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → ((D .⋆IdL (λFr (curryF-ESO-object-preimage λF)
          .F-hom ϕ .N-ob c) (~ i)) ))) ⟩
      D .id ⋆⟨ D ⟩ λFr (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c ∎
      ))
    curryF-ESO-morphism-preimage-isIso λF .sec =
      makeNatTransPath (funExt (λ (γ : Γ .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
        curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c ⋆⟨ D ⟩
          curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR
            (curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))
    curryF-ESO-morphism-preimage-isIso λF .ret =
      makeNatTransPath (funExt (λ (γ : Γ .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
         curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c ⋆⟨ D ⟩
           curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR
            (curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))


    -- to prove that curryF is an equivalence,
    -- we construct the inverse functor, uncurryF
    uncurryF : Functor (FUNCTOR Γ (FUNCTOR C D)) (FUNCTOR (Γ ×C C) D)
    uncurryF .F-ob λF = curryF-ESO-object-preimage λF
    -- stolen from curryF-full-preimage
    uncurryF .F-hom {F} {G} λη .N-ob (γ , c) = λη .N-ob γ .N-ob c
    uncurryF .F-hom {F} {G} λη .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
      uncurryF .F-ob F .F-hom (ϕ₁ , ϕ₂) ⋆⟨ D ⟩
        uncurryF .F-hom λη .N-ob (γ₂ , c₂)
        ≡⟨ solveCat! D ⟩
      F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩ (F .F-ob γ₂ .F-hom ϕ₂ ⋆⟨ D ⟩
        λη .N-ob γ₂ .N-ob c₂)
        ≡⟨ (λ i → (F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩ (λη .N-ob γ₂ .N-hom ϕ₂ (i)))) ⟩
      F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩
        (λη .N-ob γ₂ .N-ob c₁ ⋆⟨ D ⟩ G .F-ob γ₂ .F-hom ϕ₂)
        ≡⟨ solveCat! D ⟩
      (F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩
        λη .N-ob γ₂ .N-ob c₁) ⋆⟨ D ⟩ G .F-ob γ₂ .F-hom ϕ₂
       ≡⟨ (λ i → (((λη .N-hom (ϕ₁) (i)) .N-ob c₁) ⋆⟨ D ⟩
         G .F-ob γ₂ .F-hom ϕ₂)) ⟩
      (λη .N-ob γ₁ .N-ob c₁ ⋆⟨ D ⟩ G .F-hom (ϕ₁) .N-ob c₁) ⋆⟨ D ⟩
        G .F-ob γ₂ .F-hom ϕ₂
        ≡⟨ solveCat! D ⟩
      uncurryF .F-hom λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩
        uncurryF .F-ob G .F-hom (ϕ₁ , ϕ₂) ∎
    uncurryF .F-id = makeNatTransPath (funExt (λ x → refl ))
    uncurryF .F-seq λη₁ λη₂ = makeNatTransPath (funExt (λ x → refl ))


    open WeakInverse
    open NatIso

    -- curryF is an equivalence. Done using η ε isos constructed explicitly.
    -- most of the time, these are the identity
    curryF-isEquivalence : WeakInverse curryF
    curryF-isEquivalence =
      record { invFunc = uncurryF ; η = η-iso ; ε = ε-iso } where
      -- separate definition to sidestep Agda termination issue
      η-trans : NatTrans 𝟙⟨ FUNCTOR (Γ ×C C) D ⟩ (uncurryF ∘F curryF)
      η-trans .N-ob F .N-ob (γ , c) = D .id
      η-trans .N-ob F .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
        (F .F-hom (ϕ₁ , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ (λ i →
            (F .F-hom ((Γ .⋆IdR ϕ₁) (~ i) , (C .⋆IdL ϕ₂) (~ i)) ⋆⟨ D ⟩ D .id)) ⟩
        (F .F-hom ((ϕ₁ , C .id) ⋆⟨ Γ ×C C ⟩ (Γ .id , ϕ₂))) ⋆⟨ D ⟩ D .id
          ≡⟨ (λ i → (F .F-seq (ϕ₁ , C .id) (Γ .id , ϕ₂)) (i) ⋆⟨ D ⟩ D .id) ⟩
        (F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ F .F-hom (Γ .id , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂)  ∎
      η-trans .N-hom {F} {G} β =
        makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

      η-iso : NatIso 𝟙⟨ FUNCTOR (Γ ×C C) D ⟩ (uncurryF ∘F curryF)
      η-iso .trans = η-trans

      η-iso .nIso F .inv .N-ob (γ , c) = D .id
      η-iso .nIso F .inv .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
        ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂)
          ≡⟨ sym (η-iso .trans .N-ob F .N-hom (ϕ₁ , ϕ₂)) ⟩
        (F .F-hom (ϕ₁ , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ (F .F-hom (ϕ₁ , ϕ₂))  ∎
      η-iso .nIso F .sec = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      η-iso .nIso F .ret = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

      ε-iso : NatIso (curryF ∘F uncurryF) 𝟙⟨ FUNCTOR Γ (FUNCTOR C D) ⟩
      ε-iso .trans .N-ob λF = curryF-ESO-morphism-preimage λF
      ε-iso .trans .N-hom {λF} {λG} λβ = makeNatTransPath (funExt (λ γ →
        makeNatTransPath (funExt (λ c →
          -- TODO: For some reason this doesn't simplify to just solvecat...
          (λβ .N-ob γ .N-ob c) ⋆⟨ D ⟩ D .id
            ≡⟨ solveCat! D ⟩
          D .id ⋆⟨ D ⟩ λβ .N-ob γ .N-ob c ∎ ))))
      ε-iso .nIso = (λ λF → curryF-ESO-morphism-preimage-isIso λF)


    open Cubical.Categories.Equivalence.Base._≃ᶜ_

    curryEquivalence : FUNCTOR (Γ ×C C) D ≃ᶜ FUNCTOR Γ (FUNCTOR C D)
    curryEquivalence .func = curryF
    curryEquivalence ._≃ᶜ_.isEquiv = ∣ curryF-isEquivalence ∣₁

    -- We also want a notion of currying out the left argument.
    -- We do this by composing
    -- a swapping functor with the right-sided currying functor
    -- To show that this left-handed currying is also an equivalence,
    -- we will need to show that
    -- the swapping functor is an equivalence
    swapArgs : Functor (FUNCTOR (C ×C Γ) D) (FUNCTOR (Γ ×C C) D)
    swapArgs .F-ob F .F-ob (c , γ) = F .F-ob (γ , c)
    swapArgs .F-ob F .F-hom (ψ , ϕ) = F .F-hom (ϕ , ψ)
    swapArgs .F-ob F .F-id = F .F-id
    swapArgs .F-ob F .F-seq (ψ₁ , ϕ₁) (ψ₂ , ϕ₂) = F .F-seq (ϕ₁ , ψ₁) (ϕ₂ , ψ₂)
    swapArgs .F-hom η .N-ob (γ , c) = η .N-ob (c , γ)
    swapArgs .F-hom η .N-hom (ϕ , ψ) = η .N-hom (ψ , ϕ)
    swapArgs .F-id = makeNatTransPath (funExt λ (γ , c) → refl)
    swapArgs .F-seq η η' = makeNatTransPath (funExt λ (γ , c) → refl)

    swapArgs-inv : Functor (FUNCTOR (Γ ×C C) D) (FUNCTOR (C ×C Γ) D)
    swapArgs-inv .F-ob F .F-ob (γ , c) = F .F-ob (c , γ)
    swapArgs-inv .F-ob F .F-hom (ϕ , ψ) = F .F-hom (ψ , ϕ)
    swapArgs-inv .F-ob F .F-id = F .F-id
    swapArgs-inv .F-ob F .F-seq (ϕ₁ , ψ₁) (ϕ₂ , ψ₂) =
      F .F-seq (ψ₁ , ϕ₁) (ψ₂ , ϕ₂)
    swapArgs-inv .F-hom η .N-ob (γ , c) = η .N-ob (c , γ)
    swapArgs-inv .F-hom η .N-hom (ψ , ϕ) = η .N-hom (ϕ , ψ)
    swapArgs-inv .F-id = makeNatTransPath (funExt λ (γ , c) → refl)
    swapArgs-inv .F-seq η η' = makeNatTransPath (funExt λ (γ , c) → refl)

    swapArgs-isEquivalence : WeakInverse swapArgs
    swapArgs-isEquivalence =
      record { invFunc = swapArgs-inv ; η = the-η ; ε = the-ε } where
      η-morphisms : N-ob-Type 𝟙⟨ FUNCTOR (C ×C Γ) D ⟩
                              (funcComp swapArgs-inv swapArgs)
      η-morphisms F .N-ob γ = D .id
      η-morphisms F .N-hom ϕ = solveCat! D

      the-η : NatIso 𝟙⟨ FUNCTOR (C ×C Γ) D ⟩ (funcComp swapArgs-inv swapArgs)
      the-η .trans .N-ob = η-morphisms
      the-η .trans .N-hom α =
        makeNatTransPath (funExt (λ (c , γ) → solveCat! D))
      the-η .nIso F .inv .N-ob (c , γ) = D .id
      the-η .nIso F .inv .N-hom (ψ , ϕ) = solveCat! D
      the-η .nIso F .sec = makeNatTransPath (funExt (λ (c , γ) → solveCat! D))
      the-η .nIso F .ret = makeNatTransPath (funExt (λ (c , γ) → solveCat! D))

      ε-morphisms : N-ob-Type (funcComp swapArgs swapArgs-inv)
                              𝟙⟨ FUNCTOR (Γ ×C C) D ⟩
      ε-morphisms F .N-ob c = D .id
      ε-morphisms F .N-hom ψ = solveCat! D

      the-ε : NatIso (funcComp swapArgs swapArgs-inv) 𝟙⟨ FUNCTOR (Γ ×C C) D ⟩
      the-ε .trans .N-ob = ε-morphisms
      the-ε .trans .N-hom α =
        makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      the-ε .nIso F .inv .N-ob (γ , c) = D .id
      the-ε .nIso F .inv .N-hom (φ , ψ) = solveCat! D
      the-ε .nIso F .sec = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      the-ε .nIso F .ret = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

    curryFl : Functor (FUNCTOR (C ×C Γ) D) (FUNCTOR Γ (FUNCTOR C D))
    curryFl = curryF ∘F swapArgs


    curryFl-isEquivalence : WeakInverse curryFl
    curryFl-isEquivalence =
      isEquivalenceComp swapArgs-isEquivalence curryF-isEquivalence
