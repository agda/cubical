
module Cubical.Categories.Presheaf.Properties where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Instances.Lift
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Equivalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Instances.Slice as Slice
import Cubical.Categories.Instances.Elements as Elements
import Cubical.Functions.Fibration as Fibration

private
  variable
    ℓ ℓ' : Level
    ℓS ℓS' : Level
    e e' : Level


-- (PresheafCategory C) / F ≃ᶜ PresheafCategory (∫ᴾ F)
module _ {ℓS : Level} (C : Category ℓ ℓ') (F : Functor (C ^op) (SET ℓS)) where
  open Category
  open Functor
  open _≃ᶜ_
  open WeakInverse
  open NatTrans
  open NatIso
  open Slice (PresheafCategory C ℓS) F
  open Elements.Contravariant {C = C}

  open Fibration.ForSets

  -- specific case of fiber under natural transformation
  fibersEqIfRepsEqNatTrans : ∀ {A} (ϕ : A ⇒ F) {c x x'} {px : x ≡ x'} {a' : fiber (ϕ ⟦ c ⟧) x} {b' : fiber (ϕ ⟦ c ⟧) x'}
                  → fst a' ≡ fst b'
                  → PathP (λ i → fiber (ϕ ⟦ c ⟧) (px i)) a' b'
  fibersEqIfRepsEqNatTrans ϕ {c} {x} {x'} {px} {a , fiba} {b , fibb} p
    = fibersEqIfRepsEq {isSetB = snd (F ⟅ c ⟆)} (ϕ ⟦ c ⟧) p

  -- ========================================
  --            K : Slice → PresheafCategory
  -- ========================================

  -- action on (slice) objects
  K-ob : (s : SliceCat .ob) → (PresheafCategory (∫ᴾ F) ℓS .ob)
  -- we take (c , x) to the fiber in A of ϕ over x
  K-ob (sliceob {A} ϕ) .F-ob (c , x)
    = (fiber (ϕ ⟦ c ⟧) x)
    , isOfHLevelΣ 2 (snd (A ⟅ c ⟆)) λ _ → isSet→isGroupoid (snd (F ⟅ c ⟆)) _ _
  -- for morphisms, we just apply A ⟪ h ⟫ (plus equality proof)
  K-ob (sliceob {A} ϕ) .F-hom {d , y} {c , x} (h , com) (b , eq)
    = ((A ⟪ h ⟫) b)
    , ((ϕ ⟦ c ⟧) ((A ⟪ h ⟫) b)
    ≡[ i ]⟨ (ϕ .N-hom h) i b ⟩
      (F ⟪ h ⟫) ((ϕ ⟦ d ⟧) b)
    ≡[ i ]⟨ (F ⟪ h ⟫) (eq i) ⟩
      (F ⟪ h ⟫) y
    ≡⟨ com ⟩
      x
    ∎)
  -- functoriality follows from functoriality of A
  K-ob (sliceob {A} ϕ) .F-id {x = (c , x)}
    = funExt λ { (a , fibp)
                → fibersEqIfRepsEqNatTrans ϕ (λ i → A .F-id i a) }
  K-ob (sliceob {A} ϕ) .F-seq {x = (c , x)} {(d , y)} {(e , z)} (f' , eq1) (g' , eq2)
    = funExt λ { ( a , fibp )
                  → fibersEqIfRepsEqNatTrans ϕ (λ i → (A .F-seq f' g') i a) }


  -- action on morphisms (in this case, natural transformation)
  K-hom : {sA sB : SliceCat .ob}
        → (ε : SliceCat [ sA , sB ])
        → (K-ob sA) ⇒ (K-ob sB)
  K-hom {sA = s1@(sliceob {A} ϕ)} {s2@(sliceob {B} ψ)} (slicehom ε com) = natTrans η-ob (λ h → funExt (η-hom h))
    where
      P = K-ob s1
      Q = K-ob s2

      -- just apply the natural transformation (ε) we're given
      -- this ensures that we stay in the fiber over x due to the commutativity given by slicenesss
      η-ob : (el : (∫ᴾ F) .ob) → (fst (P ⟅ el ⟆) → fst (Q ⟅ el ⟆) )
      η-ob (c , x) (a , ϕa≡x) = ((ε ⟦ c ⟧) a) , εψ≡ϕ ∙ ϕa≡x
        where
          εψ≡ϕ : (ψ ⟦ c ⟧) ((ε ⟦ c ⟧) a) ≡ (ϕ ⟦ c ⟧) a
          εψ≡ϕ i = ((com i) ⟦ c ⟧) a

      η-hom : ∀ {el1 el2} (h : (∫ᴾ F) [ el1 , el2 ]) (ae : fst (P ⟅ el2 ⟆)) → η-ob el1 ((P ⟪ h ⟫) ae) ≡ (Q ⟪ h ⟫) (η-ob el2 ae)
      η-hom {el1 = (c , x)} {d , y} (h , eqh) (a , eqa)
        = fibersEqIfRepsEqNatTrans ψ (λ i → ε .N-hom h i a)


  K : Functor SliceCat (PresheafCategory (∫ᴾ F) ℓS)
  K .F-ob = K-ob
  K .F-hom = K-hom
  K .F-id = makeNatTransPath
                          (funExt λ cx@(c , x)
                                  → funExt λ aeq@(a , eq)
                                            → fibersEqIfRepsEq {isSetB = snd (F ⟅ c ⟆)} _ refl)
  K .F-seq (slicehom α eqa) (slicehom β eqb)
    = makeNatTransPath
        (funExt λ cx@(c , x)
        → funExt λ aeq@(a , eq)
        → fibersEqIfRepsEq {isSetB = snd (F ⟅ c ⟆)} _ refl)


  -- ========================================
  --            L : PresheafCategory → Slice
  -- ========================================

  -- action on objects (presheaves)
  L-ob : (P : PresheafCategory (∫ᴾ F) ℓS .ob)
        → SliceCat .ob
  L-ob P = sliceob {S-ob = L-ob-ob} L-ob-hom
    where
      -- sends c to the disjoint union of all the images under P
      LF-ob : (c : C .ob) → (SET _) .ob
      LF-ob c = (Σ[ x ∈ fst (F ⟅ c ⟆) ] fst (P ⟅ c , x ⟆)) , isSetΣ (snd (F ⟅ c ⟆)) (λ x → snd (P ⟅ c , x ⟆))

      -- defines a function piecewise over the fibers by applying P
      LF-hom : ∀ {x y}
              → (f : C [ y , x ])
              → (SET _) [ LF-ob x , LF-ob y ]
      LF-hom {x = c} {d} f (x , a) = ((F ⟪ f ⟫) x) , (P ⟪ f , refl ⟫) a

      L-ob-ob : Functor (C ^op) (SET _)
      L-ob-ob .F-ob = LF-ob
      L-ob-ob .F-hom = LF-hom
      L-ob-ob .F-id {x = c}
        = funExt idFunExt
          where
            idFunExt : ∀ (un : fst (LF-ob c))
                      → (LF-hom (C .id) un) ≡ un
            idFunExt (x , X) = ΣPathP (leftEq , rightEq)
              where
                leftEq : (F ⟪ C .id ⟫) x ≡ x
                leftEq i = F .F-id i x

                rightEq : PathP (λ i → fst (P ⟅ c , leftEq i ⟆))
                          ((P ⟪ C .id , refl ⟫) X) X
                rightEq = left ▷ right
                  where
                    -- the id morphism in (∫ᴾ F)
                    ∫id = C .id , funExt⁻ (F .F-id) x

                    -- functoriality of P gives us close to what we want
                    right : (P ⟪ ∫id ⟫) X ≡ X
                    right i = P .F-id i X

                    -- but need to do more work to show that (C .id , refl) ≡ ∫id
                    left : PathP (λ i → fst (P ⟅ c , leftEq i ⟆))
                                  ((P ⟪ C .id , refl ⟫) X)
                                  ((P ⟪ ∫id ⟫) X)
                    left i = (P ⟪ ∫ᴾhomEq {F = F} (C .id , refl) ∫id (λ i → (c , leftEq i)) refl refl i ⟫) X
      L-ob-ob .F-seq {x = c} {d} {e} f g
        = funExt seqFunEq
          where
            seqFunEq : ∀ (un : fst (LF-ob c))
                      → (LF-hom (g ⋆⟨ C ⟩ f) un) ≡ (LF-hom g) (LF-hom f un)
            seqFunEq un@(x , X) = ΣPathP (leftEq , rightEq)
              where
                -- the left component is comparing the action of F on x
                -- equality follows from functoriality of F
                -- leftEq : fst (LF-hom (g ⋆⟨ C ⟩ f) un) ≡ fst ((LF-hom g) (LF-hom f un))
                leftEq : (F ⟪ g ⋆⟨ C ⟩ f ⟫) x ≡ (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
                leftEq i = F .F-seq f g i x

                -- on the right, equality also follows from functoriality of P
                -- but it's more complicated because of heterogeneity
                -- since leftEq is not a definitional equality
                rightEq : PathP (λ i → fst (P ⟅ e , leftEq i ⟆))
                                ((P ⟪ g ⋆⟨ C ⟩ f , refl ⟫) X)
                                ((P ⟪ g , refl ⟫) ((P ⟪ f , refl ⟫) X))
                rightEq = left ▷ right
                  where
                    -- functoriality of P only gets us to this weird composition on the left
                    right : (P ⟪ (g , refl) ⋆⟨ (∫ᴾ F) ⟩ (f , refl) ⟫) X ≡ (P ⟪ g , refl ⟫) ((P ⟪ f , refl ⟫) X)
                    right i = P .F-seq (f , refl) (g , refl) i X

                    -- so we need to show that this composition is actually equal to the one we want
                    left : PathP (λ i → fst (P ⟅ e , leftEq i ⟆))
                                  ((P ⟪ g ⋆⟨ C ⟩ f , refl ⟫) X)
                                  ((P ⟪ (g , refl) ⋆⟨ (∫ᴾ F) ⟩ (f , refl) ⟫) X)
                    left i = (P ⟪ ∫ᴾhomEq {F = F} (g ⋆⟨ C ⟩ f , refl) ((g , refl) ⋆⟨ (∫ᴾ F) ⟩ (f , refl)) (λ i → (e , leftEq i)) refl refl i ⟫) X
      L-ob-hom : L-ob-ob ⇒ F
      L-ob-hom .N-ob c (x , _) = x
      L-ob-hom .N-hom f = funExt λ (x , _) → refl

  -- action on morphisms (aka natural transformations between presheaves)
  -- is essentially the identity (plus equality proofs for naturality and slice commutativity)
  L-hom : ∀ {P Q} → PresheafCategory (∫ᴾ F) ℓS [ P , Q ] →
        SliceCat [ L-ob P , L-ob Q ]
  L-hom {P} {Q} η = slicehom arr com
    where
      A = S-ob (L-ob P)
      ϕ = S-arr (L-ob P)
      B = S-ob (L-ob Q)
      ψ = S-arr (L-ob Q)
      arr : A ⇒ B
      arr .N-ob c (x , X) = x , ((η ⟦ c , x ⟧) X)
      arr .N-hom {c} {d} f = funExt natu
        where
          natuType : fst (A ⟅ c ⟆) → Type _
          natuType xX@(x , X) = ((F ⟪ f ⟫) x , (η ⟦ d , (F ⟪ f ⟫) x ⟧) ((P ⟪ f , refl ⟫) X)) ≡ ((F ⟪ f ⟫) x , (Q ⟪ f , refl ⟫) ((η ⟦ c , x ⟧) X))
          natu : ∀ (xX : fst (A ⟅ c ⟆)) → natuType xX
          natu (x , X) = ΣPathP (refl , λ i → (η .N-hom (f , refl) i) X)

      com : arr ⋆⟨ PresheafCategory C ℓS ⟩ ψ ≡ ϕ
      com = makeNatTransPath (funExt comFunExt)
        where
          comFunExt : ∀ (c : C .ob)
                    → (arr ●ᵛ ψ) ⟦ c ⟧ ≡ ϕ ⟦ c ⟧
          comFunExt c = funExt λ x → refl

  L : Functor (PresheafCategory (∫ᴾ F) ℓS) SliceCat
  L .F-ob = L-ob
  L .F-hom = L-hom
  L .F-id {cx} = SliceHom-≡-intro' (makeNatTransPath (funExt λ c → refl))
  L .F-seq {cx} {dy} P Q = SliceHom-≡-intro' (makeNatTransPath (funExt λ c → refl))

  -- ========================================
  --              η : 𝟙 ≅ LK
  -- ========================================

  module _ where
    open Iso
    -- the iso we need
    -- a type is isomorphic to the disjoint union of all its fibers
    typeSectionIso : ∀ {A B : Type ℓS} {isSetB : isSet B} → (ϕ : A → B)
                  → Iso A (Σ[ b ∈ B ] fiber ϕ b)
    typeSectionIso ϕ .fun a = (ϕ a) , (a , refl)
    typeSectionIso ϕ .inv (b , (a , eq)) = a
    typeSectionIso {isSetB = isSetB} ϕ .sec (b , (a , eq))
      = ΣPathP (eq
                , ΣPathP (refl
                        , isOfHLevel→isOfHLevelDep 1 (λ b' → isSetB _ _) refl eq eq))
    typeSectionIso ϕ .ret a = refl

    -- the natural transformation
    -- just applies typeSectionIso
    ηTrans : 𝟙⟨ SliceCat ⟩ ⇒ (L ∘F K)
    ηTrans .N-ob sob@(sliceob {A} ϕ) = slicehom A⇒LK comm
      where
        LKA = S-ob  (L ⟅ K ⟅ sob ⟆ ⟆)
        ψ = S-arr  (L ⟅ K ⟅ sob ⟆ ⟆)

        A⇒LK : A ⇒ LKA
        A⇒LK .N-ob c = typeSectionIso {isSetB = snd (F ⟅ c ⟆)} (ϕ ⟦ c ⟧) .fun
        A⇒LK .N-hom {c} {d} f = funExt homFunExt
          where
            homFunExt : (x : fst (A ⟅ c ⟆))
                      → (((ϕ ⟦ d ⟧) ((A ⟪ f ⟫) x)) , ((A ⟪ f ⟫) x , refl))  ≡ ((F ⟪ f ⟫) ((ϕ ⟦ c ⟧) x) , (A ⟪ f ⟫) x , _)
            homFunExt x = ΣPathP ((λ i → (ϕ .N-hom f i) x) , fibersEqIfRepsEqNatTrans ϕ refl)

        comm : (A⇒LK) ●ᵛ ψ ≡ ϕ
        comm = makeNatTransPath (funExt λ x → refl)
    ηTrans .N-hom {sliceob {A} α} {sliceob {B} β} (slicehom ϕ eq)
      = SliceHom-≡-intro' (makeNatTransPath (funExt (λ c → funExt λ a → natFunExt c a)))
      where
        natFunExt : ∀ (c : C .ob) (a : fst (A ⟅ c ⟆))
                  → ((β ⟦ c ⟧) ((ϕ ⟦ c ⟧) a) , (ϕ ⟦ c ⟧) a , _) ≡ ((α ⟦ c ⟧) a , (ϕ ⟦ c ⟧) a , _)
        natFunExt c a = ΣPathP ((λ i → ((eq i) ⟦ c ⟧) a) , fibersEqIfRepsEqNatTrans β refl)

    -- isomorphism follows from typeSectionIso
    ηIso : ∀ (sob : SliceCat .ob)
          → isIsoC SliceCat (ηTrans ⟦ sob ⟧)
    ηIso sob@(sliceob ϕ) = sliceIso _ _ (FUNCTORIso _ _ _ isIsoCf)
      where
        isIsoCf : ∀ (c : C .ob)
                → isIsoC _ (ηTrans .N-ob sob .S-hom ⟦ c ⟧)
        isIsoCf c = Morphism.CatIso→isIso (Iso→CatIso (typeSectionIso {isSetB = snd (F ⟅ c ⟆)} (ϕ ⟦ c ⟧)))


  -- ========================================
  --              ε : KL ≅ 𝟙
  -- ========================================

  module _ where
    open Iso
    -- the iso we deserve
    -- says that a type family at x is isomorphic to the fiber over x of that type family packaged up
    typeFiberIso : ∀ {ℓ ℓ'} {A : Type ℓ} {isSetA : isSet A} {x} (B : A → Type ℓ')
                  → Iso (B x) (fiber {A = Σ[ a ∈ A ] B a} (λ (x , _) → x) x)
    typeFiberIso {x = x} _ .fun b = (x , b) , refl
    typeFiberIso _ .inv ((a , b) , eq) = subst _ eq b
    typeFiberIso {isSetA = isSetA} {x = x} B .sec ((a , b) , eq)
      = fibersEqIfRepsEq {isSetB = isSetA} (λ (x , _) → x) (ΣPathP (sym eq , symP (transport-filler (λ i → B (eq i)) b)))
    typeFiberIso {x = x} _ .ret b = sym (transport-filler refl b)

    -- the natural isomorphism
    -- applies typeFiberIso (inv)
    εTrans : (K ∘F L) ⇒ 𝟙⟨ PresheafCategory (∫ᴾ F) ℓS ⟩
    εTrans .N-ob P = natTrans γ-ob (λ f → funExt (λ a → γ-homFunExt f a))
      where
        KLP = K ⟅ L ⟅ P ⟆ ⟆

        γ-ob : (el : (∫ᴾ F) .ob)
            → (fst (KLP ⟅ el ⟆) → fst (P ⟅ el ⟆) )
        γ-ob el@(c , _) = typeFiberIso {isSetA = snd (F ⟅ c ⟆)} (λ x → fst (P ⟅ c , x ⟆)) .inv

        -- naturality
        -- the annoying part is all the substs
        γ-homFunExt : ∀ {el2 el1} → (f' : (∫ᴾ F) [ el2 , el1 ])
              → (∀ (a : fst (KLP ⟅ el1 ⟆)) → γ-ob el2 ((KLP ⟪ f' ⟫) a) ≡ (P ⟪ f' ⟫) (γ-ob el1 a))
        γ-homFunExt {d , y} {c , x} f'@(f , comm) a@((x' , X') , eq) i
          = comp (λ j → fst (P ⟅ d , eq' j ⟆)) (λ j → λ { (i = i0) → left j
                                                        ; (i = i1) → right j }) ((P ⟪ f , refl ⟫) X')
            where
              -- fiber equality proof that we get from an application of KLP
              eq' = snd ((KLP ⟪ f' ⟫) a)

              -- top right of the commuting diagram
              -- "remove" the subst from the inside
              right : PathP (λ i → fst (P ⟅ d , eq' i ⟆)) ((P ⟪ f , refl ⟫) X') ((P ⟪ f , comm ⟫) (subst _ eq X'))
              right i = (P ⟪ f , refl≡comm i ⟫) (X'≡subst i)
                where
                  refl≡comm : PathP (λ i → (F ⟪ f ⟫) (eq i) ≡ (eq' i)) refl comm
                  refl≡comm = isOfHLevel→isOfHLevelDep 1 (λ (v , w) → snd (F ⟅ d ⟆) ((F ⟪ f ⟫) w) v) refl comm λ i → (eq' i , eq i)

                  X'≡subst : PathP (λ i → fst (P ⟅ c , eq i ⟆)) X' (subst (λ v → fst (P ⟅ c , v ⟆)) eq X')
                  X'≡subst = transport-filler (λ i → fst (P ⟅ c , eq i ⟆)) X'

              -- bottom left of the commuting diagram
              -- "remove" the subst from the outside
              left : PathP (λ i → fst (P ⟅ d , eq' i ⟆)) ((P ⟪ f , refl ⟫) X') (subst (λ v → fst (P ⟅ d , v ⟆)) eq' ((P ⟪ f , refl ⟫) X'))
              left = transport-filler (λ i → fst (P ⟅ d , eq' i ⟆)) ((P ⟪ f , refl ⟫) X')
    εTrans .N-hom {P} {Q} α = makeNatTransPath (funExt λ cx → funExt λ xX' → ε-homFunExt cx xX')
      where
        KLP = K ⟅ L ⟅ P ⟆ ⟆

        -- naturality of the above construction applies a similar argument as in `γ-homFunExt`
        ε-homFunExt : ∀ (cx@(c , x) : (∫ᴾ F) .ob) (xX'@((x' , X') , eq) : fst (KLP ⟅ cx ⟆))
                    → subst (λ v → fst (Q ⟅ c , v ⟆)) (snd ((K ⟪ L ⟪ α ⟫ ⟫ ⟦ cx ⟧) xX')) ((α ⟦ c , x' ⟧) X')
                    ≡ (α ⟦ c , x ⟧) (subst _ eq X')
        ε-homFunExt cx@(c , x) xX'@((x' , X') , eq) i
          = comp (λ j → fst (Q ⟅ c , eq j ⟆)) (λ j → λ { (i = i0) → left j
                                                        ; (i = i1) → right j }) ((α ⟦ c , x' ⟧) X')
          where
            eq' : x' ≡ x
            eq' = snd ((K ⟪ L ⟪ α ⟫ ⟫ ⟦ cx ⟧) xX')

            right : PathP (λ i → fst (Q ⟅ c , eq i ⟆)) ((α ⟦ c , x' ⟧) X') ((α ⟦ c , x ⟧) (subst _ eq X'))
            right i = (α ⟦ c , eq i ⟧) (X'≡subst i)
              where
                -- this is exactly the same as the one from before, can refactor?
                X'≡subst : PathP (λ i → fst (P ⟅ c , eq i ⟆)) X' (subst (λ v → fst (P ⟅ c , v ⟆)) eq X')
                X'≡subst = transport-filler _ _

            -- extracted out type since need to use in in 'left' body as well
            leftTy : (x' ≡ x) → Type _
            leftTy eq* = PathP (λ i → fst (Q ⟅ c , eq* i ⟆)) ((α ⟦ c , x' ⟧) X') (subst (λ v → fst (Q ⟅ c , v ⟆)) eq' ((α ⟦ c , x' ⟧) X'))

            left : leftTy eq
            left = subst
                    (λ eq* → leftTy eq*)
                    eq'≡eq
                    (transport-filler _ _)
              where
                eq'≡eq : eq' ≡ eq
                eq'≡eq = snd (F ⟅ c ⟆) _ _ eq' eq

    εIso : ∀ (P : PresheafCategory (∫ᴾ F) ℓS .ob)
          → isIsoC (PresheafCategory (∫ᴾ F) ℓS) (εTrans ⟦ P ⟧)
    εIso P = FUNCTORIso _ _ _ isIsoC'
      where
        isIsoC' : ∀ (cx : (∫ᴾ F) .ob)
                → isIsoC (SET _) ((εTrans ⟦ P ⟧) ⟦ cx ⟧)
        isIsoC' cx@(c , _) = Morphism.CatIso→isIso (Iso→CatIso (invIso (typeFiberIso {isSetA = snd (F ⟅ c ⟆)} _)))


  -- putting it all together

  preshSlice≃preshElem : SliceCat ≃ᶜ PresheafCategory (∫ᴾ F) ℓS
  preshSlice≃preshElem .func = K
  preshSlice≃preshElem .isEquiv = ∣ w-inv ∣₁
    where
      w-inv : WeakInverse K
      w-inv .invFunc = L
      w-inv .η .trans = ηTrans
      w-inv .η .nIso = ηIso
      w-inv .ε .trans = εTrans
      w-inv .ε .nIso = εIso

-- Isomorphism between presheaves of different levels
PshIso : (C : Category ℓ ℓ') (P : Presheaf C ℓS) (Q : Presheaf C ℓS') → Type _
PshIso {ℓS = ℓS} {ℓS' = ℓS'} C P Q =
  NatIso (LiftF ℓS' ∘F P) (LiftF ℓS ∘F Q)
