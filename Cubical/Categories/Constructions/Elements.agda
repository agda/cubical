{-# OPTIONS --cubical --no-import-sorts --safe #-}

-- The Category of Elements

module Cubical.Categories.Constructions.Elements where

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaves
open import Cubical.Categories.Equivalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Sigma

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Constructions.Slice as Slice

private
  variable
    ℓ ℓ' : Level

-- some issues
-- * always need to specify objects during composition because can't infer isSet
open Precategory
open Functor


getIsSet : {C : Precategory ℓ ℓ'} (F : Functor C (SET ℓ)) → (c : C .ob) → isSet (fst (F ⟅ c ⟆))
getIsSet F c = snd (F ⟅ c ⟆)


module _ {C : Precategory ℓ ℓ'} where
  infix 50 ∫_
  ∫_ : Functor C (SET ℓ) → Precategory ℓ (ℓ-max ℓ ℓ')
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ F) .ob = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)
  -- morphisms are f : c → c' which take x to x'
  (∫ F) .Hom[_,_] (c , x) (c' , x')  = Σ[ f ∈ C [ c , c' ] ] x' ≡ (F ⟪ f ⟫) x
  (∫ F) .id (c , x) = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)
  (∫ F) ._⋆_ {c , x} {c₁ , x₁} {c₂ , x₂} (f , p) (g , q)
    = (f ⋆⟨ C ⟩ g) , (x₂
              ≡⟨ q ⟩
                (F ⟪ g ⟫) x₁         -- basically expanding out function composition
              ≡⟨ cong (F ⟪ g ⟫) p ⟩
                (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
              ≡⟨ funExt⁻ (sym (F .F-seq _ _)) _ ⟩
                (F ⟪ f ⋆⟨ C ⟩ g ⟫) x
              ∎)
  (∫ F) .⋆IdL o@{c , x} o1@{c' , x'} f'@(f , p) i
    = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdL i
      where
        isS = getIsSet F c
        isS' = getIsSet F c'
        cIdL = C .⋆IdL f

        -- proof from composition with id
        p' : x' ≡ (F ⟪ C .id c ⋆⟨ C ⟩ f ⟫) x
        p' = snd ((∫ F) ._⋆_ ((∫ F) .id o) f')
  (∫ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
     = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdR i
       where
         cIdR = C .⋆IdR f
         isS' = getIsSet F c'

         p' : x' ≡ (F ⟪ f ⋆⟨ C ⟩ C .id c' ⟫) x
         p' = snd ((∫ F) ._⋆_ f' ((∫ F) .id o1))
  (∫ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
    = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS₃ x₃ ((F ⟪ a ⟫) x)) p1 p2 cAssoc i
      where
        cAssoc = C .⋆Assoc f g h
        isS₃ = getIsSet F c₃

        p1 : x₃ ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x
        p1 = snd ((∫ F) ._⋆_ ((∫ F) ._⋆_ {o} {o1} {o2} f' g') h')

        p2 : x₃ ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x
        p2 = snd ((∫ F) ._⋆_ f' ((∫ F) ._⋆_ {o1} {o2} {o3} g' h'))


  -- same thing but for presheaves
  ∫ᴾ_ : Functor (C ^op) (SET ℓ) → Precategory ℓ (ℓ-max ℓ ℓ')
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ᴾ F) .ob = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)
  -- morphisms are f : c → c' which take x to x'
  (∫ᴾ F) .Hom[_,_] (c , x) (c' , x')  = Σ[ f ∈ C [ c , c' ] ] x ≡ (F ⟪ f ⟫) x'
  (∫ᴾ F) .id (c , x) = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)
  (∫ᴾ F) ._⋆_ {c , x} {c₁ , x₁} {c₂ , x₂} (f , p) (g , q)
    = (f ⋆⟨ C ⟩ g) , (x
              ≡⟨ p ⟩
                (F ⟪ f ⟫) x₁         -- basically expanding out function composition
              ≡⟨ cong (F ⟪ f ⟫) q ⟩
                (F ⟪ f ⟫) ((F ⟪ g ⟫) x₂)
              ≡⟨ funExt⁻ (sym (F .F-seq _ _)) _ ⟩
                (F ⟪ f ⋆⟨ C ⟩ g ⟫) x₂
              ∎)
  (∫ᴾ F) .⋆IdL o@{c , x} o1@{c' , x'} f'@(f , p) i
    = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x')) p' p cIdL i
      where
        isS = getIsSet F c
        isS' = getIsSet F c'
        cIdL = C .⋆IdL f

        -- proof from composition with id
        p' : x ≡ (F ⟪ C .id c ⋆⟨ C ⟩ f ⟫) x'
        p' = snd ((∫ᴾ F) ._⋆_ ((∫ᴾ F) .id o) f')
  (∫ᴾ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
     = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x')) p' p cIdR i
       where
         cIdR = C .⋆IdR f
         isS = getIsSet F c

         p' : x ≡ (F ⟪ f ⋆⟨ C ⟩ C .id c' ⟫) x'
         p' = snd ((∫ᴾ F) ._⋆_ f' ((∫ᴾ F) .id o1))
  (∫ᴾ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
    = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x₃)) p1 p2 cAssoc i
      where
        cAssoc = C .⋆Assoc f g h
        isS = getIsSet F c

        p1 : x ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x₃
        p1 = snd ((∫ᴾ F) ._⋆_ ((∫ᴾ F) ._⋆_ {o} {o1} {o2} f' g') h')

        p2 : x ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x₃
        p2 = snd ((∫ᴾ F) ._⋆_ f' ((∫ᴾ F) ._⋆_ {o1} {o2} {o3} g' h'))

  -- helpful results

  module _ {F : Functor (C ^op) (SET ℓ)} where

    -- morphisms are equal as long as the morphisms in C are equals
    ∫ᴾhomEq : ∀ {o1 o1' o2 o2'} (f : (∫ᴾ F) [ o1 , o2 ]) (g : (∫ᴾ F) [ o1' , o2' ])
            → (p : o1 ≡ o1') (q : o2 ≡ o2')
            → (eqInC : PathP (λ i → C [ fst (p i) , fst (q i) ]) (fst f) (fst g))
            → PathP (λ i → (∫ᴾ F) [ p i , q i ]) f g
    ∫ᴾhomEq (f , eqf) (g , eqg) p q eqInC
      = ΣPathP (eqInC
               , isOfHLevel→isOfHLevelDep 1 {A = Σ[ (o1 , o2) ∈ (∫ᴾ F) .ob × (∫ᴾ F) .ob ] (C [ fst o1 , fst o2 ])}
                                            {B = λ ((o1 , o2) , f) → snd o1 ≡ (F ⟪ f ⟫) (snd o2)}
                                            (λ ((o1 , o2) , f) → snd (F ⟅ (fst o1) ⟆) (snd o1) ((F ⟪ f ⟫) (snd o2)))
                                            eqf
                                            eqg
                                            λ i → ((p i , q i) , eqInC i))

  -- BIG THEOREM
  module _ (F : Functor (C ^op) (SET ℓ)) where
    open _≃ᶜ_
    open isEquivalence
    open NatTrans
    open NatIso
    open Slice (PreShv C) F ⦃ isC = isCatPreShv {C = C} ⦄

    -- fibers are equal when their representatives are equal
    fiberEqIfRepsEq : ∀ {A} (ϕ : A ⇒ F) {c x x'} {px : x ≡ x'} {a' : fiber (ϕ ⟦ c ⟧) x} {b' : fiber (ϕ ⟦ c ⟧) x'}
                    → fst a' ≡ fst b'
                    → PathP (λ i → fiber (ϕ ⟦ c ⟧) (px i)) a' b'
    fiberEqIfRepsEq ϕ {c} {x} {x'} {px} {a , fiba} {b , fibb} p
      = ΣPathP (p , isOfHLevel→isOfHLevelDep 1 (λ (v , w) → snd (F ⟅ c ⟆) ((ϕ ⟦ c ⟧) v) w) _ _ λ i → (p i , px i))


    -- Functor from Slice to PreShv (∫ᴾ F)
    -- call it K

    -- action on (slice) objects
    K-ob : (s : SliceCat .ob) → (PreShv (∫ᴾ F) .ob)
    -- we take (c , x) to the fiber in A of ϕ over x
    K-ob (sliceob {A} ϕ) .F-ob (c , x)
      = (fiber (ϕ ⟦ c ⟧) x)
      , isOfHLevelΣ 2 (snd (A ⟅ c ⟆)) λ _ → isSet→isGroupoid (snd (F ⟅ c ⟆)) _ _
    -- for morhpisms, we just apply A ⟪ h ⟫ (plus equality proof)
    K-ob (sliceob {A} ϕ) .F-hom {d , y} {c , x} (h , com) (b , eq)
      = ((A ⟪ h ⟫) b)
      , ((ϕ ⟦ c ⟧) ((A ⟪ h ⟫) b)
      ≡[ i ]⟨ (ϕ .N-hom h) i b ⟩
        (F ⟪ h ⟫) ((ϕ ⟦ d ⟧) b)
      ≡[ i ]⟨ (F ⟪ h ⟫) (eq i) ⟩
        (F ⟪ h ⟫) y
      ≡⟨ sym com ⟩
        x
      ∎)
    -- functoriality follows from functoriality of A
    K-ob (sliceob {A} ϕ) .F-id {x = (c , x)}
      = funExt λ { (a , fibp)
                 → fiberEqIfRepsEq ϕ (λ i → A .F-id i a) }
    K-ob (sliceob {A} ϕ) .F-seq {x = (c , x)} {(d , y)} {(e , z)} (f' , eq1) (g' , eq2)
      = funExt λ { ( a , fibp )
                   → fiberEqIfRepsEq ϕ (λ i → (A .F-seq f' g') i a) }


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
          = fiberEqIfRepsEq ψ (λ i → ε .N-hom h i a)


    K : Functor SliceCat (PreShv (∫ᴾ F))
    K .F-ob = K-ob
    K .F-hom = K-hom


    -- reverse functor from presheaf to slice
    L-ob : (P : PreShv (∫ᴾ F) .ob)
         → SliceCat .ob
    L-ob P = sliceob {S-ob = L-ob-ob} L-ob-hom
      where
        LF-ob : (c : C .ob) → (SET _) .ob
        LF-ob c = (Σ[ x ∈ fst (F ⟅ c ⟆) ] fst (P ⟅ c , x ⟆)) , isSetΣ (snd (F ⟅ c ⟆)) (λ x → snd (P ⟅ c , x ⟆))

        LF-hom : ∀ {x y}
               → (f : C [ y , x ])
               → (SET _) [ LF-ob x , LF-ob y ]
        LF-hom {x = c} {d} f (x , a) = ((F ⟪ f ⟫) x) , (P ⟪ f , refl ⟫) a

        L-ob-ob : Functor (C ^op) (SET _)
        -- sends c to the disjoint union of all the images under P
        L-ob-ob .F-ob = LF-ob
        -- defines a function piecewise over the fibers by applying P
        L-ob-ob .F-hom = LF-hom
        L-ob-ob .F-id {x = c}
          = funExt idFunExt
            where
              idFunExt : ∀ (un : fst (LF-ob c))
                       → (LF-hom (C .id c) un) ≡ un
              idFunExt (x , X) = ΣPathP (leftEq , rightEq)
                where
                  leftEq : (F ⟪ C .id c ⟫) x ≡ x
                  leftEq i = F .F-id i x

                  rightEq : PathP (λ i → fst (P ⟅ c , leftEq i ⟆))
                            ((P ⟪ C .id c , refl ⟫) X) X
                  rightEq = left ▷ right
                    where
                      -- the id morphism in (∫ᴾ F)
                      ∫id = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)

                      -- functoriality of P gives us close to what we want
                      right : (P ⟪ ∫id ⟫) X ≡ X
                      right i = P .F-id i X

                      -- but need to do more work to show that (C .id c , refl) ≡ ∫id
                      left : PathP (λ i → fst (P ⟅ c , leftEq i ⟆))
                                   ((P ⟪ C .id c , refl ⟫) X)
                                   ((P ⟪ ∫id ⟫) X)
                      left i = (P ⟪ ∫ᴾhomEq {F = F} (C .id c , refl) ∫id (λ i → (c , leftEq i)) refl refl i ⟫) X
        L-ob-ob .F-seq {x = c} {d} {e} f g
          = funExt seqFunEq
            where
              -- for every (x , X) where x is in F ⟅ c ⟆ and X is its image under P
              -- the functions obtained by sequencing then functoring and functoring
              -- then sequencing do the same thing
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

    L-hom : ∀ {P Q} → PreShv (∫ᴾ F) [ P , Q ] →
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
                 -- → (x , ((η ⟦ d , ())))

        com : arr ⋆⟨ PreShv C ⟩ ψ ≡ ϕ
        com = makeNatTransPath (funExt comFunExt)
          where
            comFunExt : ∀ (c : C .ob)
                      → (arr ●ᵛ ψ) ⟦ c ⟧ ≡ ϕ ⟦ c ⟧
            comFunExt c = funExt λ x → refl

    L : Functor (PreShv (∫ᴾ F)) SliceCat
    L .F-ob = L-ob
    L .F-hom = L-hom

    module _ where
      open Iso
      open Morphism renaming (isIso to isIsoC)
      -- the iso we deserve
      typeSectionIso : ∀ {A B : Type ℓ} {isSetB : isSet B} → (ϕ : A → B)
                    → Iso A (Σ[ b ∈ B ] fiber ϕ b)
      typeSectionIso ϕ .fun a = (ϕ a) , (a , refl)
      typeSectionIso ϕ .inv (b , (a , eq)) = a
      typeSectionIso {isSetB = isSetB} ϕ .rightInv (b , (a , eq))
        = ΣPathP (eq
                 , ΣPathP (refl
                          , isOfHLevel→isOfHLevelDep 1 (λ b' → isSetB _ _) refl eq eq))
      typeSectionIso ϕ .leftInv a = refl

      -- THE NATURAL ISOMORPHISM
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
              homFunExt x = ΣPathP ((λ i → (ϕ .N-hom f i) x) , fiberEqIfRepsEq ϕ refl)

          comm : (A⇒LK) ●ᵛ ψ ≡ ϕ
          comm = makeNatTransPath (funExt λ x → refl)
      ηTrans .N-hom {sliceob {A} α} {sliceob {B} β} (slicehom ϕ eq)
        = SliceHom-≡-intro' (makeNatTransPath (funExt (λ c → funExt λ a → natFunExt c a)))
        where
          natFunExt : ∀ (c : C .ob) (a : fst (A ⟅ c ⟆))
                    → ((β ⟦ c ⟧) ((ϕ ⟦ c ⟧) a) , (ϕ ⟦ c ⟧) a , _) ≡ ((α ⟦ c ⟧) a , (ϕ ⟦ c ⟧) a , _)
          natFunExt c a = ΣPathP ((λ i → ((eq i) ⟦ c ⟧) a) , fiberEqIfRepsEq β refl)


      ηIso : ∀ (sob : SliceCat .ob)
           → isIsoC {C = SliceCat} (ηTrans ⟦ sob ⟧)
      ηIso sob@(sliceob ϕ) = sliceIso _ _ (FUNCTORIso _ _ _ isIsoCf)
        where
          isIsoCf : ∀ (c : C .ob)
                  → isIsoC (ηTrans .N-ob sob .S-hom ⟦ c ⟧)
          isIsoCf c = CatIso→isIso (Iso→CatIso (typeSectionIso {isSetB = snd (F ⟅ c ⟆)} (ϕ ⟦ c ⟧)))

    preshvSlice≃preshvElem : SliceCat ≃ᶜ PreShv (∫ᴾ F)
    preshvSlice≃preshvElem .func = K
    preshvSlice≃preshvElem .isEquiv .invFunc = L
    preshvSlice≃preshvElem .isEquiv .η .trans = ηTrans
    preshvSlice≃preshvElem .isEquiv .η .nIso = ηIso
