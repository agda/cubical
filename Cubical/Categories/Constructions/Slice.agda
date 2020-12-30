{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open Iso
open import Cubical.Foundations.HLevels
open Precategory
open import Cubical.Core.Glue
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport using (transpFill)

module Cubical.Categories.Constructions.Slice {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') (c : C .ob) {{isC : isCategory C}} where

open import Cubical.Data.Sigma


-- just a helper to prevent redundency
TypeC : Type (ℓ-suc (ℓ-max ℓ ℓ'))
TypeC = Type (ℓ-max ℓ ℓ')

-- Components of a slice category

record SliceOb : TypeC where
  constructor sliceob
  field
    {S-ob} : C .ob
    S-arr : C [ S-ob , c ]

open SliceOb public

record SliceHom (a b : SliceOb) : Type ℓ' where
  constructor slicehom
  field
    S-hom : C [ S-ob a , S-ob b ]
    -- commutative diagram
    S-comm : S-hom ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a

open SliceHom

-- Helpers for working with equality
SliceOb-≡-intro : ∀ {a b} {f g}
                 → (p : a ≡ b)
                 → PathP (λ i → C [ p i , c ]) f g
                 → sliceob {a} f ≡ sliceob {b} g
SliceOb-≡-intro p q = λ i → sliceob {p i} (q i)

module _ -- {A : I → Type ℓ} {B : (i : I) → (a : A i) → Type ℓ'}
         {xf yg : SliceOb}where
  private
    x = xf .S-ob
    f = xf .S-arr
    y = yg .S-ob
    g = yg .S-arr

  -- TODO: rename to ...PathΣ
  SOPathIsoPathSO : Iso (xf ≡ yg) (Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g)
  SOPathIsoPathSO .fun p = (λ i → (p i) .S-ob) , (λ i → (p i) .S-arr)
  SOPathIsoPathSO .inv (p , q) i = sliceob {p i} (q i)
  SOPathIsoPathSO .rightInv _ = refl
  SOPathIsoPathSO .leftInv _ = refl

  SOPath≃PathSO = isoToEquiv SOPathIsoPathSO

  SOPath≡PathSO = ua (isoToEquiv SOPathIsoPathSO)

-- intro and elim for working with SliceHom equalities (is there a better way to do this?)
SliceHom-≡-intro : ∀ {a b} {f g} {c₁} {c₂}
                → (p : f ≡ g)
                → PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
                → slicehom f c₁ ≡ slicehom g c₂
SliceHom-≡-intro p q = λ i → slicehom (p i) (q i)

SliceHom-≡-elim : ∀ {a b} {f g} {c₁} {c₂}
                → slicehom f c₁ ≡ slicehom g c₂
                → Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
SliceHom-≡-elim r = (λ i → S-hom (r i)) , λ i → S-comm (r i)

-- SliceHom is isomorphic to the Sigma type with the same components
SliceHom-Σ-Iso : ∀ {a b}
            → Iso (SliceHom a b) (Σ[ h ∈ C [ S-ob a , S-ob b ] ] h ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a)
SliceHom-Σ-Iso .fun (slicehom h c) = h , c
SliceHom-Σ-Iso .inv (h , c) = slicehom h c
SliceHom-Σ-Iso .rightInv = λ x → refl
SliceHom-Σ-Iso .leftInv = λ x → refl


-- Precategory definition

SliceCat : Precategory _ _
SliceCat .ob = SliceOb
SliceCat .Hom[_,_] = SliceHom
SliceCat .id (sliceob {x} f) = slicehom (C .id x) (C .⋆IdL _)
SliceCat ._⋆_ {sliceob j} {sliceob k} {sliceob l} (slicehom f p) (slicehom g p') =
  slicehom
    (f ⋆⟨ C ⟩ g)
    ( f ⋆⟨ C ⟩ g ⋆⟨ C ⟩ l
    ≡⟨ C .⋆Assoc _ _ _ ⟩
      f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ l)
    ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) p' ⟩
      f ⋆⟨ C ⟩ k
    ≡⟨ p ⟩
      j
    ∎)
SliceCat .⋆IdL (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdL C _) (toPathP (isC .isSetHom _ _ _ _))
SliceCat .⋆IdR (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdR C _) (toPathP (isC .isSetHom _ _ _ _))
SliceCat .⋆Assoc f g h =
  SliceHom-≡-intro (⋆Assoc C _ _ _) (toPathP (isC .isSetHom _ _ _ _))


-- SliceCat is a Category

instance
  isCatSlice : isCategory SliceCat
  isCatSlice .isSetHom {a} {b} (slicehom f c₁) (slicehom g c₂) p q = cong isoP p'≡q'
    where
      -- paths between SliceHoms are equivalent to the projection paths
      p' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      p' = SliceHom-≡-elim p
      q' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      q' = SliceHom-≡-elim q

      -- we want all paths between (dependent) paths of this type to be equal
      B = λ v → v ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a

      -- need the groupoidness for dependent paths
      homIsGroupoidDep : isOfHLevelDep 2 B
      homIsGroupoidDep = isOfHLevel→isOfHLevelDep 2 (λ v x y → isSet→isGroupoid (isC .isSetHom) _ _ x y)

      -- we first prove that the projected paths are equal
      p'≡q' : p' ≡ q'
      p'≡q' = ΣPathP ((isC .isSetHom _ _ _ _) , toPathP (homIsGroupoidDep _ _ _ _ _))

      -- and then we can use equivalence to lift these paths up
      -- to actual SliceHom paths
      isoP = λ g → cong (inv SliceHom-Σ-Iso) (fun (ΣPathIsoPathΣ) g)

-- symCI-id : PathP

module _ ⦃ isU : isUnivalent C ⦄ where
  open CatIso
  open Iso

  module _ { xf yg : SliceOb } where
    x = xf .S-ob
    y = yg .S-ob
    pToI-isEquiv : isEquiv (pathToIso {C = C} x y)
    pToI-isEquiv = isU .univ x y

    pathIsoEquiv : (x ≡ y) ≃ (CatIso x y)
    pathIsoEquiv = pathToIso {C = C} x y , pToI-isEquiv

    isoPathEquiv : (CatIso x y) ≃ (x ≡ y)
    isoPathEquiv = invEquiv pathIsoEquiv

    cIso' : Iso (x ≡ y) (CatIso x y)
    cIso' = equivToIso pathIsoEquiv
  instance
    preservesUnivalenceSlice : isUnivalent SliceCat
    preservesUnivalenceSlice .univ xf@(sliceob {x} f) yg@(sliceob {y} g) = isoToIsEquiv sIso
      where
        cIso : Iso (x ≡ y) (CatIso x y)
        cIso = cIso' {xf = xf} {yg}

        sIso : Iso (xf ≡ yg) (CatIso xf yg)
        sIso .fun p = pathToIso xf yg p
        sIso .inv (catiso kc kc⁻¹ s r) = SliceOb-≡-intro x≡y (symP (sym (kc⁻¹ .S-comm) ◁ k⁻¹f≡f))
          where
            -- morphisms in C from kc and kc⁻¹
            k = kc .S-hom
            k⁻¹ = kc⁻¹ .S-hom

            -- the iso in SliceCat we're given induces an iso in C between x and y
            extractIso : CatIso {C = C} x y
            extractIso .mor = k
            extractIso .inv = k⁻¹
            extractIso .sec i = (s i) .S-hom
            extractIso .ret i = (r i) .S-hom

            -- and we can use univalence of C to get x ≡ y
            x≡y : x ≡ y
            x≡y = cIso .inv extractIso

            -- to show that f ≡ g, we show that k⁻¹ ≡ id
            -- by using C's isomorphism
            pToI≡id : PathP (λ i → C [ x≡y (~ i) , x ]) (pathToIso {C = C} x y x≡y .inv) (C .id x)
            pToI≡id = J (λ y p → PathP (λ i → C [ p (~ i) , x ]) (pathToIso {C = C} x y p .inv) (C .id x))
                        (λ j → JRefl pToIFam pToIBase j .inv)
                        x≡y
              where
                idx = C .id x
                pToIFam = (λ z _ → CatIso {C = C} x z)
                pToIBase = catiso (C .id x) idx (C .⋆IdL idx) (C .⋆IdL idx)

            k⁻¹≡pToI : k⁻¹ ≡ pathToIso {C = C} x y x≡y .inv
            k⁻¹≡pToI i = cIso .rightInv extractIso (~ i) .inv

            k⁻¹≡id : PathP (λ i → C [ x≡y (~ i) , x ]) k⁻¹ (C .id x)
            k⁻¹≡id = k⁻¹≡pToI ◁ pToI≡id

            k⁻¹f≡f : PathP (λ i → C [ x≡y (~ i) , c ]) (k⁻¹ ⋆⟨ C ⟩ f) f
            k⁻¹f≡f = (λ i → (k⁻¹≡id i) ⋆⟨ C ⟩ f) ▷ C .⋆IdL _

        sIso .rightInv is@(catiso kc lc s r) i = catiso (kc'≡kc i) (lc'≡lc i) (s'≡s i) (r'≡r i)
          where
            kc' = (sIso .fun) (sIso .inv is) .mor
            lc' = (sIso .fun) (sIso .inv is) .inv
            k' = kc' .S-hom
            l' = lc' .S-hom
            k = kc .S-hom
            l = lc .S-hom

            -- the iso in SliceCat we're given induces an iso in C between x and y
            extractIso : CatIso {C = C} x y
            extractIso .mor = k
            extractIso .inv = l
            extractIso .sec i = (s i) .S-hom
            extractIso .ret i = (r i) .S-hom

            -- we do the equality component wise

            k'≡k : k' ≡ k
            k'≡k i = (cIso .rightInv extractIso) i .mor
            kcom'≡kcom : PathP (λ j → (k'≡k j) ⋆⟨ C ⟩ g ≡ f) (kc' .S-comm) (kc .S-comm)
            kcom'≡kcom = isSetHomP _ _ λ i → (k'≡k i) ⋆⟨ C ⟩ g
            kc'≡kc : kc' ≡ kc
            kc'≡kc i = slicehom (k'≡k i) (kcom'≡kcom i)

            l'≡l : l' ≡ l
            l'≡l i = (cIso .rightInv extractIso) i .inv
            lcom'≡lcom : PathP (λ j → (l'≡l j) ⋆⟨ C ⟩ f ≡ g) (lc' .S-comm) (lc .S-comm)
            lcom'≡lcom = isSetHomP _ _ λ i → (l'≡l i) ⋆⟨ C ⟩ f
            lc'≡lc : lc' ≡ lc
            lc'≡lc i = slicehom (l'≡l i) (lcom'≡lcom i)

            s' = (sIso .fun) (sIso .inv is) .sec
            s'≡s : PathP (λ i → lc'≡lc i ⋆⟨ SliceCat ⟩ kc'≡kc i ≡ SliceCat .id _) s' s
            s'≡s = isSetHomP _ _ λ i → lc'≡lc i ⋆⟨ SliceCat ⟩ kc'≡kc i

            r' = (sIso .fun) (sIso .inv is) .ret
            r'≡r : PathP (λ i → kc'≡kc i ⋆⟨ SliceCat ⟩ lc'≡lc i ≡ SliceCat .id _) r' r
            r'≡r = isSetHomP _ _ λ i → kc'≡kc i ⋆⟨ SliceCat ⟩ lc'≡lc i

        sIso .leftInv p = allTog
          where
            p' = (sIso .inv) (sIso .fun p)

            pOb : x ≡ y
            pOb i = (p i) .S-ob

            p'Ob : x ≡ y
            p'Ob i = (p' i) .S-ob


            pMor : PathP (λ i → C [ pOb i , c ]) f g
            pMor i = (p i) .S-arr

            p'Mor : PathP (λ i → C [ p'Ob i , c ]) f g
            p'Mor i = (p' i) .S-arr

            extractIso : ∀ {yg' : _} → CatIso xf yg' → CatIso {C = C} x (yg' .S-ob)
            extractIso (catiso kc lc s r) .mor = kc .S-hom
            extractIso (catiso kc lc s r) .inv = lc .S-hom
            extractIso (catiso kc lc s r) .sec i = (s i) .S-hom
            extractIso (catiso kc lc s r) .ret i = (r i) .S-hom

            a1 : extractIso (pathToIso xf yg p) ≡ cIso .fun pOb
            a1 = J (λ yg' p̃ → extractIso (pathToIso xf yg' p̃) ≡ cIso' {xf = xf} {yg'} .fun (λ i → (p̃ i) .S-ob))
                   (cong extractIso (JRefl pToIFam' pToIBase') ∙ sym (JRefl pToIFam pToIBase)) p
               where
                 -- TODO : extract out logic
                 idx = C .id x
                 pToIFam = (λ z _ → CatIso {C = C} x z)
                 pToIBase = catiso (C .id x) idx (C .⋆IdL idx) (C .⋆IdL idx)

                 idxf = SliceCat .id xf
                 pToIFam' = (λ z _ → CatIso {C = SliceCat} xf z)
                 pToIBase' = catiso (SliceCat .id xf) idxf (SliceCat .⋆IdL idxf) (SliceCat .⋆IdL idxf)

            -- TODO: rename
            pppp : p'Ob ≡ (cIso .inv) (extractIso (sIso .fun p))
            pppp = refl
            ppp : p'Ob ≡ (cIso .inv) (cIso .fun pOb)
            -- ideas:
            -- use J
            -- rewrite fun to try to make this follow definitionally
            ppp = pppp ∙ (cong (cIso .inv) a1)
            -- ppp = J (λ yg' p̃ → {!(λ i → (sIso .inv) (sIso .fun p̃) .S-ob) (cIso .inv) (cIso .fun pOb)!}) {!!} p -- (refl {x = p'} i j) .S-ob

            p'Ob≡pOb : p'Ob ≡ pOb
            p'Ob≡pOb = ppp ∙ cIso .leftInv pOb

            p'Mor≡pMor : PathP (λ j → PathP (λ i → C [ (p'Ob≡pOb j) i , c ]) f g) p'Mor pMor
            p'Mor≡pMor = isOfHLevel→isOfHLevelDep 2 {B = λ a → C [ a , c ]} (λ a → isC .isSetHom {x = a}) _ _ p'Mor pMor p'Ob≡pOb

            -- to put it all together, use something like ΣPathP≡PathPΣ from Data.Sigma
            allTog : p' ≡ p
            -- allTog = transpFill {A = xf ≡ yg} {!i0!} (λ i → inS ((SOPath≡PathSO ∙ sym SOPath≡PathSO) i)) p' ∙ fromPathP (compPathP left right)
            allTog i = comp (λ i' → SOPath≡PathSO {xf = xf} {yg} (~ i'))
                            (λ j → λ { (i = i0) → left (~ j) ; (i = i1) → right j })
                            (p'Σ≡pΣ i)
              where
                p'ΣT : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                p'ΣT = transport SOPath≡PathSO p'
                p'Σ : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                p'Σ = (p'Ob , p'Mor)

                -- using the computation rule to ua
                p'ΣT≡p'Σ : p'ΣT ≡ p'Σ
                p'ΣT≡p'Σ = uaβ SOPath≃PathSO p'


                pΣT : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                pΣT = transport SOPath≡PathSO p
                pΣ : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                pΣ = (pOb , pMor)-- transport SOPathP≡PathPSO p

                -- using the computation rule to ua
                pΣT≡pΣ : pΣT ≡ pΣ
                pΣT≡pΣ = uaβ SOPath≃PathSO p

                p'Σ≡pΣ : p'Σ ≡ pΣ
                p'Σ≡pΣ = ΣPathP (p'Ob≡pOb , p'Mor≡pMor)

                left : PathP (λ i → SOPath≡PathSO {xf = xf} {yg} i) p' p'Σ
                left = transport-filler SOPath≡PathSO p' ▷ p'ΣT≡p'Σ

                right : PathP (λ i → SOPath≡PathSO {xf = xf} {yg} (~ i)) pΣ p
                right = sym (pΣT≡pΣ) ◁ symP (transport-filler SOPath≡PathSO p)
