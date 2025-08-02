
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport using (transpFill)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Morphism

open import Cubical.Data.Sigma

open Category
open isUnivalent
open Iso

module Cubical.Categories.Constructions.Slice.Base {ℓ ℓ' : Level} (C : Category ℓ ℓ') (c : C .ob) where

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

open SliceHom public

-- Helpers for working with equality
-- can probably replace these by showing that SliceOb is isomorphic to Sigma and
-- that paths are isomorphic to Sigma? But sounds like that would need a lot of transp

SliceOb-≡-intro : ∀ {a b} {f : C [ a , c ]} {g : C [ b , c ]}
                 → (p : a ≡ b)
                 → PathP (λ i → C [ p i , c ]) f g
                 → sliceob {a} f ≡ sliceob {b} g
SliceOb-≡-intro p q = λ i → sliceob {p i} (q i)

module _ {xf yg : SliceOb} where
  private
    x = xf .S-ob
    f = xf .S-arr
    y = yg .S-ob
    g = yg .S-arr

  -- a path between slice objects is the "same" as a pair of paths between C obs and C arrows
  SOPathIsoPathΣ : Iso (xf ≡ yg) (Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g)
  SOPathIsoPathΣ .fun p = (λ i → (p i) .S-ob) , (λ i → (p i) .S-arr)
  SOPathIsoPathΣ .inv (p , q) i = sliceob {p i} (q i)
  SOPathIsoPathΣ .rightInv _ = refl
  SOPathIsoPathΣ .leftInv _ = refl

  SOPath≃PathΣ = isoToEquiv SOPathIsoPathΣ

  SOPath≡PathΣ = ua (isoToEquiv SOPathIsoPathΣ)

-- If the type of objects of C forms a set then so does the type of objects of the slice cat
module _ (isSetCOb : isSet (C .ob)) where
  isSetSliceOb : isSet SliceOb
  isSetSliceOb x y =
    subst
      (λ t → isProp t)
      (sym (SOPath≡PathΣ {xf = x} {yg = y}))
      (isPropΣ
        (isSetCOb (x .S-ob) (y .S-ob))
        λ x≡y →
          subst
            (λ t → isProp t)
            (sym (ua (PathP≃Path (λ i → C [ x≡y i , c ]) (x .S-arr) (y .S-arr))))
            (C .isSetHom (transport (λ i → C [ x≡y i , c ]) (x .S-arr)) (y .S-arr)))

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


SliceHom-≡-intro' : ∀ {a b} {f g : C [ a .S-ob , b .S-ob ]} {c₁} {c₂}
                  → (p : f ≡ g)
                  → slicehom f c₁ ≡ slicehom g c₂
SliceHom-≡-intro' {a} {b} {f} {g} {c₁} {c₂} p i = slicehom (p i) (c₁≡c₂ i)
  where
    c₁≡c₂ : PathP (λ i → (p i) ⋆⟨ C ⟩ (b .S-arr) ≡ a .S-arr) c₁ c₂
    c₁≡c₂ = isOfHLevel→isOfHLevelDep 1 (λ _ → C .isSetHom _ _) c₁ c₂ p

-- SliceHom is isomorphic to the Sigma type with the same components
SliceHom-Σ-Iso : ∀ {a b}
            → Iso (SliceHom a b) (Σ[ h ∈ C [ S-ob a , S-ob b ] ] h ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a)
SliceHom-Σ-Iso .fun (slicehom h c) = h , c
SliceHom-Σ-Iso .inv (h , c) = slicehom h c
SliceHom-Σ-Iso .rightInv = λ x → refl
SliceHom-Σ-Iso .leftInv = λ x → refl


-- Category definition

SliceCat : Category (ℓ-max ℓ ℓ') ℓ'
ob SliceCat = SliceOb
Hom[_,_] SliceCat = SliceHom
id SliceCat = slicehom (C .id) (C .⋆IdL _)
_⋆_ SliceCat {sliceob j} {sliceob k} {sliceob l} (slicehom f p) (slicehom g p') =
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
⋆IdL SliceCat (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdL C _) (toPathP (C .isSetHom _ _ _ _))
⋆IdR SliceCat (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdR C _) (toPathP (C .isSetHom _ _ _ _))
⋆Assoc SliceCat f g h =
  SliceHom-≡-intro (⋆Assoc C _ _ _) (toPathP (C .isSetHom _ _ _ _))
isSetHom SliceCat {a} {b} (slicehom f c₁) (slicehom g c₂) p q = cong isoP p'≡q'
    where
      -- paths between SliceHoms are equivalent to the projection paths
      p' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      p' = SliceHom-≡-elim p
      q' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      q' = SliceHom-≡-elim q

      -- we want all paths between (dependent) paths of this type to be equal
      B = λ v → v ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a

      -- need the groupoidness for dependent paths
      isGroupoidDepHom : isOfHLevelDep 2 B
      isGroupoidDepHom = isOfHLevel→isOfHLevelDep 2 (λ v x y → isSet→isGroupoid (C .isSetHom) _ _ x y)

      -- we first prove that the projected paths are equal
      p'≡q' : p' ≡ q'
      p'≡q' = ΣPathP (C .isSetHom _ _ _ _ , toPathP (isGroupoidDepHom _ _ _ _ _))

      -- and then we can use equivalence to lift these paths up
      -- to actual SliceHom paths
      isoP = λ g → cong (inv SliceHom-Σ-Iso) (fun (ΣPathIsoPathΣ) g)

-- SliceCat is univalent if C is univalent

module _ ⦃ isU : isUnivalent C ⦄ where
  open isIsoC
  open Iso

  module _ { xf yg : SliceOb } where
    private
      x = xf .S-ob
      y = yg .S-ob

    -- names for the equivalences/isos

    pathIsoEquiv : (x ≡ y) ≃ (CatIso _ x y)
    pathIsoEquiv = univEquiv isU x y

    isoPathEquiv : (CatIso _ x y) ≃ (x ≡ y)
    isoPathEquiv = invEquiv pathIsoEquiv

    pToIIso' : Iso (x ≡ y) (CatIso _ x y)
    pToIIso' = equivToIso pathIsoEquiv

    -- the iso in SliceCat we're given induces an iso in C between x and y
    module _ ( cIso@(kc , isiso lc s r) : CatIso SliceCat xf yg ) where
      extractIso' : CatIso C x y
      extractIso' .fst = kc .S-hom
      extractIso' .snd .inv = lc .S-hom
      extractIso' .snd .sec i = (s i) .S-hom
      extractIso' .snd .ret i = (r i) .S-hom

  instance
    preservesUnivalenceSlice : isUnivalent SliceCat
    -- we prove the equivalence by going through Iso
    preservesUnivalenceSlice .univ xf@(sliceob {x} f) yg@(sliceob {y} g) = isoToIsEquiv sIso
      where
        -- this is just here because the type checker can't seem to infer xf and yg
        pToIIso : Iso (x ≡ y) (CatIso _ x y)
        pToIIso = pToIIso' {xf = xf} {yg}

        -- the meat of the proof
        sIso : Iso (xf ≡ yg) (CatIso _ xf yg)
        sIso .fun p = pathToIso p -- we use the normal pathToIso via path induction to get an isomorphism
        sIso .inv is@(kc , isiso lc s r) = SliceOb-≡-intro x≡y (symP (sym (lc .S-comm) ◁ lf≡f))
          where
            -- we get a path between xf and yg by combining paths between
            -- x and y, and f and g
            -- 1. x≡y follows from univalence of C
            -- 2. f≡g is more tricky; by commutativity, we know that g ≡ l ⋆ f
              -- so we want l to be id; we get this by showing: id ≡ pathToIso x y x≡y ≡ l
              -- where the first step follows from path induction, and the second from univalence of C

            -- morphisms in C from kc and lc
            k = kc .S-hom
            l = lc .S-hom

            -- extract out the iso between x and y
            extractIso : CatIso C x y
            extractIso = extractIso' is

            -- and we can use univalence of C to get x ≡ y
            x≡y : x ≡ y
            x≡y = pToIIso .inv extractIso

            -- to show that f ≡ g, we show that l ≡ id
            -- by using C's isomorphism
            pToI≡id : PathP (λ i → C [ x≡y (~ i) , x ]) (pathToIso {C = C} x≡y .snd .inv) (C .id)
            pToI≡id = J (λ y p → PathP (λ i → C [ p (~ i) , x ]) (pathToIso {C = C} p .snd .inv) (C .id))
                        (λ j → JRefl pToIFam pToIBase j .snd .inv)
                        x≡y
              where
                idx = C .id
                pToIFam = (λ z _ → CatIso C x z)
                pToIBase = catiso (C .id) idx (C .⋆IdL idx) (C .⋆IdL idx)

            l≡pToI : l ≡ pathToIso {C = C} x≡y .snd .inv
            l≡pToI i = pToIIso .rightInv extractIso (~ i) .snd .inv

            l≡id : PathP (λ i → C [ x≡y (~ i) , x ]) l (C .id)
            l≡id = l≡pToI ◁ pToI≡id

            lf≡f : PathP (λ i → C [ x≡y (~ i) , c ]) (l ⋆⟨ C ⟩ f) f
            lf≡f = (λ i → (l≡id i) ⋆⟨ C ⟩ f) ▷ C .⋆IdL _

        sIso .rightInv is@(kc , isiso lc s r) i = catiso (kc'≡kc i) (lc'≡lc i) (s'≡s i) (r'≡r i)
          -- we prove rightInv using a combination of univalence and the fact that homs are an h-set
          where
            kc' = (sIso .fun) (sIso .inv is) .fst
            lc' = (sIso .fun) (sIso .inv is) .snd .inv
            k' = kc' .S-hom
            l' = lc' .S-hom
            k = kc .S-hom
            l = lc .S-hom

            extractIso : CatIso C x y
            extractIso = extractIso' is

            -- we do the equality component wise

            -- mor

            k'≡k : k' ≡ k
            k'≡k i = (pToIIso .rightInv extractIso) i .fst

            kcom'≡kcom : PathP (λ j → (k'≡k j) ⋆⟨ C ⟩ g ≡ f) (kc' .S-comm) (kc .S-comm)
            kcom'≡kcom = isSetHomP1 {C = C} _ _ λ i → (k'≡k i) ⋆⟨ C ⟩ g
            kc'≡kc : kc' ≡ kc
            kc'≡kc i = slicehom (k'≡k i) (kcom'≡kcom i)

            -- inv

            l'≡l : l' ≡ l
            l'≡l i = (pToIIso .rightInv extractIso) i .snd .inv

            lcom'≡lcom : PathP (λ j → (l'≡l j) ⋆⟨ C ⟩ f ≡ g) (lc' .S-comm) (lc .S-comm)
            lcom'≡lcom = isSetHomP1 {C = C} _ _ λ i → (l'≡l i) ⋆⟨ C ⟩ f

            lc'≡lc : lc' ≡ lc
            lc'≡lc i = slicehom (l'≡l i) (lcom'≡lcom i)

            -- sec

            s' = (sIso .fun) (sIso .inv is) .snd .sec
            s'≡s : PathP (λ i → lc'≡lc i ⋆⟨ SliceCat ⟩ kc'≡kc i ≡ SliceCat .id) s' s
            s'≡s = isSetHomP1 {C = SliceCat} _ _ λ i → lc'≡lc i ⋆⟨ SliceCat ⟩ kc'≡kc i

            -- ret

            r' = (sIso .fun) (sIso .inv is) .snd .ret
            r'≡r : PathP (λ i → kc'≡kc i ⋆⟨ SliceCat ⟩ lc'≡lc i ≡ SliceCat .id) r' r
            r'≡r = isSetHomP1 {C = SliceCat} _ _ λ i → kc'≡kc i ⋆⟨ SliceCat ⟩ lc'≡lc i

        sIso .leftInv p = p'≡p
          -- to show that the round trip is equivalent to the identity
          -- we show that this is true for each component (S-ob, S-arr)
          -- and then combine
          -- specifically, we show that p'Ob≡pOb and p'Mor≡pMor
          -- and it follows that p'≡p
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

            -- we first show that it's equivalent to use sIso first then extract, or to extract first than use pToIIso
            extractCom : extractIso' (sIso .fun p) ≡ pToIIso .fun pOb
            extractCom = J (λ yg' p̃ → extractIso' (pathToIso p̃) ≡ pToIIso' {xf = xf} {yg'} .fun (λ i → (p̃ i) .S-ob))
                           (cong extractIso' (JRefl pToIFam' pToIBase') ∙ sym (JRefl pToIFam pToIBase))
                           p
               where
                 idx = C .id
                 pToIFam = (λ z _ → CatIso C x z)
                 pToIBase = catiso (C .id) idx (C .⋆IdL idx) (C .⋆IdL idx)

                 idxf = SliceCat .id
                 pToIFam' = (λ z _ → CatIso SliceCat xf z)
                 pToIBase' = catiso (SliceCat .id) idxf (SliceCat .⋆IdL idxf) (SliceCat .⋆IdL idxf)

            -- why does this not follow definitionally?
            -- from extractCom, we get that performing the roundtrip on pOb gives us back p'Ob
            ppp : p'Ob ≡ (pToIIso .inv) (pToIIso .fun pOb)
            ppp = cong (pToIIso .inv) extractCom

            -- apply univalence of C
            -- this gives us the first component that we want
            p'Ob≡pOb : p'Ob ≡ pOb
            p'Ob≡pOb = ppp ∙ pToIIso .leftInv pOb

            -- isSetHom gives us the second component, path between morphisms
            p'Mor≡pMor : PathP (λ j → PathP (λ i → C [ (p'Ob≡pOb j) i , c ]) f g) p'Mor pMor
            p'Mor≡pMor = isSetHomP2l {C = C} _ _ p'Mor pMor p'Ob≡pOb

            -- we can use the above paths to show that p' ≡ p
            p'≡p : p' ≡ p
            p'≡p i = comp (λ i' → SOPath≡PathΣ {xf = xf} {yg} (~ i'))
                            (λ j → λ { (i = i0) → left (~ j) ; (i = i1) → right (~ j) })
                            (p'Σ≡pΣ i)
              where
                -- we break up p' and p into their constituent paths
                -- first via transport and then via our component definitions from before
                -- we show that p'ΣT ≡ p'Σ (and same for p) via univalence
                -- and p'Σ≡pΣ follows from our work from above
                p'ΣT : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                p'ΣT = transport SOPath≡PathΣ p'
                p'Σ : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                p'Σ = (p'Ob , p'Mor)

                pΣT : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                pΣT = transport SOPath≡PathΣ p
                pΣ : Σ[ p ∈ x ≡ y ] PathP (λ i → C [ p i , c ]) f g
                pΣ = (pOb , pMor)-- transport SOPathP≡PathPSO p

                -- using the computation rule to ua
                p'ΣT≡p'Σ : p'ΣT ≡ p'Σ
                p'ΣT≡p'Σ = uaβ SOPath≃PathΣ p'

                pΣT≡pΣ : pΣT ≡ pΣ
                pΣT≡pΣ = uaβ SOPath≃PathΣ p

                p'Σ≡pΣ : p'Σ ≡ pΣ
                p'Σ≡pΣ = ΣPathP (p'Ob≡pOb , p'Mor≡pMor)

                -- two sides of the square we're connecting
                left : PathP (λ i → SOPath≡PathΣ {xf = xf} {yg} i) p' p'Σ
                left = transport-filler SOPath≡PathΣ p' ▷ p'ΣT≡p'Σ

                right : PathP (λ i → SOPath≡PathΣ {xf = xf} {yg} i) p pΣ
                right = transport-filler SOPath≡PathΣ p ▷ pΣT≡pΣ

-- properties
-- TODO: move to own file

open isIsoC renaming (inv to invC)

-- make a slice isomorphism from just the hom
sliceIso : ∀ {a b} (f : C [ a .S-ob , b .S-ob ]) (c : (f ⋆⟨ C ⟩ b .S-arr) ≡ a .S-arr)
         → isIsoC C f
         → isIsoC SliceCat (slicehom f c)
sliceIso f c isof .invC = slicehom (isof .invC) (sym (invMoveL (isIso→areInv isof) c))
sliceIso f c isof .sec = SliceHom-≡-intro' (isof .sec)
sliceIso f c isof .ret = SliceHom-≡-intro' (isof .ret)
