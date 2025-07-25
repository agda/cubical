{-# OPTIONS --lossy-unification #-}

{-
This file contains
1. Definitions of cellular homotopies and their finite counterpart
2. A proof that (finite) cellular homotopies induce (finite) chain complex maps
-}

module Cubical.CW.Homotopy where

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map
open import Cubical.CW.ChainComplex

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.SetTruncation as ST hiding (map)
open import Cubical.HITs.Truncation as TR hiding (map)

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.ChainComplex

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn

private
  variable
    ℓ ℓ' ℓ'' : Level

-- A cellular homotopy between two cellular maps
record cellHom {C : CWskel ℓ} {D : CWskel ℓ'} (f g : cellMap C D) : Type (ℓ-max ℓ ℓ') where
  constructor cellhom
  open SequenceMap
  field
    hom : (n : ℕ) → (x : C .fst n) → CW↪ D n (f .map n x) ≡ CW↪ D n (g .map n x)
    coh : (n : ℕ) → (c : C .fst n)
      → Square (cong (CW↪ D (suc n)) (hom n c))
                (hom (suc n) (CW↪ C n c))
                (cong (CW↪ D (suc n)) (f .comm n c))
                (cong (CW↪ D (suc n)) (g .comm n c))

-- Finite cellular homotopies
record finCellHom (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'}
                  (f g : finCellMap m C D) : Type (ℓ-max ℓ ℓ') where
  constructor fincellhom
  open FinSequenceMap
  field
    fhom : (n : Fin (suc m)) (x : C .fst (fst n))
         → CW↪ D (fst n) (f .fmap n x) ≡ CW↪ D (fst n) (g .fmap n x)
    fcoh : (n : Fin m) (c : C .fst (fst n))
      → Square (cong (CW↪ D (suc (fst n))) (fhom (injectSuc n) c))
                (fhom (fsuc n) (CW↪ C (fst n) c))
                (cong (CW↪ D (suc (fst n))) (f .fcomm n c))
                (cong (CW↪ D (suc (fst n))) (g .fcomm n c))

open finCellHom

finCellHom↓ : {m : ℕ} {C : CWskel ℓ} {D : CWskel ℓ'}
  {f g : finCellMap (suc m) C D}
  → finCellHom (suc m) f g → finCellHom m (finCellMap↓ f) (finCellMap↓ g)
fhom (finCellHom↓ ϕ) n x = fhom ϕ (injectSuc n) x
fcoh (finCellHom↓ {m = suc m} ϕ) n x = fcoh ϕ (injectSuc n) x

cofibIso : (n : ℕ) (C : CWskel ℓ)
  → Iso (Susp (cofibCW n C)) (SphereBouquet (suc n) (CWskel-fields.A C n))
cofibIso n C =
  compIso (congSuspIso (BouquetIso-gen n
                         (CWskel-fields.card C n)
                         (CWskel-fields.α C n)
                         (CWskel-fields.e C n)))
          sphereBouquetSuspIso

-- Building a chain homotopy from a cell homotopy
module preChainHomotopy (m : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
  (f g : finCellMap m C D) (H : finCellHom m f g) (n : Fin m) where
  open FinSequenceMap
  private
    ℤ[AC_] = CWskel-fields.ℤ[A_] C
    ℤ[AD_] = CWskel-fields.ℤ[A_] D

  -- the homotopy expressed as a map Susp (cofibCW n C) → cofibCW (suc n) D
  Hn+1/Hn : Susp (cofibCW (fst n) C) → cofibCW (suc (fst n)) D
  Hn+1/Hn north = inl tt
  Hn+1/Hn south = inl tt
  Hn+1/Hn (merid (inl tt) i) = inl tt
  Hn+1/Hn (merid (inr x) i) =
       ((push (f .fmap (fsuc n) x))
    ∙∙ (cong inr (H .fhom (fsuc n) x))
    ∙∙ (sym (push (g .fmap (fsuc n) x)))) i
  Hn+1/Hn (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → push (f .fcomm n x j) (~ k)
                   ; (i = i1) → push (g .fcomm n x j) (~ k)
                   ; (j = i0) → push (fhom H (injectSuc n) x i) (~ k) })
          (inr (H .fcoh n x j i))

  -- the homotopy expressed as a map of sphere bouquets
  bouquetHomotopy : SphereBouquet (suc (fst n)) (CWskel-fields.A C (fst n))
                 → SphereBouquet (suc (fst n)) (CWskel-fields.A D (suc (fst n)))
  bouquetHomotopy = Iso.fun bouquetIso ∘ Hn+1/Hn ∘ Iso.inv (cofibIso (fst n) C)
    where
    bouquetIso = BouquetIso-gen (suc (fst n))
                  (CWskel-fields.card D (suc (fst n)))
                  (CWskel-fields.α D (suc (fst n)))
                  (CWskel-fields.e D (suc (fst n)))

  -- the homotopy as a map of abelian groups
  chainHomotopy : AbGroupHom (ℤ[AC (fst n) ]) (ℤ[AD (suc (fst n)) ])
  chainHomotopy = bouquetDegree bouquetHomotopy

-- Now, we would like to prove the chain homotopy equation ∂H + H∂ = f - g
-- MMmaps (Meridian-to-Meridian maps) are a convenient abstraction for the kind of maps
-- that we are going to manipulate
module MMmaps (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m) where
  MMmap : (m1 m2 : (x : C .fst (suc (fst n)))
    → cofibCW (fst n) D) → Type (ℓ-max ℓ ℓ')
  MMmap m1 m2 = (x : C .fst (fst n))
              → m1 (CW↪ C (fst n) x) ≡ m2 (CW↪ C (fst n) x)

  -- the suspension of a cell map as a MMmap
  MMΣcellMap : (f : finCellMap m C D)
       → MMmap (λ x → (inr (f .FinSequenceMap.fmap (fsuc n) x))) (λ x → inl tt)
  MMΣcellMap f x =
      sym (push (f .FinSequenceMap.fmap (injectSuc n) x)
    ∙ (cong inr (f .FinSequenceMap.fcomm n x)))

  -- Addition of MMmaps
  MMmap-add : (m1 m2 m3 : (x : C .fst (suc (fst n)))
    → cofibCW (fst n) D)
    → MMmap m1 m2 → MMmap m2 m3 → MMmap m1 m3
  MMmap-add m1 m2 m3 e1 e2 x = (e1 x) ∙ (e2 x)

  -- Extracting a map between suspensions of cofibCWs from a MMmap
  realiseMMmap : (m1 m2 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
     → MMmap m1 m2 → Susp (cofibCW (fst n) C) → Susp (cofibCW (fst n) D)
  realiseMMmap m1 m2 e north = north
  realiseMMmap m1 m2 e south = north
  realiseMMmap m1 m2 e (merid (inl tt) i) = north
  realiseMMmap m1 m2 e (merid (inr x) i) =
    (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
  realiseMMmap m1 m2 e (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → merid (m1 (CW↪ C (fst n) x)) (~ k)
                   ; (i = i1) → merid (m2 (CW↪ C (fst n) x)) (~ k)
                   ; (j = i0) → merid (e x i) (~ k) })
          (south)

  -- Extracting a map between sphere bouquets from a MMmap
  bouquetMMmap : (m1 m2 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
                 → MMmap m1 m2
                 → SphereBouquet (suc (fst n)) (CWskel-fields.A C (fst n))
                 → SphereBouquet (suc (fst n)) (CWskel-fields.A D (fst n))
  bouquetMMmap m1 m2 f =
      Iso.fun (cofibIso (fst n) D)
    ∘ realiseMMmap m1 m2 f
    ∘ Iso.inv (cofibIso (fst n) C)


-- Expressing the chain homotopy at the level of MMmaps
-- There, it is easy to prove the chain homotopy equation
module MMchainHomotopy* (m : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
  (f g : finCellMap m C D) (H : finCellHom m f g) (n : Fin m) where
  open FinSequenceMap

  open MMmaps C D

  merid-f merid-g merid-tt : (x : C .fst (suc (fst n))) → cofibCW (fst n) D
  merid-f = λ x → inr (f .fmap (fsuc n) x)
  merid-g = λ x → inr (g .fmap (fsuc n) x)
  merid-tt = λ x → inl tt

  MM∂H : MMmap m n merid-f merid-g
  MM∂H x = (sym (cong inr (f .fcomm n x)))
        ∙∙ (cong inr (fhom H (injectSuc n) x))
        ∙∙ (cong inr (g .fcomm n x))

  -- the suspension of f as a MMmap
  MMΣf : MMmap m n merid-f merid-tt
  MMΣf = MMΣcellMap m n f

  -- the suspension of g as a MMmap
  MMΣg : MMmap m n merid-g merid-tt
  MMΣg = MMΣcellMap m n g

  -- the suspension of H∂ as a MMmap
  MMΣH∂ : MMmap m n merid-tt merid-tt
  MMΣH∂ x = sym ((push (f .fmap (injectSuc n) x))
         ∙∙ (cong inr (H .fhom (injectSuc n) x))
         ∙∙ (sym (push (g .fmap (injectSuc n) x))))

  -- the chain homotopy equation at the level of MMmaps
  MMchainHomotopy : ∀ x →
    MMmap-add m n merid-f merid-tt merid-tt
      (MMmap-add m n merid-f merid-g merid-tt MM∂H MMΣg) MMΣH∂ x
    ≡ MMΣf x
  MMchainHomotopy x =
    sym (doubleCompPath-elim (MM∂H x) (MMΣg x) (MMΣH∂ x)) ∙ aux2
    where
      aux : Square (MMΣf x) (MMΣg x) (MM∂H x) (sym (MMΣH∂ x))
      aux i j =
         hcomp (λ k →
           λ {(i = i0) → compPath-filler (push (f .fmap (injectSuc n) x))
                            (λ i₁ → inr (f .fcomm n x i₁)) k (~ j)
            ; (i = i1) → compPath-filler (push (g .fmap (injectSuc n) x))
                            (λ i₁ → inr (g .fcomm n x i₁)) k (~ j)
            ; (j = i1) → (push (f .fmap (injectSuc n) x)
                       ∙∙ (λ i → inr (H .fhom (injectSuc n) x i))
                       ∙∙ (λ i₁ → push (g .fmap (injectSuc n) x) (~ i₁))) i})
                (doubleCompPath-filler
                  (push (f .fmap (injectSuc n) x))
                  (λ i → (inr (H .fhom (injectSuc n) x i)))
                  (λ i₁ → push (g .fmap (injectSuc n) x) (~ i₁)) j i)

      aux2 : (MM∂H x ∙∙ MMΣg x ∙∙ MMΣH∂ x) ≡ MMΣf x
      aux2 i j =
        hcomp (λ k → λ { (j = i0) → MM∂H x ((~ i) ∧ (~ k))
                       ; (j = i1) → MMΣH∂ x (i ∨ k)
                       ; (i = i1) → MMΣf x j })
              (aux (~ i) j)

-- Now we want to transform our MMmap equation to the actual equation
-- First, we connect the involved MMmaps to cofibCW maps
module realiseMMmap (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f g : finCellMap m C D) (H : finCellHom m f g) (n : Fin m) where
  open FinSequenceMap
  open MMmaps C D
  open MMchainHomotopy* m C D f g H
  open preChainHomotopy m C D f g H

  -- an alternative extraction function, that will be useful in some computations
  realiseMMmap2 : (n : Fin m)
       (m1 m2 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
    → MMmap m n m1 m2 → Susp (cofibCW (fst n) C) → Susp (cofibCW (fst n) D)
  realiseMMmap2 n m1 m2 e north = north
  realiseMMmap2 n m1 m2 e south = north
  realiseMMmap2 n m1 m2 e (merid (inl tt) i) = north
  realiseMMmap2 n m1 m2 e (merid (inr x) i) =
    (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
  realiseMMmap2 n m1 m2 e (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → merid (e x (~ j)) (~ k)
                   ; (i = i1) → merid (m2 (CW↪ C (fst n) x)) (~ k)
                   ; (j = i0) → merid (m2 (CW↪ C (fst n) x)) (~ k) })
          (south)

  -- auxiliary lemma which says the two realisation functions are equal
  realiseMMmap1≡2 : (n : Fin m) (m1 m2 : (x : C .fst (suc (fst n)))
    → cofibCW (fst n) D) (e : MMmap m n m1 m2) (x : Susp (cofibCW (fst n) C))
    → realiseMMmap m n m1 m2 e x ≡ realiseMMmap2 n m1 m2 e x
  realiseMMmap1≡2 n m1 m2 e north = refl
  realiseMMmap1≡2 n m1 m2 e south = refl
  realiseMMmap1≡2 n m1 m2 e (merid (inl tt) i) = refl
  realiseMMmap1≡2 n m1 m2 e (merid (inr x) i) = refl
  realiseMMmap1≡2 n m1 m2 e (merid (push x j) i) l =
    hcomp (λ k → λ { (i = i0) → merid (e x ((~ j) ∧ l)) (~ k)
                   ; (i = i1) → merid (m2 (CW↪ C (fst n) x)) (~ k)
                   ; (j = i0) → merid (e x (i ∨ l)) (~ k) })
          south

  -- realisation of MMΣf is equal to Susp f
  realiseMMΣcellMap : (f : finCellMap m C D) (x : Susp (cofibCW (fst n) C))
    → realiseMMmap m n (λ x → (inr (f .fmap (fsuc n) x)))
                        (λ x → inl tt) (MMΣcellMap m n f) x
     ≡ suspFun (prefunctoriality.fn+1/fn m f n) x
  realiseMMΣcellMap f x =
    realiseMMmap1≡2 n (λ x → (inr (f .fmap (fsuc n) x))) (λ x → inl tt)
                      (MMΣcellMap m n f) x ∙ aux x
    where
      aux : (x : Susp (cofibCW (fst n) C)) →
        realiseMMmap2 n (λ x → (inr (f .fmap (fsuc n) x)))
                        (λ x → inl tt) (MMΣcellMap m n f) x
        ≡ suspFun (prefunctoriality.fn+1/fn m f n) x
      aux north = refl
      aux south l = merid (inl tt) l
      aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
      aux (merid (inr x) i) l =
        hcomp (λ k →
          λ { (i = i0) → merid (inr (f .fmap (fsuc n) x)) (~ k)
            ; (i = i1) → merid (inl tt) (l ∨ (~ k))
            ; (l = i1) → merid (inr (f .fmap (fsuc n) x)) (~ k ∨ i) })
         south
      aux (merid (push x j) i) l =
        hcomp (λ k →
         λ {(i = i0) → merid ((push (f .fmap (injectSuc n) x)
                            ∙ (cong inr (f .fcomm n x))) j) (~ k)
          ; (i = i1) → merid (inl tt) (l ∨ (~ k))
          ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
          ; (l = i1) → merid ((push (f .fmap (injectSuc n) x)
                             ∙ (cong inr (f .fcomm n x))) j) (i ∨ (~ k)) })
          south

  -- realisation of MMΣf is equal to Susp f
  realiseMMΣf : (x : Susp (cofibCW (fst n) C)) →
        realiseMMmap m n (merid-f n) (merid-tt n) (MMΣf n) x
        ≡ suspFun (prefunctoriality.fn+1/fn m f n) x
  realiseMMΣf = realiseMMΣcellMap f

  -- realisation of MMΣg is equal to Susp g
  realiseMMΣg : (x : Susp (cofibCW (fst n) C)) →
        realiseMMmap m n (merid-g n) (merid-tt n) (MMΣg n) x
        ≡ suspFun (prefunctoriality.fn+1/fn m g n) x
  realiseMMΣg = realiseMMΣcellMap g

  -- a compact version of ∂ ∘ H
  cof∂H : Susp (cofibCW (fst n) C) → Susp (cofibCW (fst n) D)
  cof∂H north = north
  cof∂H south = north
  cof∂H (merid (inl tt) i) = north
  cof∂H (merid (inr x) i) =
    ((merid (inr (f .fmap (fsuc n) x)))
    ∙∙ refl
    ∙∙ (sym (merid (inr (g .fmap (fsuc n) x))))) i
  cof∂H (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → merid (inr (f .fcomm n x j)) (~ k)
                   ; (i = i1) → merid (inr (g .fcomm n x j)) (~ k)
                   ; (j = i0) → merid (inr (fhom H (injectSuc n) x i)) (~ k) })
          (south)

  -- realisation of MM∂H is equal to cof∂H
  realiseMM∂H : (x : Susp (cofibCW (fst n) C)) →
    realiseMMmap m n (merid-f n) (merid-g n) (MM∂H n) x
    ≡ suspFun (to_cofibCW (fst n) D) (δ (suc (fst n)) D (Hn+1/Hn n x))
  realiseMM∂H x = aux2 x ∙ aux x
    where
      aux : (x : Susp (cofibCW (fst n) C))
        → cof∂H x
         ≡ suspFun (to_cofibCW (fst n) D) (δ (suc (fst n)) D (Hn+1/Hn n x))
      aux north = refl
      aux south = refl
      aux (merid (inl tt) i) = refl
      aux (merid (inr x) i) j =
        hcomp (λ k →
         λ { (i = i0) → merid (inr (f .fmap (fsuc n) x)) (~ k)
           ; (i = i1) → merid (inr (g .fmap (fsuc n) x)) (~ k)
           ; (j = i1) → suspFun (to_cofibCW (fst n) D) (δ (suc (fst n)) D
                (doubleCompPath-filler (push (f .fmap (fsuc n) x))
                                       (cong inr (H .fhom (fsuc n) x))
                                       (sym (push (g .fmap (fsuc n) x))) k i)) })
         south
      aux (merid (push x j) i) k =
        hcomp (λ l →
         λ { (i = i0) → merid (inr (f .fcomm n x j)) (~ l)
           ; (i = i1) → merid (inr (g .fcomm n x j)) (~ l)
           ; (j = i0) → merid (inr (fhom H (injectSuc n) x i)) (~ l)
           ; (k = i1) → suspFun (to_cofibCW (fst n) D) (δ (suc (fst n)) D
         (hfill (λ k → λ { (i = i0) → push (f .fcomm n x j) (~ k)
                       ; (i = i1) → push (g .fcomm n x j) (~ k)
                       ; (j = i0) → push (fhom H (injectSuc n) x i) (~ k)})
                (inS (inr (H .fcoh n x j i))) l))})
            south

      aux2 : (x : Susp (cofibCW (fst n) C)) →
        realiseMMmap m n (λ x → (inr (f .fmap (fsuc n) x)))
                         (λ x → (inr (g .fmap (fsuc n) x))) (MM∂H n) x
        ≡ cof∂H x
      aux2 north = refl
      aux2 south = refl
      aux2 (merid (inl tt) i) = refl
      aux2 (merid (inr x) i) = refl
      aux2 (merid (push x j) i) l =
        hcomp (λ k →
         λ { (i = i0) → merid (inr (f .fcomm n x (j ∨ (~ l)))) (~ k)
           ; (i = i1) → merid (inr (g .fcomm n x (j ∨ (~ l)))) (~ k)
           ; (j = i0) → merid (doubleCompPath-filler
                                (sym (cong inr (f .fcomm n x)))
                                (cong inr (fhom H (injectSuc n) x))
                                (cong inr (g .fcomm n x)) (~ l) i) (~ k) })
         south

-- realisation of MMΣH∂ (suc n) is equal to Susp H∂
realiseMMΣH∂ : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f g : finCellMap (suc m) C D) (H : finCellHom (suc m) f g)
      (n : Fin m) (x : Susp (cofibCW (suc (fst n)) C)) →
       MMmaps.realiseMMmap C D (suc m) (fsuc n) (λ x → inl tt) (λ x → inl tt)
         (MMchainHomotopy*.MMΣH∂ (suc m) C D f g H (fsuc n) ) x
      ≡ suspFun (preChainHomotopy.Hn+1/Hn (suc m) C D f g H (injectSuc n)
               ∘ suspFun (to_cofibCW (fst n) C)
               ∘ δ (suc (fst n)) C) x
realiseMMΣH∂ C D (suc m) f g H n x =
  realiseMMmap1≡2 fzero (fsuc n) (λ x → inl tt)
    (λ x → inl tt) (MMΣH∂ (fsuc n)) x ∙ aux x
  where
  open FinSequenceMap
  open MMmaps C D
  open MMchainHomotopy* (suc (suc m)) C D f g H
  open preChainHomotopy (suc (suc m)) C D f g H
  open realiseMMmap C D (suc (suc m)) f g H

  aux : (x : Susp (cofibCW (suc (fst n)) C)) →
    realiseMMmap.realiseMMmap2 C D (suc (suc m)) f g H fzero (fsuc n)
      (λ x₁ → inl tt) (λ x₁ → inl tt)
      (MMchainHomotopy*.MMΣH∂ (suc (suc m)) C D f g H (fsuc n)) x
    ≡ suspFun (Hn+1/Hn (injectSuc n)
    ∘ (suspFun (to_cofibCW (fst n) C))
    ∘ (δ (suc (fst n)) C)) x
  aux north = refl
  aux south l = merid (inl tt) l
  aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
  aux (merid (inr x) i) l =
    hcomp (λ k → λ { (i = i0) → merid (inl tt) (~ k)
                   ; (i = i1) → merid (inl tt) (l ∨ (~ k))
                   ; (l = i1) → merid (inl tt) (~ k ∨ i) })
          south
  aux (merid (push x j) i) l =
    hcomp (λ k →
     λ { (i = i0) → merid (((push (f .fmap (injectSuc (fsuc n)) x))
                 ∙∙ (cong inr (H .fhom (injectSuc (fsuc n)) x))
                 ∙∙ (sym (push (g .fmap (injectSuc (fsuc n)) x)))) j) (~ k)
       ; (i = i1) → merid (inl tt) (l ∨ (~ k))
       ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
       ; (l = i1) → merid (((push (f .fmap (injectSuc (fsuc n)) x))
                  ∙∙ (cong inr (H .fhom (injectSuc (fsuc n)) x))
                  ∙∙ (sym (push (g .fmap (injectSuc (fsuc n)) x)))) j)
                     (i ∨ (~ k))})
     south

-- realisation of MMΣH∂ zero is constant
realiseMMΣH∂₀ : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f g : finCellMap (suc m) C D) (H : finCellHom (suc m) f g)
      (x : Susp (cofibCW zero C)) →
       MMmaps.realiseMMmap C D (suc m) fzero (λ x → inl tt) (λ x → inl tt)
         (MMchainHomotopy*.MMΣH∂ (suc m) C D f g H fzero) x
      ≡ north
realiseMMΣH∂₀ C D m f g H x =
  realiseMMmap1≡2 fzero fzero (λ x → inl tt)
    (λ x → inl tt) (MMΣH∂ fzero) x ∙ aux x
  where
  open FinSequenceMap
  open MMmaps C D
  open MMchainHomotopy* (suc m) C D f g H
  open preChainHomotopy (suc m) C D f g H
  open realiseMMmap C D (suc m) f g H

  aux : (x : Susp (cofibCW zero C)) →
    realiseMMmap.realiseMMmap2 C D (suc m) f g H fzero fzero
      (λ x₁ → inl tt) (λ x₁ → inl tt)
      (MMchainHomotopy*.MMΣH∂ (suc m) C D f g H fzero) x
    ≡ north
  aux north = refl
  aux south = refl
  aux (merid (inl x) i) = refl
  aux (merid (inr x) i) j =
    hcomp (λ k → λ { (j = i0) → doubleCompPath-filler (merid (inl tt)) (λ _ → south) (λ i → merid (inl tt) (~ i)) k i
                   ; (j = i1) → north
                   ; (i = i0) → merid (inl tt) ((~ j) ∧ (~ k))
                   ; (i = i1) → merid (inl tt) ((~ j) ∧ (~ k)) })
          (merid (inl tt) (~ j))
  aux (merid (push a i₁) i) with (C .snd .snd .snd .fst a)
  aux (merid (push a i₁) i) | ()

-- Then, we connect the addition of MMmaps to the addition of abelian maps
module bouquetAdd where
  open MMmaps

  module _ (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m)
           (m1 m2 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
           (f : MMmap C D m n m1 m2)
           (a : CWskel-fields.A D (fst n)) where

    bouquetMMmap∈cohom-raw : (t : CWskel-fields.A C (fst n))
      → S₊ (suc (fst n)) → S₊ (suc (fst n))
    bouquetMMmap∈cohom-raw t x =
      pickPetal a (bouquetMMmap C D m n m1 m2 f (inr (t , x)))

    bouquetMMmap∈cohom : (t : CWskel-fields.A C (fst n))
      → S₊ (suc (fst n)) → coHomK (suc (fst n))
    bouquetMMmap∈cohom t x = ∣ bouquetMMmap∈cohom-raw t x ∣ₕ

    bouquetMMmap∈cohom' : (x : Susp (cofibCW (fst n) C)) → coHomK (suc (fst n))
    bouquetMMmap∈cohom' x =
      ∣ pickPetal a (Iso.fun (cofibIso (fst n) D)
                   (realiseMMmap C D m n m1 m2 f x)) ∣ₕ

  realiseAdd-merid : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m)
    (m1 m2 m3 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
    (f : MMmap C D m n m1 m2)
    (g : MMmap C D m n m2 m3)
    (b : _)
     → Square (λ j → (realiseMMmap C D m n m1 m2 f (merid b j)))
               (λ j →  (realiseMMmap C D m n m1 m3
                         (MMmap-add C D m n m1 m2 m3 f g) (merid b j)))
               (λ _ → north)
               (λ i →  realiseMMmap C D m n m2 m3 g (merid b i))
  realiseAdd-merid C D m n m1 m2 m3 f g (inl tt) i j = north
  realiseAdd-merid C D m n m1 m2 m3 f g (inr x) i j =
    hcomp (λ k → λ { (i ∨ j = i0) → merid (m1 x) (~ k)
                   ; (i ∨ (~ j) = i0) → merid (m2 x) (~ k)
                   ; (i ∧ (~ j) = i1) → merid (m1 x) (~ k)
                   ; (i ∧ j = i1) → merid (m3 x) (~ k)
                   ; (j = i0) → merid (m1 x) (~ k) })
          south
  realiseAdd-merid C D m n m1 m2 m3 f g (push a l) i j =
    hcomp (λ k →
     λ { (i ∨ j = i0) → merid (m1 (CW↪ C (fst n) a)) (~ k)
       ; (i ∨ (~ j) = i0) → merid (m2 (CW↪ C (fst n) a)) (~ k)
       ; (i ∨ l = i0) → merid (f a j) (~ k)
       ; (i ∧ (~ j) = i1) → merid (m1 (CW↪ C (fst n) a)) (~ k)
       ; (i ∧ j = i1) → merid (m3 (CW↪ C (fst n) a)) (~ k)
       ; (i ∧ (~ l) = i1) → merid (MMmap-add C D m n m1 m2 m3 f g a j) (~ k)
       ; (j = i0) → merid (m1 (CW↪ C (fst n) a)) (~ k)
       ; (j ∧ (~ l) = i1) → merid (g a i) (~ k)
       ; (l = i0) → merid (doubleCompPath-filler (refl) (f a) (g a) i j) (~ k)})
       south

  bouquetMMmap∈cohom'+ :
    (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m)
    (m1 m2 m3 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
    (f : MMmap C D m n m1 m2)
    (g : MMmap C D m n m2 m3)
    (a : CWskel-fields.A D (fst n))
    (x : _)
     → bouquetMMmap∈cohom' C D m n m1 m3 (MMmap-add C D m n m1 m2 m3 f g) a x
     ≡ bouquetMMmap∈cohom' C D m n m1 m2 f a x
     +ₖ bouquetMMmap∈cohom' C D m n m2 m3 g a x
  bouquetMMmap∈cohom'+ C D m (zero , p) m1 m2 m3 f g a north = refl
  bouquetMMmap∈cohom'+ C D m (zero , p) m1 m2 m3 f g a south = refl
  bouquetMMmap∈cohom'+ C D m (zero , p) m1 m2 m3 f g a (merid b i) j =
    ((sym (PathP→compPathL (help b))
      ∙ sym (lUnit _))
    ∙ ∙≡+₁ (λ i → bouquetMMmap∈cohom' C D m (zero , p) m1 m2 f a (merid b i))
           (λ i → bouquetMMmap∈cohom' C D m (zero , p) m2 m3 g a (merid b i))) j i
    where
    help : (b : _)
      → PathP (λ i → ∣ base ∣ₕ
                     ≡ cong (bouquetMMmap∈cohom' C D m (zero , p) m2 m3 g a)
                            (merid b) i)
           (cong (bouquetMMmap∈cohom' C D m (zero , p) m1 m2 f a)
                  (merid b))
           (cong (bouquetMMmap∈cohom' C D m (zero , p) m1 m3
                   (MMmap-add C D m (zero , p) m1 m2 m3 f g) a)
                 (merid b))
    help b i j =
      ∣ pickPetal a (Iso.fun (cofibIso zero D)
                     (realiseAdd-merid C D m (zero , p) m1 m2 m3 f g b i j)) ∣ₕ
  bouquetMMmap∈cohom'+ C D m (suc n , p) m1 m2 m3 f g a north = refl
  bouquetMMmap∈cohom'+ C D m (suc n , p) m1 m2 m3 f g a south = refl
  bouquetMMmap∈cohom'+ C D m (suc n , p) m1 m2 m3 f g a (merid b i) j =
    ((sym (PathP→compPathL (help b))
      ∙ sym (lUnit _))
    ∙ ∙≡+₂ n (λ i → bouquetMMmap∈cohom' C D m (suc n , p) m1 m2 f a (merid b i))
           (λ i → bouquetMMmap∈cohom' C D m (suc n , p) m2 m3 g a (merid b i))) j i
    where
    help : (b : _)
      → PathP (λ i → ∣ north ∣ₕ
                    ≡ cong (bouquetMMmap∈cohom' C D m (suc n , p) m2 m3 g a)
                           (merid b) i)
           (cong (bouquetMMmap∈cohom' C D m (suc n , p) m1 m2 f a)
                 (merid b))
           (cong (bouquetMMmap∈cohom' C D m (suc n , p) m1 m3
                   (MMmap-add C D m (suc n , p) m1 m2 m3 f g) a)
                 (merid b))
    help b i j =
      ∣ pickPetal a (Iso.fun (cofibIso (suc n) D)
                     (realiseAdd-merid C D m (suc n , p) m1 m2 m3 f g b i j)) ∣ₕ

  bouquetMMmap∈cohom+ : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m)
    (m1 m2 m3 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
    (f : MMmap C D m n m1 m2)
    (g : MMmap C D m n m2 m3)
    (t : CWskel-fields.A C (fst n))
    (a : CWskel-fields.A D (fst n))
    (x : S₊ (suc (fst n)))
     → bouquetMMmap∈cohom C D m n m1 m3
         (MMmap-add C D m n m1 m2 m3 f g) a t x
     ≡ bouquetMMmap∈cohom C D m n m1 m2 f a t x
    +ₖ bouquetMMmap∈cohom C D m n m2 m3 g a t x
  bouquetMMmap∈cohom+ C D m n m1 m2 m3 f g t a x =
    bouquetMMmap∈cohom'+ C D m n m1 m2 m3 f g a
      (Iso.inv (cofibIso (fst n) C) (inr (t , x)))

  module _  (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ) (n : Fin m)
            (m1 m2 m3 : (x : C .fst (suc (fst n))) → cofibCW (fst n) D)
            (f : MMmap C D m n m1 m2) (g : MMmap C D m n m2 m3) where
    realiseMMmap-hom :
        bouquetDegree (bouquetMMmap C D m n m1 m3
                        (MMmap-add C D m n m1 m2 m3 f g))
      ≡ addGroupHom _ _ (bouquetDegree (bouquetMMmap C D m n m1 m2 f))
                        (bouquetDegree (bouquetMMmap C D m n m2 m3 g))
    realiseMMmap-hom =
      agreeOnℤFinGenerator→≡ λ t → funExt λ a
        → sym (isGeneratorℤFinGenerator'
                (λ a₁ → degree (suc (fst n))
                  λ x → pickPetal a (bouquetMMmap C D m n m1 m3
                                      (MMmap-add C D m n m1 m2 m3 f g)
                           (inr (a₁ , x)))) t)
         ∙ cong (fst (Hⁿ-Sⁿ≅ℤ (fst n)) .Iso.fun ∘ ∣_∣₂)
                (funExt (bouquetMMmap∈cohom+ C D m n m1 m2 m3 f g t a))
        ∙∙ IsGroupHom.pres· (snd (Hⁿ-Sⁿ≅ℤ (fst n)))
             (∣ (λ x → ∣ pickPetal a
                         (bouquetMMmap C D m n m1 m2 f (inr (t , x))) ∣ₕ) ∣₂)
             (∣ (λ x → ∣ pickPetal a
                         (bouquetMMmap C D m n m2 m3 g (inr (t , x))) ∣ₕ) ∣₂)
        ∙∙ cong₂ _+_ (isGeneratorℤFinGenerator'
                (λ a₁ → degree (suc (fst n))
                  λ x → pickPetal a (bouquetMMmap C D m n m1 m2 f
                           (inr (a₁ , x)))) t)
                      (isGeneratorℤFinGenerator'
                (λ a₁ → degree (suc (fst n))
                  λ x → pickPetal a (bouquetMMmap C D m n m2 m3 g
                           (inr (a₁ , x)))) t)

-- Now we have all the ingredients, we can get the chain homotopy equation
module chainHomEquation (m : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
  (f g : finCellMap m C D) (H : finCellHom m f g) (n : Fin m) where
  open SequenceMap
  open MMmaps C D m n
  open MMchainHomotopy* m C D f g H n
  open preChainHomotopy m C D f g H

  private
    ℤ[AC_] = CWskel-fields.ℤ[A_] C
    ℤ[AD_] = CWskel-fields.ℤ[A_] D

  -- The four abelian group maps that are involved in the equation
  ∂H H∂ fn gn : AbGroupHom (ℤ[AC (fst n) ]) (ℤ[AD (fst n) ])

  ∂H = compGroupHom (chainHomotopy n) (∂ D (fst n))
  -- H∂ = compGroupHom (∂ C (fst n)) (chainHomotopy (injectSuc n))
  H∂ = bouquetDegree (bouquetMMmap merid-tt merid-tt MMΣH∂)
  fn = prefunctoriality.chainFunct m f n
  gn = prefunctoriality.chainFunct m g n

  -- Technical lemma regarding suspensions of Iso's
  suspIso-suspFun : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'}
    {C : Type ℓ''} {D : Type ℓ'''}
    (e1 : Iso A B) (e2 : Iso C D) (f : C → A)
    → Iso.fun (congSuspIso e1) ∘ (suspFun f) ∘ Iso.inv (congSuspIso e2)
     ≡ suspFun (Iso.fun e1 ∘ f ∘ Iso.inv e2)
  suspIso-suspFun e1 e2 f i north = north
  suspIso-suspFun e1 e2 f i south = south
  suspIso-suspFun e1 e2 f i (merid a j) =
    merid ((Iso.fun e1 ∘ f ∘ Iso.inv e2) a) j

  BouquetIso : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
    → Iso (cofibCW n C) (SphereBouquet n (Fin (CWskel-fields.card C n)))
  BouquetIso C n =
    BouquetIso-gen n
      (CWskel-fields.card C n) (CWskel-fields.α C n) (CWskel-fields.e C n)

  -- Technical lemma to pull bouquetSusp out of a suspended cofibCW map
  cofibIso-suspFun : (n : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
    (f : cofibCW n C → cofibCW n D)
    → Iso.fun (cofibIso n D) ∘ (suspFun f) ∘ Iso.inv (cofibIso n C)
    ≡ bouquetSusp→ ((Iso.fun (BouquetIso D n)) ∘ f ∘ Iso.inv (BouquetIso C n))
  cofibIso-suspFun n C D f =
    cong (λ X → Iso.fun sphereBouquetSuspIso ∘ X ∘ Iso.inv sphereBouquetSuspIso)
           (suspIso-suspFun (BouquetIso D n) (BouquetIso C n) f)

  -- connecting MM∂H to ∂H
  bouquet∂H : bouquetDegree (bouquetMMmap merid-f merid-g MM∂H) ≡ ∂H
  bouquet∂H =
    cong (λ X → bouquetDegree ((Iso.fun (cofibIso (fst n) D))
                ∘ X ∘ (Iso.inv (cofibIso (fst n) C))))
         (funExt (realiseMMmap.realiseMM∂H C D m f g H n))
      ∙ cong bouquetDegree ιδH≡pre∂∘H
      ∙ bouquetDegreeComp (preboundary.pre∂ D (fst n))
                          (bouquetHomotopy n)
    where
      ιδH : SphereBouquet (suc (fst n))
              (Fin (CWskel-fields.card C (fst n)))
          → SphereBouquet (suc (fst n))
              (Fin (CWskel-fields.card D (fst n)))
      ιδH = Iso.fun (cofibIso (fst n) D)
           ∘ suspFun (to_cofibCW (fst n) D)
           ∘ δ (suc (fst n)) D
           ∘ Hn+1/Hn n
           ∘ Iso.inv (cofibIso (fst n) C)

      ιδH≡pre∂∘H : ιδH ≡ (preboundary.pre∂ D (fst n))
                        ∘ bouquetHomotopy n
      ιδH≡pre∂∘H =
        cong (λ X → Iso.fun (cofibIso (fst n) D)
                     ∘ suspFun (to_cofibCW (fst n) D)
                     ∘ δ (suc (fst n)) D ∘ X ∘ Hn+1/Hn n
                     ∘ Iso.inv (cofibIso (fst n) C))
              (sym (funExt (Iso.leftInv (BouquetIso D (suc (fst n))))))

  -- connecting MMΣf to fn+1
  bouquetΣf : bouquetDegree (bouquetMMmap merid-f merid-tt MMΣf) ≡ fn
  bouquetΣf = cong (λ X → bouquetDegree ((Iso.fun (cofibIso (fst n) D))
                         ∘ X ∘ (Iso.inv (cofibIso (fst n) C))))
         (funExt (realiseMMmap.realiseMMΣf C D m f g H n))
    ∙ (cong bouquetDegree (cofibIso-suspFun (fst n) C D
                           (prefunctoriality.fn+1/fn m f n)))
    ∙ sym (bouquetDegreeSusp (prefunctoriality.bouquetFunct m f n))

  -- connecting MMΣg to gn+1
  bouquetΣg : bouquetDegree (bouquetMMmap merid-g merid-tt MMΣg) ≡ gn
  bouquetΣg = cong (λ X → bouquetDegree ((Iso.fun (cofibIso (fst n) D))
                          ∘ X ∘ (Iso.inv (cofibIso (fst n) C))))
         (funExt (realiseMMmap.realiseMMΣg C D m f g H n))
    ∙ (cong bouquetDegree (cofibIso-suspFun (fst n) C D
                            (prefunctoriality.fn+1/fn m g n)))
    ∙ sym (bouquetDegreeSusp (prefunctoriality.bouquetFunct m g n))

  -- Alternative formulation of the chain homotopy equation
  chainHomotopy1 : addGroupHom _ _ (addGroupHom _ _ ∂H gn) H∂ ≡ fn
  chainHomotopy1 =
      cong (λ X → addGroupHom _ _ X H∂) aux
    ∙ aux2
    ∙ cong (λ X → bouquetDegree (bouquetMMmap merid-f merid-tt X))
      (funExt MMchainHomotopy)
    ∙ bouquetΣf
    where
      module T = MMchainHomotopy* m C D f g H n
      MM∂H+MMΣg = MMmap-add T.merid-f T.merid-g T.merid-tt T.MM∂H T.MMΣg
      MM∂H+MMΣg+MMΣH∂ = MMmap-add merid-f merid-tt merid-tt MM∂H+MMΣg MMΣH∂

      aux : addGroupHom _ _ ∂H gn
        ≡ bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg)
      aux = cong₂ (λ X Y → addGroupHom _ _ X Y) (sym bouquet∂H) (sym bouquetΣg)
            ∙ sym (bouquetAdd.realiseMMmap-hom C D m n
                    T.merid-f T.merid-g T.merid-tt T.MM∂H T.MMΣg)

      aux2 : addGroupHom _ _
                (bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg)) H∂
           ≡ bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg+MMΣH∂)
      aux2 = sym (bouquetAdd.realiseMMmap-hom C D m n
                     T.merid-f T.merid-tt T.merid-tt MM∂H+MMΣg T.MMΣH∂)

  -- Standard formulation of the chain homotopy equation
  chainHomotopy2 : subtrGroupHom _ _ fn gn ≡ addGroupHom _ _ ∂H H∂
  chainHomotopy2 =
    GroupHom≡ (funExt λ x → aux (fn .fst x) (∂H .fst x) (gn .fst x)
               (H∂ .fst x) (cong (λ X → X .fst x) chainHomotopy1))
     where
      open AbGroupStr (snd (ℤ[AD (fst n) ]))
        renaming (_+_ to _+G_ ; -_ to -G_ ; +Assoc to +AssocG ; +Comm to +CommG)
      aux : ∀ w x y z → (x +G y) +G z ≡ w → w +G (-G y) ≡ x +G z
      aux w x y z H = cong (λ X → X +G (-G y)) (sym H)
        ∙ sym (+AssocG (x +G y) z (-G y))
        ∙ cong (λ X → (x +G y) +G X) (+CommG z (-G y))
        ∙ +AssocG (x +G y) (-G y) z
        ∙ cong (λ X → X +G z) (sym (+AssocG x y (-G y))
                              ∙ cong (λ X → x +G X) (+InvR y)
                              ∙ +IdR x)

module chainHomEquationSuc (m : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
  (f g : finCellMap (suc m) C D) (H : finCellHom (suc m) f g) (n : Fin m) where
  open SequenceMap
  open MMmaps C D (suc m) (fsuc n)
  open MMchainHomotopy* (suc m) C D f g H (fsuc n)
  open preChainHomotopy (suc m) C D f g H
  open chainHomEquation (suc m) C D f g H (fsuc n)

  private
    ℤ[AC_] = CWskel-fields.ℤ[A_] C
    ℤ[AD_] = CWskel-fields.ℤ[A_] D

  H∂' : AbGroupHom (ℤ[AC (suc (fst n)) ]) (ℤ[AD (suc (fst n)) ])
  H∂' = compGroupHom (∂ C (fst n)) (chainHomotopy (injectSuc n))

  -- connecting MMΣH∂ to H∂'
  bouquetΣH∂ : H∂ ≡ H∂'
  bouquetΣH∂ =
     cong (λ X → bouquetDegree ((Iso.fun (cofibIso (suc (fst n)) D))
                ∘ X ∘ (Iso.inv (cofibIso (suc (fst n)) C))))
         (funExt (realiseMMΣH∂ C D m f g H n))
      ∙ cong bouquetDegree (cofibIso-suspFun _ C D (Hn+1/Hn (injectSuc n)
                          ∘ suspFun (to_cofibCW (fst n) C) ∘ δ (suc (fst n)) C))
      ∙ sym (bouquetDegreeSusp Hιδ)
      ∙ cong bouquetDegree Hιδ≡H∘pre∂
      ∙ bouquetDegreeComp (bouquetHomotopy (injectSuc n))
                          (preboundary.pre∂ C (fst n))
    where
    Hιδ : SphereBouquet (suc (fst n)) (Fin (CWskel-fields.card C (suc (fst n))))
        → SphereBouquet (suc (fst n)) (Fin (CWskel-fields.card D (suc (fst n))))
    Hιδ = Iso.fun (BouquetIso D (suc (fst n)))
                ∘ (Hn+1/Hn (injectSuc n))
                ∘ suspFun (to_cofibCW (fst n) C)
          ∘ δ (suc (fst n)) C ∘ Iso.inv (BouquetIso C (suc (fst n)))

    Hιδ≡H∘pre∂ : Hιδ ≡ bouquetHomotopy (injectSuc n) ∘ (preboundary.pre∂ C (fst n))
    Hιδ≡H∘pre∂ = cong (λ X → Iso.fun (BouquetIso D (suc (fst n)))
                             ∘ (Hn+1/Hn (injectSuc n)) ∘ X
                             ∘ suspFun (to_cofibCW (fst n) C) ∘ δ (suc (fst n)) C
                             ∘ Iso.inv (BouquetIso C (suc (fst n))))
                      (sym (funExt (Iso.leftInv (cofibIso (fst n) C))))

  chainHomotopySuc : subtrGroupHom _ _ fn gn ≡ addGroupHom _ _ ∂H H∂'
  chainHomotopySuc = chainHomotopy2 ∙ cong (addGroupHom _ _ ∂H) bouquetΣH∂

module chainHomEquationZero (m : ℕ) (C : CWskel ℓ) (D : CWskel ℓ')
  (f g : finCellMap (suc m) C D) (H : finCellHom (suc m) f g) where
  open SequenceMap
  open MMmaps C D (suc m) fzero
  open MMchainHomotopy* (suc m) C D f g H fzero
  open preChainHomotopy (suc m) C D f g H
  open chainHomEquation (suc m) C D f g H fzero

  private
    ℤ[AC_] = CWskel-fields.ℤ[A_] C
    ℤ[AD_] = CWskel-fields.ℤ[A_] D

  H∂' : AbGroupHom (ℤ[AC 0 ]) (ℤ[AD 0 ])
  H∂' = compGroupHom (augmentation.ϵ C) trivGroupHom

  MMΣH∂-const : ∀ x → bouquetMMmap merid-tt merid-tt MMΣH∂ x ≡ inl tt
  MMΣH∂-const x = cong (Iso.fun (cofibIso 0 D)) (realiseMMΣH∂₀ C D m f g H (Iso.inv (cofibIso 0 C) x))

  bouquetΣH∂ : H∂ ≡ H∂'
  bouquetΣH∂ = cong bouquetDegree (funExt MMΣH∂-const)
             ∙ bouquetDegreeConst _ _ _
             ∙ GroupHom≡ refl

  chainHomotopyZero : subtrGroupHom _ _ fn gn ≡ addGroupHom _ _ ∂H H∂'
  chainHomotopyZero = chainHomotopy2 ∙ cong (addGroupHom _ _ ∂H) bouquetΣH∂

-- Going from a cell homotopy to a chain homotopy
cellHom-to-ChainHomotopy : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  {f g : finCellMap (suc (suc m)) C D} (H : finCellHom (suc (suc m)) f g)
  → finChainHomotopy (suc m) (finCellMap→finChainComplexMap m f)
                             (finCellMap→finChainComplexMap m g)
cellHom-to-ChainHomotopy {C = C} {D} m {f} {g} H .finChainHomotopy.fhtpy (zero , _) =
  trivGroupHom
cellHom-to-ChainHomotopy {C = C} {D} m {f} {g} H .finChainHomotopy.fhtpy (suc n , n<m) =
  preChainHomotopy.chainHomotopy (suc (suc m)) C D f g H (injectSuc (n , n<m))
cellHom-to-ChainHomotopy {C = C} {D} m {f} {g} H .finChainHomotopy.fbdryhtpy (zero , _) =
  chainHomEquationZero.chainHomotopyZero (suc m) C D f g H
cellHom-to-ChainHomotopy {C = C} {D} m {f} {g} H .finChainHomotopy.fbdryhtpy (suc n , n<m) =
  chainHomEquationSuc.chainHomotopySuc (suc m) C D f g H (n , <ᵗ-trans-suc n<m)
