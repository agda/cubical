{-# OPTIONS --lossy-unification #-}

{-This file contains:

1. Definition of cellular maps
2. Definition of finite cellular maps
3. The induced map on chain complexes and homology by (finite) cellular maps

-}

module Cubical.CW.Map where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.ChainComplex

open import Cubical.HITs.S1
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.SequentialColimit

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.ChainComplex
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open Sequence

private
  variable
    ℓ ℓ' ℓ'' : Level
    C D E : CWskel ℓ

-- Maps
cellMap : (C : CWskel ℓ) (D : CWskel ℓ') → Type (ℓ-max ℓ ℓ')
cellMap C D = SequenceMap (realiseSeq C) (realiseSeq D)

-- Extracting a map between the realisations of the CWskel complexes
realiseCellMap : cellMap C D → realise C → realise D
realiseCellMap mp C∞ = realiseSequenceMap mp C∞

-- The identity as a cellular map
idCellMap : (C : CWskel ℓ) → cellMap C C
idCellMap C = idSequenceMap _

-- Composition of two cellular maps
composeCellMap : (g : cellMap D E) (f : cellMap C D) → cellMap C E
composeCellMap = composeSequenceMap


----- finite versions of above -----
module _ (m : ℕ) where
  finCellMap : (C : CWskel ℓ) (D : CWskel ℓ') → Type (ℓ-max ℓ ℓ')
  finCellMap C D = FinSequenceMap (realiseFinSeq m C) (realiseFinSeq m D)

  idFinCellMap : (C : CWskel ℓ) → finCellMap C C
  idFinCellMap C = idFinSequenceMap m (realiseFinSeq m C)

  composeFinCellMap : (g : finCellMap D E) (f : finCellMap C D) → finCellMap C E
  composeFinCellMap = composeFinSequenceMap m

open FinSequenceMap
finCellMap→FinSeqColim : (C : CWskel ℓ) (D : CWskel ℓ')
  {m : ℕ} → finCellMap m C D → FinSeqColim m (realiseSeq C) → FinSeqColim m (realiseSeq D)
finCellMap→FinSeqColim C D {m = m} f (fincl n x) = fincl n (fmap f n x)
finCellMap→FinSeqColim C D {m = m} f (fpush n x i) =
  (fpush n (fmap f (injectSuc n) x) ∙ cong (fincl (fsuc n)) (fcomm f n x)) i

finCellMap↓ : {m : ℕ} {C : CWskel ℓ} {D : CWskel ℓ'}  → finCellMap (suc m) C D → finCellMap m C D
fmap (finCellMap↓ {m = m} ϕ) x = fmap ϕ (injectSuc x)
fcomm (finCellMap↓ {m = suc m} {C = C} ϕ) x r = fcomm ϕ (injectSuc x) r

-- A cellular map between two CW complexes

-- A cellMap from C to D is a family of maps Cₙ → Dₙ that commute with
-- the inclusions Xₙ ↪ Xₙ₊₁

-- From a cellMap to a family of maps between free abelian groups
module prefunctoriality (m : ℕ) (f : finCellMap m C D) (n' : Fin m) where
  open FinSequenceMap
  open CWskel-fields

  n = fst n'

  fn+1/fn : cofibCW (fst n') C → cofibCW (fst n') D
  fn+1/fn (inl tt) = inl tt
  fn+1/fn (inr x) = inr (f .fmap (fsuc n') x)
  fn+1/fn (push x i) =
    (push (f .fmap (injectSuc n') x) ∙ (cong inr (f .fcomm n' x))) i

  bouquetFunct : SphereBouquet n (Fin (card C n))
    → SphereBouquet n (Fin (card D n))
  bouquetFunct = Iso.fun (BouquetIso-gen n (card D n) (α D n) (e D n))
                 ∘ fn+1/fn
                 ∘ Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n))

  chainFunct : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] n)
  chainFunct = bouquetDegree bouquetFunct

module _ (m : ℕ) (C : CWskel ℓ) (n' : Fin m) where
  open prefunctoriality m (idFinCellMap m C) n'
  open SequenceMap
  open CWskel-fields

  fn+1/fn-id : fn+1/fn ≡ idfun _
  fn+1/fn-id = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → rUnit (push a) (~ j) i}

  bouquetFunct-id : bouquetFunct ≡ idfun _
  bouquetFunct-id =
    cong (λ f → Iso.fun (BouquetIso-gen n (card C n) (α C n) (e C n))
                ∘ f
                ∘ Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)))
         fn+1/fn-id
    ∙ funExt (Iso.rightInv (BouquetIso-gen n (card C n) (α C n) (e C n)))

  chainFunct-id : chainFunct ≡ idGroupHom
  chainFunct-id = cong bouquetDegree bouquetFunct-id ∙ bouquetDegreeId

module _ (m : ℕ) (g : finCellMap m D E) (f : finCellMap m C D) (n' : Fin m) where
  module pf1 = prefunctoriality m f n'
  module pf2 = prefunctoriality m g n'
  module pf3 = prefunctoriality m (composeFinCellMap m g f) n'
  open FinSequenceMap
  open CWskel-fields
  private
    n = fst n'

  fn+1/fn-comp : pf2.fn+1/fn ∘ pf1.fn+1/fn ≡ pf3.fn+1/fn
  fn+1/fn-comp = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → help a j i}
    where
    help : (a : fst C n)
      → cong (pf2.fn+1/fn ∘ pf1.fn+1/fn) (push a) ≡ cong pf3.fn+1/fn (push a)
    help a = cong-∙ pf2.fn+1/fn (push (f .fmap (injectSuc n') a))
                                (λ i₁ → inr (f .fcomm n' a i₁))
           ∙∙ sym (assoc _ _ _)
           ∙∙ sym (cong₂ _∙_ refl
                   (cong-∙ inr (g .fcomm n' (fmap f (injectSuc n') a))
                               (cong (g .fmap (fsuc n')) (f .fcomm n' a))))

  bouquetFunct-comp : pf2.bouquetFunct ∘ pf1.bouquetFunct ≡ pf3.bouquetFunct
  bouquetFunct-comp = funExt λ x
    → cong (Iso.fun (BouquetIso-gen n (card E n) (α E n) (e E n)))
       (cong pf2.fn+1/fn
         (Iso.leftInv (BouquetIso-gen n (card D n) (α D n) (e D n)) _)
     ∙ funExt⁻ fn+1/fn-comp
         (Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)) x))

  chainFunct-comp : compGroupHom pf1.chainFunct pf2.chainFunct ≡ pf3.chainFunct
  chainFunct-comp =
       sym (bouquetDegreeComp∙ (pf2.bouquetFunct , refl)
                               (pf1.bouquetFunct , refl))
    ∙ cong bouquetDegree bouquetFunct-comp

-- Now we prove the commutativity condition to get a fully fledged chain map
module functoriality (m : ℕ) (f : finCellMap (suc m) C D) where
  open CWskel-fields
  open SequenceMap
  module pf* = prefunctoriality m (finCellMap↓ f)
  open prefunctoriality (suc m) f
  open FinSequenceMap

  -- δ ∘ fn+1/fn ≡ f ∘ δ
  commδ : (n : Fin (suc m)) (x : cofibCW (fst n) C)
    → δ (fst n) D (fn+1/fn n x)
     ≡ suspFun (f .fmap (injectSuc n)) (δ (fst n) C x)
  commδ n (inl x) = refl
  commδ n (inr x) = refl
  commδ n (push a i) j =
    hcomp (λ k → λ { (i = i0) → north
          ; (i = i1) → south
          ; (j = i0) → δ (fst n) D (compPath-filler
                           (push (f .fmap (injectSuc n) a))
                             (cong inr (f .fcomm n a)) k i)
          ; (j = i1) → merid (f .fmap (injectSuc n) a) i })
   (merid (f .fmap (injectSuc n) a) i)

  -- Σto_cofibCW ∘ Σf ≡ Σfn+1/fn ∘ Σto_cofibCW
  commToCofibCWSusp : (n : Fin (suc m)) (x : Susp (fst C (suc (fst n))))
     → suspFun (to_cofibCW (fst n) D) (suspFun (f .fmap (fsuc n)) x)
      ≡ suspFun (fn+1/fn n) (suspFun (to_cofibCW (fst n) C) x)
  commToCofibCWSusp n north = refl
  commToCofibCWSusp n south = refl
  commToCofibCWSusp n (merid a i) = refl

  -- commδ and commToCofibCWSusp give us the chain map equation at the level of cofibCWs
  -- now we massage isomorphisms and suspensions to get the proper equation between SphereBouquets
  funct∘pre∂ : (n : Fin (suc m))
    → SphereBouquet (suc (fst n)) (Fin (card C (suc (fst n))))
    → SphereBouquet (suc (fst n)) (Fin (card D (fst n)))
  funct∘pre∂ n = (bouquetSusp→ (bouquetFunct n)) ∘ (preboundary.pre∂ C (fst n))

  pre∂∘funct : (n : Fin m)
    → (SphereBouquet (suc (fst n)) (Fin (card C (suc (fst n)))))
    → SphereBouquet (suc (fst n)) (Fin (card D (fst n)))
  pre∂∘funct n = preboundary.pre∂ D (fst n) ∘ bouquetFunct (fsuc n)

  commPre∂Funct : (n : Fin m) → funct∘pre∂ (injectSuc n) ≡ pre∂∘funct n
  commPre∂Funct n = funExt λ x → cong (fun (iso1 D (fst n))) (main x)
    where
      open preboundary
      open Iso

      bouquet : (C : CWskel ℓ) (n m : ℕ) → Type
      bouquet = λ C n m → SphereBouquet n (Fin (snd C .fst m))

      iso1 : (C : CWskel ℓ) (n : ℕ)
        → Iso (Susp (bouquet C n n)) (bouquet C (suc n) n)
      iso1 C n = sphereBouquetSuspIso

      iso2 : (C : CWskel ℓ) (n : ℕ) → Iso (cofibCW n C) (bouquet C n n)
      iso2 C n =
        BouquetIso-gen n (snd C .fst n) (snd C .snd .fst n)
                         (snd C .snd .snd .snd n)

      step2aux : ∀ x → suspFun (bouquetFunct (injectSuc n)) x
                      ≡ suspFun (fun (iso2 D (fst n)))
                          (suspFun (fn+1/fn (injectSuc n))
                            (suspFun (inv (iso2 C (fst n))) x))
      step2aux north = refl
      step2aux south = refl
      step2aux (merid a i) = refl

      step3aux : ∀ x
        → suspFun (inv (iso2 C (fst n))) (suspFun (fun (iso2 C (fst n))) x) ≡ x
      step3aux north = refl
      step3aux south = refl
      step3aux (merid a i) j = merid (leftInv (iso2 C (fst n)) a j) i

      module _ (x : bouquet C (suc (fst n)) (suc (fst n))) where
        step1 = cong (suspFun (bouquetFunct (injectSuc n)))
                       (leftInv (iso1 C (fst n))
                         (((suspFun (fun (iso2 C (fst n))))
                         ∘ (suspFun (to_cofibCW (fst n) C))
            ∘ (δ (suc (fst n)) C) ∘ (inv (iso2 C (suc (fst n))))) x))

        step2 = step2aux (((suspFun (fun (iso2 C (fst n))))
                         ∘ (suspFun (to_cofibCW (fst n) C))
                        ∘ (δ (suc (fst n)) C) ∘ (inv (iso2 C (suc (fst n))))) x)

        step3 =
          cong ((suspFun (fun (iso2 D (fst n))))
              ∘ (suspFun (fn+1/fn (injectSuc n))))
               (step3aux (((suspFun (to_cofibCW (fst n) C))
                         ∘ (δ (suc (fst n)) C)
                         ∘ (inv (iso2 C (suc (fst n))))) x))

        step4 = cong (suspFun (fun (iso2 D (fst n))))
          (sym (commToCofibCWSusp (injectSuc n)
            (((δ (suc (fst n)) C) ∘ (inv (iso2 C (suc (fst n))))) x)))

        step5 = λ i → suspFun (fun (iso2 D (fst n)))
                        (suspFun (to fst (injectSuc n) cofibCW D)
                         (suspFun (f .fmap (p i))
                          (δ (suc (fst n)) C (inv (iso2 C (suc (fst n))) x))))
          where
          p : fsuc (injectSuc n) ≡ injectSuc (fsuc n)
          p = Σ≡Prop (λ _ → isProp<ᵗ) refl

        step6 = cong ((suspFun (fun (iso2 D (fst n))))
                     ∘ (suspFun (to_cofibCW (fst n) D)))
                 (sym (commδ (fsuc n) (inv (iso2 C (suc (fst n))) x)))

        step7 =  cong ((suspFun (fun (iso2 D (fst n))))
                      ∘ (suspFun (to_cofibCW (fst n) D))
                      ∘ (δ (suc (fst n)) D))
                   (sym (leftInv (iso2 D (suc (fst n)))
                     (((fn+1/fn (fsuc n)) ∘ (inv (iso2 C (suc (fst n))))) x)))

        main = step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5 ∙ step6 ∙ step7

  -- finally, we take bouquetDegree to get the equation at the level
  -- of abelian groups
  comm∂Funct : (n : Fin m)
    → compGroupHom (chainFunct (fsuc n)) (∂ D (fst n))
     ≡ compGroupHom (∂ C (fst n)) (chainFunct (injectSuc n))
  comm∂Funct n = (sym (degree-pre∂∘funct n))
               ∙∙ cong bouquetDegree (sym (commPre∂Funct n))
               ∙∙ (degree-funct∘pre∂ n)
    where
      degree-funct∘pre∂ : (n : Fin m)
        → bouquetDegree (funct∘pre∂ (injectSuc n))
        ≡ compGroupHom (∂ C (fst n)) (chainFunct (injectSuc n))
      degree-funct∘pre∂ n =
          bouquetDegreeComp (bouquetSusp→ (bouquetFunct (injectSuc n)))
                            (preboundary.pre∂ C (fst n))
        ∙ cong (compGroupHom (∂ C (fst n)))
               (sym (bouquetDegreeSusp (bouquetFunct (injectSuc n))))

      degree-pre∂∘funct : (n : Fin m)
        → bouquetDegree (pre∂∘funct n)
         ≡ compGroupHom (chainFunct (fsuc n)) (∂ D (fst n))
      degree-pre∂∘funct n =
        bouquetDegreeComp (preboundary.pre∂ D (fst n)) (bouquetFunct (fsuc n))

-- Now we prove the commutativity condition for the augmentation map
module augmentationFunct (m : ℕ) (f : finCellMap (suc m) C D) where
  open CWskel-fields
  open SequenceMap
  module pf* = prefunctoriality m (finCellMap↓ f)
  open prefunctoriality (suc m) f
  open FinSequenceMap

  commε : (x : Susp (cofibCW 0 C))
    → ((augmentation.ε D) ∘ (suspFun (fn+1/fn fzero))) x
     ≡ augmentation.ε C x
  commε north = refl
  commε south = refl
  commε (merid (inl x) i) = refl
  commε (merid (inr x) i) = refl
  commε (merid (push x i₁) i) with (C .snd .snd .snd .fst x)
  commε (merid (push x i₁) i) | ()

  commPreϵ : (x : SphereBouquet 1 (A C 0))
           → ((augmentation.preϵ D) ∘ (bouquetSusp→ (bouquetFunct fzero))) x ≡ augmentation.preϵ C x
  commPreϵ x = cong ((ε D) ∘ (suspFun (inv (iso2 D)))) (leftInv (iso1 D) (((suspFun (bouquetFunct fzero)) ∘ (inv (iso1 C))) x))
             ∙ cong (ε D) (funExt⁻ aux (inv (iso1 C) x))
             ∙ commε (((suspFun (inv (iso2 C))) ∘ (inv (iso1 C))) x)
    where
      open Iso
      open augmentation

      bouquet : (C : CWskel ℓ) (n : ℕ) → Type
      bouquet = λ C n → SphereBouquet n (Fin (snd C .fst 0))

      iso1 : (C : CWskel ℓ) → Iso (Susp (bouquet C 0)) (bouquet C 1)
      iso1 C = sphereBouquetSuspIso

      iso2 : (C : CWskel ℓ) → Iso (cofibCW 0 C) (bouquet C 0)
      iso2 C = BouquetIso-gen 0 (snd C .fst 0) (snd C .snd .fst 0) (snd C .snd .snd .snd 0)

      aux : (suspFun (inv (iso2 D))) ∘ (suspFun (bouquetFunct fzero))
             ≡ (suspFun (fn+1/fn fzero)) ∘ (suspFun (inv (iso2 C)))
      aux = (sym (suspFunComp (inv (iso2 D)) (bouquetFunct fzero)))
          ∙ cong suspFun (funExt (λ x → leftInv (iso2 D) (((fn+1/fn fzero) ∘ (inv (iso2 C))) x)))
          ∙ (suspFunComp (fn+1/fn fzero) (inv (iso2 C)))

  commϵFunct : compGroupHom (chainFunct fzero) (augmentation.ϵ D)
               ≡ compGroupHom (augmentation.ϵ C) (idGroupHom)
  commϵFunct = (λ i → compGroupHom (bouquetDegreeSusp (bouquetFunct fzero) i) (augmentation.ϵ D))
             ∙ sym (bouquetDegreeComp (augmentation.preϵ D) (bouquetSusp→ (bouquetFunct fzero)))
             ∙ cong bouquetDegree (funExt commPreϵ)
             ∙ sym (compGroupHomId (augmentation.ϵ C))

open finChainComplexMap

-- Main statement of functoriality
-- From a cellMap, we can get a ChainComplexMap between augmented chain complexes
finCellMap→finChainComplexMap : (m : ℕ) (f : finCellMap (suc (suc m)) C D)
  → finChainComplexMap (suc m) (CW-AugChainComplex C) (CW-AugChainComplex D)
fchainmap (finCellMap→finChainComplexMap m f) (zero , _) = idGroupHom
fchainmap (finCellMap→finChainComplexMap m f) (suc n , n<m) = prefunctoriality.chainFunct (suc (suc m)) f (injectSuc (n , n<m))
fbdrycomm (finCellMap→finChainComplexMap m f) (zero , _) = augmentationFunct.commϵFunct (suc m) f
fbdrycomm (finCellMap→finChainComplexMap m f) (suc n , n<m) = functoriality.comm∂Funct (suc m) f (n , <ᵗ-trans-suc n<m)

finCellMap→finChainComplexMapId : (m : ℕ)
  → finCellMap→finChainComplexMap m (idFinCellMap (suc (suc m)) C)
   ≡ idFinChainMap (suc m) (CW-AugChainComplex C)
finCellMap→finChainComplexMapId m = finChainComplexMap≡
  λ { (zero , _) → refl
    ; (suc n , n<m) → cong bouquetDegree (bouquetFunct-id _ _ (injectSuc (n , n<m))) ∙ bouquetDegreeId }

finCellMap→finChainComplexMapComp : (m : ℕ)
  (g : finCellMap (suc (suc m)) D E) (f : finCellMap (suc (suc m)) C D)
  → finCellMap→finChainComplexMap m (composeFinCellMap _ g f)
   ≡ compFinChainMap (finCellMap→finChainComplexMap m f)
                     (finCellMap→finChainComplexMap m g)
finCellMap→finChainComplexMapComp m g f = finChainComplexMap≡
  λ { (zero , _) → sym (compGroupHomId idGroupHom)
    ; (suc n , n<m) → cong bouquetDegree (sym (bouquetFunct-comp _ g f (injectSuc (n , n<m)))) ∙ bouquetDegreeComp _ _ }

-- And thus a map of homology
finCellMap→HomologyMap : (m : ℕ) (f : finCellMap (suc (suc (suc m))) C D)
  → GroupHom (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
finCellMap→HomologyMap {C = C} {D = D} m f =
  finChainComplexMap→HomologyMap (suc m)
    (finCellMap→finChainComplexMap _ f) flast

finCellMap→HomologyMapId : (m : ℕ)
  → finCellMap→HomologyMap m (idFinCellMap (suc (suc (suc m))) C)
   ≡ idGroupHom
finCellMap→HomologyMapId m =
  cong (λ r → finChainComplexMap→HomologyMap (suc m) r flast)
        (finCellMap→finChainComplexMapId _)
  ∙ finChainComplexMap→HomologyMapId _

finCellMap→HomologyMapComp : (m : ℕ)
  (g : finCellMap (suc (suc (suc m))) D E)
  (f : finCellMap (suc (suc (suc m))) C D)
  → finCellMap→HomologyMap m (composeFinCellMap _ g f)
   ≡ compGroupHom (finCellMap→HomologyMap m f)
                  (finCellMap→HomologyMap m g)
finCellMap→HomologyMapComp m g f =
  (cong (λ r → finChainComplexMap→HomologyMap (suc m) r flast)
        (finCellMap→finChainComplexMapComp _ _ _))
  ∙ finChainComplexMap→HomologyMapComp _ _ _

-- sanity check: chainFunct of a cellular map fₙ : Cₙ → Dₙ
-- is just functoriality of ℤ[-] when n = 1.
module _ (m : ℕ) (f : finCellMap (suc (suc (suc m))) C D) where
  open CWskel-fields
  open FinSequenceMap
  open prefunctoriality _ f

  cellMap↾₁ : Fin (card C 0) → Fin (card D 0)
  cellMap↾₁ = fst (CW₁-discrete D) ∘ fmap f (1 , tt) ∘ invEq (CW₁-discrete C)

  chainFunct' : AbGroupHom (ℤ[A C ] 0) (ℤ[A D ] 0)
  chainFunct' = ℤFinFunct cellMap↾₁

  chainFunct₀ : chainFunct' ≡ chainFunct fzero
  chainFunct₀ =
    agreeOnℤFinGenerator→≡ λ t → funExt λ x
    → sumFin-choose _+_ 0 (λ _ → refl) +Comm
        (λ a → ℤFinFunctGenerator cellMap↾₁ (ℤFinGenerator t) a x)
        (S⁰×S⁰→ℤ true (pickPetal x (bouquetFunct fzero (inr (t , false)))))
        t (ℤFinFunctGenerator≡ cellMap↾₁ t x ∙ main₁ t x)
        (main₂ cellMap↾₁ x t)
    ∙ isGeneratorℤFinGenerator'
        (λ a → degree 0 λ s
             → pickPetal x (bouquetFunct fzero (inr (a , s)))) t
    where
    F = Pushout→Bouquet 0 (card D 0) (α D 0) (e D 0)


    lem₂ : {k : ℕ} (t : Fin k) (x : Fin k)
      → ℤFinGenerator x t ≡ S⁰×S⁰→ℤ true (pickPetal x (inr (t , false)))
    lem₂ {k = suc k} t x with (fst x ≟ᵗ fst t)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    main₁ : (t : _) (x : _)
      → ℤFinGenerator (cellMap↾₁ t) x
       ≡ S⁰×S⁰→ℤ true
          (pickPetal x
            (F (fst (e D 0) (f .fmap (1 , tt) (invEq (CW₁-discrete C) t)))))
    main₁ t x = (ℤFinGeneratorComm (cellMap↾₁ t) x
      ∙ lem₂ (cellMap↾₁ t) x)
      ∙ cong (S⁰×S⁰→ℤ true ∘ pickPetal x ∘ F)
             (lem₁ _)
      where
      lem₀ : (x : Pushout (α D 0) fst)
        → inr (CW₁-discrete D .fst (invEq (e D 0) x)) ≡ x
      lem₀ (inl x) = ⊥.rec (CW₀-empty D x)
      lem₀ (inr x) j = inr (secEq (CW₁-discrete D) x j)

      lem₁ : (x : _)
        → inr (CW₁-discrete D .fst x) ≡ fst (e D 0) x
      lem₁ x = (λ i → inr (CW₁-discrete D .fst
                            (retEq (e D 0) x (~ i))))
              ∙ lem₀ (fst (e D 0) x)

    main₂ : (f' : _) (x : _) (t : _) (x' : Fin (card C zero))
      → ¬ x' ≡ t
      → ℤFinFunctGenerator {n = card C zero} {m = card D zero}
                        f' (ℤFinGenerator t) x' x
       ≡ pos 0
    main₂ f' x t x' p with (f' x' .fst ≟ᵗ x .fst) | (fst t ≟ᵗ fst x')
    ... | lt x₁ | r = refl
    ... | eq x₂ | r = lem
      where
      lem : _
      lem with (fst t ≟ᵗ fst x')
      ... | lt x = refl
      ... | eq x = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) (sym x)))
      ... | gt x = refl
    ... | gt x₁ | r = refl
