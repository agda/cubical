{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.AsModule.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra.AsModule.Base

open import Cubical.Algebra.CommRing using (CommRing→Ring)

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    R : CommRing ℓ

open AlgebraHoms

idCAlgHom : (A : CommAlgebra R ℓ) → _
idCAlgHom A = idAlgebraHom (CommAlgebra→Algebra A)

idCAlgEquiv : (A : CommAlgebra R ℓ) → CommAlgebraEquiv A A
fst (idCAlgEquiv A) = idEquiv (fst A)
snd (idCAlgEquiv A) = snd (idCAlgHom A)

infix  3 _≃CAlg∎
infixr 2 _≃CAlg⟨_⟩_

_≃CAlg∎ : (A : CommAlgebra R ℓ) → CommAlgebraEquiv A A
A ≃CAlg∎ = idCAlgEquiv A

_≃CAlg⟨_⟩_ : {B C : CommAlgebra R ℓ}
             (A : CommAlgebra R ℓ) (f : CommAlgebraEquiv A B) (g : CommAlgebraEquiv B C)
           → CommAlgebraEquiv A C
A ≃CAlg⟨ f ⟩ g = g ∘≃a f

-- An R-algebra is the same as a CommRing A with a CommRingHom φ : R → A
module CommAlgChar (R : CommRing ℓ) {ℓ' : Level} where
 open Iso
 open CommRingTheory


 CommRingWithHom : Type (ℓ-max ℓ (ℓ-suc ℓ'))
 CommRingWithHom = Σ[ A ∈ CommRing ℓ' ] CommRingHom R A

 toCommAlg : CommRingWithHom → CommAlgebra R ℓ'
 toCommAlg (A , φ , φIsHom) =
  commAlgebraFromCommRing
    A
    (λ r a → (φ r) · a)
    (λ r s x → cong (_· x) (pres· r s) ∙ sym (·Assoc _ _ _))
    (λ r x y → ·DistR+ _ _ _)
    (λ r s x → cong (_· x) (pres+ r s) ∙ ·DistL+ _ _ _)
    (λ x → cong (_· x) pres1 ∙ ·IdL x)
    λ r x y → sym (·Assoc _ _ _)
  where
  open CommRingStr (snd A)
  open IsCommRingHom φIsHom

 fromCommAlg : CommAlgebra R ℓ' → CommRingWithHom
 fromCommAlg A = (CommAlgebra→CommRing A) , φ , φIsHom
  where
  open CommRingStr (snd R) renaming (_·_ to _·r_) hiding (·IdL)
  open CommAlgebraStr (snd A)
  open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
  φ : ⟨ R ⟩ → ⟨ A ⟩
  φ r = r ⋆ 1a
  φIsHom : IsCommRingHom (R .snd) φ ((CommAlgebra→CommRing A) .snd)
  φIsHom = makeIsCommRingHom (⋆IdL _) (λ _ _ → ⋆DistL+ _ _ _)
           λ x y → cong (λ a → (x ·r y) ⋆ a) (sym (·IdL _)) ∙ ⋆Dist· _ _ _ _

 -- helpful for localisations
 module _ (Aφ : CommRingWithHom) where
   open CommRingStr
   private
     A = fst Aφ
   CommAlgebra→CommRing≡ : CommAlgebra→CommRing (toCommAlg Aφ) ≡ A
   fst (CommAlgebra→CommRing≡ i) = fst A
   0r (snd (CommAlgebra→CommRing≡ i)) = 0r (snd A)
   1r (snd (CommAlgebra→CommRing≡ i)) = 1r (snd A)
   _+_ (snd (CommAlgebra→CommRing≡ i)) = _+_ (snd A)
   _·_ (snd (CommAlgebra→CommRing≡ i)) = _·_ (snd A)
   -_ (snd (CommAlgebra→CommRing≡ i)) = -_ (snd A)
   -- note that the proofs of the axioms might differ!
   isCommRing (snd (CommAlgebra→CommRing≡ i)) = isProp→PathP (λ i → isPropIsCommRing _ _ _ _ _ )
              (isCommRing (snd (CommAlgebra→CommRing (toCommAlg Aφ)))) (isCommRing (snd A)) i


 CommRingWithHomRoundTrip : (Aφ : CommRingWithHom) → fromCommAlg (toCommAlg Aφ) ≡ Aφ
 CommRingWithHomRoundTrip (A , φ) = ΣPathP (CommAlgebra→CommRing≡ (A , φ) , φPathP)
  where
  open CommRingStr
  -- this only works because fst (CommAlgebra→CommRing≡ (A , φ) i) = fst A definitionally!
  φPathP : PathP (λ i → CommRingHom R (CommAlgebra→CommRing≡ (A , φ) i))
                 (snd (fromCommAlg (toCommAlg (A , φ)))) φ
  φPathP = CommRingHomPathP _ _ _ _ _ _ λ i x → ·IdR (snd A) (fst φ x) i


 CommAlgRoundTrip : (A : CommAlgebra R ℓ') → toCommAlg (fromCommAlg A) ≡ A
 CommAlgRoundTrip A = ΣPathP (refl , AlgStrPathP)
  where
  open CommAlgebraStr ⦃...⦄
  instance
   _ = snd A
  AlgStrPathP : PathP (λ i → CommAlgebraStr R ⟨ A ⟩) (snd (toCommAlg (fromCommAlg A))) (snd A)
  CommAlgebraStr.0a (AlgStrPathP i) = 0a
  CommAlgebraStr.1a (AlgStrPathP i) = 1a
  CommAlgebraStr._+_ (AlgStrPathP i) = _+_
  CommAlgebraStr._·_ (AlgStrPathP i) = _·_
  CommAlgebraStr.-_ (AlgStrPathP i) = -_
  CommAlgebraStr._⋆_ (AlgStrPathP i) r x = (⋆AssocL r 1a x ∙ cong (r ⋆_) (·IdL x)) i
  CommAlgebraStr.isCommAlgebra (AlgStrPathP i) = isProp→PathP
    (λ i → isPropIsCommAlgebra _ _ _ _ _ _ (CommAlgebraStr._⋆_ (AlgStrPathP i)))
    (CommAlgebraStr.isCommAlgebra (snd (toCommAlg (fromCommAlg A)))) isCommAlgebra i

 CommAlgIso : Iso (CommAlgebra R ℓ') CommRingWithHom
 fun CommAlgIso = fromCommAlg
 inv CommAlgIso = toCommAlg
 rightInv CommAlgIso = CommRingWithHomRoundTrip
 leftInv CommAlgIso = CommAlgRoundTrip

 open IsCommRingHom

 isCommRingWithHomHom : (A B : CommRingWithHom) → CommRingHom (fst A) (fst B) → Type (ℓ-max ℓ ℓ')
 isCommRingWithHomHom (_ , f) (_ , g) h = h ∘cr f ≡ g

 CommRingWithHomHom : CommRingWithHom → CommRingWithHom → Type (ℓ-max ℓ ℓ')
 CommRingWithHomHom (A , f) (B , g) = Σ[ h ∈ CommRingHom A B ] h ∘cr f ≡ g

 toCommAlgebraHom : (A B : CommRingWithHom) (h : CommRingHom (fst A) (fst B))
                  → isCommRingWithHomHom A B h
                  → CommAlgebraHom (toCommAlg A) (toCommAlg B)
 toCommAlgebraHom (A , f) (B , g) h commDiag =
   makeCommAlgebraHom (fst h) (pres1 (snd h)) (pres+ (snd h)) (pres· (snd h)) pres⋆h
   where
   open CommRingStr ⦃...⦄
   instance
    _ = snd A
    _ = snd B
   pres⋆h : ∀ r x → fst h (fst f r · x) ≡ fst g r · fst h x
   pres⋆h r x = fst h (fst f r · x)       ≡⟨ pres· (snd h) _ _ ⟩
                fst h (fst f r) · fst h x ≡⟨ cong (λ φ → fst φ r · fst h x) commDiag ⟩
                fst g r · fst h x ∎

 fromCommAlgebraHom : (A B : CommAlgebra R ℓ') → CommAlgebraHom A B
                    → CommRingWithHomHom (fromCommAlg A) (fromCommAlg B)
 fst (fst (fromCommAlgebraHom A B f)) = fst f
 pres0 (snd (fst (fromCommAlgebraHom A B f))) = IsAlgebraHom.pres0 (snd f)
 pres1 (snd (fst (fromCommAlgebraHom A B f))) = IsAlgebraHom.pres1 (snd f)
 pres+ (snd (fst (fromCommAlgebraHom A B f))) = IsAlgebraHom.pres+ (snd f)
 pres· (snd (fst (fromCommAlgebraHom A B f))) = IsAlgebraHom.pres· (snd f)
 pres- (snd (fst (fromCommAlgebraHom A B f))) = IsAlgebraHom.pres- (snd f)
 snd (fromCommAlgebraHom A B f) =
  CommRingHom≡ (funExt (λ x → IsAlgebraHom.pres⋆ (snd f) x 1a ∙ cong (x ⋆_) (IsAlgebraHom.pres1 (snd f))))
  where
  open CommAlgebraStr (snd A) using (1a)
  open CommAlgebraStr (snd B) using (_⋆_)

 isCommRingWithHomEquiv : (A B : CommRingWithHom) → CommRingEquiv (fst A) (fst B) → Type (ℓ-max ℓ ℓ')
 isCommRingWithHomEquiv A B e = isCommRingWithHomHom A B (CommRingEquiv→CommRingHom e)

 CommRingWithHomEquiv : CommRingWithHom → CommRingWithHom → Type (ℓ-max ℓ ℓ')
 CommRingWithHomEquiv A B = Σ[ e ∈ CommRingEquiv (fst A) (fst B) ] isCommRingWithHomEquiv A B e

 toCommAlgebraEquiv : (A B : CommRingWithHom) (e : CommRingEquiv (fst A) (fst B))
                    → isCommRingWithHomEquiv A B e
                    → CommAlgebraEquiv (toCommAlg A) (toCommAlg B)
 fst (toCommAlgebraEquiv A B e eCommDiag) = e .fst
 snd (toCommAlgebraEquiv A B e eCommDiag) = toCommAlgebraHom A B _ eCommDiag .snd



module CommAlgebraHoms {R : CommRing ℓ} where
  open AlgebraHoms

  idCommAlgebraHom : (A : CommAlgebra R ℓ') → CommAlgebraHom A A
  idCommAlgebraHom A = idAlgebraHom (CommAlgebra→Algebra A)

  compCommAlgebraHom : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') (C : CommAlgebra R ℓ''')
                  → CommAlgebraHom A B → CommAlgebraHom B C → CommAlgebraHom A C
  compCommAlgebraHom A B C = compAlgebraHom {A = CommAlgebra→Algebra A}
                                            {B = CommAlgebra→Algebra B}
                                            {C = CommAlgebra→Algebra C}

  _∘ca_ : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
        → CommAlgebraHom B C → CommAlgebraHom A B → CommAlgebraHom A C
  g ∘ca f = compCommAlgebraHom _ _ _ f g

  compIdCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                    → compCommAlgebraHom _ _ _ (idCommAlgebraHom A) f ≡ f
  compIdCommAlgebraHom = compIdAlgebraHom

  idCompCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                    → compCommAlgebraHom _ _ _ f (idCommAlgebraHom B) ≡ f
  idCompCommAlgebraHom = idCompAlgebraHom

  compAssocCommAlgebraHom : {A B C D : CommAlgebra R ℓ'}
                         (f : CommAlgebraHom A B) (g : CommAlgebraHom B C) (h : CommAlgebraHom C D)
                       → compCommAlgebraHom _ _ _ (compCommAlgebraHom _ _ _ f g) h
                       ≡ compCommAlgebraHom _ _ _ f (compCommAlgebraHom _ _ _ g h)
  compAssocCommAlgebraHom = compAssocAlgebraHom

module CommAlgebraEquivs {R : CommRing ℓ} where
  open AlgebraEquivs

  compCommAlgebraEquiv : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
                    → CommAlgebraEquiv A B → CommAlgebraEquiv B C → CommAlgebraEquiv A C
  compCommAlgebraEquiv {A = A} {B = B} {C = C} = compAlgebraEquiv {A = CommAlgebra→Algebra A}
                                                            {B = CommAlgebra→Algebra B}
                                                            {C = CommAlgebra→Algebra C}


  isSetCommAlgStr : (A : Type ℓ') → isSet (CommAlgebraStr R A)
  isSetCommAlgStr A =
    let open CommAlgebraStr
    in isOfHLevelSucIfInhabited→isOfHLevelSuc 1 (λ str →
       isOfHLevelRetractFromIso 2 CommAlgebraStrIsoΣ $
       isSetΣ (str .is-set) λ _ →
       isSetΣ (str .is-set) (λ _ →
       isSetΣ (isSet→ (isSet→ (str .is-set))) λ _ →
       isSetΣ (isSet→ (isSet→ (str .is-set))) (λ _ →
       isSetΣ (isSet→ (str .is-set)) λ _ →
       isSetΣSndProp (isSet→ (isSet→ (str .is-set))) (λ _ →
       isPropIsCommAlgebra R _ _ _ _ _ _))))

-- the CommAlgebra version of uaCompEquiv
module CommAlgebraUAFunctoriality {R : CommRing ℓ} where
 open CommAlgebraStr
 open CommAlgebraEquivs

 caracCommAlgebra≡ : {A B : CommAlgebra R ℓ'} (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracCommAlgebra≡  _ _ α =
   isEmbedding→Inj (iso→isEmbedding (invIso ΣPathIsoPathΣ)) _ _ $
   Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetCommAlgStr _) _ _) α

 uaCompCommAlgebraEquiv : {A B C : CommAlgebra R ℓ'} (f : CommAlgebraEquiv A B) (g : CommAlgebraEquiv B C)
                  → uaCommAlgebra (compCommAlgebraEquiv f g) ≡ uaCommAlgebra f ∙ uaCommAlgebra g
 uaCompCommAlgebraEquiv f g = caracCommAlgebra≡ _ _ (
   cong ⟨_⟩ (uaCommAlgebra (compCommAlgebraEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaCommAlgebra f) ∙ cong ⟨_⟩ (uaCommAlgebra g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaCommAlgebra f) (uaCommAlgebra g)) ⟩
   cong ⟨_⟩ (uaCommAlgebra f ∙ uaCommAlgebra g) ∎)

open CommAlgebraHoms
open CommAlgebraEquivs
open CommAlgebraUAFunctoriality
recPT→CommAlgebra : {R : CommRing ℓ} {A : Type ℓ'} (𝓕  : A → CommAlgebra R ℓ'')
           → (σ : ∀ x y → CommAlgebraEquiv (𝓕 x) (𝓕 y))
           → (∀ x y z → σ x z ≡ compCommAlgebraEquiv (σ x y) (σ y z))
          ------------------------------------------------------
           → ∥ A ∥₁ → CommAlgebra R ℓ''
recPT→CommAlgebra 𝓕 σ compCoh = GpdElim.rec→Gpd isGroupoidCommAlgebra 𝓕
  (3-ConstantCompChar 𝓕 (λ x y → uaCommAlgebra (σ x y))
                          λ x y z → sym (  cong uaCommAlgebra (compCoh x y z)
                                         ∙ uaCompCommAlgebraEquiv (σ x y) (σ y z)))

open CommAlgebraHoms

contrCommAlgebraHom→contrCommAlgebraEquiv : {R : CommRing ℓ} {A : Type ℓ'}
        (σ : A → CommAlgebra R ℓ'')
      → (∀ x y → isContr (CommAlgebraHom (σ x) (σ y)))
      ----------------------------------------------------------------------------
      → ∀ x y → isContr (CommAlgebraEquiv (σ x) (σ y))
contrCommAlgebraHom→contrCommAlgebraEquiv σ contrHom x y = σEquiv ,
  λ e → Σ≡Prop (λ _ → isPropIsAlgebraHom _ _ _ _)
           (Σ≡Prop isPropIsEquiv (cong fst (contrHom _ _ .snd (CommAlgebraEquiv→CommAlgebraHom e))))
  where
  open Iso
  χ₁ = contrHom x y .fst
  χ₂ = contrHom y x .fst
  χ₁∘χ₂≡id : χ₁ ∘ca χ₂ ≡ idCommAlgebraHom _
  χ₁∘χ₂≡id = isContr→isProp (contrHom _ _) _ _

  χ₂∘χ₁≡id : χ₂ ∘ca χ₁ ≡ idCommAlgebraHom _
  χ₂∘χ₁≡id = isContr→isProp (contrHom _ _) _ _

  σIso : Iso ⟨ σ x ⟩ ⟨ σ y ⟩
  fun σIso = fst χ₁
  inv σIso = fst χ₂
  rightInv σIso = funExt⁻ (cong fst χ₁∘χ₂≡id)
  leftInv σIso = funExt⁻ (cong fst χ₂∘χ₁≡id)

  σEquiv : CommAlgebraEquiv (σ x) (σ y)
  fst σEquiv = isoToEquiv σIso
  snd σEquiv = snd χ₁

CommAlgebra→Ring : {R : CommRing ℓ} → CommAlgebra R ℓ' → Ring ℓ'
CommAlgebra→Ring = CommRing→Ring ∘ CommAlgebra→CommRing

module _ {R : CommRing ℓ} {A B : CommAlgebra R ℓ'} where
  open CommAlgebraStr ⦃...⦄
  instance
   _ = snd A
   _ = snd B
  open IsAlgebraHom

  CommAlgebraHom→RingHom : CommAlgebraHom A B → RingHom (CommAlgebra→Ring A) (CommAlgebra→Ring B)
  fst (CommAlgebraHom→RingHom ϕ) = fst ϕ
  IsRingHom.pres0 (snd (CommAlgebraHom→RingHom ϕ)) = pres0 (snd ϕ)
  IsRingHom.pres1 (snd (CommAlgebraHom→RingHom ϕ)) = pres1 (snd ϕ)
  IsRingHom.pres+ (snd (CommAlgebraHom→RingHom ϕ)) = pres+ (snd ϕ)
  IsRingHom.pres· (snd (CommAlgebraHom→RingHom ϕ)) = pres· (snd ϕ)
  IsRingHom.pres- (snd (CommAlgebraHom→RingHom ϕ)) = pres- (snd ϕ)

  CommAlgebraHomFromRingHom :
      (ϕ : RingHom (CommAlgebra→Ring A) (CommAlgebra→Ring B))
    → ((r : fst R) (x : fst A) → (fst ϕ) (r ⋆ x)  ≡ r ⋆ (fst ϕ x))
    → CommAlgebraHom A B
  fst (CommAlgebraHomFromRingHom ϕ pres*) = fst ϕ
  pres0 (snd (CommAlgebraHomFromRingHom ϕ pres*)) = IsRingHom.pres0 (snd ϕ)
  pres1 (snd (CommAlgebraHomFromRingHom ϕ pres*)) = IsRingHom.pres1 (snd ϕ)
  pres+ (snd (CommAlgebraHomFromRingHom ϕ pres*)) = IsRingHom.pres+ (snd ϕ)
  pres· (snd (CommAlgebraHomFromRingHom ϕ pres*)) = IsRingHom.pres· (snd ϕ)
  pres- (snd (CommAlgebraHomFromRingHom ϕ pres*)) = IsRingHom.pres- (snd ϕ)
  pres⋆ (snd (CommAlgebraHomFromRingHom ϕ pres*)) = pres*

module _ {R S : CommRing ℓ} (f : CommRingHom S R) where
  baseChange : CommAlgebra R ℓ' → CommAlgebra S ℓ'
  baseChange A =
    Iso.inv (CommAlgChar.CommAlgIso S) (fst asRingHom , compCommRingHom f (snd asRingHom))
    where
      asRingHom : CommAlgChar.CommRingWithHom R
      asRingHom = Iso.fun (CommAlgChar.CommAlgIso R) A

  baseChangeHom : (A B : CommAlgebra R ℓ') → CommAlgebraHom A B → CommAlgebraHom (baseChange A) (baseChange B)
  baseChangeHom A B ϕ =
    CommAlgChar.toCommAlgebraHom S (fst homA , snd homA ∘cr f) (fst homB , snd homB ∘cr f) (fst pbSliceHom) (snd pbSliceHom)
    where open RingHoms
          homA = Iso.fun (CommAlgChar.CommAlgIso R) A
          homB = Iso.fun (CommAlgChar.CommAlgIso R) B

          asSliceHom : Σ[ h ∈ CommRingHom (CommAlgebra→CommRing A) (CommAlgebra→CommRing B) ] h ∘cr (snd homA) ≡ snd homB
          asSliceHom = CommAlgChar.fromCommAlgebraHom R A B ϕ

          pbSliceHom : Σ[ k ∈ CommRingHom (CommAlgebra→CommRing A) (CommAlgebra→CommRing B) ]
                       k ∘cr ((snd homA) ∘cr f) ≡ ((snd homB) ∘cr f)
          pbSliceHom = fst asSliceHom , CommRingHom≡ λ i x → fst ((snd asSliceHom) i) (fst f x)
