{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩; withOpaqueStr)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.Ring

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

CommAlgebra : (R : CommRing ℓ) (ℓ' : Level) → Type _
CommAlgebra R ℓ' = Σ[ A ∈ CommRing ℓ' ] CommRingHom R A

module _ {R : CommRing ℓ} where
  CommAlgebra→CommRing : (A : CommAlgebra R ℓ') → CommRing ℓ'
  CommAlgebra→CommRing = fst

  ⟨_⟩ₐ : (A : CommAlgebra R ℓ') → Type ℓ'
  ⟨ A ⟩ₐ = A .fst .fst

  record IsCommAlgebraHom (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') (f : ⟨ A ⟩ₐ → ⟨ B ⟩ₐ) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    no-eta-equality
    field
      isCommRingHom : IsCommRingHom (A .fst .snd) f (B .fst .snd)
      commutes : (f , isCommRingHom) ∘cr snd A ≡ snd B

  unquoteDecl IsCommAlgebraHomIsoΣ = declareRecordIsoΣ IsCommAlgebraHomIsoΣ (quote IsCommAlgebraHom)

  isPropIsCommAlgebraHom : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') (f : ⟨ A ⟩ₐ → ⟨ B ⟩ₐ)
    → isProp (IsCommAlgebraHom A B f)
  isPropIsCommAlgebraHom A B f =
    isOfHLevelRetractFromIso 1 IsCommAlgebraHomIsoΣ $
    isPropΣ (isPropIsCommRingHom (A .fst .snd) f (B .fst .snd))
             λ _ → isSetΣSndProp (isSet→ is-set) (λ _ → isPropIsCommRingHom _ _ _) _ _
    where
    open CommRingStr (B .fst .snd) using (is-set)

  CommAlgebraHom : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → Type _
  CommAlgebraHom A B = Σ[ f ∈ (⟨ A ⟩ₐ → ⟨ B ⟩ₐ) ]  IsCommAlgebraHom A B f

  CommRingHom→CommAlgebraHom :
    {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
    → (f : CommRingHom (A .fst) (B .fst))
    → f ∘cr snd A ≡ snd B
    → CommAlgebraHom A B
  CommRingHom→CommAlgebraHom f commutes .fst = f .fst
  CommRingHom→CommAlgebraHom f commutes .snd =
    record { isCommRingHom = f .snd ; commutes = commutes }

  CommAlgebraHom→CommRingHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraHom A B
                             → CommRingHom (CommAlgebra→CommRing A) (CommAlgebra→CommRing B)
  CommAlgebraHom→CommRingHom f = f .fst , IsCommAlgebraHom.isCommRingHom (f .snd)

  ⟨_⟩ᵣ→ = CommAlgebraHom→CommRingHom

  CommAlgebraHom→Triangle : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → (f : CommAlgebraHom A B)
                             → ⟨ f ⟩ᵣ→ ∘cr A .snd  ≡ B .snd
  CommAlgebraHom→Triangle f = IsCommAlgebraHom.commutes (f .snd)

  idCAlgHom : (A : CommAlgebra R ℓ') → CommAlgebraHom A A
  idCAlgHom A = CommRingHom→CommAlgebraHom (idCommRingHom (fst A)) (CommRingHom≡ refl)

  idCommAlgebraHom = idCAlgHom

  compCommAlgebraHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
                      → (g : CommAlgebraHom B C) → (f : CommAlgebraHom A B)
                      → CommAlgebraHom A C
  compCommAlgebraHom {A = A} {B = B} {C = C} g f =
    CommRingHom→CommAlgebraHom (⟨ g ⟩ᵣ→ ∘cr ⟨ f ⟩ᵣ→) pasting
    where
      opaque
        pasting : (⟨ g ⟩ᵣ→ ∘cr ⟨ f ⟩ᵣ→) ∘cr snd A ≡ snd C
        pasting =
          CommRingHom≡ $
                  (⟨ g ⟩ᵣ→ ∘cr (⟨ f ⟩ᵣ→ ∘cr snd A)) .fst ≡⟨ cong (λ h → (⟨ g ⟩ᵣ→ ∘cr h) .fst) (CommAlgebraHom→Triangle f) ⟩
                  (⟨ g ⟩ᵣ→ ∘cr snd B) .fst             ≡⟨ cong fst (CommAlgebraHom→Triangle g) ⟩
                  (C .snd .fst) ∎

  ⟨_⟩ₐ→ : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} (f : CommAlgebraHom A B) → ⟨ A ⟩ₐ → ⟨ B ⟩ₐ
  ⟨ f ⟩ₐ→ = f .fst

  _$ca_ : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} → (φ : CommAlgebraHom A B) → (x : ⟨ A ⟩ₐ) → ⟨ B ⟩ₐ
  _$ca_ φ x = φ .fst x

  infixr 9 _∘ca_ -- same as functions
  _∘ca_ : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
        → CommAlgebraHom B C → CommAlgebraHom A B → CommAlgebraHom A C
  g ∘ca f = compCommAlgebraHom g f

  opaque
    CommAlgebraHom≡ :
      {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {f g : CommAlgebraHom A B}
      → f .fst ≡ g .fst
      → f ≡ g
    CommAlgebraHom≡ {B = B} p = Σ≡Prop (λ _ → isPropIsCommAlgebraHom _ _ _) p
      where open CommRingStr (B .fst .snd) using (is-set)

  CommAlgebraEquiv : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → Type _
  CommAlgebraEquiv A B = Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd

  idCAlgEquiv : (A : CommAlgebra R ℓ') → CommAlgebraEquiv A A
  idCAlgEquiv A = (idCommRingEquiv (fst A)) ,
                   CommRingHom≡ refl

  CommAlgebraEquiv≡ :
      {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {f g : CommAlgebraEquiv A B}
      → f .fst .fst .fst ≡ g .fst .fst .fst
      → f ≡ g
  CommAlgebraEquiv≡ {B = B} p =
    Σ≡Prop (λ _ → isSetΣSndProp (isSetΠ (λ _ → isSetB)) (λ _ → isPropIsCommRingHom _ _ _) _ _)
           (CommRingEquiv≡ p)
    where open CommRingStr (B .fst .snd) using () renaming (is-set to isSetB)

  isSetCommAlgebraEquiv : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'')
                          → isSet (CommAlgebraEquiv A B)
  isSetCommAlgebraEquiv A B =
    isSetΣSndProp
      (isSetCommRingEquiv _ _)
      (λ e → isSetΣSndProp (isSet→ isSetB) (λ _ → isPropIsCommRingHom _ _ _) _ _)
    where open CommRingStr (B .fst .snd) using () renaming (is-set to isSetB)

  {-
    Contrary to most algebraic structures, this one only contains
    law and structure of a CommAlgebra, which it is *in addition*
    to its CommRing structure.
  -}
  record CommAlgebraStr (A : Type ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    open CommRingStr {{...}}
    instance
      _ : CommRingStr (R .fst)
      _ = (R .snd)

    field
      crStr : CommRingStr A
      _⋆_ : ⟨ R ⟩ → A → A
      ⋆Assoc : (r s : ⟨ R ⟩) (x : A) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x)
      ⋆DistR+ : (r : ⟨ R ⟩) (x y : A) → r ⋆ (CommRingStr._+_ crStr x y) ≡ CommRingStr._+_ crStr(r ⋆ x) (r ⋆ y)
      ⋆DistL+ : (r s : ⟨ R ⟩) (x : A) → (r + s) ⋆ x ≡ CommRingStr._+_ crStr (r ⋆ x) (s ⋆ x)
      ⋆IdL    : (x : A) → 1r ⋆ x ≡ x
      ⋆AssocL : (r : ⟨ R ⟩) (x y : A) → CommRingStr._·_ crStr (r ⋆ x) y ≡ r ⋆ (CommRingStr._·_ crStr x y)
    infixl 7 _⋆_

  {- TODO: make laws opaque -}
  CommAlgebra→CommAlgebraStr : (A : CommAlgebra R ℓ') → CommAlgebraStr ⟨ A ⟩ₐ
  CommAlgebra→CommAlgebraStr A =
    let open CommRingStr ⦃...⦄
        instance
          _ : CommRingStr (R .fst)
          _ = R .snd
          _ = A .fst .snd
    in record
       { crStr = A .fst .snd
       ; _⋆_ = λ r x → (A .snd .fst r) · x
       ; ⋆Assoc = λ r s x → cong (_· x) (IsCommRingHom.pres· (A .snd .snd) r s) ∙ sym (·Assoc _ _ _)
       ; ⋆DistR+ = λ r x y → ·DistR+ _ _ _
       ; ⋆DistL+ = λ r s x → cong (_· x) (IsCommRingHom.pres+ (A .snd .snd) r s) ∙ ·DistL+ _ _ _
       ; ⋆IdL = λ x → cong (_· x) (IsCommRingHom.pres1 (A .snd .snd)) ∙ ·IdL x
       ; ⋆AssocL = λ r x y → sym (·Assoc (A .snd .fst r) x y)
       }

  module CommAlgebraHom {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} (f : CommAlgebraHom A B) where
    open IsCommRingHom (IsCommAlgebraHom.isCommRingHom (f .snd))
    open CommRingStr ⦃...⦄
    open CommAlgebraStr ⦃...⦄
    private instance
      _ = CommAlgebra→CommAlgebraStr A
      _ = CommAlgebra→CommAlgebraStr B
      _ = B .fst .snd

    opaque
      pres⋆ : (r : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → f $ca (r ⋆ x) ≡ r ⋆ f $ca x
      pres⋆ r x = f $ca (r ⋆ x)                        ≡⟨ pres· (A .snd .fst r) x ⟩
                  (f $ca (A .snd .fst r)) · (f $ca x)  ≡⟨ cong (_· (f $ca x)) (cong (λ g → g .fst r) (CommAlgebraHom→Triangle f)) ⟩
                  r ⋆ f $ca x ∎

  CommAlgebraHomFromCommRingHom :
    {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
    → (f : CommRingHom (A .fst) (B .fst))
    → ((r : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → f .fst (CommAlgebraStr._⋆_ (CommAlgebra→CommAlgebraStr A) r x)
                                 ≡ CommAlgebraStr._⋆_ (CommAlgebra→CommAlgebraStr B) r (f .fst x))
    → CommAlgebraHom A B
  CommAlgebraHomFromCommRingHom {A = A} {B = B} f pres⋆ = CommRingHom→CommAlgebraHom f
    let open CommRingStr ⦃...⦄
        open CommAlgebraStr ⦃...⦄
        instance
          _ = A .fst .snd
          _ = B .fst .snd
          _ = CommAlgebra→CommAlgebraStr B
    in CommRingHom≡
      (funExt (λ (r : ⟨ R ⟩) →
              f .fst (A .snd .fst r)        ≡⟨ cong (λ u → f .fst u) (sym (·IdR _)) ⟩
              f .fst ((A .snd .fst r) · 1r) ≡⟨ pres⋆ r (CommRingStr.1r (A .fst .snd)) ⟩
              r ⋆ (f .fst 1r)               ≡⟨ cong (r ⋆_) (IsCommRingHom.pres1 (f .snd)) ⟩
              r ⋆ 1r                        ≡⟨ ·IdR _ ⟩
              B .snd .fst r ∎))

{- Convenient forgetful functions -}
module _ {R : CommRing ℓ} where
  CommAlgebra→Ring : (A : CommAlgebra R ℓ') → Ring ℓ'
  CommAlgebra→Ring A = CommRing→Ring (fst A)


  CommAlgebraHom→RingHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraHom A B
                             → RingHom (CommAlgebra→Ring A) (CommAlgebra→Ring B)
  CommAlgebraHom→RingHom = CommRingHom→RingHom ∘ CommAlgebraHom→CommRingHom

  CommAlgebraEquiv→CommRingHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraEquiv A B
                             → CommRingHom (CommAlgebra→CommRing A) (CommAlgebra→CommRing B)
  CommAlgebraEquiv→CommRingHom e = CommRingEquiv→CommRingHom (e .fst)

  CommAlgebraEquiv→CommAlgebraHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraEquiv A B
                             → CommAlgebraHom A B
  CommAlgebraEquiv→CommAlgebraHom f =
    CommRingHom→CommAlgebraHom (CommRingEquiv→CommRingHom (f .fst)) $ CommRingHom≡ (cong (fst) (f .snd))
