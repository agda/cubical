
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Explicit.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Data.Strict2Group.Explicit.Base
open import Cubical.Data.Strict2Group.Explicit.Notation

S2G : (ℓ : Level) → Type (ℓ-suc ℓ)
S2G ℓ = Strict2GroupExp ℓ

S2GΣBase : (ℓ : Level) → Type (ℓ-suc ℓ)
S2GΣBase ℓ =
  Σ[ C₀ ∈ Group ℓ ]
  Σ[ C₁ ∈ Group ℓ ]
  Σ[ s ∈ morph C₁ C₀ ]
  Σ[ t ∈ morph C₁ C₀ ]
  Σ[ i ∈ morph C₀ C₁ ]
     ((g f : Group.type C₁) → s .fst g ≡ t .fst f → Group.type C₁) -- ∘

S2GΣRest : {ℓ : Level} → (S2GΣBase ℓ) → Type ℓ
S2GΣRest (C₀ , C₁ , s , t , i , ∘)
  = Σ[ si ∈ ((x : TC₀) → src (id x) ≡ x) ]
    Σ[ ti ∈ ((x : TC₀) → tar (id x) ≡ x) ]
    Σ[ s∘ ∈ ((g f : TC₁) → (coh : CohCond g f) → src (∘ g f coh) ≡ src f) ]
    Σ[ t∘ ∈ ((g f : TC₁) → (coh : CohCond g f) → tar (∘ g f coh) ≡ tar g) ]
    Σ[ isMorph∘ ∈ ({g f g' f' : TC₁} (c : CohCond g f) (c' : CohCond g' f') → ∘ (g ∙₁ g') (f ∙₁ f') (∙c c c') ≡ (∘ g f c) ∙₁ (∘ g' f' c')) ]
    Σ[ assoc∘ ∈ ({h g f : TC₁} → (c1 : CohCond g f) → (c2 : CohCond h g) → ∘ (∘ h g c2) f  ((s∘ h g c2) ∙ c1) ≡ ∘ h (∘ g f c1) (c2 ∙ (sym (t∘ g f c1)))) ]
    Σ[ lUnit∘ ∈ ((f : TC₁) → ∘ (id (tar f)) f (si (tar f)) ≡ f) ]
    ((f : TC₁) → ∘ f (id (src f)) (sym (ti (src f))) ≡ f) -- rUnit∘
    where open S2GBaseNotation C₀ C₁ s t i ∘

S2GΣ : (ℓ : Level) → Type (ℓ-suc ℓ)
S2GΣ ℓ = Σ[ X ∈ S2GΣBase ℓ ] (S2GΣRest X)

S2GΣ→S2G : {ℓ : Level} → S2GΣ ℓ → S2G ℓ
S2GΣ→S2G ((C₀ , C₁ , s , t , i , ∘) , (si , ti , s∘ , t∘ , isMorph∘ , assoc∘ , lUnit∘ , rUnit∘)) = strict2groupexp C₀ C₁ s t i ∘ si ti s∘ t∘ isMorph∘ assoc∘ lUnit∘ rUnit∘

-- Σ-type of data needed to define the type of PathPs between the base data for an S2G
S2GΣBase≡ : {ℓ : Level} → (SB SB' : S2GΣBase ℓ) → Type (ℓ-suc ℓ)
S2GΣBase≡
  (C₀ , C₁ , s , t , i , ∘ )
  (C₀' , C₁' , s' , t' , i' , ∘')
  = Σ[ p-C₀ ∈ (C₀ ≡ C₀') ]
    Σ[ p-C₁ ∈ (C₁ ≡ C₁') ]
    Σ[ p-s ∈ (PathP (λ j → morph (p-C₁ j) (p-C₀ j)) s s') ]
    Σ[ p-t ∈ (PathP (λ j → morph (p-C₁ j) (p-C₀ j)) t t') ]
    Σ[ p-i ∈ (PathP (λ j → morph (p-C₀ j) (p-C₁ j)) i i') ]
      (PathP (λ j → (g f : Group.type (p-C₁ j)) → (fst (p-s j)) g ≡ (fst (p-t j)) f → Group.type (p-C₁ j)) ∘ ∘') -- p∘

S2GΣRest≡ : {ℓ : Level} {SB SB' : S2GΣBase ℓ} (SR : S2GΣRest {ℓ = ℓ} SB) (SR' : S2GΣRest {ℓ = ℓ} SB') (pSB : S2GΣBase≡ {ℓ = ℓ} SB SB') → Type ℓ
S2GΣRest≡ {ℓ}
  {C₀ , C₁ , s , t , i , ∘}
  {C₀' , C₁' , s' , t' , i' , ∘'}
  (si , ti , s∘ , t∘ , isMorph∘ , assoc∘ , lUnit∘ , rUnit∘)
  (si' , ti' , s∘' , t∘' , isMorph∘' , assoc∘' , lUnit∘' , rUnit∘')
  (p-C₀ , p-C₁ , p-s , p-t , p-i , p∘)
  = Σ[ p-si ∈ (PathP (λ j → (x : Group.type (p-C₀ j)) → ((p-s j) .fst) (((p-i j) .fst) x) ≡ x) si si') ]
    Σ[ p-ti ∈ (PathP (λ j → (x : Group.type (p-C₀ j)) → ((p-t j) .fst) (((p-i j) .fst) x) ≡ x) ti ti') ]
    Σ[ p-s∘ ∈ (PathP (λ j → (g f : Group.type (p-C₁ j)) → (coh : (p-s j) .fst g ≡ (p-t j) .fst f) → (p-s j) .fst ((p∘ j) g f coh) ≡ (p-s j) .fst f) s∘ s∘') ]
    Σ[ p-t∘ ∈ (PathP (λ j → (g f : Group.type (p-C₁ j)) → (coh : (p-s j) .fst g ≡ (p-t j) .fst f) → (p-t j) .fst ((p∘ j) g f coh) ≡ (p-t j) .fst g) t∘ t∘') ]
    Σ[ p-isMorph∘ ∈ PathP
       (λ j → {g f g' f' : TC₁j j}
         (coh1 : CohCondj j g f)
         (coh2 : CohCondj j g' f')
           → (p∘ j) (∙₁j j g g') (∙₁j j f f') (∙cj j coh1 coh2) ≡ ∙₁j j (p∘ j g f coh1) (p∘ j g' f' coh2))
        isMorph∘ isMorph∘' ]
    Σ[ p-assococ∘ ∈ (PathP
       (λ j → {h g f : TC₁j j}
         (coh1 : CohCondj j g f)
         (coh2 : CohCondj j h g)
          → (p∘ j (p∘ j h g coh2) f (p-s∘ j h g coh2 ∙ coh1)) ≡ (p∘ j h (p∘ j g f coh1) (coh2 ∙ (sym (p-t∘ j g f coh1)))))
        assoc∘ assoc∘') ]
    Σ[ p-lUnit∘ ∈ (PathP
       (λ j → (f : TC₁j j)
         → p∘ j (idj j (tarj j f)) f (p-si j (tarj j f)) ≡ f)
       lUnit∘ lUnit∘') ]
        (PathP (λ j → (f : TC₁j j)
          → p∘ j f (idj j (srcj j f)) (sym (p-ti j (srcj j f))) ≡ f)
        rUnit∘ rUnit∘') -- p-rUnit∘
    where
      TC₁j = λ (j : I) → Group.type (p-C₁ j)
      TC₀j = λ (j : I) → Group.type (p-C₀ j)

      CohCondj : (j : I) (g f : TC₁j j) → Type ℓ
      CohCondj j g f = (p-s j) .fst g ≡ (p-t j) .fst f

      ∙₁j = λ (j : I) → isGroup.comp (Group.groupStruc (p-C₁ j))
      ∙₀j = λ (j : I) → isGroup.comp (Group.groupStruc (p-C₀ j))

      idj = λ (j : I) → fst (p-i j)
      srcj = λ (j : I) → fst (p-s j)
      tarj = λ (j : I) → fst (p-t j)
      src∙₁j = λ (j : I) → snd (p-s j)
      tar∙₁j = λ (j : I) → snd (p-t j)

      ∙cj : (j : I) → {g f g' f' : TC₁j j} → (c1 : CohCondj j g f) → (c2 : CohCondj j g' f') → (p-s j) .fst (∙₁j j g g') ≡ (p-t j) .fst (∙₁j j f f')
      ∙cj j {g} {f} {g'} {f'} c1 c2 =
        src∙₁j j g g' ∙
        cong (λ z → ∙₀j j z (srcj j g')) c1 ∙
        cong (λ z → ∙₀j j (tarj j f) z) c2 ∙
        sym (tar∙₁j j f f')


S2GR≡ : {ℓ : Level}
  {SB SB' : S2GΣBase ℓ} {SR : S2GΣRest {ℓ = ℓ} SB} {SR' : S2GΣRest {ℓ = ℓ} SB'}
  {pSB : S2GΣBase≡ {ℓ = ℓ} SB SB'} (pSR : S2GΣRest≡ {ℓ = ℓ} {SB = SB} {SB' = SB'} SR SR' pSB)
  → S2GΣ→S2G (SB , SR) ≡ S2GΣ→S2G (SB' , SR')
S2GR≡ {ℓ}
  {C₀ , C₁ , s , t , i , ∘} -- SB
  {C₀' , C₁' , s' , t' , i' , ∘'} --SB'
  {si , ti , s∘ , t∘} -- SR
  {si' , ti' , s∘' , t∘'} -- SR'
  {p-C₀ , p-C₁ , p-s , p-t , p-i , p∘} -- pSB
  (p-si , p-ti , p-s∘ , p-t∘ , p-isMorph∘ , p-assococ∘ , p-lUnit∘ , p-rUnit∘) j
  = strict2groupexp (p-C₀ j) (p-C₁ j) (p-s j) (p-t j) (p-i j) (p∘ j) (p-si j) (p-ti j) (p-s∘ j) (p-t∘ j) (p-isMorph∘ j) (p-assococ∘ j) (p-lUnit∘ j) (p-rUnit∘ j)
