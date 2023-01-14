{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.NonPresheaf.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.NonPresheaf.Forget

open Category
open Functor
open NatTrans

private
  variable
    ℓ ℓ' ℓS : Level

freePresheaf : (C : Category ℓ ℓ') → isSet (ob C)
  → NonPresheaf C ℓS → Presheaf C (ℓ-max (ℓ-max ℓ ℓ') ℓS)
fst (F-ob (freePresheaf C isSetObC X) c) = Σ[ d ∈ ob C ] C [ c , d ] × fst (X d)
snd (F-ob (freePresheaf C isSetObC X) c) = isSetΣ isSetObC λ d → isSet× (isSetHom C) (snd (X d))
F-hom (freePresheaf C isSetObC X) {d}{c} φ (e , ψ , x) = e , φ ⋆⟨ C ⟩ ψ , x
F-id (freePresheaf C isSetObC X) {c} i (d , φ , x) = d , ⋆IdL C φ i , x
F-seq (freePresheaf C isSetObC X) {e}{d}{c} ψ φ i (f , ω , x) = f , ⋆Assoc C φ ψ ω i , x

FreePresheaf : (C : Category ℓ ℓ') → isSet (ob C)
  → Functor (NonPresheafCategory C ℓS) (PresheafCategory C (ℓ-max (ℓ-max ℓ ℓ') ℓS))
F-ob (FreePresheaf C isSetObC) X = freePresheaf C isSetObC X
N-ob (F-hom (FreePresheaf C isSetObC) {X} {Y} f) c (d , φ , x) = d , φ , f d x
N-hom (F-hom (FreePresheaf C isSetObC) {X} {Y} f) {c} {c'} g = refl
F-id (FreePresheaf C isSetObC) {X} = makeNatTransPath (funExt (λ c → funExt λ {(d , φ , x) → refl}))
F-seq (FreePresheaf C isSetObC) {X}{Y}{Z} f g = makeNatTransPath (funExt (λ c → funExt λ {(d , φ , x) → refl}))

-- Prove relative adjunction w.r.t. a level-lift between SETs?
