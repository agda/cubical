{-
  Reflexive directed multigraphs (with loops)
-}
{-# OPTIONS --safe #-}
module Cubical.Data.Graph.Reflexive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Graph.Base

private variable ℓv ℓv'  ℓe ℓe'  : Level


record RGraph ℓv ℓe : Type (ℓ-suc (ℓ-max ℓv ℓe)) where
  no-eta-equality
  field
    Node : Type ℓv
    Edge : Node → Node → Type ℓe
    Refl : (x : Node) → Edge x x

open RGraph public

record RGraphHom (G  : RGraph ℓv  ℓe ) (H : RGraph ℓv' ℓe')
                : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-max ℓv' ℓe'))) where
  no-eta-equality
  field
    _$g_ : Node G → Node H
    _<$g>_ : ∀ {v w : Node G} → Edge G v w → Edge H (_$g_ v) (_$g_ w)
    presRefl   : ∀ (v : Node G) → _<$g>_ (Refl G v) ≡ Refl H (_$g_ v)

open RGraphHom public

module _ {ℓv ℓe ℓv' ℓe' ℓv'' ℓe''}
         {G : RGraph ℓv ℓe}{G' : RGraph ℓv' ℓe'}{G'' : RGraph ℓv'' ℓe''} where
  _⋆RGrHom_ : RGraphHom G G' → RGraphHom G' G'' → RGraphHom G G''
  (ϕ ⋆RGrHom ψ) $g v = ψ $g (ϕ $g v)
  (ϕ ⋆RGrHom ψ) <$g> e = ψ <$g> (ϕ <$g> e)
  (ϕ ⋆RGrHom ψ) .presRefl v =
    ((ψ <$g> (ϕ <$g> Refl G v)))  ≡⟨ cong (ψ <$g>_) (presRefl ϕ v) ⟩
    ( ψ <$g> (Refl G' (ϕ $g v)))  ≡⟨ presRefl ψ (ϕ $g v) ⟩
    Refl G'' ((ϕ ⋆RGrHom ψ) $g v) ∎

  _∘RGrHom_ : RGraphHom G' G'' → RGraphHom G G' → RGraphHom G G''
  ψ ∘RGrHom ϕ = ϕ ⋆RGrHom ψ

IdRHom : ∀ {ℓv ℓe} {G : RGraph ℓv ℓe} → RGraphHom G G
IdRHom {G} ._$g_ = λ z → z
IdRHom {G} ._<$g>_ = λ z → z
IdRHom {G} .presRefl x = refl

RGrHom≡ : ∀ {ℓg ℓg' ℓh ℓh'}
  {G : RGraph ℓg ℓg'} {H : RGraph ℓh ℓh'} {ϕ ψ : RGraphHom G H}
  → (ϕ≡ψ : ∀ v → ϕ $g v ≡ ψ $g v)
  → (ϕ→≡ψ→ : (∀ {v w} (e : G .Edge v w)
    → PathP (λ i → H .Edge (ϕ≡ψ v i) (ϕ≡ψ w i)) (ϕ <$g> e) (ψ <$g> e)))
  → ((v : G .Node)
    → PathP (λ i → ϕ→≡ψ→ (Refl G v) i ≡ Refl H (ϕ≡ψ v i)) (ϕ .presRefl v) (ψ .presRefl v))
  → ϕ ≡ ψ
RGrHom≡ ϕ≡ψ _ _ i $g v = ϕ≡ψ v i
RGrHom≡ _ ϕ→≡ψ→ _ i <$g> e = ϕ→≡ψ→ e i
RGrHom≡ _ _ presRefl≡presRefl i .presRefl v = presRefl≡presRefl v i

ReflGraph→Graph : RGraph ℓv ℓe → Graph ℓv ℓe
Node (ReflGraph→Graph G) = Node G
Edge (ReflGraph→Graph G) = Edge G
