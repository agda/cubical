{-

  This file formalizes Thm. 1 and Cor. 3 of section X.3
  of Mac Lane's "Categories for the working mathematician"

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Limits.RightKan where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Limits

module _ {ℓC ℓC' ℓM ℓM' ℓA ℓA' : Level}
         {C : Category ℓC ℓC'}
         {M : Category ℓM ℓM'}
         {A : Category ℓA ℓA'}
         (limitA : Limits {ℓ-max ℓC' ℓM} {ℓ-max ℓC' ℓM'} A)
         (K : Functor M C)
         (T : Functor M A)
         where

 open Category
 open Functor
 open Cone
 open LimCone


 _↓Diag : ob C → Category (ℓ-max ℓC' ℓM) (ℓ-max ℓC' ℓM')
 ob (x ↓Diag) = Σ[ u ∈ ob M ] C [ x , K .F-ob u ]
 Hom[_,_] (x ↓Diag) (u , f) (v , g) = Σ[ h ∈ M [ u , v ] ] f ⋆⟨ C ⟩ K .F-hom h ≡ g
 id (x ↓Diag) {x = (u , f)} = id M , cong (seq' C f) (F-id K) ∙ ⋆IdR C f
 _⋆_ (x ↓Diag) {x = (u , f)} (h , hComm) (k , kComm) = (h ⋆⟨ M ⟩ k)
                                                     , cong (seq' C f) (F-seq K h k)
                                                     ∙ sym (⋆Assoc C _ _ _)
                                                     ∙ cong (λ l → seq' C l (F-hom K k)) hComm
                                                     ∙ kComm
 ⋆IdL (x ↓Diag) _ = Σ≡Prop (λ _ → isSetHom C _ _) (⋆IdL M _)
 ⋆IdR (x ↓Diag) _ = Σ≡Prop (λ _ → isSetHom C _ _) (⋆IdR M _)
 ⋆Assoc (x ↓Diag) _ _ _ = Σ≡Prop (λ _ → isSetHom C _ _) (⋆Assoc M _ _ _)
 isSetHom (x ↓Diag) = isSetΣSndProp (isSetHom M) λ _ → isSetHom C _ _

 private
  i : (x : ob C) → Functor (x ↓Diag) M
  F-ob (i x) = fst
  F-hom (i x) = fst
  F-id (i x) = refl
  F-seq (i x) _ _ = refl

  j : {x y : ob C} (f : C [ x , y ]) → Functor (y ↓Diag) (x ↓Diag)
  F-ob (j f) (u , g) = u , f ⋆⟨ C ⟩ g
  F-hom (j f) (h , hComm) = h , ⋆Assoc C _ _ _ ∙ cong (seq' C f) hComm
  F-id (j f) = Σ≡Prop (λ _ → isSetHom C _ _) refl
  F-seq (j f) _ _ = Σ≡Prop (λ _ → isSetHom C _ _) refl


 T* : (x : ob C) → Functor (x ↓Diag) A
 T* x = funcComp T (i x)

 RanOb : ob C → ob A
 RanOb x = limitA (x ↓Diag) (T* x) .lim


 RanCone : {x y : ob C} → C [ x , y ] → Cone (T* y) (RanOb x)
 coneOut (RanCone {x = x} f) v = limOut (limitA (x ↓Diag) (T* x)) (j f .F-ob v)
 coneOutCommutes (RanCone {x = x} f) h = limOutCommutes (limitA (x ↓Diag) (T* x)) (j f .F-hom h)

 private
   -- technical lemmas for proving functoriality
  RanConeRefl : ∀ {x} v →
                limOut (limitA (x ↓Diag) (T* x)) v
              ≡ limOut (limitA (x ↓Diag) (T* x)) (j (id C) .F-ob v)
  RanConeRefl {x = x} (v , f) =
              cong (λ p → limOut (limitA (x ↓Diag) (T* x)) (v , p)) (sym (⋆IdL C f))

  RanConeTrans : ∀ {x y z} (f : C [ x , y ]) (g : C [ y , z ]) v →
                 limOut (limitA (x ↓Diag) (T* x)) (j f .F-ob (j g .F-ob v))
               ≡ limOut (limitA (x ↓Diag) (T* x)) (j (f ⋆⟨ C ⟩ g) .F-ob v)
  RanConeTrans {x = x} {y = y} {z = z} f g  (v , h) =
               cong (λ p → limOut (limitA (x ↓Diag) (T* x)) (v , p)) (sym (⋆Assoc C f g h))


 -- the right Kan-extension
 Ran : Functor C A
 F-ob Ran = RanOb
 F-hom Ran {y = y} f = limArrow (limitA (y ↓Diag) (T* y)) _ (RanCone f)
 F-id Ran {x = x} =
  limArrowUnique (limitA (x ↓Diag) (T* x)) _ _ _ (λ v → (⋆IdL A _) ∙ RanConeRefl v)
 F-seq Ran {x = x} {y = y} {z = z} f g =
  limArrowUnique (limitA (z ↓Diag) (T* z)) _ _ _ path
  where
  path : ∀ v →
         (F-hom Ran f) ⋆⟨ A ⟩ (F-hom Ran g) ⋆⟨ A ⟩ (limOut (limitA (z ↓Diag) (T* z)) v)
       ≡ coneOut (RanCone (f ⋆⟨ C ⟩ g)) v
  path v = (F-hom Ran f) ⋆⟨ A ⟩ (F-hom Ran g) ⋆⟨ A ⟩ (limOut (limitA (z ↓Diag) (T* z)) v)
         ≡⟨ ⋆Assoc A _ _ _ ⟩
           (F-hom Ran f) ⋆⟨ A ⟩ ((F-hom Ran g) ⋆⟨ A ⟩ (limOut (limitA (z ↓Diag) (T* z)) v))
         ≡⟨ cong (seq' A (F-hom Ran f)) (limArrowCommutes (limitA _ _) _ _ _) ⟩
           (F-hom Ran f) ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) (j g .F-ob v)
         ≡⟨ limArrowCommutes (limitA _ _) _ _ _ ⟩
           limOut (limitA (x ↓Diag) (T* x)) (j f .F-ob (j g .F-ob v))
         ≡⟨ RanConeTrans f g v ⟩
           coneOut (RanCone (f ⋆⟨ C ⟩ g)) v ∎


 open NatTrans
 RanNatTrans : NatTrans (funcComp Ran K) T
 N-ob RanNatTrans u = coneOut (RanCone (id C)) (u , id C)
 N-hom RanNatTrans {x = u} {y = v} f =
     Ran .F-hom (K .F-hom f) ⋆⟨ A ⟩ coneOut (RanCone (id C)) (v , id C)
   ≡⟨ cong (λ g → Ran .F-hom (K .F-hom f) ⋆⟨ A ⟩ g) (sym (RanConeRefl (v , id C))) ⟩
     Ran .F-hom (K .F-hom f) ⋆⟨ A ⟩ limOut (limitA ((K .F-ob v) ↓Diag) (T* (K .F-ob v))) (v , id C)
   ≡⟨ limArrowCommutes (limitA _ _) _ _ _ ⟩
     coneOut (RanCone (K .F-hom f)) (v , id C)
   ≡⟨ cong (λ g → limOut (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u))) (v , g))
                         (⋆IdR C (K .F-hom f) ∙ sym (⋆IdL C (K .F-hom f))) ⟩
     coneOut (RanCone (id C)) (v , K .F-hom f)
   ≡⟨ sym (coneOutCommutes (RanCone (id C)) (f , ⋆IdL C _)) ⟩
     coneOut (RanCone (id C)) (u , id C) ⋆⟨ A ⟩ T .F-hom f ∎

 -- the universal property
 private ε = RanNatTrans

 NatTransCone : (S : Functor C A) (α : NatTrans (S ∘F K) T) (x : ob C)
              → Cone (T* x) (S .F-ob x)
 coneOut (NatTransCone S α x) (v , f) = S .F-hom f ⋆⟨ A ⟩ α .N-ob v
 coneOutCommutes (NatTransCone S α x) {u = (u , f)} {v = (v , g)} (h , f⋆Kh≡g) =
     (S .F-hom f ⋆⟨ A ⟩ α .N-ob u) ⋆⟨ A ⟩ T .F-hom h
   ≡⟨ ⋆Assoc A _ _ _ ⟩
     S .F-hom f ⋆⟨ A ⟩ (α .N-ob u ⋆⟨ A ⟩ T .F-hom h)
   ≡⟨ cong (seq' A (S .F-hom f)) (sym (α .N-hom h)) ⟩
     S .F-hom f ⋆⟨ A ⟩ ((S ∘F K) .F-hom h ⋆⟨ A ⟩ α .N-ob v)
   ≡⟨ sym (⋆Assoc A _ _ _) ⟩
     (S .F-hom f ⋆⟨ A ⟩ (S ∘F K) .F-hom h) ⋆⟨ A ⟩ α .N-ob v
   ≡⟨ cong (λ x → x ⋆⟨ A ⟩ (α .N-ob v)) (sym (S .F-seq _ _)) ⟩
     S .F-hom (f ⋆⟨ C ⟩ K .F-hom h) ⋆⟨ A ⟩ α .N-ob v
   ≡⟨ cong (λ x → S .F-hom x ⋆⟨ A ⟩ (α .N-ob v)) f⋆Kh≡g ⟩
     S .F-hom g ⋆⟨ A ⟩ α .N-ob v ∎


 RanUnivProp : ∀ (S : Functor C A) (α : NatTrans (S ∘F K) T)
             → ∃![ σ ∈ NatTrans S Ran ] α ≡ (σ ∘ˡ K) ●ᵛ ε
 RanUnivProp S α = uniqueExists σ pathNatTrans (λ _ → isSetNatTrans _ _) pathUnique
   where
   σ : NatTrans S Ran
   N-ob σ x = limArrow (limitA (x ↓Diag) (T* x)) _ (NatTransCone S α x)
   N-hom σ {x = x} {y = y} f = preCompUnique (N-ob σ x ⋆⟨ A ⟩ Ran .F-hom f)
                                             (limitA (y ↓Diag) (T* y) .limCone)
                                             (limitA (y ↓Diag) (T* y) .univProp)
                                             (S .F-hom f ⋆⟨ A ⟩ N-ob σ y)
                                             equalUpToConeOut

     where
     equalUpToConeOut : ∀ (u : ob (y ↓Diag))
                      → (S .F-hom f ⋆⟨ A ⟩ N-ob σ y) ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) u
                      ≡ (N-ob σ x ⋆⟨ A ⟩ Ran .F-hom f) ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) u
     equalUpToConeOut (u , g) =
         (S .F-hom f ⋆⟨ A ⟩ N-ob σ y) ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) (u , g)
       ≡⟨ ⋆Assoc A _ _ _ ⟩
         S .F-hom f ⋆⟨ A ⟩ (N-ob σ y ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) (u , g))
       ≡⟨ cong (seq' A (S .F-hom f)) (limArrowCommutes (limitA _ _) _ _ _) ⟩
         S .F-hom f ⋆⟨ A ⟩ (S .F-hom g ⋆⟨ A ⟩ α .N-ob u)
       ≡⟨ sym (⋆Assoc A _ _ _) ⟩
         (S .F-hom f ⋆⟨ A ⟩ S .F-hom g) ⋆⟨ A ⟩ α .N-ob u
       ≡⟨ cong (λ h → h ⋆⟨ A ⟩ α .N-ob u) (sym (S .F-seq _ _)) ⟩
         S .F-hom (f ⋆⟨ C ⟩ g) ⋆⟨ A ⟩ α .N-ob u
       ≡⟨ sym (limArrowCommutes (limitA _ _) _ _ _) ⟩
         N-ob σ x ⋆⟨ A ⟩ limOut (limitA (x ↓Diag) (T* x)) (u , f ⋆⟨ C ⟩ g)
       ≡⟨ cong (seq' A (N-ob σ x)) (sym (limArrowCommutes (limitA _ _) _ _ _)) ⟩
         N-ob σ x ⋆⟨ A ⟩ (Ran .F-hom f ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) (u , g))
       ≡⟨ sym (⋆Assoc A _ _ _) ⟩
         (N-ob σ x ⋆⟨ A ⟩ Ran .F-hom f) ⋆⟨ A ⟩ limOut (limitA (y ↓Diag) (T* y)) (u , g) ∎


   pathNatTrans : α ≡ (σ ∘ˡ K) ●ᵛ ε
   pathNatTrans = makeNatTransPath (funExt path)
     where
     path : ∀ (u : ob M)
          → α .N-ob u
          ≡ limArrow (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u))) _ (NatTransCone S α (F-ob K u))
              ⋆⟨ A ⟩ limOut (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u))) (u , id C ⋆⟨ C ⟩ id C)
     path u =
         α .N-ob u
       ≡⟨ sym (⋆IdL A _) ⟩
         id A ⋆⟨ A ⟩ α .N-ob u
       ≡⟨ cong (λ x → x ⋆⟨ A ⟩ α .N-ob u) (sym (S .F-id)) ⟩
         S .F-hom (id C) ⋆⟨ A ⟩ α .N-ob u
       ≡⟨ cong (λ x → S .F-hom x ⋆⟨ A ⟩ α .N-ob u) (sym (⋆IdL C _)) ⟩
         S .F-hom (id C ⋆⟨ C ⟩ id C) ⋆⟨ A ⟩ α .N-ob u
       ≡⟨ refl ⟩
         NatTransCone S α (F-ob K u) .coneOut (u , id C ⋆⟨ C ⟩ id C)
       ≡⟨ sym (limArrowCommutes (limitA _ _) _ _ _) ⟩
         limArrow (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u))) _ (NatTransCone S α (F-ob K u))
           ⋆⟨ A ⟩ limOut (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u))) (u , id C ⋆⟨ C ⟩ id C) ∎

   pathUnique : ∀ (τ : NatTrans S Ran) → α ≡ (τ ∘ˡ K) ●ᵛ ε → σ ≡ τ
   pathUnique τ α≡ετK = makeNatTransPath
                          (funExt (λ x →
                             limArrowUnique (limitA (x ↓Diag) (T* x)) _ _ _ (isConeMorτ x)))
     where
     isConeMorτ : ∀ (x : ob C) → isConeMor (NatTransCone S α x) (limitA (x ↓Diag) (T* x) .limCone) (τ .N-ob x)
     isConeMorτ x (u , f) =
       let p : f ≡ f ⋆⟨ C ⟩ (id C ⋆⟨ C ⟩ id C)
           p = sym (⋆IdR C f) ∙ cong (seq' C f) (sym (⋆IdR C (id C)))
       in
         τ .N-ob x ⋆⟨ A ⟩ limOut (limitA (x ↓Diag) (T* x)) (u , f)
       ≡⟨ (λ i → τ .N-ob x ⋆⟨ A ⟩ limOut (limitA (x ↓Diag) (T* x)) (u , p i)) ⟩
         τ .N-ob x ⋆⟨ A ⟩ limOut (limitA (x ↓Diag) (T* x)) (u , f ⋆⟨ C ⟩ (id C ⋆⟨ C ⟩ id C))
       ≡⟨ cong (seq' A (τ .N-ob x)) (sym (limArrowCommutes
                                         (limitA ((K .F-ob u) ↓Diag) (T* (K .F-ob u)))
                                         _ _ _)) ⟩
         τ .N-ob x ⋆⟨ A ⟩ (Ran .F-hom f ⋆⟨ A ⟩ ε .N-ob u)
       ≡⟨ sym (⋆Assoc A _ _ _) ⟩
         (τ .N-ob x ⋆⟨ A ⟩ Ran .F-hom f) ⋆⟨ A ⟩ ε .N-ob u
       ≡⟨ cong (λ g → g ⋆⟨ A ⟩ ε .N-ob u) (sym (τ .N-hom f)) ⟩
         (S .F-hom f ⋆⟨ A ⟩ τ .N-ob (K .F-ob u)) ⋆⟨ A ⟩ ε .N-ob u
       ≡⟨ ⋆Assoc A _ _ _ ⟩
         S .F-hom f ⋆⟨ A ⟩ (τ .N-ob (K .F-ob u) ⋆⟨ A ⟩ ε .N-ob u)
       ≡⟨ cong (seq' A (S .F-hom f)) (cong (λ γ → γ .N-ob u) (sym α≡ετK)) ⟩
         S .F-hom f ⋆⟨ A ⟩ α .N-ob u ∎




 open isIso
 open NatIso

 RanNatIso : isFullyFaithful K → NatIso (funcComp Ran K) T
 trans (RanNatIso isFFK) = RanNatTrans
 nIso (RanNatIso isFFK) u = LimIso _ (limitA (K .F-ob u ↓Diag) (T* (K .F-ob u)))
                                     (Initial→LimCone _ uInitial) .fst .fst .snd
   where
   invKHom : {u v : ob M} → C [ K .F-ob u , K .F-ob v ] → M [ u , v ]
   invKHom f = invEq (K .F-hom , (isFFK _ _)) f

   secKHom : ∀ {u v : ob M} (f : C [ K .F-ob u , K .F-ob v ])
           → K .F-hom (invKHom f) ≡ f
   secKHom f = secEq (K .F-hom , (isFFK _ _)) f

   uInitial : Initial (K .F-ob u ↓Diag)
   fst uInitial = u , id C ⋆⟨ C ⟩ id C
   fst (snd uInitial (v , f)) = invKHom f -- the unique arrow u→v in Ku↓
                              , cong₂ (seq' C) (⋆IdL C _) (secKHom f) ∙ ⋆IdL C f
   snd (snd uInitial (v , f)) (g , tr) = Σ≡Prop (λ _ → isSetHom C _ _) path -- is indeed unique
     where
     path : invKHom f ≡ g
     path = isFullyFaithful→Faithful {F = K} isFFK _ _ _ _
              (secKHom f ∙∙ sym tr ∙∙ cong (λ x → x ⋆⟨ C ⟩ K .F-hom g) (⋆IdL C _) ∙ ⋆IdL C _)
