{-# OPTIONS --safe #-}
module Cubical.HITs.CauchyReals.Closeness where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv hiding (_■)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

import Cubical.Functions.Logic as L

open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Properties as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems



-- HoTT Lemma (11.3.8)
refl∼ : ∀ r ε → r ∼[ ε ] r
refl∼ = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x x₁ =
   rat-rat x x x₁
     (subst ((ℚ.- (fst x₁)) ℚ.<_) (sym (+InvR x))
       (minus-< 0 (fst x₁) ((0<→< (fst x₁) (snd x₁)))))
        --(minus-< 0 (fst x₁) (snd x₁)))
        ((subst ( ℚ._< (fst x₁)) (sym (+InvR x)) ((0<→< (fst x₁) (snd x₁)))))
 w .Elimℝ-Prop.limA x p _ ε =
  let e1 = /2₊ (/2₊ ε)
      zz = +CancelL- (fst (/2₊ ε)) (fst (/2₊ ε)) (fst ε)
            (ε/2+ε/2≡ε (fst ε))
          ∙ cong ( ℚ._-_ (fst ε)) (sym (ε/2+ε/2≡ε (fst (/2₊ ε))))
  in lim-lim x x ε e1 e1 p p
        (subst (0<_) zz (snd ((/2₊ ε))))
       (subst (λ e → x e1 ∼[ e ] x e1)
       (ℚ₊≡ (ε/2+ε/2≡ε (fst (/2₊ ε)) ∙
          zz ))
       (p e1 e1))
 w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isProp∼ _ _ _


-- HoTT Lemma (11.3.12)
sym∼ : ∀ r r' ε → r ∼[ ε ] r' → r' ∼[ ε ] r
sym∼ r r' ε (rat-rat q r₁ .ε x x₁) =
 rat-rat r₁ q ε (subst ((ℚ.- fst ε) ℚ.<_)
  ((ℚ.-Distr' q r₁ ∙ ℚ.+Comm (ℚ.- q) r₁))
    $ minus-< (q ℚ.- r₁) (fst ε) x₁)
  (subst2 ℚ._<_ (ℚ.-Distr' q r₁ ∙ ℚ.+Comm (ℚ.- q) r₁)
    (ℚ.-Invol (fst ε)) (minus-< (ℚ.- fst ε)  (q ℚ.- r₁) x))

sym∼ r r' ε (rat-lim q y .ε δ p v x) =
 lim-rat y q ε δ p v (sym∼ _ _ _ x)
sym∼ r r' ε (lim-rat x r₁ .ε δ p v x₁) =
  rat-lim r₁ x ε δ p v (sym∼ _ _ _ x₁)
sym∼ r r' ε (lim-lim x y .ε δ η p p' v x₁) =
 let z = ((sym∼ (x δ) (y η) _ x₁))
     z' = subst (λ xx → Σ _ λ v → y η ∼[ (fst ε ℚ.- xx) , v ] x δ)
            (ℚ.+Comm (fst δ) (fst η))
             (v , z)
 in lim-lim y x ε η δ  p' p (fst z') (snd z')
sym∼ r r' ε (isProp∼ .r .ε .r' x x₁ i) =
  isProp∼ r' ε r (sym∼ _ _ _ x) (sym∼ _ _ _ x₁) i

-- HoTT Theorem (11.3.9)
isSetℝ : isSet ℝ
isSetℝ = lem722 (λ r r' → ∀ ε →  r ∼[ ε ] r')
  (λ _ _ → isPropΠ λ _ → isProp∼ _ _ _)
   eqℝ
   refl∼

∼≃≡ : ∀ r r' → (∀ ε → r ∼[ ε ] r') ≃  (r ≡ r')
∼≃≡ r r' = propBiimpl→Equiv (isPropΠ λ _ → isProp∼ _ _ _) (isSetℝ _ _) (eqℝ _ _)
  (J (λ r' _ → ∀ ε → r ∼[ ε ] r') (refl∼ _))

≡→∼ : ∀ {ε r r'} → r ≡ r' → r ∼[ ε ] r'
≡→∼ {ε} {r} {r'} p = invEq (∼≃≡ r r') p ε




rat-rat' : ℚ → ℚ₊ → ℚ → hProp ℓ-zero
rat-rat' q ε r .fst = ((ℚ.- fst ε) ℚ.< (q ℚ.- r)) × ((q ℚ.- r) ℚ.< fst ε)
rat-rat' q ε r .snd = isProp× (ℚ.isProp< (ℚ.- fst ε) (q ℚ.- r))
                        (ℚ.isProp< (q ℚ.- r) (fst ε))


rat-rat'-sym : ∀ q ε r → ⟨ rat-rat' q ε r ⟩ → ⟨ rat-rat' r ε q ⟩
rat-rat'-sym q ε r x .fst =
  subst ((ℚ.- fst ε) ℚ.<_) (ℚ.-Distr' q r ∙ ℚ.+Comm (ℚ.- q) r)
   (minus-< (q ℚ.- r) (fst ε) (snd x))
rat-rat'-sym q ε r x .snd =
  subst2 (ℚ._<_) (ℚ.-Distr' q r ∙ ℚ.+Comm (ℚ.- q) r) (ℚ.-Invol (fst ε))
   (minus-<  (ℚ.- fst ε) (q ℚ.- r) (fst x))

Σ< : (ℚ₊ → Type) → (ℚ → Type)
Σ< P q = Σ _ (P ∘ (q ,_) )

rat-lim' : ℚ₊ → (ℚ₊ → ℚ₊ → hProp ℓ-zero) → hProp ℓ-zero
rat-lim' ε a =
  (∃[ δ ∈ ℚ₊ ]
      Σ< (fst ∘ a δ) (((fst ε) ℚ.- (fst δ)))  ) , squash₁

lim-lim' : ℚ₊ → (ℚ₊ → ℚ₊ → ℚ₊ → hProp ℓ-zero) → hProp ℓ-zero
lim-lim' ε a =
  (∃[ (δ , η)  ∈ ℚ₊ × ℚ₊ ]
      Σ< (fst ∘ a δ η) ((fst ε) ℚ.- (fst δ ℚ.+ fst η)) ) , squash₁


w-prop' : (ℚ₊ → hProp ℓ-zero) → Type
w-prop' = λ △ → ∀ ε → ⟨
               ( △ ε ) L.⇔ (L.∃[ θ ∶ ℚ₊ ]
                  (L.∃[ v ] (△ (((fst ε) ℚ.- (fst θ)) , v)))) ⟩


substΣ< : (P : Σ (ℚ₊ → hProp ℓ-zero) w-prop') → ∀ {x y} → x ≡ y →
             Σ< (fst ∘ (fst P)) x → Σ< (fst ∘ (fst P)) y
substΣ< P = subst (Σ< (fst ∘ (fst P)))


pre-w-rel' : Σ (ℚ₊ → hProp ℓ-zero) w-prop' →
           Σ (ℚ₊ → hProp ℓ-zero) w-prop' → ℚ₊ → ℚ₊ → Type

w-rel'  : Σ (ℚ₊ → hProp ℓ-zero) w-prop' →
           Σ (ℚ₊ → hProp ℓ-zero) w-prop' → ℚ₊ → Type

pre-w-rel' = λ (△ , _) (◻ , _) ε η
       → (⟨ △ η ⟩ →  ⟨ ◻ (ε ℚ₊+ η) ⟩)


w-rel' = λ △ ◻ ε →
     ∀ η → pre-w-rel' △ ◻ ε η
           × pre-w-rel' ◻ △  ε η

w-rel'-sym : ∀ △ ◻ ε → w-rel' △ ◻ ε → w-rel' ◻ △  ε
w-rel'-sym △ ◻ ε x η = fst Σ-swap-≃ (x η)

w-rel'⇒ : ∀ x y → (∀ ε → w-rel' x y ε) → ∀ ε
          → ⟨ fst x ε ⟩ → ⟨ fst y ε ⟩
w-rel'⇒ x y x₁ ε x₂ =
 let z = fst (snd x ε) x₂
     z' = PT.map (λ (δ , xx) →
              /2₊ δ , PT.map
                  (λ (xxx , xxx') →
                    substΣ< y
                      (cong (λ zz → fst (/2₊ δ) ℚ.+ (fst ε ℚ.- zz))
                        (sym (ε/2+ε/2≡ε (fst δ))) ∙
                          lem--08 {fst (/2₊ δ)} {fst ε})
                       (_ , (fst (x₁ (/2₊ δ) _) xxx')))
                      xx) z
 in snd (snd y ε)
       z'

w-rel'→≡ : ∀ x y → (∀ ε → w-rel' x y ε) → x ≡ y
w-rel'→≡ x y p =
  Σ≡Prop (λ x₁ → isPropΠ λ x →
     (snd (x₁ x L.⇔
     L.∃[∶]-syntax
     (λ θ → L.∃[]-syntax (λ v₁ → x₁ ((fst x ℚ.- fst θ) , v₁))))))
      (funExt λ ε →
   L.⇔toPath (w-rel'⇒ x y p ε)
     (w-rel'⇒ y x (λ ε₁ → w-rel'-sym x y ε₁ (p ε₁)) ε))



r-r : ℚ → ℚ → Σ _ w-prop'
r-r q r .fst ε = rat-rat' q ε r
r-r q r .snd ε .fst x =
 let z = getθ ε (q ℚ.- r) x
 in ∣ fst z , ∣ fst (snd z)  , snd (snd z) ∣₁ ∣₁
r-r q r .snd ε .snd =
  PT.rec (snd (rat-rat' q ε r)) (uncurry λ q* →
   PT.rec (snd (rat-rat' q ε r))
     λ (x₁ , y) →
       weak0<' (q ℚ.- r) ε q* (fst y) , weak0< (q ℚ.- r) ε q* (snd y) )



r-l : (a : ℚ₊ → Σ _ w-prop')

        → Σ _ w-prop'
r-l a .fst ε = rat-lim' ε (fst ∘ a)
r-l a .snd ε .fst =
  PT.rec
      squash₁
       λ (q' , v , pp) →
          let aa = fst ((snd (a q')) ((fst ε ℚ.- fst q') , v)) pp
          in PT.map
              (map-snd λ {a''} →
               (PT.map
                λ x₂ →
                  strength-lem-01 ε q' a'' (fst x₂) ,
                   ∣ q' ,
                    subst {A = ℚ}
                    (λ qq → Σ (0< qq)
                        (λ x₃ → ⟨ a q' .fst (qq , x₃) ⟩))
                    (sym (ℚ.+Assoc (fst ε) (ℚ.- (fst q')) (ℚ.- (fst a'')))
                      ∙∙ cong (fst ε ℚ.+_)
                            (ℚ.+Comm (ℚ.- (fst q')) (ℚ.- (fst a'')))
                      ∙∙ (ℚ.+Assoc (fst ε) (ℚ.- (fst a'')) (ℚ.- (fst q')))) x₂ ∣₁))
              aa

r-l a .snd ε .snd =
       PT.rec
      squash₁
        (uncurry λ q' →
           PT.rec squash₁ (uncurry λ v →
              PT.map λ (q'' , zz) →
                let zzz = snd (snd (a q'') (fst ε ℚ.- fst q'' ,
                     strength-lem-01 ε q' q'' (fst zz)))
                            ∣ q' ,
                              ∣ subst {A = ℚ}
                       (λ qq → Σ (0< qq)
                        (λ x₃ → ⟨ a q'' .fst (qq , x₃) ⟩))
                         ((sym (ℚ.+Assoc (fst ε) (ℚ.- (fst q')) (ℚ.- (fst q'')))
                      ∙∙ cong (fst ε ℚ.+_)
                            (ℚ.+Comm (ℚ.- (fst q')) (ℚ.- (fst q'')))
                      ∙∙ (ℚ.+Assoc (fst ε) (ℚ.- (fst q'')) (ℚ.- (fst q')))))
                         zz ∣₁ ∣₁
                in q'' , _ , zzz))


l-l : (𝕒 : ℚ₊ → ℚ₊ → Σ _ w-prop')

  → Σ (ℚ₊ → hProp ℓ-zero) w-prop'

l-l 𝕒 .fst ε = lim-lim' ε (λ x x₁ → fst (𝕒 x x₁))
l-l 𝕒 .snd ε .fst =
 PT.rec squash₁
 (λ ((δ , η) , (v , y)) →
    PT.map (map-snd (λ {q'} → PT.map
          (λ (x , x') → strength-lem-01 ε (δ ℚ₊+ η) q' x , ∣ (δ , η) ,
            subst (Σ< (fst ∘ (fst (𝕒 δ η))))
              (+AssocCommR (fst ε) (ℚ.- (fst δ ℚ.+ fst η))
                (ℚ.- fst q'))
                (x , x')
            ∣₁ )))
              (fst (snd (𝕒 δ η) _) y))
l-l 𝕒 .snd ε .snd =
  PT.rec squash₁
     (uncurry λ q' →
       PT.rec squash₁ (uncurry λ v →
         PT.map (map-snd
           λ {(δ , η)} (x , x') → strength-lem-01 ε q' (δ ℚ₊+ η) x ,
            (snd (snd (𝕒 δ η) _) ∣ q' , ∣
              subst (Σ< (fst ∘ (fst (𝕒 δ η))))
               (sym ((+AssocCommR (fst ε) (ℚ.- (fst δ ℚ.+ fst η))
                (ℚ.- fst q'))))
               (x , x') ∣₁ ∣₁) )))

rel-r-r : ∀ 𝕢 → (q r : ℚ) (ε : Σ ℚ 0<_) →
     (ℚ.- fst ε) ℚ.< (q ℚ.- r) →
     (q ℚ.- r) ℚ.< fst ε → w-rel' (r-r 𝕢 q) (r-r 𝕢 r) ε
rel-r-r 𝕢 q r ε x x₁ η =
 let z : (((q ℚ.- r) ℚ.+ (𝕢 ℚ.- q)) ≡ (𝕢 ℚ.- r))
     z = lem--09 {q} {r} {𝕢}
 in (λ (u , v) →
      subst2 ℚ._<_
           (sym $ ℚ.-Distr (fst ε) (fst η))
           z
            (ℚ.<Monotone+ (ℚ.- fst ε) (q ℚ.- r)
               (ℚ.- fst η)  (𝕢 ℚ.- q) x u)

               , subst (ℚ._< fst ε ℚ.+ fst η)
                   z
                 (ℚ.<Monotone+ (q ℚ.- r) (fst ε) (𝕢 ℚ.- q) (fst η)  x₁ v))
  , (λ (u , v) →
       let zz = ℚ.<Monotone+  (ℚ.- (fst ε)) (ℚ.- (q ℚ.- r))
                       (ℚ.- fst η) (𝕢 ℚ.- r)
                           (ℚ.minus-< (q ℚ.- r) (fst ε)   x₁) u

       in subst2 ℚ._<_ (sym $ ℚ.-Distr (fst ε) (fst η) )
                   (lem--010 {q} {r} {𝕢}) zz
               ,
           let zz = ℚ.<Monotone+
                      (ℚ.- (q ℚ.- r)) (ℚ.- (ℚ.- (fst ε))) (𝕢 ℚ.- r)
                       (fst η) (minus-< (ℚ.- (fst ε)) (q ℚ.- r) x) v
           in subst2 {x = (ℚ.- (q ℚ.- r)) ℚ.+ (𝕢 ℚ.- r)} {𝕢 ℚ.- q}
                {z = (ℚ.- (ℚ.- fst ε)) ℚ.+ fst η} {fst (ε ℚ₊+ η)}
               ℚ._<_
                (lem--010 {q} {r} {𝕢}) (lem--012 {fst ε} {fst η}) zz)

rel-r-l : ∀ 𝕢 → (q : ℚ) (y : ℚ₊ → Σ (ℚ₊ → hProp ℓ-zero) w-prop')
     (ε : ℚ₊) (p : (δ ε₁ : ℚ₊) → w-rel' (y δ) (y ε₁) (δ ℚ₊+ ε₁))
     (δ : ℚ₊) (v₁ : 0< (fst ε ℚ.- fst δ)) →
     w-rel' (r-r 𝕢 q) (y δ) ((fst ε ℚ.- fst δ) , v₁) →
     w-rel' (r-r 𝕢 q) (r-l y) ε
rel-r-l 𝕢 q y ε p δ v₁ x η .fst xx' =
 let z = fst (x η) xx'
 in ∣ δ , (subst {x = fst η ℚ.+ (fst ε ℚ.- fst δ)}
               {y = (fst (ε ℚ₊+ η) ℚ.- fst δ)} 0<_
               (lem--013 {fst η} {fst ε} {fst δ})
               (+0< (fst η) (fst ε ℚ.- fst δ) (snd η) v₁) ,
        subst (fst ∘ fst (y δ)) (ℚ₊≡ (lem--014 {fst ε} {fst δ} {fst η})) z ) ∣₁

rel-r-l 𝕢 q y ε p δ v₁ x η .snd =
   PT.rec (snd (rat-rat' 𝕢 (ε ℚ₊+ η) q))
    λ (σ* , (xx , xx')) →
      let z = fst (p _ _ _) xx'
          z' = snd (x _) z
      in subst
              {x = (((fst ε ℚ.- fst δ) , v₁) ℚ₊+
                 ((σ* ℚ₊+ δ) ℚ₊+ ((fst η ℚ.- fst σ*) , xx)))}
                {(ε ℚ₊+ η)}
             (λ xxx → ⟨ rat-rat' 𝕢 xxx q ⟩)
               (ℚ₊≡ (lem--015 {fst ε} {fst δ} {fst σ*} {fst η})) z'

rel-l-l' : (x y : ℚ₊ → Σ (ℚ₊ → hProp ℓ-zero) w-prop') (ε δ η : ℚ₊)
     (p : (δ₁ ε₁ : ℚ₊) → w-rel' (x δ₁) (x ε₁) (δ₁ ℚ₊+ ε₁))
     (p' : (δ₁ ε₁ : ℚ₊) → w-rel' (y δ₁) (y ε₁) (δ₁ ℚ₊+ ε₁))
     (v₁ : 0< (fst ε ℚ.- (fst δ ℚ.+ fst η))) → ∀ η' →
     (∀ η' →
       pre-w-rel' (x δ) (y η) ((fst ε ℚ.- (fst δ ℚ.+ fst η)) , v₁) η') →
     pre-w-rel' (r-l x) (r-l y) ε η'
rel-l-l' x y ε δ η p p' v₁ η' x₁ =
   PT.map (λ (a , (xx , xx')) →
       let zz = fst (p a δ _) xx'
           zz' = x₁ _ zz
       in η ,
            subst (ℚ.0<_)
                (lem-02  (fst ε) (fst δ) (fst η) (fst η'))
                  (+0< (fst ε ℚ.- (fst δ ℚ.+ fst η))
                   (fst (δ ℚ₊+ η'))  v₁ (snd (δ ℚ₊+ η')))
             , (subst (fst ∘ y η .fst)
             (ℚ₊≡ (lem-01 (fst ε) (fst δ) (fst η) (fst η') (fst a))) zz'))



rel-l-l : (x y : ℚ₊ → Σ (ℚ₊ → hProp ℓ-zero) w-prop') (ε δ η : ℚ₊)
     (p : (δ₁ ε₁ : ℚ₊) → w-rel' (x δ₁) (x ε₁) (δ₁ ℚ₊+ ε₁))
     (p' : (δ₁ ε₁ : ℚ₊) → w-rel' (y δ₁) (y ε₁) (δ₁ ℚ₊+ ε₁))
     (v₁ : 0< (fst ε ℚ.- (fst δ ℚ.+ fst η))) →
     w-rel' (x δ) (y η) ((fst ε ℚ.- (fst δ ℚ.+ fst η)) , v₁) →
     w-rel' (r-l x) (r-l y) ε
rel-l-l x y ε δ η p p' v₁ x₁ η₁ =
  rel-l-l' x y ε δ η p p' v₁ η₁ (fst ∘ x₁)
   , let zz : Σ (0< (fst ε ℚ.- (fst η ℚ.+ fst δ)))
                  λ v →
                    (η' : ℚ₊) →
                pre-w-rel' (y η) (x δ)
             ((fst ε ℚ.- (fst η ℚ.+ fst δ)) , v) η'
         zz =
               subst
                  (λ xxx → Σ (0< (fst ε ℚ.- xxx))
                  λ v →
                    (η' : ℚ₊) →
                pre-w-rel' (y η) (x δ)
             ((fst ε ℚ.- xxx) , v) η')
                  (ℚ.+Comm (fst δ) (fst η))
                  (v₁ , snd ∘ x₁)
     in rel-l-l' y x ε η δ  p' p (fst zz) η₁ (snd zz)

w-prop : (ℚ₊ → ℝ → hProp ℓ-zero) → Type
w-prop =
 λ ♢ → (∀ u ε → ⟨ (♢ ε u)  L.⇔ (L.∃[ θ ∶ ℚ₊ ]
                     L.∃[ v ] ♢ (((fst ε) ℚ.- (fst θ)) , v) u)
                    ⟩ ) ×
                      (∀ u v ε η →
                         u ∼[ ε ] v →
                           (⟨ ♢ η u ⟩ → ⟨ ♢ (ε ℚ₊+ η) v ⟩ ))


substΣ<' : (P : Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop) → ∀ r → ∀ {x y} → x ≡ y →
             Σ< (fst ∘ (flip (fst P) r)) x → Σ< (fst ∘ flip (fst P) r) y
substΣ<' P r = subst (Σ< (fst ∘ (flip (fst P) r)))


isProp-w-prop :  ∀ ♢ → isProp (w-prop ♢)
isProp-w-prop ♢ =
  isProp× (isPropΠ2 λ u ε →
              snd (
     ♢ ε u L.⇔
     L.∃[∶]-syntax
     (λ θ → L.∃[]-syntax (λ v₁ → ♢ ((fst ε ℚ.- fst θ) , v₁) u)))
     )
    (isPropΠ6 λ _ v ε η _ _ →
        snd (♢ (ε ℚ₊+ η) v))

w-rel : Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop →
          Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop → ℚ₊ → Type
w-rel = λ (♢ , _) (♥ , _) ε →
         (∀ u η → (⟨ ♢ η u ⟩ →  ⟨ ♥ (ε ℚ₊+ η) u ⟩)
                  × (⟨ ♥ η u ⟩ →  ⟨ ♢ (ε ℚ₊+ η) u ⟩))

isSym-w-rel : ∀ a a' → (∀ ε → w-rel a a' ε) → (∀ ε → w-rel a' a ε)
isSym-w-rel a a' w ε u η = fst Σ-swap-≃ (w ε u η)

w-rel→⇒ : ∀ a a' → (∀ ε → w-rel a a' ε)
             → ∀ ε u → ⟨ fst a ε u ⟩ → ⟨ fst a' ε u ⟩
w-rel→⇒ a a' x ε u x₁ =
  w-rel'⇒ ((flip (fst a) u) , (fst (snd a) u))
    ((flip (fst a') u) , (fst (snd a') u))
     (λ ε₁ → x ε₁ u)
    ε x₁

w-rel→≡ : ∀ a a' → (∀ ε → w-rel a a' ε) → a ≡ a'
w-rel→≡ a a' w =
  Σ≡Prop isProp-w-prop
    (funExt₂ λ ε u →
       L.⇔toPath (w-rel→⇒ a a' w ε u)
         (w-rel→⇒ a' a (isSym-w-rel a a' w) ε u))

rel-l-l-l : ∀ {𝕒 : ℚ₊ → Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop}

              → (x y : ℚ₊ → ℝ) → ∀ ε δ η
              (p : ∀ δ₁ ε₁ → x δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] x ε₁)
              (p' : ∀ δ₁ ε₁ → y δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] y ε₁)
              (v₁ : 0< (fst ε ℚ.- (fst δ ℚ.+ fst η)))
              (r : x δ ∼[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , v₁ ] y η)

    →
              w-rel'
     (l-l
      (λ q η₁ → (λ ε₁ → fst (𝕒 q) ε₁ (x η₁)) , fst (snd (𝕒 q)) (x η₁)))
     (l-l
      (λ q η₁ → (λ ε₁ → fst (𝕒 q) ε₁ (y η₁)) , fst (snd (𝕒 q)) (y η₁)))
     ε
rel-l-l-l {𝕒} x y ε δ η p p' v₁ r η₁ .fst =
  PT.map
    λ ((δ* , η*) , (xx , xx')) →
     let z = snd (snd (𝕒 δ*)) (x η*) _ _ _ (p _ δ) xx'
         z' = snd (snd (𝕒 δ*)) _ _ _ _ r z
     in (δ* , η) , (+₃0<' (fst η₁ ℚ.- (fst δ* ℚ.+ fst η*))
                   (fst ε ℚ.- (fst δ ℚ.+ fst η))
                    (fst δ ℚ.+ fst η*)
                   (fst (ε ℚ₊+ η₁) ℚ.- (fst δ* ℚ.+ fst η))
                   xx v₁ (snd (δ ℚ₊+ η*))
                     (lem--016 {fst η₁} {fst δ*} {fst η*} {fst ε} {fst δ}) ,
            subst (λ xx → ⟨ 𝕒 δ* .fst xx (y η)⟩)
              (ℚ₊≡ (lem-03 (fst ε) (fst η₁)
                 (fst δ) (fst η) (fst δ*) (fst η*)))
                 z')
rel-l-l-l {𝕒}  x y ε δ η p p' v₁ r  η₁ .snd =
  PT.map λ ((δ* , η*) , (xx , xx')) →
     let z = snd (snd (𝕒 δ*)) (y η*) _ _ _ (p' _ η) xx'
         z' = snd (snd (𝕒 δ*)) _ _ _ _ (sym∼ _ _ _ r) z

     in (δ* , δ) , (
            +₃0<' (fst η₁ ℚ.- (fst δ* ℚ.+ fst η*))
                   (fst ε ℚ.- (fst δ ℚ.+ fst η))
                    (fst η ℚ.+ fst η*)
                   (fst (ε ℚ₊+ η₁) ℚ.- (fst δ* ℚ.+ fst δ))
                   xx v₁ (snd (η ℚ₊+ η*))
                    (lem--017 {fst η₁} {fst δ*} {fst η*} {fst ε} {fst δ})  ,
            (
            subst (λ xx → ⟨ 𝕒 δ* .fst xx (x δ)⟩)
              (ℚ₊≡ (lem-04 (fst ε) (fst η₁)
                 (fst δ) (fst η) (fst δ*) (fst η*)))
                 z') )
module ∼' where

 w' : ℚ → Recℝ (Σ (ℚ₊ → hProp ℓ-zero) w-prop') w-rel'
 w' 𝕢 .Recℝ.ratA 𝕢' = r-r 𝕢 𝕢'
 w' 𝕢 .Recℝ.limA 𝕒 _ = r-l 𝕒
 w' 𝕢 .Recℝ.eqA = w-rel'→≡
 w' 𝕢 .Recℝ.rat-rat-B = rel-r-r 𝕢
 w' 𝕢 .Recℝ.rat-lim-B = rel-r-l 𝕢
 w' 𝕢 .Recℝ.lim-rat-B x r ε δ p v₁ x₁ =
   w-rel'-sym (r-r 𝕢 r)  (r-l x)  ε
     (rel-r-l 𝕢 r x ε p δ v₁
      (w-rel'-sym (x δ) (r-r 𝕢 r) ((fst ε ℚ.- fst δ) , v₁) x₁))

 w' 𝕢 .Recℝ.lim-lim-B = rel-l-l
 w' 𝕢 .Recℝ.isPropB a a' ε =
  isPropΠ λ x →
     isProp× (isProp→ (snd (a' .fst (ε ℚ₊+ x))))
             (isProp→ (snd (a .fst (ε ℚ₊+ x))))





 w'' : (𝕒 : ℚ₊ → Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop)
     → ((δ ε : ℚ₊) → w-rel (𝕒 δ) (𝕒 ε) (δ ℚ₊+ ε))
     → Casesℝ (Σ (ℚ₊ → hProp ℓ-zero) w-prop') w-rel'
 w'' 𝕒 𝕡 .Casesℝ.ratA 𝕢 = r-l
    (λ q → (λ ε → fst (𝕒 q) ε (rat 𝕢)) ,
          fst (snd (𝕒 q)) (rat 𝕢))


 w'' 𝕒 𝕡 .Casesℝ.limA 𝕩 𝕔 =
   l-l (λ q  η →
       (λ ε → fst (𝕒 q) ε (𝕩 η))
       , fst (snd (𝕒 q)) (𝕩 η) )


 w'' 𝕒 𝕡 .Casesℝ.eqA = w-rel'→≡
 w'' 𝕒 𝕡 .Casesℝ.rat-rat-B q r ε x x₁ η .fst =
   PT.map
     (uncurry λ q' →
      λ (xx , xx') →
       let z = snd (snd (𝕒 q')) _ _ _ _
               (rat-rat q r ε x x₁) xx'
       in q' , (substΣ<' (𝕒 q') _
             (ℚ.+Assoc (fst ε) (fst η) (ℚ.- fst q')) (_ , z)))
 w'' 𝕒 𝕡 .Casesℝ.rat-rat-B q r ε x x₁ η .snd =
   PT.map
     (uncurry λ q' →
      λ (xx , xx') →
       let z = snd (snd (𝕒 q')) _ _ _ _
               (sym∼ _ _ ε (rat-rat q r ε x x₁)) xx'
       in q' , (substΣ<' (𝕒 q') _ (ℚ.+Assoc (fst ε) (fst η) (ℚ.- fst q')) (_ , z)))

 w'' 𝕒 𝕡 .Casesℝ.rat-lim-B q y ε δ p v₁ r v' u' x η .fst =
   PT.map
     λ ((δ* , η*) , (xx , xx')) →
      let z = snd (snd (𝕒 _)) _ _ _ _ r xx'
      in ((δ* , η*) , δ) , substΣ<' (𝕒 (δ* , η*)) _
             (lem--018 {fst ε} {fst δ} {fst η} {δ*} ) (_ , z)
 w'' 𝕒 𝕡 .Casesℝ.rat-lim-B q y ε δ p v₁ r v' u' x η .snd =
   PT.map
     λ ((δ* , η*) , (xx , xx')) →
      let z = snd (snd (𝕒 _)) _ _ _ _ (p _ _) xx'
          z' = snd (snd (𝕒 _)) _ _ _ _ (sym∼ _ _ _ r) z
      in δ* , substΣ<' (𝕒 δ*) _
             (lem--019 {fst ε} {fst δ} {fst η*}  {fst η} {fst δ*} ) (_ , z')
 w'' 𝕒 𝕡 .Casesℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ η .fst =
   PT.map λ ((δ* , η*) , (xx , xx')) →
      let z = snd (snd (𝕒 _)) _ _ _ _ (p _ _)  xx'
          z'  = snd (snd (𝕒 _)) _ _ _ _ u z
      in δ* , substΣ<' (𝕒 δ*) _
            (lem--020 {fst ε} {fst δ} {fst η*}  {fst η} {fst δ*}) (_ , z')
 w'' 𝕒 𝕡 .Casesℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ η .snd =
    PT.map
     λ ((δ* , η*) , (xx , xx')) →
      let z = snd (snd (𝕒 _)) _ _ _ _ (sym∼ _ _ _ u) xx'
      in ((δ* , η*) , δ) , substΣ<' (𝕒 (δ* , η*)) _
            ((lem--021 {fst ε} {fst δ} {fst η}  {δ*})) (_ , z)
 w'' 𝕒 𝕡 .Casesℝ.lim-lim-B = rel-l-l-l {𝕒}
 w'' 𝕒 𝕡 .Casesℝ.isPropB a a' ε =
  isPropΠ λ x →
     isProp× (isProp→ (snd (a' .fst (ε ℚ₊+ x))))
             (isProp→ (snd (a .fst (ε ℚ₊+ x))))

 isPropHlp : {P  Q  : ℝ → ℚ₊ →  Type} (P' Q' : ℝ → ℚ₊ →  hProp ℓ-zero) →
         (x₂ : ℝ) → isProp ((η₂ : ℚ₊) →
          ( P x₂ η₂  → ⟨ P' x₂ η₂ ⟩) × ( Q x₂ η₂  → ⟨ Q' x₂ η₂ ⟩))
 isPropHlp P' Q' x =
   isPropΠ λ η → isProp× (isProp→ (snd (P' x η))) (isProp→ (snd (Q' x η)))

 w : Recℝ (Σ (ℚ₊ → ℝ → hProp ℓ-zero) w-prop) w-rel
 w .Recℝ.ratA 𝕢 =
    (λ q 𝕣 → fst (Recℝ.go (w' 𝕢) 𝕣) q)
   , (λ u ε → snd (Recℝ.go (w' 𝕢) u) ε)
   , λ u v ε η x → fst (Recℝ.go~ (w' 𝕢)  x η)

 w .Recℝ.limA 𝕒 𝕡 =
     (λ q 𝕣 → fst (Casesℝ.go (w'' 𝕒 𝕡) 𝕣) q)
   , (λ u ε → snd (Casesℝ.go (w'' 𝕒 𝕡) u) ε)
   , λ u v ε η x → fst (Casesℝ.go~ (w'' 𝕒 𝕡)  x η) --

 w .Recℝ.eqA = w-rel→≡

 w .Recℝ.rat-rat-B q r ε u v = Elimℝ-Prop.go www
  where
  www : Elimℝ-Prop _
  www .Elimℝ-Prop.ratA x η =

    rat-rat'-sym x (ε ℚ₊+ η) r
      ∘S (fst (rel-r-r x q r ε u v η))
      ∘S rat-rat'-sym q η x ,
     rat-rat'-sym x (ε ℚ₊+ η) q ∘S (snd (rel-r-r  x q r ε u v η)) ∘S
      rat-rat'-sym r η x
  www .Elimℝ-Prop.limA x p x₁ η =
       PT.map (λ (δ* , (xx , xx'))
         → δ* , substΣ< (Elimℝ.go (Recℝ.d (w' r)) (x δ*))
                   (ℚ.+Assoc (fst ε) (fst η) (ℚ.- fst δ*))
                    (_ , fst (x₁ _ _) xx'))
     , PT.map (λ (δ* , (xx , xx'))
         → δ* , substΣ< (Recℝ.go (w' q) (x δ*))
             ((ℚ.+Assoc (fst ε) (fst η) (ℚ.- fst δ*)))
              (_ , snd (x₁ _ _) xx'  ))
  www .Elimℝ-Prop.isPropA = isPropHlp
      (λ x η → fst (Recℝ.go (w' r) x) (ε ℚ₊+ η))
      λ x η → fst (Recℝ.go (w' q) x) (ε ℚ₊+ η)


 w .Recℝ.rat-lim-B q y ε p δ v₁ x = Elimℝ-Prop.go www
  where
  www : Elimℝ-Prop _
  www .Elimℝ-Prop.ratA x* η .fst xx =
   let zz = fst (x (rat x*)  η) xx
   in ∣ δ ,  substΣ<' (y δ) _ (lem--022 {fst ε} {fst δ} {fst η}) (_ , zz) ∣₁

  www .Elimℝ-Prop.ratA x* η .snd =
    PT.rec (snd (fst (Recℝ.go (w' q) (rat x*)) (ε ℚ₊+ η)))
      λ (δ* , (xx , xx')) →
       let zz = snd (p δ _ (rat x*) _) xx'
           zz' = snd (x (rat x*)  _) zz
       in subst {x = (((fst ε ℚ.- fst δ) , v₁) ℚ₊+
             ((δ ℚ₊+ δ*) ℚ₊+ ((fst η ℚ.- fst δ*) , xx)))}
            {y = (ε ℚ₊+ η)} (fst ∘ fst (Recℝ.go (w' q) (rat x*)))
             (ℚ₊≡ (lem--023 {fst ε} {fst δ} {fst δ*} {fst η})) zz'

  www .Elimℝ-Prop.limA x* p* x₁* η* .fst =
    PT.map λ (δ* , (xx , xx')) →
       let z = fst (x (x* δ*) (_ , xx)) xx'

       in (δ , δ*) , substΣ<' (y δ) _
              (lem--024 {fst ε} {fst δ} {fst η*} {fst δ*}) (_ , z)
  www .Elimℝ-Prop.limA x'' pp'' x₁'' η'' .snd =
     PT.map λ ((δ* , η*) , (xx , xx')) →
      let z = fst (p _ _ _ _) xx'
          z' = snd (x (x'' η*) _) z
      in η* , substΣ< (Elimℝ.go (Recℝ.d (w' q)) (x'' η*))
                   (lem--025 {fst ε} {fst δ} {fst δ*} {fst η''}) (_ , z')

  www .Elimℝ-Prop.isPropA = isPropHlp
      (λ x η → fst (Casesℝ.go (w'' y p) x) (ε ℚ₊+ η))
      λ x η → fst (Recℝ.go (w' q) x) (ε ℚ₊+ η)

 w .Recℝ.lim-rat-B x r ε δ p v₁ x₁  = Elimℝ-Prop.go www
  where
  www : Elimℝ-Prop _
  www .Elimℝ-Prop.ratA x' η' .fst =
    PT.rec (snd (fst (Recℝ.go (w' r) (rat x')) (ε ℚ₊+ η')))
      λ (δ* , (xx , xx')) →
       let zz = snd (p δ _ (rat x') _) xx'
           zz' = fst (x₁ (rat x') _) zz
       in subst
            {x = (((fst ε ℚ.- fst δ) , v₁) ℚ₊+
             ((δ ℚ₊+ δ*) ℚ₊+ ((fst η' ℚ.- fst δ*) , xx)))}
             {(ε ℚ₊+ η')}
             (fst ∘ (fst (Recℝ.go (w' r) (rat x'))))
            (ℚ₊≡ $ lem--026 {fst ε} {fst δ} {fst δ*} {fst η'}) zz'
  www .Elimℝ-Prop.ratA x' η' .snd xx =
   let zz = snd (x₁ (rat x')  η') xx
   in ∣ δ , substΣ<' (x δ) _ (lem--027 {fst ε} {fst δ} {fst η'}) (_ , zz) ∣₁

  www .Elimℝ-Prop.limA x' p' x₁' η' .fst =
    PT.map λ ((δ* , η*) , (xx , xx')) →
      let z = fst (p _ _ _ _) xx'
          z' = fst (x₁ (x' η*) _) z
      in η* , substΣ< (Recℝ.go (w' r) (x' η*))
                ((lem--028 {fst ε} {fst δ}  {fst δ*} {fst η'}  {fst η*})) (_ , z')
  www .Elimℝ-Prop.limA x' p' x₁' η' .snd =
    PT.map λ (δ* , (xx , xx')) →
      let z = snd (x₁ (x' δ*) ((fst η' ℚ.- fst δ*) , xx)) xx'

      in (δ , δ*) , substΣ<' (x δ) _
          (lem--029 {fst ε} {fst δ} {fst η'} {fst δ*}) (_ , z)
  www .Elimℝ-Prop.isPropA = isPropHlp
      (λ x η → fst (Recℝ.go (w' r) x) (ε ℚ₊+ η))
      λ x₂ η → fst (Casesℝ.go (w'' x p) x₂) (ε ℚ₊+ η)

 w .Recℝ.lim-lim-B x y ε δ η p p' v₁ x₁ = Elimℝ-Prop.go www
  where
  www : Elimℝ-Prop _
  www .Elimℝ-Prop.ratA x* η' .fst =
    PT.map λ ((δ* , η*) , (xx , xx')) →
     let z = fst ((p _ _) _ _) xx'
         z' = fst (x₁ _ _) z
     in η , substΣ<' (y η) _
           (lem--030 {fst ε} {fst δ} {fst η} {δ*}  {fst η'}) (_ , z')
  www .Elimℝ-Prop.ratA x* η' .snd =
    PT.map λ ((δ* , η*) , (xx , xx')) →
     let z = fst ((p' _ _) _ _) xx'
         z' = snd (x₁ _ _) z
     in δ , substΣ<' (x δ) _
         (lem--031 {fst ε} {fst δ} {fst η} {δ*}  {fst η'} ) (_ , z')
  www .Elimℝ-Prop.limA x* p* x₁' η₁ .fst =
   PT.map λ ((δ* , η*) , (xx , xx')) →
   let z = (fst (p δ* δ (x* η*) _)) xx'
       z' : fst
              (y η .fst
               (((fst ε ℚ.- (fst δ ℚ.+ fst η)) , v₁) ℚ₊+
                ((δ* ℚ₊+ δ) ℚ₊+ ((fst η₁ ℚ.- (fst δ* ℚ.+ fst η*)) , xx)))
               (x* η*))
       z' = fst (x₁ _ _) z
   in (η , η*) ,
          substΣ<' (y η) _
        (lem--032 {fst ε} {fst δ} {fst η} {fst δ*}  {fst η₁} {fst η*})
           (_ , z')
  www .Elimℝ-Prop.limA x* p x₁' η₁ .snd =
   PT.map λ ((δ* , η*) , (xx , xx')) →
    let z = (fst (p' _ _ _ _)) xx'
        z' = snd (x₁ _ _) z
    in (δ , η*) , substΣ<' (x δ) _
          (lem--033  {fst ε} {fst δ} {fst η} {fst δ*}  {fst η₁} {fst η*}) (_ , z')

  www .Elimℝ-Prop.isPropA = isPropHlp
      (λ x₂ η₂ → fst (Casesℝ.go (w'' y p') x₂) (ε ℚ₊+ η₂))
      λ x₂ η₂ → fst (Casesℝ.go (w'' x p) x₂) (ε ℚ₊+ η₂)

 w .Recℝ.isPropB a a' ε = isPropΠ2 λ u x →
     isProp× (isProp→ (snd (a' .fst (ε ℚ₊+ x) u)))
             (isProp→ (snd (a .fst (ε ℚ₊+ x) u)))


 -- pre-~' : ℝ → Σ (ℚ₊ → ℝ → (hProp ℓ-zero)) _
 -- pre-~' = Recℝ.go w


-- HoTT Theorem (11.3.16)

_∼'[_]_ : ℝ → ℚ₊ → ℝ → Type
x ∼'[ ε ] y = ⟨ fst (Recℝ.go ∼'.w x) ε y ⟩

_∼'[_]ₚ_ : ℝ → ℚ₊ → ℝ → hProp ℓ-zero
x ∼'[ ε ]ₚ y = fst (Recℝ.go ∼'.w x) ε y


-- (11.3.17)
_ : ∀ r r' ε → (rat r) ∼'[ ε ] (rat r') ≡
              ((ℚ.- fst ε) ℚ.< (r ℚ.- r'))
               × ((r ℚ.- r') ℚ.< fst ε)
_ = λ r r' ε → refl

-- (11.3.18)
_ : ∀ r x y ε → (rat r) ∼'[ ε ] (lim x y) ≡
              (∃[ δ ∈ ℚ₊ ] Σ[ v ∈ _ ] ((rat r) ∼'[ (fst ε ℚ.- fst δ) , v ] x δ))
_ = λ r x y ε → refl

-- (11.3.19)
_ : ∀ r x y ε → (lim x y) ∼'[ ε ] (rat r) ≡
              (∃[ δ ∈ ℚ₊ ] Σ[ v ∈ _ ]
                ((x δ) ∼'[ (fst ε ℚ.- fst δ) , v ] rat r ))
_ = λ r x y ε → refl

-- (11.3.20)
_ : ∀ x y x' y' ε → (lim x y) ∼'[ ε ] (lim x' y') ≡
               (∃[ (δ , η) ∈ (ℚ₊ × ℚ₊) ] Σ[ v ∈ _ ]
                ((x δ) ∼'[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , v ] (x' η) ))
_ = λ x y x' y' ε → refl

-- (11.3.23)
triangle∼' : ∀ u v w ε η
      → u ∼[ ε ] v
      → v ∼'[ η ] w
      → u ∼'[ ε ℚ₊+ η ] w
triangle∼' u v w ε η x =
  snd ((Recℝ.go~ ∼'.w {x = u} {v} {ε} x w η ))


-- (11.3.21)
rounded∼' : ∀ u v ε →
             ⟨ (u ∼'[ ε ]ₚ v) L.⇔
              (L.∃[ δ ]
                L.∃[ _ ] u ∼'[ (fst ε ℚ.- fst δ) , _ ]ₚ v) ⟩
rounded∼' u v ε = fst (snd (Recℝ.go ∼'.w u)) v ε


∼→∼' : ∀ x y ε → x ∼[ ε ] y → x ∼'[ ε ] y
∼→∼' x y ε (rat-rat q r .ε x₁ x₂) = x₁ , x₂
∼→∼' x y ε (rat-lim q y₁ .ε δ p v₁ x₁) =
 ∣ δ , v₁ , ∼→∼' (rat q) (y₁ δ) _ x₁ ∣₁
∼→∼' x y ε (lim-rat x₁ r .ε δ p v₁ x₂) =
 ∣ δ , v₁ , ∼→∼' (x₁ δ) (rat r)  _ x₂ ∣₁
∼→∼' x y ε (lim-lim x₁ y₁ .ε δ η p p' v₁ x₂) =
  ∣ (δ , η) , (v₁ , (∼→∼' _ _ _ x₂)) ∣₁
∼→∼' x y ε (isProp∼ .x .ε .y x₁ x₂ i) =
  snd (x ∼'[ ε ]ₚ y) (∼→∼' x y ε x₁) (∼→∼' x y ε x₂) i

∼'→∼ : ∀ x y ε → x ∼'[ ε ] y → x ∼[ ε ] y
∼'→∼ = Elimℝ-Prop2.go w
 where
 w : Elimℝ-Prop2 _
 w .Elimℝ-Prop2.rat-ratA r q ε =
   uncurry $ rat-rat r q ε
 w .Elimℝ-Prop2.rat-limA r x y x₁ ε =
    PT.rec (isProp∼ _ _ _)
      λ (δ , (xx , xx')) → rat-lim r x ε δ y  xx (x₁ _ _ xx')

 w .Elimℝ-Prop2.lim-ratA x y r x₁ ε =
    PT.rec (isProp∼ _ _ _)
      λ (δ , (xx , xx')) → lim-rat x r ε δ y  xx (x₁ _ _ xx')
 w .Elimℝ-Prop2.lim-limA x y x' y' x₁ ε =
    PT.rec (isProp∼ _ _ _)
      λ ((δ , η) , (xx , xx')) →
        lim-lim x x' ε δ η y y' xx (x₁ _ _ _ xx')
 w .Elimℝ-Prop2.isPropA _ _ = isPropΠ2 λ _ _ → isProp∼ _ _ _


sym∼' : ∀ r r' ε → r ∼'[ ε ] r' → r' ∼'[ ε ] r
sym∼' r r' ε =
  ∼→∼' r' r ε ∘S sym∼ r r' ε ∘S ∼'→∼ r r' ε



-- (11.3.22)
triangle∼'' : ∀ u v w ε η
      → u ∼'[ ε ] v
      → v ∼[ η ] w
      → u ∼'[ ε ℚ₊+ η ] w
triangle∼'' u v w ε η x y =
  subst (u ∼'[_] w) (ℚ₊≡ (ℚ.+Comm (fst η) (fst ε)))
   (sym∼' w u _ (triangle∼' w v u η ε (sym∼ v w η y) (sym∼' u v ε x)))

-- HoTT Theorem (11.3.32)
∼'⇔∼ : ∀ x y ε → ⟨ x ∼'[ ε ]ₚ y L.⇔ x ∼[ ε ]ₚ y ⟩
∼'⇔∼ x y z = ∼'→∼ x y z , ∼→∼' x y z


infixr 6 _∙⇔_

_∙⇔_ : ∀ {ℓ} {A B C : Type ℓ}
         → ((A → B) × (B → A))
         → ((B → C) × (C → B))
         → ((A → C) × (C → A))
_∙⇔_ (x , _) (y , _) .fst = y ∘ x
_∙⇔_ (_ , x) (_ , y) .snd = x ∘ y

sym⇔ : ∀ {ℓ} {A B : Type ℓ}
    → ((A → B) × (B → A))
    → ((B → A) × (A → B))
sym⇔ (x , y) = y , x


-- HoTT (11.3.33)
rounded∼ : ∀ u v ε →
             ⟨ (u ∼[ ε ]ₚ v) L.⇔
              (L.∃[ δ ]
                L.∃[ p ] u ∼[ (fst ε ℚ.- fst δ) , p ]ₚ v) ⟩
rounded∼ u v ε = sym⇔
      (∼'⇔∼ u v ε) ∙⇔ rounded∼' u v ε ∙⇔
     (PT.map (map-snd (PT.map (map-snd (fst (∼'⇔∼ u v _)))))
   ,  PT.map (map-snd (PT.map (map-snd (snd (∼'⇔∼ u v _))))))

-- HoTT (11.3.36)

triangle∼ : ∀ {u v w ε η}
      → u ∼[ ε ] v
      → v ∼[ η ] w
      → u ∼[ ε ℚ₊+ η ] w
triangle∼ {u} {v} {w} {ε} {η} x  =
  ∼'→∼ u w (ε ℚ₊+ η) ∘ triangle∼' u v w ε η x ∘ ∼→∼' v w _



_ : ∀ r x y ε → (rat r) ∼'[ ε ] (lim x y) ≡
              (∃[ δ ∈ ℚ₊ ] Σ[ v ∈ _ ] ((rat r) ∼'[ (fst ε ℚ.- fst δ) , v ] x δ))
_ = λ r x y ε → refl

_ : ∀ r x y ε → (lim x y) ∼'[ ε ] (rat r) ≡
              (∃[ δ ∈ ℚ₊ ] Σ[ v ∈ _ ]
                ((x δ) ∼'[ (fst ε ℚ.- fst δ) , v ] rat r ))
_ = λ r x y ε → refl


_ : ∀ x y x' y' ε → (lim x y) ∼'[ ε ] (lim x' y') ≡
               (∃[ (δ , η) ∈ (ℚ₊ × ℚ₊) ] Σ[ v ∈ _ ]
                ((x δ) ∼'[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , v ] (x' η) ))
_ = λ x y x' y' ε → refl

