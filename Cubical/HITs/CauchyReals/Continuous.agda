{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Continuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order



open ℚ.HLP

 -- HoTT Lemma (11.3.41)


-- -- 11.3.42



⊤Pred : ℝ → hProp ℓ-zero
⊤Pred = (λ _ → Unit , isPropUnit )



∼→≤ : ∀ u q → u ≤ᵣ (rat q) → ∀ v ε → u ∼'[ ε ] v → v ≤ᵣ rat (q ℚ.+ fst ε)
∼→≤ u q u≤q v ε u∼v = xxx

 where

 opaque
  unfolding _≤ᵣ_
  ∼→≤-rat-u : ∀ u q → rat u ≤ᵣ (rat q) → ∀  v ε
              → rat u ∼'[ ε ] v → v ≤ᵣ rat (q ℚ.+ fst ε)
  ∼→≤-rat-u r q u≤q = Elimℝ-Prop.go w
   where
   w : Elimℝ-Prop λ v → ∀ ε
              → rat r ∼'[ ε ] v → v ≤ᵣ rat (q ℚ.+ fst ε)
   w .Elimℝ-Prop.ratA x ε (u , v) = ≤ℚ→≤ᵣ _ _
     (subst (ℚ._≤ q ℚ.+ fst ε) lem--05 $ ℚ.≤Monotone+ r q (x ℚ.- r) (fst ε)
       (≤ᵣ→≤ℚ r q u≤q)
       (ℚ.<Weaken≤ _ _ (ℚ.minus-<'  (fst ε) (x ℚ.- r)
       $ subst ((ℚ.- fst ε) ℚ.<_) (sym (ℚ.-[x-y]≡y-x x r)) u)))
   w .Elimℝ-Prop.limA x y x₁ ε =
        PT.rec (isProp≤ᵣ _ _)
      (uncurry λ θ →
        PT.rec (isProp≤ᵣ _ _)
         (uncurry λ θ<ε →
           PT.rec (isProp≤ᵣ _ _)
             λ (η , xx , xx') →
               let xx'* : rat r
                        ∼'[ (((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx) ] x η
                   xx'* = xx'

                   yy : (δ : ℚ₊) → fst δ ℚ.< fst θ →
                           rat r ∼[ ε ] x δ
                   yy δ δ<θ =
                     let z = triangle∼ {rat r}
                               {x η} {x δ}
                                 {(((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx)}
                                    { θ ℚ₊+  η  }
                              (∼'→∼ _ _
                               ((((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx))
                                xx')
                                 let uu = (y η δ)
                                  in ∼-monotone<
                                        (subst (ℚ._< fst (θ ℚ₊+ η))
                                           (ℚ.+Comm (fst δ) (fst η))
                                           (ℚ.<-+o
                                             (fst δ)
                                             (fst θ) (fst η)
                                             δ<θ)) uu
                     in subst∼ lem--054 z

               in sym (eqℝ _ _ λ ε' →
                     let ε* = ℚ.min₊ (ℚ./2₊ ε') (ℚ./2₊ θ)
                         ε*<ε' = snd
                           (ℚ.<→ℚ₊  (fst ε*) (fst ε')
                              (
                              ℚ.isTrans≤< (fst ε*) (fst (ℚ./2₊ ε')) (fst ε')
                               (ℚ.min≤ (fst (ℚ./2₊ ε')) (fst (ℚ./2₊ θ)))
                                (ℚ.x/2<x ε') ))

                         ε*<θ = ℚ.isTrans≤< (fst ε*) (fst (ℚ./2₊ θ)) (fst θ)
                               (ℚ.min≤' (fst (ℚ./2₊ ε')) (fst (ℚ./2₊ θ)))
                                (ℚ.x/2<x θ)

                         zzz = x₁ ε* ε  (∼→∼' _ _ _ (yy ε* ε*<θ))
                     in rat-lim (q ℚ.+ fst ε) _ _ ε* _ ε*<ε'
                            (subst (rat (q ℚ.+ fst ε)
                              ∼[ (fst ε' ℚ.- fst ε*) , ε*<ε' ]_)
                               (sym zzz) (refl∼ (rat (q ℚ.+ fst ε))
                              ((fst ε' ℚ.- fst ε*) , ε*<ε'))) )))
     ∘ fst (rounded∼' (rat r) (lim x y) ε)

   w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isProp≤ᵣ _ _

  maxLip : ((rat q)) ∼[ ε ] maxᵣ v ((rat q))
  maxLip =
         subst (_∼[ ε ] maxᵣ v ((rat q)))
           u≤q $ NonExpanding₂.go∼L maxR ((rat q)) u v ε (∼'→∼ _ _ _ u∼v)

  -- zzz =
  xxx : v ≤ᵣ rat (q ℚ.+ fst ε)
  xxx = cong (maxᵣ v ∘ rat) (sym (ℚ.≤→max q (q ℚ.+ fst ε)
          (ℚ.≤+ℚ₊ q q ε (ℚ.isRefl≤ q )))) ∙∙
            (maxᵣAssoc v (rat q) (rat (q ℚ.+ fst ε)))  ∙∙
              ∼→≤-rat-u q q (≤ᵣ-refl (rat q)) (maxᵣ v ((rat q))) ε (∼→∼' _ _ _ maxLip)

-- 11.3.43-i

∼→< : ∀ u q → u <ᵣ (rat q) → ∀ v ε → u ∼'[ ε ] v → v <ᵣ rat (q ℚ.+ fst ε)
∼→< u q u<q v ε x = invEq (<ᵣ-impl _ _)
   (PT.map (λ ((q' , r') , z , z' , z'') →
            ((q' ℚ.+ fst ε) , (r' ℚ.+ fst ε)) ,
               (∼→≤ u q' z v ε x  , ((ℚ.<-+o q' r' (fst ε) z') ,
                 ≤ℚ→≤ᵣ (r' ℚ.+ fst ε) (q ℚ.+ fst ε)
                   (ℚ.≤-+o r' q (fst ε) (≤ᵣ→≤ℚ r' q z'')))))
            (fst (<ᵣ-impl _ _) u<q))

  -- PT.map (λ ((q' , r') , z , z' , z'') →
  --           ((q' ℚ.+ fst ε) , (r' ℚ.+ fst ε)) ,
  --              (∼→≤ u q' z v ε x  , ((ℚ.<-+o q' r' (fst ε) z') ,
  --                ≤ℚ→≤ᵣ (r' ℚ.+ fst ε) (q ℚ.+ fst ε)
  --                  (ℚ.≤-+o r' q (fst ε) (≤ᵣ→≤ℚ r' q z'')))))
  --           u<q




x+[y-x]/2≡y-[y-x]/2 : ∀ x y →
  x ℚ.+ (y ℚ.- x) ℚ.· [ 1 / 2 ]
   ≡ y ℚ.- ((y ℚ.- x) ℚ.· [ 1 / 2 ])
x+[y-x]/2≡y-[y-x]/2 u v =
  ((cong (u ℚ.+_) (ℚ.·DistR+ _ _ _ ∙ ℚ.+Comm _ _)
        ∙ ℚ.+Assoc _ _ _) ∙∙
          cong₂ ℚ._+_
            distℚ! u ·[
             (ge1 +ge ((neg-ge ge1) ·ge
                      ge[ [ pos 1 / 1+ 1 ] ]))
                   ≡ (neg-ge ((neg-ge ge1) ·ge
                      ge[ [ pos 1 / 1+ 1 ] ]))   ]
           distℚ! v ·[ (( ge[ [ pos 1 / 1+ 1 ] ]))
                   ≡ (ge1 +ge neg-ge (
                      ge[ [ pos 1 / 1+ 1 ] ]))   ]
          ∙∙ (ℚ.+Comm _ _ ∙ sym (ℚ.+Assoc v
                 (ℚ.- (v ℚ.· [ 1 / 2 ]))
                  (ℚ.- ((ℚ.- u) ℚ.· [ 1 / 2 ])))
            ∙ cong (ℚ._+_ v)
                (sym (ℚ.·DistL+ -1 _ _)) ∙ cong (ℚ._-_ v)
           (sym (ℚ.·DistR+ v (ℚ.- u) [ 1 / 2 ])) ))


-- -- 11.3.43-ii

∼→<' : ∀ u q → u <ᵣ (rat q) → ∀ v
   → ∃[ ε ∈ ℚ₊ ] (u ∼'[ ε ] v → v <ᵣ rat q)
∼→<' u q u<q v =
  PT.map
      (λ ((u' , q') , z , z' , z'') →
            ℚ./2₊ (ℚ.<→ℚ₊ u' q' z')  ,
              (λ xx →
                let zwz = ∼→≤  u u'  z v _ xx
                in invEq (<ᵣ-impl _ _) ∣ (_ , q') , (zwz ,
                  (subst2
                      {x = q' ℚ.- (fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z')))}
                      {u' ℚ.+ fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))}
                      ℚ._<_
                     (sym (x+[y-x]/2≡y-[y-x]/2 u' q'))
                     (ℚ.+IdR q')
                     (ℚ.<-o+ (ℚ.- fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))) 0 q'
                          (ℚ.-ℚ₊<0 (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))))
                     , z'')) ∣₁ ))
      (fst (<ᵣ-impl _ _) u<q)


-- 11.3.44

lem-11-3-44 : ∀ u ε → u ∼'[ ε ] 0 → absᵣ u <ᵣ rat (fst ε)
lem-11-3-44 = Elimℝ-Prop.go w
 where
 opaque
  unfolding _<ᵣ_ absᵣ
  w : Elimℝ-Prop (λ z → (ε : ℚ₊) → z ∼'[ ε ] 0 → absᵣ z <ᵣ rat (fst ε))
  w .Elimℝ-Prop.ratA x ε (x₁ , x₂) =
     <ℚ→<ᵣ (ℚ.abs' x) (fst ε)
       (subst (ℚ._< fst ε) (ℚ.abs'≡abs x)
         (ℚ.absFrom<×< (fst ε) x
           (subst ((ℚ.- fst ε) ℚ.<_) (ℚ.+IdR x) x₁)
            (subst (ℚ._< (fst ε)) ((ℚ.+IdR x)) x₂)))
  w .Elimℝ-Prop.limA x p x₁ ε =
    (PT.rec squash₁
      $ uncurry λ θ → PT.rec squash₁ λ (xx , xx') →
        let zqz = ((subst∼ {ε' = (θ ℚ₊· ([ pos 1 / 1+ 2 ] , _))}
                               (ℚ.ε/6+ε/6≡ε/3 (fst θ))
                             (𝕣-lim-self
                               x p (θ ℚ₊· ([ pos 1 / 6 ] , _))
                                  (θ ℚ₊· ([ pos 1 / 6 ] , _)))))
            by▵ : Σ (ℚ.0< (fst ε ℚ.- (fst θ ℚ.· ℚ.[ 2 / 3 ] )))
                    (λ z → x (θ ℚ₊· (ℚ.[ pos 1 / 6 ] , _))
                     ∼'[ (fst ε ℚ.- (fst θ ℚ.· ℚ.[ 2 / 3 ] )) , z ]
                       0)
            by▵ =
              let zz = triangle∼' (x ( θ  ℚ₊·(ℚ.[ 1 / 6 ] , _)))
                          (lim x p) 0 (( θ  ℚ₊·(ℚ.[ 1 / 3 ] , _)))
                           ((fst ε ℚ.- fst θ) , xx)
                          zqz xx'
                  zz' : ((fst θ) ℚ.· [ 1 / 3 ])
                          ℚ.+ (fst ε ℚ.- fst θ) ≡
                          (fst ε ℚ.- (fst θ ℚ.· [ 2 / 3 ]))
                  zz' = (λ i → ((fst θ) ℚ.· [ 1 / 3 ])
                          ℚ.+ (fst ε ℚ.-
                            distℚ! (fst θ) ·[
                              (ge1) ≡ (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                                +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                                +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ] ) ] i ))
                      ∙∙ lem--055 ∙∙
                        λ i → fst ε ℚ.-
                            distℚ! (fst θ) ·[
                              (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                                +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ])
                                ≡ (ge[ ℚ.[ pos 2 / 1+ 2 ] ] ) ] i
              in sΣℚ<' zz' zz
            xxx : absᵣ (x (θ ℚ₊· ([ pos 1 / 6 ] , tt))) <ᵣ
                   rat (fst ε ℚ.- (fst θ  ℚ.· [ pos 2 / 1+ 2 ]))
            xxx = x₁ _ _  (snd (by▵))

            ggg' : absᵣ (lim x p) <ᵣ _
            ggg' = ∼→< _ _ xxx (absᵣ (lim x p))
                    ((θ  ℚ₊· ([ pos 1 / 1+ 2 ] , _))) $
                      ∼→∼' _ _ _ $
                              absᵣ-nonExpanding _ _ _ zqz

            ggg : absᵣ (lim x p) <ᵣ rat (fst ε)
            ggg = isTrans<ᵣ (absᵣ (lim x p))
                    _ (rat (fst ε)) ggg'
                      (<ℚ→<ᵣ _ _ (subst2 ℚ._<_
                           (lem--056 ∙
                             (λ i → (fst ε ℚ.-
                              ((distℚ! (fst θ) ·[
                              (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                                +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ])
                                ≡ (ge[ ℚ.[ pos 2 / 1+ 2 ] ] ) ]) i))
                                 ℚ.+
                                (fst (θ ℚ₊· ([ pos 1 / 1+ 2 ] , tt)))))
                                (ℚ.+IdR (fst ε))
                            (ℚ.<-o+ (ℚ.- (fst θ ℚ.· [ pos 1 / 1+ 2 ])) 0 (fst ε)
                           (ℚ.-ℚ₊<0 (θ ℚ₊· ([ pos 1 / 1+ 2 ] , tt))))))


        in ggg) ∘S fst (rounded∼' (lim x p) 0 ε)
  w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → squash₁


∼≃abs<ε⇐ : ∀ u v  ε →
  (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε)) → (u ∼[ ε ] v)

∼≃abs<ε⇐ u v ε = Elimℝ-Prop2Sym.go w u v ε
 where

 opaque
  unfolding _<ᵣ_ absᵣ

  w : Elimℝ-Prop2Sym λ u v → ∀ ε →
          (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε))
            → u ∼[ ε ] v
  w .Elimℝ-Prop2Sym.rat-ratA r q ε z =
    rat-rat-fromAbs r q ε
     (subst (ℚ._< fst ε) (sym (ℚ.abs'≡abs _)) (<ᵣ→<ℚ _ _ z))
  w .Elimℝ-Prop2Sym.rat-limA q x y R ε =
    PT.rec (isProp∼ _ _ _) ( λ (θ , (xx , xx')) →
          let 0<θ = ℚ.<→0< _ (<ᵣ→<ℚ 0 θ
                       (isTrans≤<ᵣ 0 _ (rat θ)
                         (0≤absᵣ _) xx))
              ww : ∀ δ η → absᵣ (rat q +ᵣ (-ᵣ lim x y))
                          ∼[ δ ℚ₊+ η ] absᵣ (rat q +ᵣ (-ᵣ (x δ)))
              ww δ η =
                let uu : ⟨ NonExpandingₚ (absᵣ ∘S (rat q +ᵣ_) ∘S -ᵣ_) ⟩
                    uu = NonExpandingₚ∘ absᵣ ((rat q +ᵣ_) ∘S -ᵣ_)
                              absᵣ-nonExpanding
                               (NonExpandingₚ∘ (rat q +ᵣ_) -ᵣ_
                                      (NonExpanding₂.go∼R sumR (rat q))
                                       (Lipschitz-ℝ→ℝ-1→NonExpanding
                                         _ (snd -ᵣR)))
                in uu (lim x y) (x δ) (δ ℚ₊+ η) (
                           sym∼ _ _ _ (𝕣-lim-self x y δ η))
              δ = ℚ./4₊ (ℚ.<→ℚ₊ θ (fst ε) (<ᵣ→<ℚ _ _ xx'))
              www = ∼→< (absᵣ (rat q +ᵣ (-ᵣ lim x y)))
                      θ
                      xx ((absᵣ (rat q +ᵣ (-ᵣ (x δ)))))
                         (δ ℚ₊+ δ)
                      (∼→∼' _ _ (δ ℚ₊+ δ) (ww δ δ))

              wwwR = R δ ((θ , 0<θ) ℚ₊+ (δ ℚ₊+ δ)) www
              zz : fst (δ ℚ₊+ δ) ℚ.+ (fst δ ℚ.+ fst δ) ≡
                     fst ε ℚ.- θ
              zz = distℚ! (fst ε ℚ.- θ)
                     ·[ (ge[ [ 1 / 4 ] ] +ge ge[ [ 1 / 4 ] ]) +ge
                        (ge[ [ 1 / 4 ] ] +ge ge[ [ 1 / 4 ] ]) ≡ ge1 ]
          in subst∼ ( sym (ℚ.+Assoc _ _ _) ∙∙
                    cong (θ ℚ.+_) zz ∙∙ lem--05 {θ} {fst ε} )
               (triangle∼ wwwR (𝕣-lim-self x y δ δ))) ∘S
          (denseℚinℝ (absᵣ (rat q +ᵣ (-ᵣ lim x y))) (rat (fst ε)))
  w .Elimℝ-Prop2Sym.lim-limA x y x' y' R ε =
      PT.rec (isProp∼ _ _ _) ( λ (θ , (xx , xx')) →
        let 0<θ = ℚ.<→0< _ (<ᵣ→<ℚ 0 θ
                       (isTrans≤<ᵣ 0 _ (rat θ)
                         (0≤absᵣ _) xx))
            ww : ∀ δ η → absᵣ (lim x y +ᵣ (-ᵣ lim x' y'))
                        ∼[ (δ ℚ₊+ η) ℚ₊+ (δ ℚ₊+ η) ]
                         absᵣ ((x δ) +ᵣ (-ᵣ (x' δ)))
            ww δ η =
              let uu = absᵣ-nonExpanding
                    ((lim x y +ᵣ (-ᵣ lim x' y')))
                    (x δ +ᵣ (-ᵣ x' δ))
                        _
                         (NonExpanding₂.go∼₂ sumR
                          _ _
                          (sym∼ _ _ _ (𝕣-lim-self x y δ η))
                          (Lipschitz-ℝ→ℝ-1→NonExpanding
                                         _ (snd -ᵣR) _ _ _
                                          (sym∼ _ _ _ (𝕣-lim-self x' y' δ η))))
              in uu
            δ = (ℚ.<→ℚ₊ θ (fst ε) (<ᵣ→<ℚ _ _ xx')) ℚ₊· ([ 1 / 6 ] , _)
            www = ∼→< (absᵣ (lim x y +ᵣ (-ᵣ lim x' y')))
                      θ
                      xx ((absᵣ (x δ +ᵣ (-ᵣ (x' δ)))))
                         ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ))
                      (∼→∼' _ _ ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ)) (ww δ δ))
            wwwR = R δ δ
                       ((θ , 0<θ) ℚ₊+ ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ)))
                         www

            zz = cong (λ x → (x ℚ.+ x) ℚ.+ x)
                  (ℚ.ε/6+ε/6≡ε/3 (fst ε ℚ.- θ))
                   ∙ sym (ℚ.+Assoc _ _ _) ∙ ℚ.ε/3+ε/3+ε/3≡ε (fst ε ℚ.- θ)
         in uncurry (lim-lim _ _ _ δ δ _ _)
              (sΣℚ< (ℚ.+CancelL- _ _ _
                        (sym (ℚ.+Assoc _ _ _) ∙∙
                    cong (θ ℚ.+_) zz ∙∙ lem--05 {θ} {fst ε} )) wwwR)
       ) ∘S (denseℚinℝ (absᵣ ((lim x y) +ᵣ (-ᵣ lim x' y'))) (rat (fst ε)))
  w .Elimℝ-Prop2Sym.isSymA x y u ε =
    sym∼ _ _ _ ∘S u ε ∘S subst (_<ᵣ rat (fst ε))
     (minusComm-absᵣ y x)
  w .Elimℝ-Prop2Sym.isPropA _ _ = isPropΠ2 λ _ _ → isProp∼ _ _ _



∼≃abs<ε : ∀ u v  ε →
  (u ∼[ ε ] v) ≃
    (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε))
∼≃abs<ε u v ε =
  propBiimpl→Equiv (isProp∼ _ _ _) (isProp<ᵣ _ _)

   ((λ x →
    lem-11-3-44 ((u +ᵣ (-ᵣ v))) ε
      (∼→∼' _ _ _ $  (subst ((u +ᵣ (-ᵣ v)) ∼[ ε ]_) (+-ᵣ v)
       (+ᵣ-∼ u v (-ᵣ v) ε x)))))
   (∼≃abs<ε⇐ u v ε)

getClampsOnQ : (a : ℚ) →
      Σ ℕ₊₁ (λ n → absᵣ (rat a) <ᵣ rat [ pos (ℕ₊₁→ℕ n) / 1+ 0 ])
getClampsOnQ = (map-snd (λ {a} → subst (_<ᵣ rat [ pos (ℕ₊₁→ℕ a) / 1+ 0 ])
      (cong rat (ℚ.abs'≡abs _ ) ∙ sym (absᵣ-rat' _))
      ∘S (<ℚ→<ᵣ _ _))) ∘ ℚ.boundℕ

getClamps : ∀ u →
   ∃[ n ∈ ℕ₊₁ ] absᵣ u <ᵣ fromNat (ℕ₊₁→ℕ n)
getClamps = Elimℝ-Prop.go w
 where
  w : Elimℝ-Prop _
  w .Elimℝ-Prop.ratA =
    ∣_∣₁ ∘ getClampsOnQ
  w .Elimℝ-Prop.limA x p x₁ =
   PT.map (λ (1+ n , v) →
   let z' = (subst∼ {ε' = ℚ./2₊ 1} ℚ.decℚ? $ 𝕣-lim-self x p (ℚ./4₊ 1) (ℚ./4₊ 1))
       z = ∼→< (absᵣ (x (ℚ./4₊ 1))) _ v (absᵣ (lim x p)) 1
              (∼→∼' _ _ _
               (∼-monotone< (ℚ.x/2<x 1) (absᵣ-nonExpanding _ _ _ z')) )

       uu = ℤ.·IdR _ ∙ (sym $ ℤ.+Comm 1 (pos 1 ℤ.+ pos n ℤ.· pos 1))

   in (suc₊₁ (1+ n)) , subst ((absᵣ (lim x p) <ᵣ_) ∘ rat) (eq/ _ _ uu) z) $ x₁ (ℚ./4₊ 1)
  w .Elimℝ-Prop.isPropA _ = squash₁



eqℝ≃< : ∀ x y → (x ≡ y) ≃ (∀ ε → absᵣ (x -ᵣ y) <ᵣ rat (fst ε))
eqℝ≃< x y = invEquiv (∼≃≡ _ _ ) ∙ₑ equivΠCod λ ε → ∼≃abs<ε _ _ _

lim≡≃∼ : ∀ x y a → (lim x y ≡ a)
                    ≃ (∀ ε → absᵣ (lim x y -ᵣ a) <ᵣ rat (fst ε) )
lim≡≃∼ _ _ _ = eqℝ≃< _ _


restrSq : ∀ n → Lipschitz-ℚ→ℚ-restr (fromNat (suc n))
                  ((2 ℚ₊· fromNat (suc n)))
                  λ x → x ℚ.· x

restrSq n q r x x₁ ε x₂ =

  subst (ℚ._< 2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε)
    (ℚ.abs·abs (q ℚ.+ r) (q ℚ.- r) ∙ cong ℚ.abs (lem--040 {q} {r})) z

 where
  zz : ℚ.abs (q ℚ.+ r) ℚ.< 2 ℚ.· fst (fromNat (suc n))
  zz = subst (ℚ.abs (q ℚ.+ r) ℚ.<_)
           (sym (ℚ.·DistR+ 1 1 (fst (fromNat (suc n)))))
          (ℚ.isTrans≤< (ℚ.abs (q ℚ.+ r)) (ℚ.abs q ℚ.+ ℚ.abs r)
            _ (ℚ.abs+≤abs+abs q r)
              (ℚ.<Monotone+ (ℚ.abs q) _ (ℚ.abs r) _ x x₁ ))

  z : ℚ.abs (q ℚ.+ r) ℚ.· ℚ.abs (q ℚ.- r) ℚ.<
        2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε
  z = ℚ.<Monotone·-onPos _ _ _ _
      zz x₂ (ℚ.0≤abs (q ℚ.+ r)) ((ℚ.0≤abs (q ℚ.- r)))


0<ℕ₊₁ : ∀ n m → 0 ℚ.< ([ ℚ.ℕ₊₁→ℤ n / m ])
0<ℕ₊₁ n m = ℚ.0<→< ([ ℚ.ℕ₊₁→ℤ n / m ]) tt

1/n<sucK : ∀ m n → ℚ.[ 1 / (suc₊₁ m) ] ℚ.< ([ ℚ.ℕ₊₁→ℤ n / 1 ])
1/n<sucK m n =
 subst (1 ℤ.<_) (ℤ.pos·pos _ _) (ℤ.suc-≤-suc (ℤ.suc-≤-suc ℤ.zero-≤pos ))

<Δ : ∀ n → [ 1 / 4 ] ℚ.< ([ pos (suc n) / 1 ])
<Δ n = 1/n<sucK 3 (1+ n)


clampedSq : ∀ (n : ℕ) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (2 ℚ₊· fromNat (suc n)))
clampedSq n =
  let ex = Lipschitz-ℚ→ℚ-extend _
             _ _ (ℚ.[ (1 , 4) ] , _) (<Δ n) (restrSq n)
  in fromLipschitz _ (_ , Lipschitz-rat∘ _ _ ex)

IsContinuous : (ℝ → ℝ) → Type
IsContinuous f =
 ∀ u ε → ∃[ δ ∈ ℚ₊ ] (∀ v → u ∼[ δ ] v → f u ∼[ ε ] f v)

IsContinuousWithPred : (P : ℝ → hProp ℓ-zero) →
                        (∀ r → ⟨ P r ⟩ → ℝ) → Type
IsContinuousWithPred P f =
  ∀ u ε u∈P  → ∃[ δ ∈ ℚ₊ ] (∀ v v∈P → u ∼[ δ ] v →  f u u∈P ∼[ ε ] f v v∈P)

Lipschitz→IsContinuous : ∀ L f → Lipschitz-ℝ→ℝ L f →  IsContinuous f
Lipschitz→IsContinuous L f p u ε =
 ∣ (ℚ.invℚ₊ L) ℚ₊· ε ,
   (λ v → subst∼ (ℚ.y·[x/y] L (fst ε))
      ∘S p u v ((invℚ₊ L) ℚ₊· ε)) ∣₁

AsContinuousWithPred : (P : ℝ → hProp ℓ-zero) → (f : ℝ → ℝ)
                      → IsContinuous f
                      → IsContinuousWithPred P (λ x _ → f x)
AsContinuousWithPred P f x u ε _ =
  PT.map (map-snd (λ y z _ → y z)) (x u ε)

IsContinuousWP∘ : ∀ P P' f g → (h : ∀ r x → ⟨ P (g r x) ⟩)
   → (IsContinuousWithPred P f)
   → (IsContinuousWithPred P' g )
   → IsContinuousWithPred P'
     (λ r x → f (g r x) (h r x))
IsContinuousWP∘ P P' f g h fC gC u ε u∈P =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ x v v∈P →
          δ∼ (g v v∈P) (h v v∈P) ∘ (x _ v∈P)) (gC u δ u∈P))
    ((fC (g u u∈P) ε (h _ u∈P)))

IsContinuous∘ : ∀ f g → (IsContinuous f) → (IsContinuous g)
                    → IsContinuous (f ∘ g)
IsContinuous∘ f g fC gC u ε =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ x v → δ∼ (g v) ∘  (x _)  ) (gC u δ))
    (fC (g u) ε)

isPropIsContinuous : ∀ f → isProp (IsContinuous f)
isPropIsContinuous f = isPropΠ2 λ _ _ → squash₁

-- HoTT Lemma 11.3.39
≡Continuous : ∀ f g → IsContinuous f → IsContinuous g
                → (∀ r → f (rat r) ≡ g (rat r))
                → ∀ u → f u ≡ g u
≡Continuous f g fC gC p = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → f z ≡ g z)
 w .Elimℝ-Prop.ratA = p
 w .Elimℝ-Prop.limA x p R = eqℝ _ _ λ ε →
   let f' = fC (lim x p) (ℚ./2₊ ε)
       g' = gC (lim x p) (ℚ./2₊ ε)
   in PT.rec2
       (isProp∼ _ _ _)
        (λ (θ , θ∼) (η , η∼) →
         let δ = ℚ./2₊ (ℚ.min₊ θ η)
             zF : f (lim x p) ∼[ ℚ./2₊ ε ] g (x δ)
             zF = subst (f (lim x p) ∼[ ℚ./2₊ ε ]_)
                  (R _)
                 (θ∼ _ (∼-monotone≤ (
                     subst (ℚ._≤ fst θ)
                      (sym (ℚ.ε/2+ε/2≡ε (fst (ℚ.min₊ θ η))))
                       (ℚ.min≤ (fst θ) (fst η)))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ)))))
             zG : g (lim x p) ∼[ ℚ./2₊ ε ] g (x δ)
             zG = η∼ _ (∼-monotone≤ (subst (ℚ._≤ fst η)
                      (sym (ℚ.ε/2+ε/2≡ε (fst (ℚ.min₊ θ η))))
                       (ℚ.min≤' (fst θ) (fst η)))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ))))
         in subst∼ (ℚ.ε/2+ε/2≡ε (fst ε)) (triangle∼ zF (sym∼ _ _ _ zG)))
        f' g'
 w .Elimℝ-Prop.isPropA _ = isSetℝ _ _



fromLipschitz' : ∀ f → ∃[ L ∈ ℚ₊ ] (Lipschitz-ℚ→ℝ L f)
                     → Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
fromLipschitz' f = PT.elim→Set
  (λ _ → isSetΣ (isSet→ isSetℝ)
   λ _ → isProp→isSet squash₁)
   (λ (L , lip) → map-snd (∣_∣₁ ∘ (L ,_)) $ fromLipschitz L (f , lip))
   λ (L , lip) (L' , lip') →
    Σ≡Prop (λ _ → squash₁)
          (funExt (≡Continuous _ _
            (Lipschitz→IsContinuous L _
              (snd (fromLipschitz L (f , lip))))
            (Lipschitz→IsContinuous L' _
              ((snd (fromLipschitz L' (f , lip')))) )
            λ _ → refl))


openPred : (P : ℝ → hProp ℓ-zero) → hProp ℓ-zero
openPred P = (∀ x → ⟨ P x ⟩ → ∃[ δ ∈ ℚ₊ ] (∀ y → x ∼[ δ ] y → ⟨ P y ⟩ ) )
   , isPropΠ2 λ _ _ → squash₁

opaque
 unfolding maxᵣ minᵣ
 <min-rr : ∀ p q r → p <ᵣ (rat q) → p <ᵣ (rat r) → p <ᵣ minᵣ (rat q) (rat r)
 <min-rr p =
  ℚ.elimBy≤ (λ x y R a b → subst (p <ᵣ_) (minᵣComm (rat x) (rat y)) (R b a))
    λ x y x≤y p<x _ → subst ((p <ᵣ_) ∘ rat)
     (sym (ℚ.≤→min _ _ x≤y) ) (p<x)


m·n/m : ∀ m n → [ pos (suc m) / 1 ] ℚ.· [ pos n / 1+ m ] ≡ [ pos n / 1 ]
m·n/m m n =
  eq/ _ _ ((λ i → ℤ.·IdR (ℤ.·Comm (pos (suc m)) (pos n) i) i)
       ∙ cong ((pos n ℤ.·_) ∘ ℚ.ℕ₊₁→ℤ) (sym (·₊₁-identityˡ (1+ m))))

3·x≡x+[x+x] : ∀ x → 3 ℚ.· x ≡ x ℚ.+ (x ℚ.+ x)
3·x≡x+[x+x] x = ℚ.·Comm _ _ ∙
  distℚ! x ·[ ge[ 3 ] ≡ ge1 +ge (ge1 +ge ge1) ]


opaque
 unfolding absᵣ _<ᵣ_
 abs'q≤Δ₁ : ∀ q n → absᵣ (rat q) <ᵣ rat [ pos (suc n) / 1+ 0 ]
      →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
 abs'q≤Δ₁ q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
           (ℚ.<Weaken≤ _ _ ((<ᵣ→<ℚ _ _ n<)))
            (subst2 ℚ._≤_
              ((ℚ.+IdR _))
                ((cong {x = [ 3 / 4 ]} {y = 1 ℚ.- [ 1 / 4 ]}
                          ([ pos (suc n) / 1 ] ℚ.+_)
                          (𝟚.toWitness
                           {Q = ℚ.discreteℚ [ 3 / 4 ] (1 ℚ.- [ 1 / 4 ])}
                            _ ))
                           ∙∙ ℚ.+Assoc _ _ _ ∙∙
                             cong (ℚ._- [ pos 1 / 1+ 3 ])
                              (ℚ.+Comm [ pos (suc n) / 1 ]
                                1 ∙
                                 ℚ.ℤ+→ℚ+ 1 (pos (suc n)) ∙
                                   cong [_/ 1 ]
                                    (sym (ℤ.pos+ 1 (suc n)))))
              (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
                (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))

abs'q≤Δ₁' : ∀ q n → ℚ.abs' q ℚ.≤ [ pos (suc n) / 1+ 0 ]
     →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
abs'q≤Δ₁' q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
          (n<)
           (subst2 ℚ._≤_
             ((ℚ.+IdR _))
               ((cong {x = [ 3 / 4 ]} {y = 1 ℚ.- [ 1 / 4 ]}
                         ([ pos (suc n) / 1 ] ℚ.+_)
                         (𝟚.toWitness
                          {Q = ℚ.discreteℚ [ 3 / 4 ] (1 ℚ.- [ 1 / 4 ])}
                           _ ))
                          ∙∙ ℚ.+Assoc _ _ _ ∙∙
                            cong (ℚ._- [ pos 1 / 1+ 3 ])
                             (ℚ.+Comm [ pos (suc n) / 1 ]
                               1 ∙
                                ℚ.ℤ+→ℚ+ 1 (pos (suc n)) ∙
                                  cong [_/ 1 ]
                                   (sym (ℤ.pos+ 1 (suc n)))))
             (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
               (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))


ℚabs-abs≤abs- : (x y : ℚ) → (ℚ.abs x ℚ.- ℚ.abs y) ℚ.≤ ℚ.abs (x ℚ.- y)
ℚabs-abs≤abs- x y =
 subst2 ℚ._≤_
   (cong ((ℚ._+ (ℚ.- (ℚ.abs y))) ∘ ℚ.abs) lem--00 )
   (sym lem--034)
  (ℚ.≤-+o
   (ℚ.abs ((x ℚ.- y) ℚ.+ y))
   (ℚ.abs (x ℚ.- y) ℚ.+ ℚ.abs y) (ℚ.- (ℚ.abs y)) (ℚ.abs+≤abs+abs (x ℚ.- y) y))

-- opaque
--  unfolding absᵣ _<ᵣ_
IsContinuousAbsᵣ : IsContinuous absᵣ
IsContinuousAbsᵣ = Lipschitz→IsContinuous _ _ absᵣ-lip

opaque
 unfolding maxᵣ minᵣ
 IsContinuousMaxR : ∀ x → IsContinuous (λ u → maxᵣ u x)
 IsContinuousMaxR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L maxR _ _ _ ε) ∣₁

 IsContinuousMaxL : ∀ x → IsContinuous (maxᵣ x)
 IsContinuousMaxL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R maxR _ _ _ ε) ∣₁

 IsContinuousMinR : ∀ x → IsContinuous (λ u → minᵣ u x)
 IsContinuousMinR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L minR _ _ _ ε) ∣₁

 IsContinuousMinL : ∀ x → IsContinuous (minᵣ x)
 IsContinuousMinL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R minR _ _ _ ε) ∣₁

IsContinuousClamp : ∀ a b → IsContinuous (clampᵣ a b)
IsContinuousClamp a b =
 IsContinuous∘ _ _
   (IsContinuousMinR _)
   (IsContinuousMaxL _)

IsContinuous-ᵣ : IsContinuous (-ᵣ_)
IsContinuous-ᵣ = Lipschitz→IsContinuous _ _ -ᵣ-lip


contDiagNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ f g → (IsContinuous f) → (IsContinuous g)
  → IsContinuous (λ x → NonExpanding₂.go ne (f x) (g x))
contDiagNE₂ ne f g fC gC u ε =
  PT.map2
    (λ (x , x') (y , y') →
      ℚ.min₊ x y , (λ v z →
          subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
           (NonExpanding₂.go∼₂ ne (ℚ./2₊ ε) (ℚ./2₊ ε)
           (x' v (∼-monotone≤ (ℚ.min≤ (fst x) (fst y)) z))
           (y' v (∼-monotone≤ (ℚ.min≤' (fst x) (fst y)) z)))))
   (fC u (ℚ./2₊ ε)) (gC u (ℚ./2₊ ε))

contDiagNE₂WP : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ P f g
     → (IsContinuousWithPred P f)
     → (IsContinuousWithPred P  g)
  → IsContinuousWithPred P (λ x x∈ → NonExpanding₂.go ne (f x x∈) (g x x∈))
contDiagNE₂WP ne P f g fC gC u ε u∈ =
    PT.map2
    (λ (x , x') (y , y') →

      ℚ.min₊ x y , (λ v v∈ z →
          subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
           (NonExpanding₂.go∼₂ ne (ℚ./2₊ ε) (ℚ./2₊ ε)
           (x' v v∈ (∼-monotone≤ (ℚ.min≤ (fst x) (fst y)) z))
           (y' v v∈ (∼-monotone≤ (ℚ.min≤' (fst x) (fst y)) z))))
           )
   (fC u (ℚ./2₊ ε) u∈) (gC u (ℚ./2₊ ε) u∈)

opaque
 unfolding _+ᵣ_
 cont₂+ᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → f x +ᵣ g x)
 cont₂+ᵣ = contDiagNE₂ sumR




 IsContinuous+ᵣR : ∀ x → IsContinuous (_+ᵣ x)
 IsContinuous+ᵣR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L sumR _ _ _ ε) ∣₁

 IsContinuous+ᵣL : ∀ x → IsContinuous (x +ᵣ_)
 IsContinuous+ᵣL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R sumR _ _ _ ε) ∣₁

opaque
 unfolding maxᵣ
 cont₂maxᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → maxᵣ (f x) (g x))
 cont₂maxᵣ = contDiagNE₂ maxR

opaque
 unfolding minᵣ
 cont₂minᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → minᵣ (f x) (g x))
 cont₂minᵣ = contDiagNE₂ minR




opaque
 unfolding _≤ᵣ_ absᵣ
 absᵣ-triangle : (x y : ℝ) → absᵣ (x +ᵣ y) ≤ᵣ (absᵣ x +ᵣ absᵣ y)
 absᵣ-triangle x y =
  let z = IsContinuous∘ _ _ (IsContinuous+ᵣR (absᵣ y)) IsContinuousAbsᵣ

  in ≡Continuous
     (λ x → maxᵣ (absᵣ (x +ᵣ y)) ((absᵣ x +ᵣ absᵣ y)))
     (λ x → (absᵣ x +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
       (IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣR y)) z)
     z
     (λ r → let z' = IsContinuous∘ _ _ (IsContinuous+ᵣL (absᵣ (rat r)))
                 IsContinuousAbsᵣ
      in ≡Continuous
     (λ y → maxᵣ (absᵣ ((rat r) +ᵣ y)) ((absᵣ (rat r) +ᵣ absᵣ y)))
     (λ y → (absᵣ (rat r) +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
         ((IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣL (rat r))))
           z' ) z'
     (λ r' → cong rat (ℚ.≤→max _ _
               (subst2 ℚ._≤_ (ℚ.abs'≡abs _)
                 (cong₂ ℚ._+_ (ℚ.abs'≡abs _) (ℚ.abs'≡abs _))
                (ℚ.abs+≤abs+abs r r') ) )) y) x



IsContinuousId : IsContinuous (λ x → x)
IsContinuousId u ε = ∣ ε , (λ _ x → x) ∣₁

IsContinuousConst : ∀ x → IsContinuous (λ _ → x)
IsContinuousConst x u ε = ∣ ε , (λ _ _ → refl∼ _ _ ) ∣₁


opaque
 unfolding _+ᵣ_ minᵣ maxᵣ
 +IdL : ∀ x → 0 +ᵣ x ≡ x
 +IdL = ≡Continuous _ _ (IsContinuous+ᵣL 0) IsContinuousId
   (cong rat ∘ ℚ.+IdL)

 +IdR : ∀ x → x +ᵣ 0 ≡ x
 +IdR = ≡Continuous _ _ (IsContinuous+ᵣR 0) IsContinuousId
   (cong rat ∘ ℚ.+IdR)


 +ᵣMaxDistr : ∀ x y z → (maxᵣ x y) +ᵣ z ≡ maxᵣ (x +ᵣ z) (y +ᵣ z)
 +ᵣMaxDistr x y z =
   ≡Continuous _ _
      (IsContinuous∘ _ _ (IsContinuous+ᵣR z) (IsContinuousMaxR y))
      (IsContinuous∘ _ _ (IsContinuousMaxR (y +ᵣ z)) (IsContinuous+ᵣR z))
      (λ x' →
        ≡Continuous _ _
          (IsContinuous∘ _ _ (IsContinuous+ᵣR z) (IsContinuousMaxL (rat x')))
          ((IsContinuous∘ _ _ (IsContinuousMaxL (rat x' +ᵣ z))
                                 (IsContinuous+ᵣR z)))
          (λ y' → ≡Continuous _ _
            (IsContinuous+ᵣL (maxᵣ (rat x') ( rat y')))
            (cont₂maxᵣ _ _ (IsContinuous+ᵣL (rat x'))
                           (IsContinuous+ᵣL (rat y')))
            (λ z' → cong rat $ ℚ.+MaxDistrℚ x' y' z')
            z)
          y)
      x

opaque
 unfolding _≤ᵣ_ absᵣ

 ≤ᵣ-+o : ∀ m n o →  m ≤ᵣ n → (m +ᵣ o) ≤ᵣ (n +ᵣ o)
 ≤ᵣ-+o m n o p = sym (+ᵣMaxDistr m n o) ∙ cong (_+ᵣ o) p

 ≤ᵣ-o+ : ∀ m n o →  m ≤ᵣ n → (o +ᵣ m) ≤ᵣ (o +ᵣ n)
 ≤ᵣ-o+ m n o = subst2 _≤ᵣ_ (+ᵣComm _ _) (+ᵣComm _ _)  ∘ ≤ᵣ-+o m n o


 ≤ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → (m +ᵣ o) ≤ᵣ (n +ᵣ s)
 ≤ᵣMonotone+ᵣ m n o s m≤n o≤s =
   isTrans≤ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (≤ᵣ-o+ o s n o≤s)




 lem--05ᵣ : ∀ δ q →  δ +ᵣ (q +ᵣ (-ᵣ δ)) ≡ q
 lem--05ᵣ δ q = cong (δ +ᵣ_) (+ᵣComm _ _) ∙∙
    +ᵣAssoc _ _ _  ∙∙
     (cong (_+ᵣ q) (+-ᵣ δ) ∙ +IdL q)

 abs-max : ∀ x → absᵣ x ≡ maxᵣ x (-ᵣ x)
 abs-max = ≡Continuous _ _
   IsContinuousAbsᵣ
    (cont₂maxᵣ _ _ IsContinuousId IsContinuous-ᵣ)
     λ r → cong rat (sym (ℚ.abs'≡abs r))


 absᵣNonNeg : ∀ x → 0 ≤ᵣ x → absᵣ x ≡ x
 absᵣNonNeg x p = abs-max x ∙∙ maxᵣComm _ _ ∙∙ z
  where
    z : (-ᵣ x) ≤ᵣ x
    z = subst2 _≤ᵣ_
      (+IdL (-ᵣ x))
      (sym (+ᵣAssoc _ _ _) ∙∙ cong (x +ᵣ_) (+-ᵣ x) ∙∙ +IdR x)
      (≤ᵣ-+o 0 (x +ᵣ x) (-ᵣ x)
       (≤ᵣMonotone+ᵣ 0 x 0 x p p))


 absᵣPos : ∀ x → 0 <ᵣ x → absᵣ x ≡ x
 absᵣPos x = absᵣNonNeg x ∘ <ᵣWeaken≤ᵣ _ _



 ≤lim : ∀ r x y → (∀ δ → rat r ≤ᵣ x δ) → rat r ≤ᵣ lim x y
 ≤lim r x y p = snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
        congLim _ _ _ _ p

 limConstRat : ∀ x y → lim (λ _ → (rat x)) y ≡ rat x
 limConstRat x y = eqℝ _ _ λ ε → lim-rat _ _ _ (/2₊ ε) _
   (ℚ.<→0< _ (ℚ.<→<minus _ _ (ℚ.x/2<x ε))) (refl∼  _ _)

 lim≤ : ∀ r x y → (∀ δ → x δ ≤ᵣ rat r ) → lim x y ≤ᵣ rat r
 lim≤ r x y p = maxᵣComm _ _ ∙ snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
    congLim' _ _ _ (λ δ → maxᵣComm _ _ ∙ p δ)
     ∙ limConstRat _ _


 IsContinuousWithPred∘IsContinuous : ∀ P f g
  → (g∈ : ∀ x → g x ∈ P)
  → IsContinuousWithPred P f
  → IsContinuous g
  → IsContinuous λ x → f (g x) (g∈ x)
 IsContinuousWithPred∘IsContinuous P f g g∈ fc gc u ε =
   PT.rec squash₁
          (λ (δ , δ∼) →
       PT.map (map-snd λ x v u∼v →
          δ∼ (g v) (g∈ v) (x v u∼v)
           ) (gc u δ) )
       (fc (g u) ε (g∈ u))




 IsContinuousWP∘' : ∀ P f g
    → (IsContinuous f)
    → (IsContinuousWithPred P g )
    → IsContinuousWithPred P
      (λ r x → f (g r x))
 IsContinuousWP∘' P f g fC gC u ε u∈P =
   PT.rec squash₁
     (λ (δ , δ∼) →
       PT.map (map-snd λ x v v∈P →
           δ∼ (g v v∈P) ∘ (x _ v∈P)) (gC u δ u∈P))
     ((fC (g u u∈P) ε))


 contDropPred : ∀ f → IsContinuousWithPred ⊤Pred (λ x _ → f x)
                 → IsContinuous f
 contDropPred f =
  flip (IsContinuousWithPred∘IsContinuous  ⊤Pred (λ x _ → f x)
    (idfun _) _) IsContinuousId


 ∩-openPred : ∀ P Q → ⟨ openPred P ⟩ → ⟨ openPred Q ⟩ →
               ⟨ openPred (λ x → _ , isProp× (snd (P x)) (snd (Q x))) ⟩
 ∩-openPred _ _ oP oQ x (x∈P , x∈Q) =
   PT.map2 (λ (δ , Δ) (δ' , Δ') →
      (ℚ.min₊ δ δ') , λ y x∼y →
        (Δ y (∼-monotone≤ (ℚ.min≤ _ _) x∼y))
       , Δ' y (∼-monotone≤ (ℚ.min≤' _ _) x∼y))
    (oP x x∈P) (oQ x x∈Q)





 max-lem : ∀ x x' y → maxᵣ (maxᵣ x y) (maxᵣ x' y) ≡ (maxᵣ (maxᵣ x x') y)
 max-lem x x' y = maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)
   ∙ sym (maxᵣAssoc _ _ _) ∙
     cong (maxᵣ x') (sym (maxᵣAssoc _ _ _) ∙ cong (maxᵣ x) (maxᵣIdem y))
      ∙ maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)



 minᵣIdem : ∀ x → minᵣ x x ≡ x
 minᵣIdem = ≡Continuous _ _
   (cont₂minᵣ _ _ IsContinuousId IsContinuousId)
   IsContinuousId
   (cong rat ∘ ℚ.minIdem)


 min-lem : ∀ x x' y → minᵣ (minᵣ x y) (minᵣ x' y) ≡ (minᵣ (minᵣ x x') y)
 min-lem x x' y = minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)
   ∙ sym (minᵣAssoc _ _ _) ∙
     cong (minᵣ x') (sym (minᵣAssoc _ _ _) ∙ cong (minᵣ x) (minᵣIdem y))
      ∙ minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)


 max≤-lem : ∀ x x' y → x ≤ᵣ y → x' ≤ᵣ y → maxᵣ x x' ≤ᵣ y
 max≤-lem x x' y p p' =
   sym (max-lem _ _ _)
    ∙∙ cong₂ maxᵣ p p' ∙∙ maxᵣIdem y

 max<-lem : ∀ x x' y → x <ᵣ y → x' <ᵣ y → maxᵣ x x' <ᵣ y
 max<-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.max q r , ℚ.max q' r') ,
        (max≤-lem _ _ (rat (ℚ.max q r))
          (isTrans≤ᵣ _ _ _ a (≤ℚ→≤ᵣ _ _ (ℚ.≤max q r)))
          ((isTrans≤ᵣ _ _ _ b (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))) ,
           (ℚ.<MonotoneMax _ _ _ _ a' b' , max≤-lem _ _ _ a'' b''))

 minDistMaxᵣ : ∀ x y y' →
   maxᵣ x (minᵣ y y') ≡ minᵣ (maxᵣ x y) (maxᵣ x y')
 minDistMaxᵣ x y y' = ≡Continuous _ _
    (IsContinuousMaxR _)
    (cont₂minᵣ _ _ (IsContinuousMaxR _) (IsContinuousMaxR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR)) ((IsContinuousMinR y')))
        (IsContinuous∘ _ _ (IsContinuousMinR _) (IsContinuousMaxL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR))
              ((IsContinuousMinL (rat yR))))
            (IsContinuous∘ _ _ (IsContinuousMinL (maxᵣ (rat xR) (rat yR)))
              (IsContinuousMaxL (rat xR)))
            (cong rat ∘ ℚ.minDistMax xR yR ) y')
        y)
    x


 ≤maxᵣ : ∀ m n →  m ≤ᵣ maxᵣ m n
 ≤maxᵣ m n = maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ n) (maxᵣIdem m)

 ≤min-lem : ∀ x y y' → x ≤ᵣ y → x ≤ᵣ y' →  x ≤ᵣ minᵣ y y'
 ≤min-lem x y y' p p' =
    minDistMaxᵣ x y y' ∙ cong₂ minᵣ p p'


 <min-lem : ∀ x x' y → y <ᵣ x → y <ᵣ x' →  y <ᵣ minᵣ x x'
 <min-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.min q r , ℚ.min q' r') , ≤min-lem _ _ _ a b
         , ℚ.<MonotoneMin _ _ _ _ a' b' ,
             ≤min-lem (rat (ℚ.min q' r')) x x'
              (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤ q' r')) a'')
              (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' q' r')) b'')



maxᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
maxᵣ₊ (x , 0<x) (y , 0<y) =
 maxᵣ x y , isTrans<≤ᵣ _ _ _ 0<x (≤maxᵣ _ _)


minᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
minᵣ₊ (x , 0<x) (y , 0<y) =
  minᵣ x y , <min-lem _ _ _ 0<x 0<y

minᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
minᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  minᵣ x y , ≤min-lem _ _ _ 0≤x 0≤y

maxᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
maxᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  maxᵣ x y , isTrans≤ᵣ _ _ _ 0≤x (≤maxᵣ x y)


opaque
 unfolding _≤ᵣ_ absᵣ

 maxAbsorbLMinᵣ : ∀ x y → maxᵣ x (minᵣ x y) ≡ x
 maxAbsorbLMinᵣ x =
   ≡Continuous _ _
     (IsContinuous∘ _ _
       (IsContinuousMaxL _) (IsContinuousMinL x))
       (IsContinuousConst _)
      λ y' →
        ≡Continuous _ _
           (cont₂maxᵣ _ _ IsContinuousId (IsContinuousMinR _))
         IsContinuousId
          (λ x' → cong rat (ℚ.maxAbsorbLMin x' y')) x

 maxDistMin : ∀ x y z → minᵣ x (maxᵣ y z) ≡ maxᵣ (minᵣ x y) (minᵣ x z)

 maxDistMin x y y' =
   ≡Continuous _ _
    (IsContinuousMinR _)
    (cont₂maxᵣ _ _ (IsContinuousMinR _) (IsContinuousMinR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMinL (rat xR)) ((IsContinuousMaxR y')))
        (IsContinuous∘ _ _ (IsContinuousMaxR _) (IsContinuousMinL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMinL (rat xR))
              ((IsContinuousMaxL (rat yR))))
            (IsContinuous∘ _ _ (IsContinuousMaxL (minᵣ (rat xR) (rat yR)))
              (IsContinuousMinL (rat xR)))
            (λ r →
              cong rat (ℚ.minComm _ _  ∙∙
               ℚ.maxDistMin _ _ _ ∙∙
                cong₂ ℚ.max (ℚ.minComm _ _) (ℚ.minComm _ _))) y')
        y)
    x

 min≤ᵣ : ∀ m n → minᵣ m n ≤ᵣ m
 min≤ᵣ m n = maxᵣComm _ _ ∙ maxAbsorbLMinᵣ _ _

 min≤ᵣ' : ∀ m n → minᵣ m n ≤ᵣ n
 min≤ᵣ' m n = subst (_≤ᵣ n) (minᵣComm n m) (min≤ᵣ n m)


 ≤→minᵣ : ∀ m n → m ≤ᵣ n → minᵣ m n ≡ m
 ≤→minᵣ m n p = cong₂ minᵣ (sym (maxᵣIdem m)) (sym p) ∙
   sym (minDistMaxᵣ _ _ _) ∙ maxAbsorbLMinᵣ _ _


 ≤→maxᵣ : ∀ m n → m ≤ᵣ n → maxᵣ m n ≡ n
 ≤→maxᵣ m n p = p



IsContinuous₂ : (ℝ → ℝ → ℝ) → Type
IsContinuous₂ f =
 (∀ x → IsContinuous (f x)) × (∀ x → IsContinuous (flip f x))

cont₂-fst : IsContinuous₂ (λ x _ → x)
cont₂-fst = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousId)

cont₂-snd : IsContinuous₂ (λ _ x → x)
cont₂-snd = (λ _ → IsContinuousId) , (λ _ → IsContinuousConst _)

cont₂-id : ∀ x → IsContinuous₂ (λ _ _ → x)
cont₂-id _ = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)

asIsContinuous₂-fst : ∀ f
  → IsContinuous f
  → IsContinuous₂ (λ x _ → f x)
asIsContinuous₂-fst f cf = (λ _ → IsContinuousConst _) , λ _ → cf


asIsContinuous₂-snd : ∀ f
  → IsContinuous f
  → IsContinuous₂ (λ _ x → f x)
asIsContinuous₂-snd f cf = (λ _ → cf) , (λ _ → IsContinuousConst _)


≡Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
         → IsContinuous₂ f₀
         → IsContinuous₂ f₁
         → (∀ u u' → f₀ (rat u) (rat u') ≡ f₁ (rat u) (rat u'))
             → ∀ x x' → f₀ x x' ≡ f₁ x x'
≡Cont₂ {f₀} {f₁} (f₀C , f₀C') (f₁C , f₁C') p x =
  ≡Continuous _ _ (f₀C x) (f₁C x)
    (λ q → ≡Continuous _ _ (f₀C' (rat q)) (f₁C' (rat q))
       (λ r → p r q) x)



contNE₂∘ : ∀ {h} → (ne : NonExpanding₂ h)
  {f₀ f₁ : ℝ → ℝ → ℝ}
   → IsContinuous₂ f₀
   → IsContinuous₂ f₁
  → IsContinuous₂ (λ x x' → NonExpanding₂.go ne (f₀ x x') (f₁ x x'))
contNE₂∘ ne x x₁ =
  (λ x₂ → contDiagNE₂ ne _ _ (x .fst x₂) (x₁ .fst x₂)) ,
   λ x₂ → contDiagNE₂ ne _ _ (x .snd x₂) (x₁ .snd x₂)

cont∘₂ : ∀ {g}
  {f : ℝ → ℝ → ℝ}
   → IsContinuous g
   → IsContinuous₂ f
  → IsContinuous₂ (λ x x' → g (f x x'))
cont∘₂ cG (cF , _) .fst x = IsContinuous∘ _ _ cG (cF x)
cont∘₂ cG (_ , cF) .snd x = IsContinuous∘ _ _ cG (cF x)

cont₂∘ :
  {g : ℝ → ℝ → ℝ}
  → ∀ {f f'}
   → IsContinuous₂ g
   → IsContinuous f
   → IsContinuous f'
  → IsContinuous₂ (λ x x' → g (f x) (f' x'))
cont₂∘ (cG , _) _ cF .fst x = IsContinuous∘ _ _ (cG _) cF
cont₂∘ (_ , cG) cF _ .snd x = IsContinuous∘ _ _ (cG _) cF


contNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → IsContinuous₂ (NonExpanding₂.go ne)
contNE₂ ne =
  contNE₂∘ ne
   ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
   ((λ _ → IsContinuousId) , (λ _ → IsContinuousConst _))



IsContinuousClamp₂ : ∀ x → IsContinuous₂ λ a b → clampᵣ a b x
IsContinuousClamp₂ x = (λ _ → IsContinuousMinL _) ,
   λ _ → IsContinuous∘ _ _ (IsContinuousMinR _) (IsContinuousMaxR _)

opaque
 unfolding minᵣ
 IsContinuousClamp₂∘ : ∀ {f₀} {f₁} x → IsContinuous₂ f₀ → IsContinuous₂ f₁ →
          IsContinuous₂ λ a b → clampᵣ (f₀ a b) (f₁ a b) x
 IsContinuousClamp₂∘ x =
   contNE₂∘ minR ∘
     (flip (contNE₂∘ maxR) ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)))

opaque
 unfolding maxᵣ
 IsContinuousClamp₂∘' : ∀ {f₀} {f₁} {f₂} →
          IsContinuous₂ f₀ → IsContinuous₂ f₁ → IsContinuous₂ f₂ →
          IsContinuous₂ λ a b → clampᵣ (f₀ a b) (f₁ a b) (f₂ a b)
 IsContinuousClamp₂∘' f₀C f₁C f₂C =
   contNE₂∘ minR (contNE₂∘ maxR f₀C f₂C) f₁C


opaque
 unfolding _+ᵣ_
 IsContinuous-₂∘ : ∀ {f₀} {f₁} → IsContinuous₂ f₀ → IsContinuous₂ f₁ →
      IsContinuous₂ λ a b → (f₀ a b) -ᵣ (f₁ a b)
 IsContinuous-₂∘ f₀C f₁C =
  contNE₂∘ sumR f₀C
    (cont∘₂ IsContinuous-ᵣ f₁C)




opaque
 unfolding _≤ᵣ_

 ≤Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
          → IsContinuous₂ f₀
          → IsContinuous₂ f₁
          → (∀ u u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
              → ∀ x x' → f₀ x x' ≤ᵣ f₁ x x'
 ≤Cont₂ f₀C f₁C =
   (≡Cont₂ (contNE₂∘ maxR f₀C f₁C) f₁C)




 ≤Cont : {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → f₀ (rat u) ≤ᵣ f₁ (rat u))
              → ∀ x → f₀ x ≤ᵣ f₁ x
 ≤Cont f₀C f₁C =
   ≡Continuous _ _ (contDiagNE₂ maxR _ _ f₀C f₁C ) f₁C

 ≤Cont₂Pos : {f₀ f₁ : ℝ → ℝ → ℝ}
          → IsContinuous₂ f₀
          → IsContinuous₂ f₁
          → (∀ u u' → 0 ℚ.≤ u → 0 ℚ.≤ u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
              → ∀ x x' → 0 ≤ᵣ x → 0 ≤ᵣ x' → f₀ x x' ≤ᵣ f₁ x x'
 ≤Cont₂Pos {f₀} {f₁} f₀C f₁C X x x' 0≤x 0≤x' =
   subst2 (λ x x' → f₀ x x' ≤ᵣ f₁ x x') 0≤x 0≤x'
     (≤Cont₂
       (cont₂∘ f₀C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
       (cont₂∘ f₁C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
         (λ u u' → (X _ _ (ℚ.≤max 0 u) (ℚ.≤max 0 u')))
          x x')



 ≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → x₀ ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
              → ∀ x → rat x₀ ≤ᵣ x → f₀ x ≤ᵣ f₁ x
 ≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C X x 0≤x =
   subst (λ x → f₀ x  ≤ᵣ f₁ x) 0≤x
     (≤Cont
       (IsContinuous∘ _ _  f₀C (IsContinuousMaxL (rat x₀)))
       (IsContinuous∘ _ _ f₁C (IsContinuousMaxL (rat x₀)))
         (λ u  → (X _ (ℚ.≤max x₀ u)))
          x)




 ≤ContPos'pred : {x₀ : ℚ} {f₀ f₁ : ∀ x → (rat x₀ ≤ᵣ x) → ℝ}
          → IsContinuousWithPred (λ _ → _ , isProp≤ᵣ _ _) f₀
          → IsContinuousWithPred (λ _ → _ , isProp≤ᵣ _ _) f₁
          → (∀ u x₀<u → f₀ (rat u) (≤ℚ→≤ᵣ _ _ x₀<u)
                 ≤ᵣ f₁ (rat u) (≤ℚ→≤ᵣ _ _ x₀<u) )
              → ∀ x x₀≤x → f₀ x x₀≤x ≤ᵣ f₁ x x₀≤x
 ≤ContPos'pred {x₀} {f₀} {f₁} f₀C f₁C X x 0≤x =
   subst (λ (x , x₀≤x) → f₀ x x₀≤x  ≤ᵣ f₁ x x₀≤x)
      (Σ≡Prop (λ _ → isSetℝ _ _) 0≤x)
     (≤Cont
       (IsContinuousWithPred∘IsContinuous _ _ _
          (λ _ → ≤maxᵣ _ _) f₀C (IsContinuousMaxL (rat x₀)))
       (IsContinuousWithPred∘IsContinuous _ _ _
          (λ _ → ≤maxᵣ _ _) f₁C (IsContinuousMaxL (rat x₀)))
          (λ u  →
              subst (λ qq → f₀ (maxᵣ (rat x₀) (rat u)) qq
                      ≤ᵣ f₁ (maxᵣ (rat x₀) (rat u)) qq)
                 (isSetℝ _ _ _ _) (X (ℚ.max x₀ u) (ℚ.≤max _ _))) x)




 <→≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → x₀ ℚ.< u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
              → ∀ x → rat x₀ <ᵣ x → f₀ x ≤ᵣ f₁ x
 <→≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C X x =
    PT.rec (isSetℝ _ _)
      λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
        ≤ContPos' {q'} f₀C f₁C
              ((_∘ ℚ.isTrans<≤ _ _ _
                (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ _ _ x₀≤q) q<q'))
                ∘ X ) x q'≤x



IsContinuousWithPred⊆ : ∀ (P P' : ℝ → hProp ℓ-zero) f
                       → (P'⊆P : P' ⊆ P)
                       → IsContinuousWithPred P f
                       → IsContinuousWithPred P' ((_∘ P'⊆P _) ∘ f )
IsContinuousWithPred⊆ P P' f P'⊆P X u ε u∈P =
  PT.map (map-snd ((_∘ P'⊆P _) ∘_))
   (X u ε (P'⊆P _ u∈P))

opaque
 unfolding _<ᵣ_
 <→≤ContPos'pred : {x₀ : ℚ} {f₀ f₁ : ∀ x → (rat x₀ <ᵣ x) → ℝ}
          → IsContinuousWithPred (λ _ → _ , isProp<ᵣ _ _) f₀
          → IsContinuousWithPred (λ _ → _ , isProp<ᵣ _ _) f₁
          → (∀ u x₀<u → f₀ (rat u) x₀<u
                     ≤ᵣ f₁ (rat u) x₀<u )
              → ∀ x x₀<x → f₀ x x₀<x ≤ᵣ f₁ x x₀<x
 <→≤ContPos'pred {x₀} {f₀} {f₁} f₀C f₁C X x =
    PT.elim (λ _ → isSetℝ _ _)
      λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
       let z = ≤ContPos'pred {q'}
                (IsContinuousWithPred⊆ _ _ f₀
                   (λ  _ → isTrans<≤ᵣ _ _ _
                  ((<ℚ→<ᵣ _ _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ x₀ q x₀≤q) q<q'))))
                   f₀C)
                 (IsContinuousWithPred⊆ _ _ f₁
                   (λ  _ → isTrans<≤ᵣ _ _ _
                  ((<ℚ→<ᵣ _ _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ x₀ q x₀≤q) q<q'))))
                   f₁C)
                 (λ u _ → X u _)
                       x q'≤x
      in subst (λ x₀<x → f₀ x x₀<x  ≤ᵣ f₁ x x₀<x)
             (squash₁ _ _) z



≤ContPos : {f₀ f₁ : ℝ → ℝ}
         → IsContinuous f₀
         → IsContinuous f₁
         → (∀ u → 0 ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
             → ∀ x → 0 ≤ᵣ x → f₀ x ≤ᵣ f₁ x
≤ContPos = ≤ContPos' {0}


ℚabs-min-max : ∀ u v →
      ℚ.abs (ℚ.max u v ℚ.- ℚ.min u v) ≡ ℚ.abs (u ℚ.- v)
ℚabs-min-max = ℚ.elimBy≤
  (λ x y X →
    (cong ℚ.abs (cong₂ ℚ._-_ (ℚ.maxComm _ _) (ℚ.minComm _ _)))
       ∙∙ X ∙∙
      ℚ.absComm- _ _)
  λ x y x≤y →
    cong ℚ.abs
      (cong₂ ℚ._-_
        (ℚ.≤→max _ _ x≤y) (ℚ.≤→min _ _ x≤y))
     ∙ ℚ.absComm- _ _

opaque
 unfolding absᵣ
 absᵣ-min-max : ∀ u v →
       absᵣ (maxᵣ u v -ᵣ minᵣ u v) ≡ absᵣ (u -ᵣ v)
 absᵣ-min-max =
  ≡Cont₂
    (cont∘₂ IsContinuousAbsᵣ
     (contNE₂∘ sumR
       (contNE₂ maxR)
       (cont∘₂ IsContinuous-ᵣ (contNE₂ minR) )))
    (cont∘₂ IsContinuousAbsᵣ
     (cont₂∘ (contNE₂ sumR)
       IsContinuousId IsContinuous-ᵣ))
    λ u v →
       cong rat (sym (ℚ.abs'≡abs _) ∙∙ ℚabs-min-max u v ∙∙ ℚ.abs'≡abs _)

opaque
 unfolding maxᵣ
 maxMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → maxᵣ m o ≤ᵣ maxᵣ n s
 maxMonotoneᵣ _ _ _ _ m≤n o≤s =
   max≤-lem _ _ _
     (isTrans≤ᵣ _ _ _ m≤n (≤maxᵣ _ _))
     (isTrans≤ᵣ _ _ _ o≤s
       (isTrans≤≡ᵣ _ _ _  (≤maxᵣ _ _) (maxᵣComm _ _) ))

opaque
 unfolding minᵣ
 minMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → minᵣ m o ≤ᵣ minᵣ n s
 minMonotoneᵣ m n o s m≤n o≤s =
   ≤min-lem _ _ _
     (isTrans≤ᵣ _ _ _
      (min≤ᵣ _ _) m≤n)
     (isTrans≤ᵣ _ _ _
      (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _) (min≤ᵣ _ _)) o≤s)

opaque
 unfolding _≤ᵣ_ absᵣ
 incr→max≤ : (f : ∀ x → 0 <ᵣ x → ℝ)
        → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
       → ∀ u v 0<u 0<v →
          maxᵣ (f u 0<u) (f v 0<v)
            ≤ᵣ  (f (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v))))
 incr→max≤ f incr u v 0<u 0<v =
   isTrans≤≡ᵣ _ _ _
     (maxMonotoneᵣ _ _ _ _
       (incr u 0<u (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (≤maxᵣ _ _))
       (incr v 0<v (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (isTrans≤≡ᵣ _ _ _  (≤maxᵣ _ _) (maxᵣComm _ _))))
     (maxᵣIdem _)

opaque
 unfolding minᵣ
 incr→≤min : (f : ∀ x → 0 <ᵣ x → ℝ)
        → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
       → ∀ u v 0<u 0<v →
            (f (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v))))
             ≤ᵣ  minᵣ (f u 0<u) (f v 0<v)
 incr→≤min f incr u v 0<u 0<v =
   isTrans≡≤ᵣ _ _ _
     (sym (minᵣIdem _))
      (minMonotoneᵣ _ _ _ _
        (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
            u 0<u
           (min≤ᵣ _ _))
        (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
            v 0<v
           (isTrans≡≤ᵣ _ _ _  (minᵣComm _ _) (min≤ᵣ _ _))))

absᵣ-monotoneOnNonNeg : (x y : ℝ₀₊) →
 fst x ≤ᵣ fst y → absᵣ (fst x) ≤ᵣ absᵣ (fst y)
absᵣ-monotoneOnNonNeg x y x≤y =
  subst2 _≤ᵣ_
    (sym (absᵣNonNeg (fst x) (snd x)))
    (sym (absᵣNonNeg (fst y) (snd y)))
    x≤y



ℚApproxℙ : (P : ℙ ℝ) (Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ P Q f =
   Σ[ f' ∈ (∀ q → rat q ∈ P → ℚ₊ → ℚ) ]
    (((∀ q q∈ ε  → rat (f' q q∈ ε) ∈ Q)) × (Σ[ f'-cauchy ∈ (∀ q q∈P → _) ]
      (∀ q q∈P → lim (rat ∘ f' q q∈P) (f'-cauchy q q∈P)
                ≡ fst (f (rat q) q∈P))))

ℚApprox : (f : ℝ → ℝ) → Type
ℚApprox f =
   Σ[ f' ∈ (ℚ → ℚ₊ → ℚ) ]
    Σ[ f'-cauchy ∈ (∀ q → _) ]
      (∀ q → lim (rat ∘ f' q) (f'-cauchy q)
                ≡ f (rat q))


ℚApproxℙ'Num : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) →
   ∀ q → (q∈P : rat q ∈ P) → Type

ℚApproxℙ'Num P Q f q q∈P =
     Σ[ f' ∈ (ℚ₊ → ℚ) ]
    ((∀ ε  → rat (f' ε) ∈ Q) × (Σ[ f'-cauchy ∈ (_) ]
      (lim (rat ∘ f') (f'-cauchy) ≡ fst (f (rat q) q∈P))))


ℚApproxℙ' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ' P Q f =
 ∀ q → (q∈P : rat q ∈ P) →
   ℚApproxℙ'Num P Q f q q∈P

Iso-ℚApproxℙ'-ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  Iso (ℚApproxℙ' P Q f) (ℚApproxℙ P Q f)
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.fun x =
  (λ q → fst ∘ x q) ,
   (λ q → fst ∘ snd ∘ x q) ,
    ((λ q → fst ∘ snd ∘ snd ∘ x q) ,
    (λ q → snd ∘ snd ∘ snd ∘ x q))
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.inv = _
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.rightInv _ = refl
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.leftInv _ = refl


ℚApproxℙ'≃ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  ℚApproxℙ' P Q f ≃ ℚApproxℙ P Q f
ℚApproxℙ'≃ℚApproxℙ P Q f =
 isoToEquiv (Iso-ℚApproxℙ'-ℚApproxℙ P Q f)



IsUContinuousℚℙ : (P : ℙ ℝ) → (∀ q → rat q ∈ P → ℝ) → Type
IsUContinuousℚℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v u∈ v∈ → ℚ.abs (u ℚ.- v) ℚ.< fst δ  → f u u∈ ∼[ ε ] f v v∈)

IsUContinuousℙ : (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsUContinuousℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v u∈ v∈ → u ∼[ δ ] v  → f u u∈ ∼[ ε ] f v v∈)


ℚApproxℙ'' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ'' P Q f =
 ∀ x → (x∈P : rat x ∈ P) (ε : ℚ₊) →
    Σ[ r ∈ ℚ ] ((rat r ∈ Q) × (rat r ∼[ ε ] fst (f (rat x) x∈P)))

ℚApproxℙ'→ℚApproxℙ'' : (P Q : ℙ ℝ) → ∀ f →
  (ℚApproxℙ' P Q f) → (ℚApproxℙ'' P Q f)
ℚApproxℙ'→ℚApproxℙ'' P Q f X x x∈P ε =
   fst (X x x∈P) (/2₊ ε) , fst (snd (X x x∈P)) (/2₊ ε) ,
     subst (rat (fst (X x x∈P) (/2₊ ε)) ∼[ ε ]_)
    (snd (snd (snd ( ((X x x∈P))) )))
      ((rat-lim _ _ _ (/2₊ ε) _ (snd (ℚ.<→ℚ₊ _ _ (ℚ.x/2<x ε)))
        (refl∼ _ _)))


ℚApproxℙ∘ : ∀ P Q R g f
          → IsUContinuousℙ Q ((fst ∘_) ∘ g)
          → ℚApproxℙ'' Q R g
          → ℚApproxℙ'' P Q f
          → ℚApproxℙ'' P R (curry (uncurry g ∘ uncurry f))
ℚApproxℙ∘ P Q R  g f gC gA fA q q∈ ε =
  let (δ' , Δ) = gC (/2₊ ε)
      δ = ℚ.min₊ δ' (/2₊ ε)

      uu' : rat (fst (fA q q∈ δ)) ∈ Q
      uu' = (fst (snd (fA q q∈ δ)))

      zz : rat (fst (gA (fst (fA q q∈ δ)) uu' δ))
             ∼[ /2₊ ε ℚ₊+ /2₊ ε ]
              fst (g (fst (f (rat q) q∈)) (snd (f (rat q) q∈)))
      zz = triangle∼
               ((∼-monotone≤ (ℚ.min≤' _ _)
                 ((snd (snd (gA (fst (fA q q∈ δ)) uu' δ))))))

                   (Δ _ _ uu' _ (
                     ∼-monotone≤ (ℚ.min≤ _ _)
                       (snd (snd (fA q q∈ δ)))))

  in fst (gA (fst (fA q q∈ δ)) uu' δ)
        , fst (snd (gA (fst (fA q q∈ δ)) uu' δ))
         , subst∼ (ℚ.ε/2+ε/2≡ε (fst ε)) zz

≡ContinuousWithPred : ∀ P P' → ⟨ openPred P ⟩ → ⟨ openPred P' ⟩ → ∀ f g
  → IsContinuousWithPred P  f
  → IsContinuousWithPred P' g
  → (∀ r r∈ r∈' → f (rat r) r∈  ≡ g (rat r) r∈')
  → ∀ u u∈ u∈' → f u u∈ ≡ g u u∈'
≡ContinuousWithPred P P' oP oP' f g fC gC e = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop
       (λ z → (u∈ : ⟨ P z ⟩) (u∈' : ⟨ P' z ⟩) → f z u∈ ≡ g z u∈')
 w .Elimℝ-Prop.ratA = e
 w .Elimℝ-Prop.limA x p R x∈ x∈' = PT.rec2 (isSetℝ _ _)
  (λ (Δ , PΔ) (Δ' , PΔ') → eqℝ _ _ λ ε₀ →
   let ε = ε₀
       f' = fC (lim x p) (ℚ./2₊ ε) x∈
       g' = gC (lim x p) (ℚ./2₊ ε) x∈'
   in PT.rec2
       (isProp∼ _ _ _)
        (λ (θ , θ∼) (η , η∼) →
         let δ = ℚ./2₊ (ℚ.min₊ (ℚ.min₊ Δ Δ') (ℚ.min₊ θ η))
             limX∼x = sym∼ _ _ _ (𝕣-lim-self x p δ δ)
             xδ∈P : ⟨ P (x δ) ⟩
             xδ∈P = PΔ (x δ)
                     (∼-monotone≤
                       (((subst (ℚ._≤ fst Δ)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤ (fst Δ) (fst Δ'))))))
                       limX∼x)
             xδ∈P' : ⟨ P' (x δ) ⟩
             xδ∈P' = PΔ' (x δ)
                     (∼-monotone≤ ((((subst (ℚ._≤ fst Δ')
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤' (fst Δ) (fst Δ'))))))) limX∼x)
             zF : f (lim x p) x∈ ∼[ ℚ./2₊ ε ] g (x δ) xδ∈P'
             zF = subst (f (lim x p) x∈ ∼[ ℚ./2₊ ε ]_)
                  (R _ xδ∈P xδ∈P')
                 (θ∼ _ _ (∼-monotone≤
                    ((subst (ℚ._≤ fst θ)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤'
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤ (fst θ) (fst η)))))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ)))))
             zG : g (lim x p) x∈'  ∼[ ℚ./2₊ ε ] g (x δ) xδ∈P'
             zG = η∼ _ _
                   (∼-monotone≤
                        ((subst (ℚ._≤ fst η)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤'
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤' (fst θ) (fst η)))))

                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ))))
             zz = subst∼ ((ℚ.ε/2+ε/2≡ε (fst ε))) (triangle∼ zF (sym∼ _ _ _ zG))
         in  zz)
        f' g') (oP (lim x p) x∈) (oP' (lim x p) x∈')

 w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _



opaque
 unfolding minᵣ
 ≤clampᵣ : ∀ L L' x → L ≤ᵣ L' →  L ≤ᵣ clampᵣ L L' x
 ≤clampᵣ L L' x y =
   isTrans≤≡ᵣ _ _ _ (≤maxᵣ L (minᵣ x L'))
     (cong₂ maxᵣ (sym (≤→minᵣ _ _ y) ∙ minᵣComm _ _) (minᵣComm _ _)
      ∙∙ sym (maxDistMin L' L x) ∙∙
      minᵣComm _ _ )


clamp≤ᵣ : ∀ L L' x →  clampᵣ L L' x ≤ᵣ L'
clamp≤ᵣ L L' x = min≤ᵣ' _ _
