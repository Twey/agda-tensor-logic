{-# OPTIONS --copatterns #-}

module Logic.Tensor.Properties where

open import Logic.Tensor.Syntax
open import Logic.Tensor.Semantics

open import Data.Unit hiding (⊤)
open import Data.Sum
open import Data.Product

⊤-defn : Provable ⊤
react ⊤-defn ()

⊤-id-right : ∀ {A} → Provable A → Provable (A ⊗ ⊤)
⊤-id-right s = s ⊗ₛ ⊤-defn

⊤-id-left : ∀ {A} → Provable A → Provable (⊤ ⊗ A)
⊤-id-left s = ⊤-defn ⊗ₛ s

⊥-defn : Disprovable ⊥
response ⊥-defn = tt
followup ⊥-defn = ⊤-defn

¬-defn : {A : Formula} → Disprovable A → Provable (¬ A)
react (¬-defn ¬A) tt = ¬A

⊗-defn : ∀ {A B} → Provable A × Provable B → Provable (A ⊗ B)
⊗-defn (sA , sB) = sA ⊗ₛ sB

⊗-commute : ∀ {A B} → Provable (A ⊗ B) → Provable (B ⊗ A)
react (⊗-commute s) (inj₁ b) = {!react s m!}
react (⊗-commute s) (inj₂ a) = {!!}

