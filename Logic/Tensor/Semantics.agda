{-# OPTIONS --copatterns #-}

module Logic.Tensor.Semantics where

open import Logic.Tensor.Syntax
open import Semantics.Game          renaming (_⊗_ to _⊗ₗ_) public
open import Semantics.Game.Strategy renaming (_⊗_ to _⊗ₛ_) public

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.Product using (_×_; _,_)
open import Function     using (_∘_)

⟦_⟧ : Formula → Game
⟦   ⊤   ⟧ = game ⊥-elim
⟦  ¬ A  ⟧ = game λ { tt → ⟦ A ⟧ }
⟦ A ⊗ B ⟧ = ⟦ A ⟧ ⊗ₗ ⟦ B ⟧

Provable    = Strategy  ∘ ⟦_⟧
Disprovable = Strategy′ ∘ ⟦_⟧
