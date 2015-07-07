module Logic.Tensor.Semantics where

open import Logic.Tensor.Syntax
open import Semantics.Game.Strategy
import Semantics.Game as G

open import Function using (_∘_)

⟦_⟧ : Formula → G.Game
⟦   ⊤   ⟧ = G.⊤
⟦  ¬ A  ⟧ = G.¬ ⟦ A ⟧
⟦ A ⊗ B ⟧ = ⟦ A ⟧ G.⊗ ⟦ B ⟧

Provable    = Strategy  ∘ ⟦_⟧
Disprovable = Strategy′ ∘ ⟦_⟧
