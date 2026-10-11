import AlgebraicLayouts.Relation.Rel

/-! ## Monotonicity -/

section Monotonicity

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

/-- A world-indexed relation is monotone: relatedness survives moving to a future world. -/
def RepRel.Mono {A₁ A₂ : Type} (R : RepRel W A₁ A₂) : Prop :=
  ∀ {w w' x y}, w ≤ w' → R w x y → R w' x y

/-- What monotonicity of the whole relation needs from the parameters. -/
structure RelParams.Mono (θ : RelParams P sigSem W) : Prop where
  rval : ∀ {w w' : W} {b x y}, w ≤ w' → θ.RVal w b x y → θ.RVal w' b x y
  sigRel : ∀ {T : Adt} (c : Sig T), RepRel.Mono (θ.sigRel c)

/-- Every relation in the environment is monotone. -/
def RelEnv.Mono {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ) : Prop :=
  ∀ {T : Adt} (l : LRef Δ T), RepRel.Mono (ρ.rel l)

theorem LayoutRef.rel_mono {θ : RelParams P sigSem W} (hθ : θ.Mono)
    {Δ : LCtx} {ρ : RelEnv (P := P) (W := W) Δ} (hρ : ρ.Mono) {T : Adt}
    (r : LayoutRef Sig Δ T) : RepRel.Mono (LayoutRef.rel θ ρ r) := by
  cases r with
  | var l => exact hρ l
  | concrete c => exact hθ.sigRel c

/-- Related computations stay related: free, from the future-world quantifier. -/
theorem CompRel.mono {θ : RelParams P sigSem W} {A₁ A₂ : Type 1} {S : W → A₁ → A₂ → Prop}
    {w w' : W} (hle : w ≤ w') {c₁ : Comp P A₁} {c₂ : Comp P A₂} :
    CompRel θ S w c₁ c₂ → CompRel θ S w' c₁ c₂ :=
  fun h w'' hle'' => h w'' (le_trans hle hle'')

theorem SumRel.mono {A B C D : Type 1} {S S' : A → C → Prop} {T T' : B → D → Prop}
    (hS : ∀ x y, S x y → S' x y) (hT : ∀ x y, T x y → T' x y) :
    ∀ x y, SumRel S T x y → SumRel S' T' x y
  | .inl x, .inl y, h => hS x y h
  | .inr x, .inr y, h => hT x y h
  | .inl _, .inr _, h => h.elim
  | .inr _, .inl _, h => h.elim

/-- **Monotonicity of the logical relation.** -/
theorem Ty.rel_mono {θ : RelParams P sigSem W} (hθ : θ.Mono) :
    {Δ : LCtx} → {ρ : RelEnv (P := P) (W := W) Δ} → ρ.Mono →
    (a : Ty Sig Δ) → {w w' : W} → w ≤ w' → ∀ x y,
      Ty.rel θ ρ a w x y → Ty.rel θ ρ a w' x y
  | _, _, _, .base _, _, _, hle, _, _, h => hθ.rval hle h
  | _, _, hρ, .atL _ r, _, _, hle, _, _, h => LayoutRef.rel_mono hθ hρ r hle h
  | _, _, hρ, .ref _ r, _, _, hle, _, _, h => LayoutRef.rel_mono hθ hρ r hle h
  | _, _, hρ, .sum a b, _, _, hle, x, y, h =>
      SumRel.mono (fun x y => Ty.rel_mono hθ hρ a hle x y)
        (fun x y => Ty.rel_mono hθ hρ b hle x y) x y h
  | _, _, hρ, .prod a b, _, _, hle, _, _, h =>
      ⟨Ty.rel_mono hθ hρ a hle _ _ h.1, Ty.rel_mono hθ hρ b hle _ _ h.2⟩
  | _, _, _, .arr _ _, _, _, hle, _, _, h =>
      fun w'' hle'' x y hxy => h w'' (le_trans hle hle'') x y hxy
  | _, _, _, .forallLayout _ _, _, _, hle, _, _, h =>
      fun L₁ L₂ R hR => CompRel.mono hle (h L₁ L₂ R hR)

/-- Extending a monotone environment with a monotone relation keeps it monotone.
(This is where a requirement "related layouts have monotone relations" will be needed.) -/
theorem RelEnv.extend_mono {Δ : LCtx} {T : Adt} {ρ : RelEnv (P := P) (W := W) Δ} (hρ : ρ.Mono)
    {L₁ L₂ : SemLayout P T} {R : RepRel W L₁.Rep L₂.Rep} (hR : R.Mono) :
    (ρ.extend L₁ L₂ R).Mono := by
  intro T' l
  cases l with
  | here => exact hR
  | there l => exact hρ l

end Monotonicity
