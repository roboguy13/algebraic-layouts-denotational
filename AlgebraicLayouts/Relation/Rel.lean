import Mathlib.Order.Basic
import AlgebraicLayouts.Abs

section Relation

variable (P : Type) [Backend P] {Sig : Adt → Type}
variable (sigSem : ∀ {T : Adt}, Sig T → SemLayout P T)

-- World preorder
variable {W : Type} [Preorder W]

/-- Relation between two representation types -/
def RepRel (W : Type) (A B : Type) : Type := W → A → B → Prop

structure RelParams (W : Type) [Preorder W] where
  /-- Related base values -/
  RVal : W → (b : Base) → Backend.Val P b → Backend.Val P b → Prop

  /-- Related backend results -/
  RP : W → P → P → Prop

  /-- Concrete layouts are related -/
  sigRel : ∀ {T : Adt} (c : Sig T), RepRel W (sigSem c).Rep (sigSem c).Rep

  /-- Predicate on whether layouts are related. -/
  Related : ∀ {T : Adt} (L1 L2 : SemLayout P T), RepRel W L1.Rep L2.Rep → Prop

variable {P sigSem}

/-- A relational layout environment: two semantic environments, and for each
layout variable a relation between the two sides' representations. -/
structure RelEnv (Δ : LCtx) where
  lenv₁ : LEnv P Δ
  lenv₂ : LEnv P Δ
  rel : ∀ {T : Adt} (l : LRef Δ T), RepRel W (lenv₁ l).Rep (lenv₂ l).Rep

def RelEnv.extend {Δ : LCtx} {T : Adt} (ρ : RelEnv (P := P) (W := W) Δ)
    (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep) :
    RelEnv (P := P) (W := W) (Δ.extend T) where
  lenv₁ := LEnv.extend P ρ.lenv₁ L₁
  lenv₂ := LEnv.extend P ρ.lenv₂ L₂
  rel := fun
    | .here => R
    | .there l => ρ.rel l

/-- Relatedness of layout references: variables use the environment,
concrete layouts use `sigRel`. -/
def LayoutRef.rel (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ) {T : Adt} :
    (r : LayoutRef Sig Δ T) →
      RepRel W (r.interp P sigSem ρ.lenv₁).Rep (r.interp P sigSem ρ.lenv₂).Rep
  | .var l => ρ.rel l
  | .concrete c => θ.sigRel c


/-- Related computations: given continuations related at every future world,
the results are related by `RP`. -/
def CompRel (θ : RelParams P sigSem W) {A₁ A₂ : Type 1} (S : W → A₁ → A₂ → Prop)
    (w : W) (c₁ : Comp P A₁) (c₂ : Comp P A₂) : Prop :=
  ∀ w', w ≤ w' → ∀ κ₁ κ₂,
    (∀ w'', w' ≤ w'' → ∀ x y, S w'' x y → θ.RP w'' (κ₁ x).down (κ₂ y).down) →
    θ.RP w' (c₁ κ₁).down (c₂ κ₂).down

/-- Relational lifting of sums: same side, related contents. -/
def SumRel {A B C D : Type 1} (S : A → C → Prop) (T : B → D → Prop) : A ⊕ B → C ⊕ D → Prop
  | .inl x, .inl y => S x y
  | .inr x, .inr y => T x y
  | _, _ => False

/-- **The logical relation**, by recursion on types. -/
def Ty.rel (θ : RelParams P sigSem W) : {Δ : LCtx} → (ρ : RelEnv (P := P) (W := W) Δ) →
    (a : Ty Sig Δ) → W → a.interp P sigSem ρ.lenv₁ → a.interp P sigSem ρ.lenv₂ → Prop
  | _, _, .base b, w, x, y => θ.RVal w b x.down y.down
  | _, ρ, .atL _ r, w, x, y => LayoutRef.rel θ ρ r w x.down y.down
  | _, ρ, .ref _ r, w, x, y => LayoutRef.rel θ ρ r w x.down y.down
  | _, ρ, .sum a b, w, x, y => SumRel (Ty.rel θ ρ a w) (Ty.rel θ ρ b w) x y
  | _, ρ, .prod a b, w, x, y => Ty.rel θ ρ a w x.1 y.1 ∧ Ty.rel θ ρ b w x.2 y.2
  | _, ρ, .arr a b, w, f, g =>
      ∀ w', w ≤ w' → ∀ x y, Ty.rel θ ρ a w' x y →
        CompRel θ (Ty.rel θ ρ b) w' (f x) (g y)
  | _, ρ, .forallLayout T body, w, F, G =>
      ∀ (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep),
        θ.Related L₁ L₂ R →
        CompRel θ (Ty.rel θ (ρ.extend L₁ L₂ R) body) w (F L₁) (G L₂)

end Relation
