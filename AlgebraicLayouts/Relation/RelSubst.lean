/-
  The relational substitution lemma and its corollaries.

  Checked together with Rel.lean and Mono.lean against the repo at aa790de +
  Abs.lean, with Mathlib (Lean 4.35.0-rc4, relaxedAutoImplicit = false).
  Axioms of `Ty.rel_subst`, `Ty.rel_instantiate`, `Ty.rel_weaken`:
  propext, Quot.sound.

  Approach: `Corr h₁ h₂ R S` says relations `R` and `S` agree once arguments
  are cast along the type equalities `h₁`, `h₂`. One lemma per type former
  (sum, product, function, `Comp`, `∀Layout`), each proved by generalizing the
  type equalities and `subst`-ing them away, avoids `HEq` in the main proof.
  Environment congruence goes through `RelEnv.ext'` (pointwise equality),
  so lifted/instantiated environments are equated rather than cast.
-/

import AlgebraicLayouts.Relation.Mono

/-! ## Relations that agree up to transport -/

section Corr

/-- `R` and `S` agree once arguments are cast along `h₁` and `h₂`. -/
def Corr {A₁ A₂ B₁ B₂ : Type 1} (h₁ : A₁ = B₁) (h₂ : A₂ = B₂)
    (R : A₁ → A₂ → Prop) (S : B₁ → B₂ → Prop) : Prop :=
  ∀ x y, R x y ↔ S (cast h₁ x) (cast h₂ y)

theorem Corr.refl {A₁ A₂ : Type 1} (R : A₁ → A₂ → Prop) : Corr rfl rfl R R :=
  fun _ _ => Iff.rfl

theorem Corr.trans {A₁ A₂ B₁ B₂ C₁ C₂ : Type 1} {h₁ : A₁ = B₁} {h₂ : A₂ = B₂}
    {h₁' : B₁ = C₁} {h₂' : B₂ = C₂} {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop}
    {T : C₁ → C₂ → Prop} (c : Corr h₁ h₂ R S) (c' : Corr h₁' h₂' S T) :
    Corr (h₁.trans h₁') (h₂.trans h₂') R T := by
  subst h₁ h₂ h₁' h₂'
  exact fun x y => (c x y).trans (c' x y)

theorem Corr.sum {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type 1}
    {hA₁ : A₁ = C₁} {hA₂ : A₂ = C₂} {hB₁ : B₁ = D₁} {hB₂ : B₂ = D₂}
    {R : A₁ → A₂ → Prop} {S : C₁ → C₂ → Prop} {R' : B₁ → B₂ → Prop} {S' : D₁ → D₂ → Prop}
    (h₁ : (A₁ ⊕ B₁) = (C₁ ⊕ D₁)) (h₂ : (A₂ ⊕ B₂) = (C₂ ⊕ D₂))
    (cA : Corr hA₁ hA₂ R S) (cB : Corr hB₁ hB₂ R' S') :
    Corr h₁ h₂ (SumRel R R') (SumRel S S') := by
  subst hA₁ hA₂ hB₁ hB₂
  intro x y
  cases x <;> cases y <;> simp only [cast_eq, SumRel] <;> first | exact cA _ _ | exact cB _ _

theorem Corr.prod {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type 1}
    {hA₁ : A₁ = C₁} {hA₂ : A₂ = C₂} {hB₁ : B₁ = D₁} {hB₂ : B₂ = D₂}
    {R : A₁ → A₂ → Prop} {S : C₁ → C₂ → Prop} {R' : B₁ → B₂ → Prop} {S' : D₁ → D₂ → Prop}
    (h₁ : (A₁ × B₁) = (C₁ × D₁)) (h₂ : (A₂ × B₂) = (C₂ × D₂))
    (cA : Corr hA₁ hA₂ R S) (cB : Corr hB₁ hB₂ R' S') :
    Corr h₁ h₂ (fun x y => R x.1 y.1 ∧ R' x.2 y.2) (fun x y => S x.1 y.1 ∧ S' x.2 y.2) := by
  subst hA₁ hA₂ hB₁ hB₂
  intro x y
  simp only [cast_eq]
  exact and_congr (cA _ _) (cB _ _)

end Corr

section RelSubst

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

theorem CompRel.congr {θ : RelParams P sigSem W} {A₁ A₂ B₁ B₂ : Type 1}
    {hA₁ : A₁ = B₁} {hA₂ : A₂ = B₂} {S : W → A₁ → A₂ → Prop} {S' : W → B₁ → B₂ → Prop}
    (c : ∀ w, Corr hA₁ hA₂ (S w) (S' w)) (w : W)
    (h₁ : Comp P A₁ = Comp P B₁) (h₂ : Comp P A₂ = Comp P B₂) :
    Corr h₁ h₂ (CompRel θ S w) (CompRel θ S' w) := by
  subst hA₁ hA₂
  have hS : S = S' := funext fun w => funext fun x => funext fun y => propext (by
    simpa only [cast_eq] using c w x y)
  subst hS
  intro c₁ c₂
  simp only [cast_eq]

end RelSubst

section RelSubst2

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

theorem Corr.arr {θ : RelParams P sigSem W} {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type 1}
    {hA₁ : A₁ = C₁} {hA₂ : A₂ = C₂} {hB₁ : B₁ = D₁} {hB₂ : B₂ = D₂}
    {RA : W → A₁ → A₂ → Prop} {SA : W → C₁ → C₂ → Prop}
    {RB : W → B₁ → B₂ → Prop} {SB : W → D₁ → D₂ → Prop}
    (cA : ∀ w, Corr hA₁ hA₂ (RA w) (SA w)) (cB : ∀ w, Corr hB₁ hB₂ (RB w) (SB w)) (w : W)
    (h₁ : (A₁ → Comp P B₁) = (C₁ → Comp P D₁)) (h₂ : (A₂ → Comp P B₂) = (C₂ → Comp P D₂)) :
    Corr h₁ h₂
      (fun f g => ∀ w', w ≤ w' → ∀ x y, RA w' x y → CompRel θ RB w' (f x) (g y))
      (fun f g => ∀ w', w ≤ w' → ∀ x y, SA w' x y → CompRel θ SB w' (f x) (g y)) := by
  subst hA₁ hA₂ hB₁ hB₂
  have eA : RA = SA := funext fun w => funext fun x => funext fun y => propext (by
    simpa only [cast_eq] using cA w x y)
  have eB : RB = SB := funext fun w => funext fun x => funext fun y => propext (by
    simpa only [cast_eq] using cB w x y)
  subst eA eB
  intro f g
  simp only [cast_eq]

theorem Corr.pi {X : Type 1} {C₁ C₂ D₁ D₂ : X → Type 1}
    {hC₁ : ∀ x, C₁ x = D₁ x} {hC₂ : ∀ x, C₂ x = D₂ x}
    {Q : X → X → Type} {Rel : ∀ x₁ x₂, Q x₁ x₂ → Prop}
    {K : ∀ x₁ x₂, Q x₁ x₂ → C₁ x₁ → C₂ x₂ → Prop} {K' : ∀ x₁ x₂, Q x₁ x₂ → D₁ x₁ → D₂ x₂ → Prop}
    (c : ∀ x₁ x₂ q, Corr (hC₁ x₁) (hC₂ x₂) (K x₁ x₂ q) (K' x₁ x₂ q))
    (h₁ : ((x : X) → C₁ x) = ((x : X) → D₁ x)) (h₂ : ((x : X) → C₂ x) = ((x : X) → D₂ x)) :
    Corr h₁ h₂
      (fun F G => ∀ x₁ x₂ q, Rel x₁ x₂ q → K x₁ x₂ q (F x₁) (G x₂))
      (fun F G => ∀ x₁ x₂ q, Rel x₁ x₂ q → K' x₁ x₂ q (F x₁) (G x₂)) := by
  have e₁ : C₁ = D₁ := funext hC₁
  have e₂ : C₂ = D₂ := funext hC₂
  subst e₁ e₂
  have eK : K = K' := funext fun x₁ => funext fun x₂ => funext fun q => funext fun a =>
    funext fun b => propext (by simpa only [cast_eq] using c x₁ x₂ q a b)
  subst eK
  intro F G
  simp only [cast_eq]

/-- Pull a relational environment back along a substitution. -/
def LSubst.relEnv (θ : RelParams P sigSem W) {Δ Δ' : LCtx} (σ : LSubst Sig Δ Δ')
    (ρ : RelEnv (P := P) (W := W) Δ') : RelEnv (P := P) (W := W) Δ where
  lenv₁ := σ.interp P sigSem ρ.lenv₁
  lenv₂ := σ.interp P sigSem ρ.lenv₂
  rel := fun l => LayoutRef.rel θ ρ (σ l)

omit [Preorder W] in
/-- Relational environments are determined by their components, pointwise. -/
theorem RelEnv.ext' {Δ : LCtx} {ρ₁ ρ₂ : RelEnv (P := P) (W := W) Δ}
    (h₁ : ∀ {T : Adt} (l : LRef Δ T), ρ₁.lenv₁ l = ρ₂.lenv₁ l)
    (h₂ : ∀ {T : Adt} (l : LRef Δ T), ρ₁.lenv₂ l = ρ₂.lenv₂ l)
    (h₃ : ∀ {T : Adt} (l : LRef Δ T), HEq (ρ₁.rel l) (ρ₂.rel l)) : ρ₁ = ρ₂ := by
  cases ρ₁ with | mk a₁ b₁ r₁ =>
  cases ρ₂ with | mk a₂ b₂ r₂ =>
  have ea : (@a₁) = (@a₂) := funext fun _ => funext fun l => h₁ l
  have eb : (@b₁) = (@b₂) := funext fun _ => funext fun l => h₂ l
  subst ea eb
  have er : (@r₁) = (@r₂) := funext fun _ => funext fun l => eq_of_heq (h₃ l)
  subst er
  rfl

/-- Equal relational environments give corresponding relations. -/
theorem Ty.rel_congr_env (θ : RelParams P sigSem W) {Δ : LCtx}
    {ρ₁ ρ₂ : RelEnv (P := P) (W := W) Δ} (E : ρ₁ = ρ₂) (a : Ty Sig Δ) (w : W) :
    Corr (congrArg (fun ρ : RelEnv (P := P) (W := W) Δ => a.interp P sigSem ρ.lenv₁) E)
      (congrArg (fun ρ : RelEnv (P := P) (W := W) Δ => a.interp P sigSem ρ.lenv₂) E)
      (Ty.rel θ ρ₁ a w) (Ty.rel θ ρ₂ a w) := by
  subst E
  exact Corr.refl _

/-- Lifting a substitution under a binder agrees with extending the pulled-back environment. -/
theorem LSubst.relEnv_lift (θ : RelParams P sigSem W) {Δ Δ' : LCtx} {T : Adt}
    (σ : LSubst Sig Δ Δ') (ρ : RelEnv (P := P) (W := W) Δ')
    (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep) :
    LSubst.relEnv θ σ.lift (ρ.extend L₁ L₂ R) = (LSubst.relEnv θ σ ρ).extend L₁ L₂ R := by
  apply RelEnv.ext'
  · intro _ l; exact LSubst.interp_lift P sigSem σ ρ.lenv₁ L₁ l
  · intro _ l; exact LSubst.interp_lift P sigSem σ ρ.lenv₂ L₂ l
  · intro _ l
    cases l with
    | here => exact HEq.rfl
    | there l =>
      show HEq (LayoutRef.rel θ (ρ.extend L₁ L₂ R) ((σ l).rename fun l' => .there l'))
        (LayoutRef.rel θ ρ (σ l))
      generalize σ l = r
      cases r <;> exact HEq.rfl

/-- **The relational substitution lemma.** -/
theorem Ty.rel_subst (θ : RelParams P sigSem W) :
    {Δ Δ' : LCtx} → (σ : LSubst Sig Δ Δ') → (ρ : RelEnv (P := P) (W := W) Δ') →
    (a : Ty Sig Δ) → (w : W) →
    Corr (Ty.interp_subst P sigSem σ ρ.lenv₁ a) (Ty.interp_subst P sigSem σ ρ.lenv₂ a)
      (Ty.rel θ ρ (a.subst σ) w) (Ty.rel θ (LSubst.relEnv θ σ ρ) a w)
  | _, _, _, _, .base _, _ => fun _ _ => Iff.rfl
  | _, _, _, _, .atL _ r, _ => by cases r <;> exact fun _ _ => Iff.rfl
  | _, _, _, _, .ref _ r, _ => by cases r <;> exact fun _ _ => Iff.rfl
  | _, _, σ, ρ, .sum a b, w =>
      Corr.sum _ _ (Ty.rel_subst θ σ ρ a w) (Ty.rel_subst θ σ ρ b w)
  | _, _, σ, ρ, .prod a b, w =>
      Corr.prod _ _ (Ty.rel_subst θ σ ρ a w) (Ty.rel_subst θ σ ρ b w)
  | _, _, σ, ρ, .arr a b, w =>
      Corr.arr (fun w => Ty.rel_subst θ σ ρ a w) (fun w => Ty.rel_subst θ σ ρ b w) w _ _
  | _, _, σ, ρ, .forallLayout T body, w =>
      Corr.pi (Rel := fun L₁ L₂ R => θ.Related L₁ L₂ R)
        (hC₁ := fun L₁ => congrArg (Comp P)
          ((Ty.interp_subst P sigSem σ.lift (LEnv.extend P ρ.lenv₁ L₁) body).trans
            (Ty.interp_congr P sigSem (LSubst.interp_lift P sigSem σ ρ.lenv₁ L₁) body)))
        (hC₂ := fun L₂ => congrArg (Comp P)
          ((Ty.interp_subst P sigSem σ.lift (LEnv.extend P ρ.lenv₂ L₂) body).trans
            (Ty.interp_congr P sigSem (LSubst.interp_lift P sigSem σ ρ.lenv₂ L₂) body)))
        (fun L₁ L₂ R => CompRel.congr
          (fun w' => (Ty.rel_subst θ σ.lift (ρ.extend L₁ L₂ R) body w').trans
            (Ty.rel_congr_env θ (LSubst.relEnv_lift θ σ ρ L₁ L₂ R) body w')) w _ _) _ _

end RelSubst2

section RelCorollaries

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

/-- Equal types give corresponding relations. -/
theorem Ty.rel_congr_ty (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ)
    {a b : Ty Sig Δ} (E : a = b) (w : W) :
    Corr (congrArg (fun a => a.interp P sigSem ρ.lenv₁) E)
      (congrArg (fun a => a.interp P sigSem ρ.lenv₂) E) (Ty.rel θ ρ a w) (Ty.rel θ ρ b w) := by
  subst E
  exact Corr.refl _

/-- Instantiating the innermost layout variable agrees with extending the environment. -/
theorem LSubst.relEnv_single (θ : RelParams P sigSem W) {Δ : LCtx} {T : Adt}
    (ρ : RelEnv (P := P) (W := W) Δ) (L : LayoutRef Sig Δ T) :
    LSubst.relEnv θ (LSubst.single L) ρ
      = ρ.extend (L.interp P sigSem ρ.lenv₁) (L.interp P sigSem ρ.lenv₂) (LayoutRef.rel θ ρ L) := by
  apply RelEnv.ext'
  · intro _ l; cases l <;> rfl
  · intro _ l; cases l <;> rfl
  · intro _ l; cases l <;> exact HEq.rfl

/-- **Layout application** (used by `layoutApp`). -/
theorem Ty.rel_instantiate (θ : RelParams P sigSem W) {Δ : LCtx} {T : Adt}
    (ρ : RelEnv (P := P) (W := W) Δ) (body : Ty Sig (Δ.extend T)) (L : LayoutRef Sig Δ T) (w : W) :
    Corr (Ty.interp_instantiate P sigSem ρ.lenv₁ body L) (Ty.interp_instantiate P sigSem ρ.lenv₂ body L)
      (Ty.rel θ ρ (body.instantiate L) w)
      (Ty.rel θ (ρ.extend (L.interp P sigSem ρ.lenv₁) (L.interp P sigSem ρ.lenv₂)
        (LayoutRef.rel θ ρ L)) body w) :=
  (Ty.rel_subst θ (LSubst.single L) ρ body w).trans
    (Ty.rel_congr_env θ (LSubst.relEnv_single θ ρ L) body w)

/-- Substitutions that agree pointwise act equally. -/
theorem Ty.subst_congr {Δ Δ' : LCtx} {σ₁ σ₂ : LSubst Sig Δ Δ'}
    (h : ∀ {T : Adt} (l : LRef Δ T), σ₁ l = σ₂ l) : (a : Ty Sig Δ) → a.subst σ₁ = a.subst σ₂
  | .base _ => rfl
  | .atL _ r => by cases r <;> simp [Ty.subst, LayoutRef.subst, h]
  | .ref _ r => by cases r <;> simp [Ty.subst, LayoutRef.subst, h]
  | .sum a b => by simp only [Ty.subst, Ty.subst_congr h a, Ty.subst_congr h b]
  | .prod a b => by simp only [Ty.subst, Ty.subst_congr h a, Ty.subst_congr h b]
  | .arr a b => by simp only [Ty.subst, Ty.subst_congr h a, Ty.subst_congr h b]
  | .forallLayout _ body => by
      simp only [Ty.subst]
      congr 1
      exact Ty.subst_congr (fun l => by cases l <;> simp [LSubst.lift, h]) body

/-- Renaming is substitution by variables. -/
theorem Ty.rename_eq_subst {Δ Δ' : LCtx} (ρ : LRen Δ Δ') :
    (a : Ty Sig Δ) → a.rename ρ = a.subst (fun l => .var (ρ l))
  | .base _ => rfl
  | .atL _ r => by cases r <;> rfl
  | .ref _ r => by cases r <;> rfl
  | .sum a b => by simp only [Ty.rename, Ty.subst, Ty.rename_eq_subst ρ a, Ty.rename_eq_subst ρ b]
  | .prod a b => by simp only [Ty.rename, Ty.subst, Ty.rename_eq_subst ρ a, Ty.rename_eq_subst ρ b]
  | .arr a b => by simp only [Ty.rename, Ty.subst, Ty.rename_eq_subst ρ a, Ty.rename_eq_subst ρ b]
  | .forallLayout _ body => by
      simp only [Ty.rename, Ty.subst]
      congr 1
      rw [Ty.rename_eq_subst ρ.lift body]
      exact Ty.subst_congr (fun l => by cases l <;> rfl) body

/-- Weakening's pulled-back environment is the original one. -/
theorem LSubst.relEnv_weaken (θ : RelParams P sigSem W) {Δ : LCtx} {T : Adt}
    (ρ : RelEnv (P := P) (W := W) Δ) (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep) :
    LSubst.relEnv θ (fun l => .var (LRef.there (T2 := T) l)) (ρ.extend L₁ L₂ R) = ρ := by
  apply RelEnv.ext'
  · intro _ l; rfl
  · intro _ l; rfl
  · intro _ l; exact HEq.rfl

/-- **Weakening** (used by `layoutLam`): a type's relation is unchanged
under a new layout binder. -/
theorem Ty.rel_weaken (θ : RelParams P sigSem W) {Δ : LCtx} {T : Adt}
    (ρ : RelEnv (P := P) (W := W) Δ) (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep)
    (a : Ty Sig Δ) (w : W) :
    Corr (Ty.interp_weaken P sigSem ρ.lenv₁ L₁ a) (Ty.interp_weaken P sigSem ρ.lenv₂ L₂ a)
      (Ty.rel θ (ρ.extend L₁ L₂ R) (a.weaken (T := T)) w) (Ty.rel θ ρ a w) :=
  ((Ty.rel_congr_ty θ (ρ.extend L₁ L₂ R) (Ty.rename_eq_subst _ a) w).trans
      (Ty.rel_subst θ _ (ρ.extend L₁ L₂ R) a w)).trans
    (Ty.rel_congr_env θ (LSubst.relEnv_weaken θ ρ L₁ L₂ R) a w)

end RelCorollaries
