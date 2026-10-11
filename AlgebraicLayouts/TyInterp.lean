import AlgebraicLayouts.Syntax

variable {Sig : Adt → Type}

abbrev PolyEnv (n : Nat) := Fin n → Type

class Backend (P : Type) where
  Val   : Base → Type
  const : {b : Base} → b.interp → Val b
  add   : Val .int → Val .int → Val .int
  eq    : Val .int → Val .int → Val .bool
  cond  : Val .bool → P → P → P
  unit : P
  op : P → P → P

variable (P : Type) [Backend P]

def Poly.interp (env : PolyEnv n) (p : Poly n) : Type :=
  match p with
  | .base b => b.interp
  | .var i => env i
  | .sum a b => a.interp env ⊕ b.interp env
  | .prod a b => a.interp env × b.interp env

def Poly.interp1 {n : Nat} (env : Fin n → Type 1) : Poly n → Type 1
  | .base b => ULift (Backend.Val P b)
  | .var i => env i
  | .sum a b => a.interp1 env ⊕ b.interp1 env
  | .prod a b => a.interp1 env × b.interp1 env

def Adt.layer : Adt → Type 1 → Type 1
| .plain p, _ => p.interp1 P Fin.elim0
| .mu body, A => body.interp1 P (fun _ => A)

inductive MuVal (body : Poly 1) : Poly 1 → Type where
| base {b : Base} (x : b.interp) : MuVal body (.base b)
| roll {i : Fin 1} (v : MuVal body body) : MuVal body (.var i)
| inl {a b : Poly 1} (v : MuVal body a) : MuVal body (.sum a b)
| inr {a b : Poly 1} (v : MuVal body b) : MuVal body (.sum a b)
| pair {a b : Poly 1} (v : MuVal body a) (w : MuVal body b) : MuVal body (.prod a b)

def Adt.interp : Adt → Type
| .plain p => p.interp Fin.elim0
| .mu body => MuVal body body

/-- `μα. 1 + (Int × α)` and the list [7, 9]. -/
def intList : Adt := .mu (.sum (.base .unit) (.prod (.base .int) (.var 0)))
def ex : intList.interp :=
  .inr (.pair (.base (7 : Int)) (.roll (.inr (.pair (.base (9 : Int)) (.roll (.inl (.base ())))))))

structure Dict (T : Adt) (A : Type) : Type 1 where
  close_ : T.layer P (ULift A) → (A → P) → P   -- build one layer, pass its handle on
  open_  : (T.layer P (ULift A) → P) → A → P   -- case-split one layer

structure SemLayout (T : Adt) : Type 1 where
  Rep  : Type
  dict : Dict P T Rep

abbrev LEnv (Δ : LCtx) : Type 1 :=
  ∀ {T : Adt}, LRef Δ T → SemLayout P T

def LEnv.extend {Δ : LCtx} {T : Adt} (lenv : LEnv P Δ) (L : SemLayout P T) : LEnv P (Δ.extend T)
| _, .here => L
| _, .there l => lenv l

-- Meaning of the concrete layouts named in the signature
variable (sigSem : ∀ {T : Adt}, Sig T → SemLayout P T)

def LayoutRef.interp {Δ} {T} (lenv : LEnv P Δ) : LayoutRef Sig Δ T → SemLayout P T
| .var l => lenv l
| .concrete c => sigSem c

abbrev Comp (B : Type 1) : Type 1 := (B → ULift.{1} P) → ULift.{1} P

def Ty.interp {Δ : LCtx} : (Ty Sig Δ) → LEnv P Δ → Type 1
| .base b, _ => ULift (Backend.Val P b)
| .atL _ l, lenv => ULift (l.interp P sigSem lenv).Rep
| .ref _ l, lenv => ULift (l.interp P sigSem lenv).Rep
| .sum a b, lenv => a.interp lenv ⊕ b.interp lenv
| .prod a b, lenv => a.interp lenv × b.interp lenv
| .arr a b, lenv => a.interp lenv → Comp P (b.interp lenv)
| .forallLayout T body, lenv => (L : SemLayout P T) → Comp P (body.interp (lenv.extend P L))

def LSubst.interp (σ : LSubst Sig Δ Δ') (lenv' : LEnv P Δ') : LEnv P Δ :=
  fun l => (σ l).interp P sigSem lenv'

def LRen.interp {Δ Δ'} (ρ : LRen Δ Δ') (lenv' : LEnv P Δ') : LEnv P Δ :=
  fun l => lenv' (ρ l)

/-- The meaning of a layout reference stays the same when weakened -/
theorem LayoutRef.interp_weaken {Δ : LCtx} {T T' : Adt} (η : LEnv P Δ) (L' : SemLayout P T')
    (L : LayoutRef Sig Δ T) :
    (L.rename (fun l => LRef.there (T2 := T') l)).interp P sigSem (η.extend P L')
      = L.interp P sigSem η := by
  cases L <;> rfl

theorem LSubst.interp_lift (σ : LSubst Sig Δ Δ') (lenv' : LEnv P Δ') (L : SemLayout P T)
    {T'} (l : LRef (Δ.extend T) T') :
    LSubst.interp P sigSem (σ.lift) (lenv'.extend P L) l = LEnv.extend P (LSubst.interp P sigSem σ lenv') L l := by
  cases l with
  | here => rfl
  | there l => exact LayoutRef.interp_weaken P sigSem lenv' L (σ l)

/-- Pointwise equal environments give equal interpretations -/
theorem Ty.interp_congr {Δ : LCtx} {η₁ η₂ : LEnv P Δ}
    (h : ∀ {T : Adt} (l : LRef Δ T), η₁ l = η₂ l) (a : Ty Sig Δ) :
    a.interp P sigSem η₁ = a.interp P sigSem η₂ := by
  induction a with
  | base b => rfl
  | atL T l => cases l with
    | var l => simp only [Ty.interp, LayoutRef.interp, h]
    | concrete c => rfl
  | ref T l => cases l with
      | var l => simp only [Ty.interp, LayoutRef.interp, h]
      | concrete c => rfl
  | sum a b aIH bIH => simp only [Ty.interp, aIH h, bIH h]
  | prod a b aIH bIH => simp only [Ty.interp, aIH h, bIH h]
  | arr a b aIH bIH => simp only [Ty.interp, aIH h, bIH h]
  | forallLayout T body bodyIH =>
      exact congrArg (fun F : SemLayout P T → Type 1 => (L : SemLayout P T) → F L)
        (funext fun L =>
          congrArg (Comp P)
            (bodyIH (η₁ := η₁.extend P L) (η₂ := η₂.extend P L) fun l => by
              cases l with
              | here => rfl
              | there l => exact h l))

theorem Ty.interp_subst (σ : LSubst Sig Δ Δ') (lenv' : LEnv P Δ') (a : Ty Sig Δ) :
    (a.subst σ).interp P sigSem lenv' = a.interp P sigSem (σ.interp P sigSem lenv') := by
  induction a generalizing Δ' with
  | base b => rfl
  | atL T l => cases l <;> rfl
  | ref T l => cases l <;> rfl
  | sum a b aIH bIH => simp only [Ty.subst, Ty.interp, aIH, bIH]
  | prod a b aIH bIH => simp only [Ty.subst, Ty.interp, aIH, bIH]
  | arr a b aIH bIH => simp only [Ty.subst, Ty.interp, aIH, bIH]
  | forallLayout T body bodyIH =>
      exact congrArg (fun F : SemLayout P T → Type 1 => (L : SemLayout P T) → F L)
        (funext fun L => by
          rw [bodyIH]
          rw [← Ty.interp_congr P sigSem (LSubst.interp_lift P sigSem σ lenv' L) body]
        )

theorem ViewPoly.interp_eq {Δ} (p : Poly n) (r : LayoutRef Sig Δ T) (lenv : LEnv P Δ) :
    (ViewPoly p r).interp P sigSem lenv
      =
    p.interp1 P (fun _ => ULift (r.interp P sigSem lenv).Rep) := by
  induction p with
  | base b => rfl
  | var i => rfl
  | sum a b aIH bIH => simp only [ViewPoly, Ty.interp, Poly.interp1, aIH, bIH]
  | prod a b aIH bIH => simp only [ViewPoly, Ty.interp, Poly.interp1, aIH, bIH]

theorem View.interp_eq (r : LayoutRef Sig Δ T) (lenv : LEnv P Δ) :
    (View T r).interp P sigSem lenv = T.layer P (ULift (r.interp P sigSem lenv).Rep) := by
  cases T with
  | plain p =>
      change (ViewPoly p r).interp P sigSem lenv = p.interp1 P Fin.elim0
      rw [ViewPoly.interp_eq P sigSem p r lenv]
      exact congrArg (fun env : Fin 0 → Type 1 => p.interp1 P env)
        (funext fun i => Fin.elim0 i)
  | mu p => exact ViewPoly.interp_eq P sigSem p r lenv

theorem Ty.interp_rename (ρ : LRen Δ Δ') (lenv' : LEnv P Δ') (a : Ty Sig Δ) :
    (a.rename ρ).interp P sigSem lenv' = a.interp P sigSem (ρ.interp P lenv') := by
  induction a generalizing Δ' with
  | base b => rfl
  | atL T l => cases l <;> rfl
  | ref T l => cases l <;> rfl
  | sum a b aIH bIH => simp only [Ty.rename, Ty.interp, aIH, bIH]
  | prod a b aIH bIH => simp only [Ty.rename, Ty.interp, aIH, bIH]
  | arr a b aIH bIH => simp only [Ty.rename, Ty.interp, aIH, bIH]
  | forallLayout T body bodyIH =>
     exact congrArg (fun F : SemLayout P T → Type 1 => (L : SemLayout P T) → F L)
        (funext fun L => congrArg (Comp P)
          ((bodyIH _ _).trans
            (Ty.interp_congr P sigSem (fun l => by cases l <;> rfl) body)))

theorem Ty.interp_weaken {Δ : LCtx} {T : Adt} (lenv : LEnv P Δ) (L : SemLayout P T) (a : Ty Sig Δ) :
    (a.weaken (T := T)).interp P sigSem (lenv.extend P L) = a.interp P sigSem lenv := by
  rw [Ty.weaken, Ty.interp_rename]; rfl

theorem Ty.interp_instantiate {Δ : LCtx} {T : Adt} (lenv : LEnv P Δ)
          (body : Ty Sig (Δ.extend T)) (L : LayoutRef Sig Δ T) :
    (body.instantiate L).interp P sigSem lenv
      =
    body.interp P sigSem (lenv.extend P (L.interp P sigSem lenv)) := by
  rw [Ty.instantiate, Ty.interp_subst]
  apply Ty.interp_congr
  intro T' l; cases l <;> rfl
