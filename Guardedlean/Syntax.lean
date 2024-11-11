declare_syntax_cat ToTExpr
syntax "[" term "]" : ToTExpr
syntax "fix" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax "fun" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax ToTExpr ToTExpr : ToTExpr
syntax ident : ToTExpr
syntax ToTExpr "::" ToTExpr : ToTExpr
syntax "adv(" ToTExpr ")" : ToTExpr
syntax "delay(" ToTExpr ")" : ToTExpr
syntax "(" ToTExpr ")" : ToTExpr
syntax "head(" ToTExpr ")" : ToTExpr
syntax "box(" ToTExpr ")" : term

structure Ctxt where
  here : Nat := 0
  previous : List Nat := []

def Ctxt.bindvar (c : Ctxt) : Ctxt where
  here := c.here +1
  previous := c.previous

def Ctxt.tick (c : Ctxt) : Ctxt where
  here := 0
  previous := c.here :: c.previous

def Ctxt.untick (c : Ctxt) : Option Ctxt :=
  match c.previous with
  | [] => none
  | x :: xs => some {here := x, previous := xs}

def Ctxt.size (c : Ctxt) : Nat := c.previous.foldl (· + ·) c.here

open Lean Elab Term
def lookup (vars : Ctxt) (index : Nat) : TermElabM (TSyntax `term) :=
  match vars, index with
  | ⟨0,[]⟩ , _ => throwError "No variables in scope"
  | ⟨0, x :: xs⟩ , i => do
    let inner ← lookup ⟨x, xs⟩ i
    `(ToTType.comp ToTType.prev $inner)
  | ⟨k+1, xs⟩ , 0 => `(ToTType.snd)
  | ⟨k+1, xs⟩ , n+1 => do
    let inner ← lookup ⟨k, xs⟩ n
    `(ToTType.comp ToTType.fst $inner)

partial def elabToTExpr (vars : Ctxt) (levels : NameMap Nat) (stx : TSyntax `ToTExpr ) : TermElabM (TSyntax `term) :=
  -- dbg_trace stx
  match stx with
  | `(ToTExpr|[$t]) => `(ToTType.const $t)
  | `(ToTExpr|fix ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(fixp (X := $A) $bodyExpr)
  | `(ToTExpr|fun ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(ToTType.lam (B := $A) $bodyExpr)
  | `(ToTExpr|$e1 $e2) => do
    let f <- elabToTExpr vars levels e1
    let a <- elabToTExpr vars levels e2
    `(ToTType.comp (ToTType.pair $f $a) ToTType.ev)
  | `(ToTExpr|$x:ident) => do
    if let some n := levels.find? x.getId then lookup vars (vars.size-n-1)
     else throwErrorAt x "Not a ToT variable"
  | `(ToTExpr|$h :: $t) => do
    let hd <- elabToTExpr vars levels h
    let tl <- elabToTExpr vars levels t
    `(ToTType.Str.cons $hd $tl)
  | `(ToTExpr|adv($d)) => do
    if let some vars' := vars.untick then
      let e <- elabToTExpr vars' levels d -- Todo: Add projection: iterate fst vars.here times
      `(ToTType.adv $e)
    else throwErrorAt stx "No ticks in the context"
  | `(ToTExpr|delay($d)) => do
    let e <- elabToTExpr vars.tick levels d
    `(ToTType.delay $e)
  | `(ToTExpr|head($d)) => do
    let arg <- elabToTExpr vars levels d
    `(ToTType.Str.headFun $arg)
  | `( ToTExpr|($t)) => elabToTExpr vars levels t
  | _ => throwErrorAt stx "Did not understand"



---------- TESTING -----------

elab_rules : term
  | `( box($t) ) => do
    let f <- elabToTExpr {} {} t
    dbg_trace Syntax.prettyPrint f
    elabTerm f none

#eval (box([4+3]) : Unit ⤳ Nat).setMorph 0 ()

def pretty_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::tl)
def ugly_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::delay(adv(tl)))
def blah : Unit ⤳ Nat := box((fun (x : Nat) => x) [12])
def blahblah : Unit ⤳ Nat := box(((fun (x : Nat) => (fun (y: Nat) => y)) [12]) [14])
def pretty_from : Unit ⤳ (ToTType.Str Nat) :=
--   box(fun (n : _) => fix (f : _) => n ::(f ([ToTType.deltaFun (Nat.succ)] n)))
   box((fix (f : ToTType.Fun Nat (ToTType.Str Nat)) => fun (n : _) => n ::delay(adv(f) n))[5])


#eval blah.val 0 ()
#eval blahblah.val 0 ()
--#eval ToTType.Str.take pretty_zeros 8
