import Lean
import Std.Lean.Expr
import Std.Data.Option.Basic

open Lean Elab Term Meta

namespace Etch.ExpressionTree

/-!
This is based on (and overrides) the core expression tree elaborator from `Lean.Elab.Extra`,
but it has support for reasoning about indices and merging them.
-/


class TypeHasIndex (α : Type _) (i : outParam <| Nat) (I : outParam <| Type _) (β : outParam <| Type _)

-- `base` is the expected base type.
class EnsureBroadcast (σ : List (ℕ × Type _)) (base : Type _) (α : Type _) (β : outParam <| Type _) where
  broadcast : α → β

def _root_.Lean.MVarId.safeAssign (m : MVarId) (v : Expr) : MetaM Unit := do
  if ← m.isAssigned then
    throwError "already assigned"
  if !(← m.isAssignable) then
    throwError "not assignable"
  unless ← isDefEq (← m.getType) (← inferType v) do
    throwError "not defeq"
  m.assign v

structure IndexData where
  iVal : Nat
  i : Expr
  type : Expr
  deriving Inhabited

def reduceIndexNat (i : Expr) : MetaM Nat := do
  let some iVal := (← whnf i).natLit? | throwError "could not reduce i{indentD i}"
  return iVal

/--
Takes a type and uses a `TypeHasIndex` instance to extract `i`, `I`, and `β` in `i//I → β` or analogues.
If no match (or can't reduce `i` to a natural number literal), fails.
-/
def extractTypeIndex (ty : Expr) : MetaM (IndexData × Expr) := do
  let f ← mkConstWithFreshMVarLevels ``TypeHasIndex
  let (#[α, i, I, β], _) ← forallMetaTelescope (← inferType f) | failure
  α.mvarId!.safeAssign ty
  discard <| synthInstance (mkAppN f #[α, i, I, β])
  let iVal ← reduceIndexNat i
  return ({iVal := iVal, i := ← instantiateMVars i, type := ← instantiateMVars I}, ← instantiateMVars β)

/--
Takes a type and returns the recursively extracted indices using `extractTypeIndex`.
-/
partial def extractTypeIndices (ty : Expr) : MetaM (List IndexData × Expr) := do
  let rec go ty (acc : Array IndexData) := do
    let some (data, ty') ← observing? (extractTypeIndex ty) | return (acc, ty)
    go ty' (acc.push data)
  let (indices, ty') ← go ty #[]
  for i in [0:indices.size - 1] do
    unless indices[i]!.iVal < indices[i+1]!.iVal do
      logError m!"Indices out of order:{indentD ty}"
      return ([], ty)
  return (indices.toList, ty')

/-
elab "test_extract% " t:term : term => do
  let e ← elabTermAndSynthesize t none
  let stuff ← extractTypeIndices e
  logInfo m!"stuff = {stuff}"
  return e

def label (i : Nat) (α : Type) := α
instance : TypeHasIndex (label i α → β) i α β where
#check test_extract% (label 1 Nat → label 2 Rat → Int)
-/

/--
Merges index lists.
Unifies types when there are coincidences.

If `preferLeft` is `true`, then does not unify and it prefers `indices1`.
-/
partial def mergeTypeIndices (indices1 indices2 : List IndexData) (preferLeft := false) : MetaM (List IndexData) := do
  match indices1, indices2 with
  | [], _ => return indices2
  | _, [] => return indices1
  | d1 :: indices1', d2 :: indices2' =>
    match compare d1.iVal d2.iVal with
    | .lt => return d1 :: (← mergeTypeIndices indices1' indices2)
    | .gt => return d2 :: (← mergeTypeIndices indices1 indices2')
    | .eq =>
      unless preferLeft do
        discard <| isDefEqGuarded d1.type d2.type
      return d1 :: (← mergeTypeIndices indices1' indices2')

def mkEnsureBroadcast (indices : List IndexData) (base? : Option Expr) (e : Expr) : TermElabM Expr := do
  if indices.isEmpty then
    if let some base := base? then
      if ← isDefEq base (← inferType e) then
        return e
      else
        mkCoe base e
    else
      return e
  else
    -- Note(kmill) This does not handle coercion as well as it could, since it's not deferring
    -- finding a coercion if there are metavariables
    let sort ← inferType indices.head!.type
    let listTy ← mkAppM ``Prod #[.const ``Nat [], sort]
    let list ← mkListLit listTy <| ← indices.mapM fun data => mkAppOptM ``Prod.mk #[Expr.const ``Nat [], sort, data.i, data.type]
    let e ← Term.elabAppArgs (explicit := false) (ellipsis := false) (expectedType? := none)
              (← mkConstWithFreshMVarLevels ``EnsureBroadcast.broadcast)
              #[]
              #[.expr list, .expr (← base?.getDM (inferType e)), .expr e]
    synthesizeSyntheticMVars (mayPostpone := true)
    -- Unfold EnsureBroadcast.broadcast (slight bug: we would like to wait until the end to do this)
    withReducibleAndInstances <| Meta.transform e
      (pre := fun e => do
        let f := e.getAppFn
        if f.isAppOf ``EnsureBroadcast.broadcast then
          if let some e ← unfoldDefinition? e then
            return .visit e.headBeta
        return .continue)

/-!

The elaborator for expression trees of `binop%`, `binop_lazy%`, `leftact%`, `rightact%`, and `unop%` terms.

At a high level, the elaborator tries to solve for a type that each of the operands in the expression tree
can be coerced to, while taking into account the expected type for the entire expression tree.
Once this type is computed (and if it exists), it inserts coercions where needed.

Here are brief descriptions of each of the operator types:
- `binop% f a b` elaborates `f a b` as a binary operator with two operands `a` and `b`,
  and each operand participates in the protocol.
- `binop_lazy% f a b` is like `binop%` but elaborates as `f a (fun () => b)`.
- `unop% f a` elaborates `f a` as a unary operator with one operand `a`, which participates in the protocol.
- `leftact% f a b` elaborates `f a b` as a left action (the `a` operand "acts upon" the `b` operand).
  Only `b` participates in the protocol since `a` can have an unrelated type, for example scalar multiplication of vectors.
- `rightact% f a b` elaborates `f a b` as a right action (the `b` operand "acts upon" the `a` operand).
  Only `a` participates in the protocol since `b` can have an unrelated type.
  This is used by `HPow` since, for example, there are both `Real -> Nat -> Real` and `Real -> Real -> Real`
  exponentiation functions, and we prefer the former in the case of `x ^ 2`, but `binop%` would choose the latter. (#2220)
- There are also `binrel%` and `binrel_no_prop%` (see the docstring for `elabBinRelCore`).

The elaborator works as follows:

1- Expand macros.
2- Convert `Syntax` object corresponding to the `binop%/...` term into a `Tree`.
   The `toTree` method visits nested `binop%/...` terms and parentheses.
3- Synthesize pending metavariables without applying default instances and using the
   `(mayPostpone := true)`.
4- Tries to compute a maximal type for the tree computed at step 2.
   We say a type α is smaller than type β if there is a (nondependent) coercion from α to β.
   We are currently ignoring the case we may have cycles in the coercion graph.
   If there are "uncomparable" types α and β in the tree, we skip the next step.
   We say two types are "uncomparable" if there isn't a coercion between them.
   Note that two types may be "uncomparable" because some typing information may still be missing.
5- We traverse the tree and inject coercions to the "maximal" type when needed.

Recall that the coercions are expanded eagerly by the elaborator.

Properties:

a) Given `n : Nat` and `i : Nat`, it can successfully elaborate `n + i` and `i + n`. Recall that Lean 3
   fails on the former.

b) The coercions are inserted in the "leaves" like in Lean 3.

c) There are no coercions "hidden" inside instances, and we can elaborate
```
axiom Int.add_comm (i j : Int) : i + j = j + i

example (n : Nat) (i : Int) : n + i = i + n := by
  rw [Int.add_comm]
```
Recall that the `rw` tactic used to fail because our old `binop%` elaborator would hide
coercions inside of a `HAdd` instance.

Remarks:

* In the new `binop%` and related elaborators the decision whether a coercion will be inserted or not
  is made at `binop%` elaboration time. This was not the case in the old elaborator.
  For example, an instance, such as `HAdd Int ?m ?n`, could be created when executing
  the `binop%` elaborator, and only resolved much later. We try to minimize this problem
  by synthesizing pending metavariables at step 3.

* For types containing heterogeneous operators (e.g., matrix multiplication), step 4 will fail
  and we will skip coercion insertion. For example, `x : Matrix Real 5 4` and `y : Matrix Real 4 8`,
  there is no coercion `Matrix Real 5 4` from `Matrix Real 4 8` and vice-versa, but
  `x * y` is elaborated successfully and has type `Matrix Real 5 8`.

* The `leftact%` and `rightact%` elaborators are to handle binary operations where only one of
  the arguments participates in the protocol. For example, in `2 ^ n + y` with `n : Nat` and `y : Real`,
  we do not want to coerce `n` to be a real as well, but we do want to elaborate `2 : Real`.
-/

-- kmill
/--
`updateIndex%(i, ty, f) x` -> `f x` while setting index `i` to have type `ty`.
-/
syntax (name := updateIndexStx) "updateIndex%(" term ", " term ", " term ")" term : term

/--
`eraseUnits%(f) x` => `f x` while not propagating `Unit` indices outwards.
Does not propagate indices into `x`.
-/
syntax (name := eraseUnitsStx) "eraseUnits%(" term ")" term : term

private inductive BinOpKind where
  | regular   -- `binop%`
  | lazy      -- `binop_lazy%`
  | leftact   -- `leftact%`
  | rightact  -- `rightact%`
deriving BEq

private inductive Tree where
  /--
  Leaf of the tree.
  We store the `infoTrees` generated when elaborating `val`. These trees become
  subtrees of the infotree nodes generated for `op` nodes.
  -/
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  /--
  `ref` is the original syntax that expanded into `binop%/...`.
  -/
  | binop (ref : Syntax) (kind : BinOpKind) (f : Expr) (lhs rhs : Tree)
  /--
  `ref` is the original syntax that expanded into `unop%`.
  -/
  | unop (ref : Syntax) (f : Expr) (arg : Tree)
  | updateIndex (ref : Syntax) (data : IndexData) (innerType : Expr) (f : Expr) (arg : Tree)
  | eraseUnits (ref : Syntax) (innerIndices : Option (List IndexData)) (f : Expr) (arg : Tree)
  /--
  Used for assembling the info tree. We store this information
  to make sure "go to definition" behaves similarly to notation defined without using `binop%` helper elaborator.
  -/
  | macroExpansion (macroName : Name) (stx stx' : Syntax) (nested : Tree)


private partial def toTree (s : Syntax) : TermElabM Tree := do
  /-
  Remark: ew used to use `expandMacros` here, but this is a bad idiom
  because we do not record the macro expansion information in the info tree.
  We now manually expand the notation in the `go` function, and save
  the macro declaration names in the `op` nodes.
  -/
  let result ← go s
  synthesizeSyntheticMVars (mayPostpone := true)
  return result
where
  go (s : Syntax) := do
    match s with
    | `(binop% $f $lhs $rhs) => processBinOp s .regular f lhs rhs
    | `(binop_lazy% $f $lhs $rhs) => processBinOp s .lazy f lhs rhs
    | `(unop% $f $arg) => processUnOp s f arg
    | `(leftact% $f $lhs $rhs) => processBinOp s .leftact f lhs rhs
    | `(rightact% $f $lhs $rhs) => processBinOp s .rightact f lhs rhs
    | `(($e)) =>
      if hasCDot e then
        processLeaf s
      else
        go e
    | `(updateIndex%($i,$ty,$f) $x) => processUpdateIndex s i ty f x
    | `(eraseUnits%($f) $x) => processEraseUnits s f x
    | _ =>
      withRef s do
        match (← liftMacroM <| expandMacroImpl? (← getEnv) s) with
        | some (macroName, s?) =>
          let s' ← liftMacroM <| liftExcept s?
          withPushMacroExpansionStack s s' do
            return .macroExpansion macroName s s' (← go s')
        | none => processLeaf s

  processBinOp (ref : Syntax) (kind : BinOpKind) (f lhs rhs : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    -- treat corresponding argument as leaf for `leftact/rightact`
    let lhs ← if kind == .leftact then processLeaf lhs else go lhs
    let rhs ← if kind == .rightact then processLeaf rhs else go rhs
    return .binop ref kind f lhs rhs

  processUnOp (ref : Syntax) (f arg : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return .unop ref f (← go arg)

  processUpdateIndex (ref : Syntax) (i ty f x : Syntax) := do
    let ie ← withSynthesize <| elabTermEnsuringType i (Expr.const ``Nat [])
    let iVal ← reduceIndexNat ie
    let tye ← elabType ty
    let fe ← elabTerm f none
    let tree ← go x
    let innerType ← mkFreshExprMVar none
    return .updateIndex ref {iVal := iVal, i := ie, type := tye} innerType fe tree

  processEraseUnits (ref : Syntax) (f arg : Syntax) := do
    let f ← elabTerm f none
    return .eraseUnits ref none f (← go arg)

  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e

-- Auxiliary function used at `analyze`
private def hasCoe (fromType toType : Expr) : TermElabM Bool := do
  if (← getEnv).contains ``CoeT then
    withLocalDeclD `x fromType fun x => do
    match ← coerceSimple? x toType with
    | .some _ => return true
    | .none   => return false
    | .undef  => return false -- TODO: should we do something smarter here?
  else
    return false

private structure AnalyzeResult where
  indices         : List IndexData := [] -- kmill
  max?            : Option Expr := none
  hasUncomparable : Bool := false -- `true` if there are two types `α` and `β` where we don't have coercions in any direction.

private def isUnknown : Expr → Bool
  | .mvar ..        => true
  | .app f _        => isUnknown f
  | .letE _ _ _ b _ => isUnknown b
  | .mdata _ b      => isUnknown b
  | _               => false

private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM (Tree × AnalyzeResult) := do
  let (indices, max?) ←
    match expectedType? with
    | none => pure ([], none)
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      let (indices, expectedType) ← extractTypeIndices expectedType -- kmill
      if isUnknown expectedType then pure ([], none) else pure (indices, some expectedType)
  (go t ).run { indices, max? }
where
  go (t : Tree) : StateRefT AnalyzeResult TermElabM Tree := do
    if (← get).hasUncomparable then
      return t
    else
      match t with
      | .macroExpansion macroName stx stx' nested => return .macroExpansion macroName stx stx' (← go nested)
      | .binop ref .leftact  f lhs rhs => return .binop ref .leftact f lhs (← go rhs)
      | .binop ref .rightact f lhs rhs => return .binop ref .rightact f (← go lhs) rhs
      | .binop ref kind f lhs rhs => return .binop ref kind f (← go lhs) (← go rhs)
      | .unop ref f arg => return .unop ref f (← go arg)
      | .updateIndex ref data innerType f tree => do
        let indices := (← get).indices
        modify fun s => {s with indices := []}
        let tree ← go tree
        let indices' := (← get).indices
        -- Unify innerType with the result
        discard <| mergeTypeIndices [{data with type := innerType}] indices'
        -- Set to the type of the index for `data`
        let indices' ← mergeTypeIndices (preferLeft := true) [data] indices'
        -- Merge the saved indices back in now that the type is updated
        let indices ← mergeTypeIndices indices indices'
        modify fun s => {s with indices := indices}
        return .updateIndex ref data innerType f tree
      | .eraseUnits ref _ f arg => do
        let indices := (← get).indices
        modify fun s => {s with indices := []}
        let arg ← go arg
        let innerIndices := (← get).indices
        let outerIndices := innerIndices.filter fun data => !data.type.isAppOf ``Unit
        let indices ← mergeTypeIndices indices outerIndices
        modify fun s => {s with indices := indices}
        return .eraseUnits ref innerIndices f arg
      | .term ref _ val =>
        let type ← instantiateMVars (← inferType val)
        let (indices', type) ← withRef ref <| extractTypeIndices type
        let newIndices ← mergeTypeIndices (← get).indices indices'
        modify fun s => { s with indices := newIndices } -- kmill
        unless isUnknown type do
          match (← get).max? with
          | none     => modify fun s => { s with max? := type }
          | some max =>
            unless (← withNewMCtxDepth <| isDefEqGuarded max type) do
              if (← hasCoe type max) then
                pure ()
              else if (← hasCoe max type) then
                modify fun s => { s with max? := type }
              else
                trace[Elab.binop] "uncomparable types: {max}, {type}"
                modify fun s => { s with hasUncomparable := true }
        return t

private def mkBinOp (lazy : Bool) (f : Expr) (lhs rhs : Expr) : TermElabM Expr := do
  let mut rhs := rhs
  if lazy then
    rhs ← mkFunUnit rhs
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none) (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def mkUnOp (f : Expr) (arg : Expr) : TermElabM Expr := do
  elabAppArgs f #[] #[Arg.expr arg] (expectedType? := none) (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def toExprCore (t : Tree) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref kind f lhs rhs =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo .anonymous ref) do
      mkBinOp (kind == .lazy) f (← toExprCore lhs) (← toExprCore rhs)
  | .unop ref f arg =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo .anonymous ref) do
      mkUnOp f (← toExprCore arg)
  | .updateIndex ref _ _ f arg =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo .anonymous ref) do
      mkUnOp f (← toExprCore arg)
  | .eraseUnits ref _ f arg =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo .anonymous ref) do
      mkUnOp f (← toExprCore arg)
  | .macroExpansion macroName stx stx' nested =>
    withRef stx <| withInfoContext' stx (mkInfo := mkTermInfo macroName stx) do
      withMacroExpansion stx stx' do
        toExprCore nested

/--
  Auxiliary function to decide whether we should coerce `f`'s argument to `maxType` or not.
  - `f` is a binary operator.
  - `lhs == true` (`lhs == false`) if are trying to coerce the left-argument (right-argument).
  This function assumes `f` is a heterogeneous operator (e.g., `HAdd.hAdd`, `HMul.hMul`, etc).
  It returns true IF
  - `f` is a constant of the form `Cls.op` where `Cls` is a class name, and
  - `maxType` is of the form `C ...` where `C` is a constant, and
  - There are more than one default instance. That is, it assumes the class `Cls` for the heterogeneous operator `f`, and
    always has the monomorphic instance. (e.g., for `HAdd`, we have `instance [Add α] : HAdd α α α`), and
  - If `lhs == true`, then there is a default instance of the form `Cls _ (C ..) _`, and
  - If `lhs == false`, then there is a default instance of the form `Cls (C ..) _ _`.

  The motivation is to support default instances such as
  ```
  @[default_instance high]
  instance [Mul α] : HMul α (Array α) (Array α) where
    hMul a as := as.map (a * ·)

  #eval 2 * #[3, 4, 5]
  ```
  If the type of an argument is unknown we should not coerce it to `maxType` because it would prevent
  the default instance above from being even tried.
-/
private def hasHeterogeneousDefaultInstances (f : Expr) (maxType : Expr) (lhs : Bool) : MetaM Bool := do
  let .const fName .. := f | return false
  let .const typeName .. := maxType.getAppFn | return false
  let className := fName.getPrefix
  let defInstances ← getDefaultInstances className
  if defInstances.length ≤ 1 then return false
  for (instName, _) in defInstances do
    if let .app (.app (.app _heteroClass lhsType) rhsType) _resultType :=
        (← getConstInfo instName).type.getForallBody then
      if  lhs && rhsType.isAppOf typeName then return true
      if !lhs && lhsType.isAppOf typeName then return true
  return false

/--
  Return `true` if polymorphic function `f` has a homogenous instance of `maxType`.
  The coercions to `maxType` only makes sense if such instance exists.

  For example, suppose `maxType` is `Int`, and `f` is `HPow.hPow`. Then,
  adding coercions to `maxType` only make sense if we have an instance `HPow Int Int Int`.
-/
private def hasHomogeneousInstance (f : Expr) (maxType : Expr) : MetaM Bool := do
  let .const fName .. := f | return false
  let className := fName.getPrefix
  try
    let inst ← mkAppM className #[maxType, maxType, maxType]
    return (← trySynthInstance inst) matches .some _
  catch _ =>
    return false

mutual
  /--
    Try to coerce elements in the `t` to `maxType` when needed.
    If the type of an element in `t` is unknown we only coerce it to `maxType` if `maxType` does not have heterogeneous
    default instances. This extra check is approximated by `hasHeterogeneousDefaultInstances`.

    Remark: If `maxType` does not implement heterogeneous default instances, we do want to assign unknown types `?m` to
    `maxType` because it produces better type information propagation. Our test suite has many tests that would break if
    we don't do this. For example, consider the term
    ```
    eq_of_isEqvAux a b hsz (i+1) (Nat.succ_le_of_lt h) heqv.2
    ```
    `Nat.succ_le_of_lt h` type depends on `i+1`, but `i+1` only reduces to `Nat.succ i` if we know that `1` is a `Nat`.
    There are several other examples like that in our test suite, and one can find them by just replacing the
    `← hasHeterogeneousDefaultInstances f maxType lhs` test with `true`


    Remark: if `hasHeterogeneousDefaultInstances` implementation is not good enough we should refine it in the future.
  -/
  private partial def applyCoe (t : Tree) (indices : List IndexData) (maxType? : Option Expr) (isPred : Bool) : TermElabM Tree := do
    go t indices none false isPred
  where
    go (t : Tree) (indices : List IndexData) (f? : Option Expr) (lhs : Bool) (isPred : Bool) : TermElabM Tree := do
      match t with
      | .binop ref .leftact f lhs rhs =>
        return .binop ref .leftact f lhs (← go rhs indices none false false)
      | .binop ref .rightact f lhs rhs =>
        return .binop ref .rightact f (← go lhs indices none false false) rhs
      | .binop ref kind f lhs rhs =>
        /-
          We only keep applying coercions to `maxType` if `f` is predicate or
          `f` has a homogenous instance with `maxType`. See `hasHomogeneousInstance` for additional details.

          Remark: We assume `binrel%` elaborator is only used with homogenous predicates.
        -/
        if let some maxType := maxType? then
          if (← pure isPred <||> hasHomogeneousInstance f maxType) then
            return .binop ref kind f (← go lhs indices f true false) (← go rhs indices f false false)
          unless indices.isEmpty do
          logErrorAt ref "(kmill, unhandled) no homogeneous instances, but there are indices"
        let r ← withRef ref do
          mkBinOp (kind == .lazy) f (← toExpr lhs none) (← toExpr rhs none)
        let infoTrees ← getResetInfoTrees
        return .term ref infoTrees r
      | .unop ref f arg =>
        return .unop ref f (← go arg indices none false false)
      | .updateIndex ref data innerType f arg =>
        -- Create inner indices using innerType
        let indices' ← mergeTypeIndices (preferLeft := true) [{data with type := innerType}] indices
        let arg ← go arg indices' none false false
        return .updateIndex ref data innerType f arg
      | .eraseUnits ref innerIndices? f arg =>
        let innerIndices := innerIndices?.get!
        let arg ← go arg innerIndices none false false
        let outerIndices := innerIndices.filter fun data => !data.type.isAppOf ``Unit
        if outerIndices.length != indices.length then
          -- Need to insert broadcast
          throwError "unimplemented(kmill): eraseUnits needs to broadcast"
        else
          return .eraseUnits ref innerIndices f arg
      | .term ref trees e =>
        let (indices', type) ← extractTypeIndices (← instantiateMVars (← inferType e))
        trace[Elab.binop] "visiting {e} : {type} =?= {maxType?}"
        if isUnknown type then
          if let some maxType := maxType? then
            if let some f := f? then
              if (← hasHeterogeneousDefaultInstances f maxType lhs) then
                unless indices.isEmpty do
                  logErrorAt ref "(kmill, unhandled) hasHeterogeneousDefaultInstances"
                -- See comment at `hasHeterogeneousDefaultInstances`
                return t
        if indices'.length == indices.length then -- kmill
          if let some maxType := maxType? then
            if (← isDefEqGuarded maxType type) then
              return t
          else
            return t
        trace[Elab.binop] "added coercion: {e}: {type} => {maxType?}"
        withRef ref <| return .term ref trees (← mkEnsureBroadcast indices maxType? e)
      | .macroExpansion macroName stx stx' nested =>
        withRef stx <| withPushMacroExpansionStack stx stx' do
          return .macroExpansion macroName stx stx' (← go nested indices f? lhs isPred)

  private partial def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
    let (tree, r) ← analyze tree expectedType?
    trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
    if r.indices.isEmpty && (r.hasUncomparable || r.max?.isNone) then
      let result ← toExprCore tree
      ensureHasType expectedType? result
    else
      let result ← toExprCore (← applyCoe tree r.indices r.max? (isPred := false))
      trace[Elab.binop] "result: {result}"
      ensureHasType expectedType? result

end

def elabOp : TermElab := fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

@[term_elab binop] def elabBinOp : TermElab := elabOp
@[term_elab binop_lazy] def elabBinOpLazy : TermElab := elabOp
@[term_elab leftact] def elabLeftact : TermElab := elabOp
@[term_elab rightact] def elabRightact : TermElab := elabOp
@[term_elab unop] def elabUnOp : TermElab := elabOp
@[term_elab updateIndexStx] def elabUpdateIndex : TermElab := elabOp
@[term_elab eraseUnitsStx] def elabEraseUnits : TermElab := elabOp

/--
  Elaboration functions for `binrel%` and `binrel_no_prop%` notations.
  We use the infrastructure for `binop%` to make sure we propagate information between the left and right hand sides
  of a binary relation.

  - `binrel% R x y` elaborates `R x y` using the `binop%/...` expression trees in both `x` and `y`.
    It is similar to how `binop% R x y` elaborates but with a significant difference:
    it does not use the expected type when computing the types of the operads.
  - `binrel_no_prop% R x y` elaborates `R x y` like `binrel% R x y`, but if the resulting type for `x` and `y`
    is `Prop` they are coerced to `Bool`.
    This is used for relations such as `==` which do not support `Prop`, but we still want
    to be able to write `(5 > 2) == (2 > 1)` for example.
-/
def elabBinRelCore (noProp : Bool) (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=  do
  match (← resolveId? stx[1]) with
  | some f => withSynthesizeLight do
    /-
    We used to use `withSynthesize (mayPostpone := true)` here instead of `withSynthesizeLight` here.
    Recall that `withSynthesizeLight` is equivalent to `withSynthesize (mayPostpone := true) (synthesizeDefault := false)`.
    It seems too much to apply default instances at binary relations. For example, we cannot elaborate
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (a ≥ 0) [a] []
    ```
    The problem is that when elaborating `a ≥ 0` we don't know yet that `a` is an `Int`.
    Then, by applying default instances, we apply the default instance to `0` that forces it to become an `Int`,
    and Lean infers that `a` has type `Nat`.
    Then, later we get a type error because `as` is `List Int` instead of `List Nat`.
    This behavior is quite counterintuitive since if we avoid this elaborator by writing
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (GE.ge a 0) [a] []
    ```
    everything works.
    However, there is a drawback of using `withSynthesizeLight` instead of `withSynthesize (mayPostpone := true)`.
    The following cannot be elaborated
    ```
    have : (0 == 1) = false := rfl
    ```
    We get a type error at `rfl`. `0 == 1` only reduces to `false` after we have applied the default instances that force
    the numeral to be `Nat`. We claim this is defensible behavior because the same happens if we do not use this elaborator.
    ```
    have : (BEq.beq 0 1) = false := rfl
    ```
    We can improve this failure in the future by applying default instances before reporting a type mismatch.
    -/
    let lhs ← withRef stx[2] <| toTree stx[2]
    let rhs ← withRef stx[3] <| toTree stx[3]
    let tree := .binop stx .regular f lhs rhs
    let (tree, r) ← analyze tree none
    trace[Elab.binrel] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      unless r.indices.isEmpty do
        throwError "(kmill, unimplemented) has indices for rel"
      -- Use default elaboration strategy + `toBoolIfNecessary`
      let lhs ← toExprCore lhs
      let rhs ← toExprCore rhs
      let lhs ← toBoolIfNecessary lhs
      let rhs ← toBoolIfNecessary rhs
      let lhsType ← inferType lhs
      let rhs ← ensureHasType lhsType rhs
      elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] expectedType? (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
    else
      let mut maxType := r.max?.get!
      /- If `noProp == true` and `maxType` is `Prop`, then set `maxType := Bool`. `See toBoolIfNecessary` -/
      if noProp then
        if (← withNewMCtxDepth <| isDefEq maxType (mkSort levelZero)) then
          maxType := Lean.mkConst ``Bool
      let result ← toExprCore (← applyCoe tree r.indices maxType (isPred := true))
      trace[Elab.binrel] "result: {result}"
      return result
  | none   => throwUnknownConstant stx[1].getId
where
  /-- If `noProp == true` and `e` has type `Prop`, then coerce it to `Bool`. -/
  toBoolIfNecessary (e : Expr) : TermElabM Expr := do
    if noProp then
      -- We use `withNewMCtxDepth` to make sure metavariables are not assigned
      if (← withNewMCtxDepth <| isDefEq (← inferType e) (mkSort levelZero)) then
        return (← ensureHasType (Lean.mkConst ``Bool) e)
    return e

@[term_elab binrel] def elabBinRel : TermElab := elabBinRelCore false

@[term_elab binrel_no_prop] def elabBinRelNoProp : TermElab := elabBinRelCore true
