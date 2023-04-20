import Etch.Stream3

namespace Etch.Deriving.AttrOrder

open Lean Elab Command Term Meta

structure Options (α : Type u) where
  (order : List α)
  (localDecl : Bool := false)
structure OptionsT where
  (order : TSyntaxArray `term)
  (localDecl : Bool)

private def mkOptions (declName : Name) (stx : TSyntax ``Parser.Term.structInst) : TermElabM OptionsT := do
  -- First do a type check just to be sure
  let expectedType ← elabType (← `($(mkIdent ``Options) $(mkIdent declName)))
  let expr ← StructInst.elabStructInst stx.raw (some expectedType)
  let typ ← inferType expr
  trace[Elab.Deriving.attr_order_total] m!"elabStructInst returns {expr}; with type {typ}; expected {expectedType}"

  -- Extract elements from syntax.
  match stx.raw with
  | `(Parser.Term.structInst| { $fields* })
  | `(Parser.Term.structInst| { $fields* : $_ }) => do
    let mut order := none
    let mut localDecl := false
    for field in fields.getElems do
      match field with
      | `(Parser.Term.structInstField| order := [$elems,*]) =>
        order := some elems.getElems
      | `(Parser.Term.structInstField| order := $_) =>
        throwErrorAt field "incorrect argument format; must be order := [attr1, attr2, …]"
      | `(Parser.Term.structInstField| localDecl := true) =>
        localDecl := true
      | `(Parser.Term.structInstField| localDecl := false) =>
        localDecl := false
      | `(Parser.Term.structInstField| localDecl := $v) =>
        throwErrorAt v "incorrect argument format; must be true or false"
      | _ => throwErrorAt field "unknown field"
    match order with
    | some elems => return { order := elems, localDecl : OptionsT }
    | none => throwErrorAt stx "missing order field"
  | _ => throwError "incorrect argument format; must be \{ order := [attr1, attr2, …] }"

def mkOrder (declName : Name) (options : OptionsT) : CommandElabM Bool := do
  let id := mkIdent declName
  let prepareName (n : String) : MacroM Name :=
    if options.localDecl then
      -- Logic similar to `Lean.Elab.Command.mkInstanceName`
      let rec getSuffix (m : Name) := match m with
      | .anonymous => ""
      | .str m "" => getSuffix m
      | .str _ s => s
      | .num m _ => getSuffix m
      let n := if "inst".isPrefixOf n then
                 n ++ (getSuffix declName.eraseMacroScopes).capitalize
               else
                 n
      mkUnusedBaseName <| Name.mkSimple n
    else
      pure <| `_root_ ++ declName.str n
  let ordID          := mkIdent <| (← liftMacroM <| prepareName "order")
  let instOrdID      := mkIdent <| (← liftMacroM <| prepareName "instAttrOrder")
  let ordHereID      := mkIdent <| (← liftMacroM <| prepareName "orderHere")
  let instOrdTotalID := mkIdent <| (← liftMacroM <| prepareName "instAttrOrderTotal")

  let ord ← `(command|
    @[reducible] def $ordID : $(mkIdent ``Shape) $id :=
      ⟨[$(options.order):term,*], by decide⟩)
  let instOrd ← `(command|
    @[reducible] instance $instOrdID:ident : $(mkIdent ``AttrOrder) $id :=
      ⟨$ordID⟩)

  let mut ordHereCases := #[]
  for arg in options.order do
    let alt ← `(Parser.Term.matchAltExpr| | $arg => $(mkIdent ``List.Find.here))
    ordHereCases := ordHereCases.push alt
  let ordHere ← `(command|
    def $ordHereID : ∀ (i : $id), $(mkIdent ``List.Here) i ($(mkIdent ``Shape.val) ($(mkIdent ``AttrOrder.order) (self := $instOrdID)))
    $ordHereCases:matchAlt*)

  let instOrdTotal ← `(command|
    instance $instOrdTotalID:ident : $(mkIdent ``AttrOrderTotal) $id :=
      ⟨$ordHereID⟩)

  let cmds := #[ord, instOrd, ordHere, instOrdTotal]
  for cmd in cmds do
    trace[Elab.Deriving.attr_order_total] cmd
    elabCommand cmd
  return true

def mkOrderTotalInstanceHandler (declNames : Array Name) (args? : Option (TSyntax ``Parser.Term.structInst)) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported yet
  else if let some args := args? then
    let opts ← liftTermElabM <| mkOptions declNames[0]! args
    mkOrder declNames[0]! opts
  else
    return false -- don't support automatically forming an order yet

initialize
  registerDerivingHandlerWithArgs ``AttrOrderTotal mkOrderTotalInstanceHandler
  registerTraceClass `Elab.Deriving.attr_order_total

end Etch.Deriving.AttrOrder
