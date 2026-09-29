module

public import proofs.UnconstrainedPACDetection.FormulaPolynomialBudget

@[expose] public section

namespace UnconstrainedPACDetection.FormulaValidBudget
open Complexity Complexity.TM FormulaPolynomialBudget

attribute [local irreducible] FormulaPolynomialBudget.Bounded FormulaWiring.levels
  FormulaWiring.varCount FormulaIndexedGraph.labels FormulaHeaders.clauses
  FormulaHeaderPreparation.occurrences FormulaHeaderPreparation.maximum
  FormulaEntityHeader.value FormulaHeaders.value SAT.CNF.encode

open Lean Meta Elab Tactic in
private partial def solveBudget (g : MVarId) : TacticM Unit := g.withContext do
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOf ``FormulaPolynomialBudget.Bounded do
    throwError "Expected a polynomial budget goal: {target}"
  for name in [``reaction_bits,``header_maximum,``header_entity,``header_reaction,
      ``header_occurrences,``header_clauses,``input_length,``levels,``variable_count,``clauses,``labels] do
    let saved ← saveState
    try
      let goals ← withTransparency .reducible <| g.apply (mkConst name)
      if goals.isEmpty then return
      saved.restore
    catch _ => saved.restore
  let f := target.appArg!
  withLocalDeclD `formula (mkConst ``SAT.CNF) fun x => do
    let body := (mkApp f x).headBeta
    if !body.containsFVar x.fvarId! then
      let goals ← g.apply (mkApp (mkConst ``FormulaPolynomialBudget.constant) body)
      unless goals.isEmpty do throwError "Constant budget left obligations"
      return
    let name ← match body.getAppFn.constName? with
      | some ``HAdd.hAdd | some ``Nat.add | some ``Nat.succ => pure ``FormulaPolynomialBudget.add
      | some ``HMul.hMul | some ``Nat.mul => pure ``FormulaPolynomialBudget.mul
      | some ``HPow.hPow | some ``Nat.pow => pure ``FormulaPolynomialBudget.pow
      | some ``HSub.hSub | some ``Nat.sub => pure ``FormulaPolynomialBudget.sub
      | _ => throwError "Unrecognized budget leaf: {body}"
    let goals ← g.apply (mkConst name)
    for goal in goals do solveBudget goal

open Lean Elab Tactic in
elab "bound_cost" : tactic => do
  let g ← getMainGoal
  solveBudget g
  replaceMainGoal []

theorem polynomial : Bounded FormulaValidWriter.budget := by
  change Bounded (fun φ => FormulaValidWriter.budget φ)
  dsimp only [FormulaValidWriter.budget,FormulaHeaders.bound,FormulaEntityHeader.bound,
    FormulaHeaders.finishBound,FormulaHeaderPreparation.timeBound,FormulaHeaderPreparation.cap,
    FormulaHeaderBridge.budget,FormulaHeaderStaging.cap,FormulaSides.budget,FormulaRows.budget,
    FormulaRowLoop.bodyBudget,FormulaRowGate.budget,FormulaAllTails.budget,FormulaMergedTails.budget,
    FormulaSwitchTailPhase.budget,FormulaSwitchTailLevels.bodyBudget,FormulaSwitchTailPorts.stepBudget,
    FormulaSwitchTailGate.budget,FormulaSwitchTailReentrant.budget,FormulaSwitchTailHeads.budget,
    FormulaAllSwitchHeads.readyBudget,FormulaSwitchHeadLevels.bodyBudget,FormulaSwitchHeadLevels.cap,
    FormulaRailClauseHeads.budget,FormulaAllRailHeads.budget,FormulaRailHeadSigns.budget,
    FormulaExternalTailPhase.budget,FormulaExternalTailPhase.railBudget,FormulaAllVariableTails.budget,
    FormulaAllVariableTails.finishBudget,FormulaVariableTailBody.budget,FormulaAllClauseTails.budget,
    FormulaClauseTailBody.budget,FormulaClauseTailHeads.loopBudget,FormulaRailTailReentrant.budget,
    FormulaRailTailBlock.budget,FormulaRailTailLoop.roundBudget,FormulaVariableTailBound.cap,opBudget]
  bound_cost

end UnconstrainedPACDetection.FormulaValidBudget
