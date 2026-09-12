import CodeLib.SepLogic.CostedSteps

/-! # Work bounds for every prefix of a terminating execution

Authoritative step determinism and the absence of steps from a normal terminal
state let one complete numerical certificate bound every costed execution from
the same initial configuration. No length restriction on the prefix is assumed.
-/

namespace Wasm.SmallStep.CostedSteps

/-- Every finite execution from the same initial state costs at most a complete
terminal execution. All charges are natural numbers; positivity is unnecessary. -/
theorem amount_le_terminal {charge : StepCost α} {initial final reached : Config α}
    {fullTrace trace : List StepKind}
    {amount prefixAmount : Nat}
    (complete : CostedSteps charge initial fullTrace final amount)
    (terminal : ∀ kind next, ¬ Step final kind next)
    (partialExecution : CostedSteps charge initial trace reached prefixAmount) :
    prefixAmount≤amount := by
  induction complete generalizing trace reached prefixAmount with
  | refl =>
    cases partialExecution with
    | refl => exact Nat.le_refl _
    | cons head _ => exact False.elim (terminal _ _ head)
  | cons first _ ih =>
    cases partialExecution with
    | refl => exact Nat.zero_le _
    | cons other rest =>
      obtain ⟨rfl,rfl⟩ := step_deterministic first other
      exact Nat.add_le_add_left (ih terminal rest) _

theorem amount_le_normal_return {charge : StepCost α} {initial reached : Config α}
    {fullTrace trace : List StepKind} {values : List Value} {store : MachineStore α}
    {amount prefixAmount : Nat}
    (complete : CostedSteps charge initial fullTrace ⟨.done values,store⟩ amount)
    (partialExecution : CostedSteps charge initial trace reached prefixAmount) :
    prefixAmount≤amount :=
  complete.amount_le_terminal (by intro kind next step; cases step) partialExecution

end Wasm.SmallStep.CostedSteps
