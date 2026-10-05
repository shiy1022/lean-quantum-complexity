import «BQP-short-machine»
set_option maxRecDepth 30000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPShortMachine.machine, ``BQPShortMachine.delegated_run,
    ``BQPShortMachine.embedded_halt, ``BQPShortMachine.delegated_outputs] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_SHORT_MACHINE_CHECKED {name}; axioms {axs}"
