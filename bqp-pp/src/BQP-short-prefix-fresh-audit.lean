import «BQP-short-machine-prefix»
set_option maxRecDepth 30000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPShortMachine.long_prefix, ``BQPShortMachine.drain_run] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_SHORT_PREFIX_CHECKED {name}; axioms {axs}"
