import Project.Mergesort.Proof

/-!
# Total correctness of the compiled merge-sort export

The semantic export initializer selects the generated function body. Reuse
its total outcome proof with an empty caller stack, initialize the actual
resources, and expose the result through the named-export specification.
-/

namespace Project.Mergesort.TotalProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Representations
open Project.Mergesort.Contracts
open Project.Mergesort.Adequacy
open scoped Wasm.SmallStep.Outcome

/-- The body configuration selected by the semantic export initializer, with
the canonical store used by the existing call-site adequacy proof. -/
abbrev exportConfig (input : Spec.Input) : Config Universal.State :=
  { expr := .running
      ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
        0, [], [], []⟩
    store := (entryConfig input).store }

/-- Initialization resolves the actual export name and checks its signature. -/
theorem startExportConfig_eq (input : Spec.Input) :
    startExportConfig? (Universal.envFor Project.Mergesort.module)
      Project.Mergesort.module "mergesort" (Spec.args input) =
      some (exportConfig input) := by
  rw [Spec.args, startExportConfig?_ofHost_zero (by decide :
    ZeroArgumentExport Project.Mergesort.module "mergesort")]
  rfl

/-- Construct a terminal execution from the canonical export configuration.
All allocator contracts are discharged by the existing concrete proofs. -/
theorem export_terminates (input : Spec.Input) :
    TerminatesWithOutcome (exportConfig input) (entryPost input) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_at
      (config := exportConfig input) entryHeap entryGlobals
      heapBase.toNat (entryPost input)
  · exact (entryHeap_facts input).1
  · exact (entryHeap_facts input).2
  · exact entryHeap_below_heapBase
  · exact entryGlobals_agree input
  · simp
  · intro hlc gs legacyPages
    dsimp only [exportConfig]
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
    ihave Hruntime' :
        runtimeModuleOwn ⟨0⟩ Project.Mergesort.module $$ [Hruntime]
    · irw_exact [← entryConfig_entry input, ← entryConfig_currentModule input] with Hruntime
    ihave Henv' :
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) $$ [Henv]
    · irw_exact [← entryConfig_entry_id input, ← entryConfig_currentHost input] with Henv
    ihave Hhost' :
        hostStateOwn (Universal.State.ofInput (serialize input)) $$ [Hhost]
    · irw_exact [← entryConfig_host input] with Hhost
    ihave Hpages' : memoryPagesOwn
        (Project.Mergesort.module.initialStore : Store Universal.State).mem.pages
        $$ [Hpages]
    · rw [show (Project.Mergesort.module.initialStore : Store Universal.State).mem.pages =
        (entryConfig input).store.wasm.mem.pages by rfl]
      iexact Hpages
    imod initialResources input $$
      [$Hheap $Hglobals $Hruntime' $Henv' $Hhost' $Hfrontier $Hpages'] with
      ⟨%heapId, Hruntime, Hsp, Hstack, Hbump, Hstreams⟩
    have hfunc1 : Func1Spec (hlc := hlc) :=
      Project.Mergesort.Func1Proof.func1_correct_of
        (Project.Mergesort.Func0Proof.func0_correct_of
          Project.Mergesort.Func5Proof.func5_correct
          Project.Mergesort.Func8Proof.func8_correct)
    iapply Project.Mergesort.DriverProof.twp_func3_body hfunc1
      Project.Mergesort.Func5Proof.func5_correct
      Project.Mergesort.Func9Proof.func9_correct
      heapId input entryStackBytes entryStackBytes_length
    isplitl_exacts [Hruntime Hsp Hstack Hbump Hstreams]
    isplitl
    · iintro %finalLocals _Hruntime Hsuccess
      iapply (twp_finish (locals := finalLocals) (values := finalLocals.values)
        (arity := 0) (remainder := []))
      isimp only [List.take_zero, List.nil_append]
      iapply Wasm.SmallStep.twp_outcome_done
      iapply_exact DriverSuccess_public heapId input with Hsuccess
    · iapply DriverOOM_public heapId input

/-- The actual named export terminates with a sorted permutation or the
precisely identified allocator OOM outcome. -/
@[proves Project.Mergesort.Spec.PublicTotalSpecification]
theorem mergesort_total_correct : Spec.PublicTotalSpecification := by
  intro input
  obtain ⟨trace, outcome, store, steps, hpost⟩ := export_terminates input
  rcases hpost with hoom | ⟨values, hreturned, hsorted⟩
  · refine ⟨.outOfMemory, ?_, trivial⟩
    exact ⟨exportConfig input, startExportConfig_eq input,
      trace, outcome, store, steps, hoom⟩
  · refine ⟨.sorted values, ?_, hsorted⟩
    exact ⟨exportConfig input, startExportConfig_eq input,
      trace, outcome, store, steps, hreturned⟩

end Project.Mergesort.TotalProof
