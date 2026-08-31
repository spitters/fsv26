// jsCoq v9.0 branch gap: backend/jsoo/jscoq_worker.ml:120 declares
//     external coq_vm_trap : unit -> unit = "coq_vm_trap"
// and calls it unconditionally at startup (line 234), but no JavaScript
// definition is linked for the jsoo backend. The wasm backend has one
// (backend/wasm/core.ts:173, a no-op that warns), so only jsoo is affected.
//
// Without this the worker dies at load time with
//     ReferenceError: coq_vm_trap is not defined
//
// The trap only matters when Rocq's bytecode VM is present. jsCoq configures
// Rocq with -bytecode-compiler no because the VM is C code, so a no-op is the
// correct behaviour here, matching the wasm backend.

//Provides: coq_vm_trap
function coq_vm_trap() {
  return;
}
