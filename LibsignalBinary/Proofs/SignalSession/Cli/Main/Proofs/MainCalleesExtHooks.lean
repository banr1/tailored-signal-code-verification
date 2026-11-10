/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgPlacement
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainCalleesExtPlaced
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
import LibsignalBinary.Proofs.TripleRatchet.Hooks
public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Placed Hook Table `H_ext` Lifted from `Y_ext`

Lifts the image-stub extern table `Y_ext img ext` across `lsExternStubTriples` to `LibsignalHooks`
and proves lookup equations for I/O, non-I/O, and panic symbols.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open Address.Helpers

/-- Placed `LibsignalHooks` lifted from `Y_ext img ext` across `lsExternStubTriples`. -/
noncomputable def H_ext (img : Obj.Image) (ext : String → Option (State → State)) : LibsignalHooks :=
  CliImgPlacement.liftHooksToPlaced (Y_ext img ext)

private theorem H_ext_not_io {img : Obj.Image} {ext : String → Option (State → State)}
    (extSym stSym : String)
    (hl : lookup extSym (CliImgPlacement.lsExternStubTriples.map fun t => (t.1, t.2.1)) =
      some stSym := by rfl_kernel)
    (hp : isCliPanicSymbol stSym = false := by
      simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
        deadCliHashbrownPanicNames, Rust.isPanicSymbol, allocName, deallocName, reallocName,
        shimName, memcpyName, memmoveName, memsetName, SignalSession.readStdinName,
        SignalSession.readFileName, SignalSession.writeFileName, SignalSession.writeStdoutName])
    (hio : stSym ∉ CliExt.ioNames := by decide) :
    H_ext img ext extSym = ext stSym :=
  (CliImgPlacement.liftHooksToPlaced_of_lookup (Y_ext img ext) hl).trans (Y_ext_of_not_io hp hio)

private theorem H_ext_io {img : Obj.Image} {ext : String → Option (State → State)}
    (extSym stSym : String)
    (hl : lookup extSym (CliImgPlacement.lsExternStubTriples.map fun t => (t.1, t.2.1)) =
      some stSym := by rfl_kernel)
    (hp : isCliPanicSymbol stSym = false := by
      simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
        deadCliHashbrownPanicNames, Rust.isPanicSymbol, SignalSession.readStdinName,
        SignalSession.readFileName, SignalSession.writeFileName, SignalSession.writeStdoutName])
    (hio : stSym ∈ CliExt.ioNames := by decide) :
    H_ext img ext extSym = (ext stSym).map (wrapIoHook img) :=
  (CliImgPlacement.liftHooksToPlaced_of_lookup (Y_ext img ext) hl).trans (Y_ext_of_io hp hio)

private theorem H_ext_panic {img : Obj.Image} {ext : String → Option (State → State)}
    (extSym : String)
    (hl : lookup extSym (CliImgPlacement.lsExternStubTriples.map fun t => (t.1, t.2.1)) =
      some "alloc::raw_vec::handle_error" := by rfl_kernel)
    (hp : isCliPanicSymbol "alloc::raw_vec::handle_error" = true := by
      simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
        deadCliHashbrownPanicNames, Rust.isPanicSymbol]) :
    H_ext img ext extSym = some Rust.panicked :=
  (CliImgPlacement.liftHooksToPlaced_of_lookup (Y_ext img ext) hl).trans (Y_ext_of_panic hp)

theorem extFullLookup_H_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    ExtFullLookup img ext (H_ext img ext) where
  alloc :=
    { alloc := H_ext_not_io lsRustAllocSymCli allocName
      dealloc := H_ext_not_io lsRustDeallocSymCli deallocName
      realloc := H_ext_not_io lsRustReallocSymCli reallocName
      shim := H_ext_not_io lsRustNoAllocShimSymCli shimName
      memcpy := H_ext_not_io "memcpy" memcpyName
      memmove := H_ext_not_io "memmove" memmoveName
      memset := H_ext_not_io "memset" memsetName }
  strlenAddr :=
    { strlen := H_ext_not_io "strlen" "strlen"
      fromUtf8 := H_ext_not_io lsFromUtf8Sym "core::str::converts::from_utf8"
      memrchr := H_ext_not_io lsMemrchrSym "core::slice::memchr::memrchr"
      handleError := H_ext_panic lsHandleErrorSym580 }
  io :=
    { readStdin := H_ext_io lsReadStdinSym SignalSession.readStdinName
      readFile := H_ext_io lsReadFileSym SignalSession.readFileName
      writeFile := H_ext_io lsWriteFileSym SignalSession.writeFileName
      writeStdout := H_ext_io lsWriteStdoutSym SignalSession.writeStdoutName }

end CryptoVerification.SignalSession.Cli.MainHops
