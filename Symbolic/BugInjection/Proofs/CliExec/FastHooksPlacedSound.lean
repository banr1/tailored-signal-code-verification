/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Hoare.LibcHooks
public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.SubroutineChoiceBridge
meta import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
meta import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
meta import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced

/-!
# Soundness of Placed Extern Hook Dispatch

Proves `FastState.Agrees`, `Memory.KeepsFrozen`, and `symtab` soundness (`FastHookPost`) for
`FastHooksPlaced.fastExecExternPlaced` and `FastHooksPlaced.hasCliHookPlaced` against
`CryptoVerification.SignalSession.cliExternsPlacedSig mmpl W` (`37` rows in
`cliHookTablePlaced mmpl W` plus `isCliPanicSymbolPlaced`), including specialization to
`CompHooks0Placed.compHooks0`:

1. **17 PQXDH / SPQR rows**: reused directly from `FastHooksRows`.
2. **17 pure libc / I/O / `core` / `std` / session / ratchet rows + `Arm64.Rust.panicked`**: proved
   directly against `FastHooksPlaced` (`fastStrlen_post` and `fastFromUtf8_post` reused from
   `FastHooksPlaced`) with zero fixed-image imports (`C1(b)`-clean).
3. **3 shared-pool `mallocng` rows (`aesEncHookMallocng`, `aesDecHookMallocng`,
   `libcruxHmacHookMallocng`)**: discharged via `SubroutineRunnerSound` and
   `SubroutineChoiceBridge` (`subroutineRunnerSound_of_subStepSound`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound

open Arm64 (ExecStatus Instr Memory Program Reg State Step Steps StepsUntil SubroutineStop
  TraceEvent decode)
open Arm64.Memory (KeepsFrozen keepsFrozen_write16 keepsFrozen_write32 keepsFrozen_write64
  keepsFrozen_writeBytes)
open Arm64.Obj (MultiPlacedLib MultiPlacement lookupBlockSym)
open Arm64.Rust (isPanicSymbol panicked)
open ProofLib (hookMemcpy hookMemmove retHook)
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (ShaState chunks64 hmacWith)
open CryptoGames.LibsignalSession (PubKeyFn aesCbcDecrypt aesCbcEncrypt)
open CryptoGames.Ratchet (X25519Fn)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (diffieHellmanHook pubFromSecretHook
  zeroizeSecretHook)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.E2E (aesDecHookMallocng aesDecOut aesEncHookMallocng aesEncOut
  fmtWriteHook0 formatInnerHook0 libcruxHmacHookMallocng restoreCallerRegs stepRustAlloc1
  stepRustDealloc1 timeAddHook writeVecHeader)
open CryptoVerification.SignalSession (CliHooks PathOk abortOnPanic cliBcmpHook
  cliExternsPlaced cliExternsPlacedSig cliHookTablePlaced cliPanicSymbolsPlaced
  cliPqxdhHookTablePlaced cliPathMaxBytes durationSinceExactHook isCliPanicSymbolPlaced
  memrchrHook readPath unitResult unmodelled vecEmptyOk writeFileHook writeStdoutHook)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (FastFs HeapIntervalsAgree
  fastPathOk fastPathOk_eq listUInt8Eq listUInt8Eq_strUtf8Bytes listUInt8IsPrefix
  lookupStrUtf8 lookupStrUtf8_eq_lookup panicExactNames panicPrefixBs
  perm_write16_eq perm_write32_eq perm_write64_eq perm_writeBytes_eq strUtf8Bytes)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastHookPost FastState
  canWrite_mono_le canWrite_of_perm_eq canWrite_split24 fastAbortOnPanic_post
  fastCompress512_post fastCompress_post fastDsmb_post fastEdNeg_post fastKemDecaps_post
  fastKemEncaps_post fastMlkemDecaps_post fastMlkemEncaps1_post fastMlkemEncaps2_post
  fastMlkemFromSeed_post fastMlkemPk1_post fastMlkemPk2_post fastMlkemValidatePk_post
  fastReadVec32_eq fastScalarMod_post fastScalarWide_post fastToEdwards_post
  fastTorsionFree_post fastWriteBytesRet_retHook_post fastWriteBytesRet_returnToLr_post
  fastWriteVecHeader fastWriteVecHeader_agrees keepsFrozen_writeVecHeader
  perm_writeVecHeader_eq)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs
  aesDecFrameBytes aesEncFrameBytes cliPanicSymbolsPlacedList fastAesDecMallocng
  fastAesDecOut fastAesEncMallocng fastAesEncOut fastBlackBox
  fastCallMallocngSubroutine fastCliBcmp fastCompress256 fastDiffieHellman
  fastDurationSince fastExecExternPlaced fastExternPlacedRaw? fastFmtWrite
  fastFormatInner fastFromUtf8_post fastHookTablePlaced fastIsCliPanicSymbolPlaced
  fastIsCliPanicSymbolPlacedBs fastLibcruxHmacMallocng fastMemcpy fastMemrchr
  fastPanicked fastPubFromSecret fastReadPath fastRestoreCallerRegs
  fastRunSubroutineLoop fastStepRustAlloc1 fastStepRustDealloc1 fastStrlen_post
  fastTimeAdd fastUnitResult fastVecEmptyOk fastWriteFile fastWriteStdout
  fastZeroizeSecret hasCliHookPlaced isSubroutineStopFast libcruxHmacFrameBytes
  mallocngSubFuel panicPlacedExactNamesBs)
open Symbolic.BugInjection.Proofs.CliExec.SubroutineChoiceBridge (
  codeROSubroutineHook_eq_of_stepsUntil isSubroutineStopB isSubroutineStopB_eq_true_iff
  multiCodeROHookEntry_eq_of_codeLoaded multiCodeROHookExit_eq_of_codeLoaded)

#guard cliPanicSymbolsPlacedList.length == 18
#guard cliPanicSymbolsPlacedList == cliPanicSymbolsPlaced
#guard (fastHookTablePlaced (fun _ => none) {} compHooks0).length == 37

theorem cliPanicSymbolsPlacedList_length : cliPanicSymbolsPlacedList.length = 18 := rfl
theorem cliPanicSymbolsPlaced_length : cliPanicSymbolsPlaced.length = 18 := rfl

theorem cliPanicSymbolsPlacedList_eq :
    cliPanicSymbolsPlacedList = cliPanicSymbolsPlaced := by decide

theorem fastHookTablePlaced_keys (subStep : FastState → Option FastState)
    (addrs : MallocngCallAddrs) (mmpl : MultiPlacement) (W : CliHooks) :
    (fastHookTablePlaced subStep addrs W).map Prod.fst =
      (cliHookTablePlaced mmpl W).map Prod.fst := by
  simp only [fastHookTablePlaced, cliHookTablePlaced, cliPqxdhHookTablePlaced,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]

theorem fastHookTablePlaced_length (subStep : FastState → Option FastState)
    (addrs : MallocngCallAddrs) (W : CliHooks) :
    (fastHookTablePlaced subStep addrs W).length = 37 := rfl

private theorem congr3 {α β γ δ : Type} (f : α → β → γ → δ)
    {a1 a2 : α} {b1 b2 : β} {c1 c2 : γ} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) :
    f a1 b1 c1 = f a2 b2 c2 := by subst ha; subst hb; subst hc; rfl

private theorem fastHookPost_of_eq {h1 h2 : State → State} {s : State} {fs' : FastState}
    (heq : h1 s = h2 s) (hp : FastHookPost h1 s fs') : FastHookPost h2 s fs' := by
  unfold FastHookPost at hp ⊢; rw [← heq]; exact hp

theorem fastPanicked_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastPanicked fs = some fs') :
    FastHookPost panicked s fs' := by
  unfold fastPanicked at hsome
  injection hsome with hsome; subst hsome
  exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩

theorem fastMemcpy_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemcpy fs = some fs') :
    FastHookPost hookMemcpy s fs' := by
  unfold fastMemcpy at hsome
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem] at hsome
  exact fastWriteBytesRet_retHook_post hag (s.readReg64 .x0) _ hsome

theorem fastMemmove_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemcpy fs = some fs') :
    FastHookPost hookMemmove s fs' :=
  fastMemcpy_post hag hsome

theorem fastCliBcmp_post {bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCliBcmp bcmp fs = some fs') :
    FastHookPost (cliBcmpHook bcmp) s fs' := by
  unfold fastCliBcmp at hsome; dsimp only at hsome
  injection hsome with hsome; subst hsome
  dsimp only [FastHookPost, cliBcmpHook, retHook]
  rw [FastState.readReg64_eq hag .lr, FastState.readReg64_eq hag .x2,
    FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastMem.readBytes_eq hag.mem, FastMem.readBytes_eq hag.mem]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

theorem fastVecEmptyOk_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastVecEmptyOk fs = some fs') :
    FastHookPost vecEmptyOk s fs' := by
  unfold fastVecEmptyOk at hsome; dsimp only at hsome
  dsimp only [FastHookPost, vecEmptyOk, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
  set r := s.readReg64 .x8
  cases hcw : fs.mem.canWrite r 24 with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
    rw [FastMem.canWrite_eq hag.mem] at hcw
    have hm1 := fastWriteVecHeader_agrees hag.mem r 0#64 1#64 0#64
    have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs
      (perm_writeVecHeader_eq s.mem r 0#64 1#64 0#64)
    exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
      keepsFrozen_writeVecHeader hcw 0#64 1#64 0#64, rfl⟩

theorem fastUnitResult_agrees (ok : Bool) {fs : FastState} {s : State} (hag : fs.Agrees s) :
    (fastUnitResult ok fs).Agrees (unitResult ok s) := by
  dsimp only [fastUnitResult, unitResult, retHook]
  rw [FastState.readReg64_eq hag .lr]
  exact FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr)

theorem fastReadPath_eq {fm : FastMem} {m : Memory} (hm : fm.Agrees m) (ptr len : BitVec 64) :
    fastReadPath fm ptr len = readPath m ptr len := by
  simp only [fastReadPath, readPath, FastMem.readBytes_eq hm]

theorem fastWriteFile_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastWriteFile fs = some fs') :
    FastHookPost writeFileHook s fs' := by
  unfold fastWriteFile at hsome; dsimp only at hsome
  dsimp only [FastHookPost, writeFileHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x3,
    FastMem.canRead_eq hag.mem, FastMem.canRead_eq hag.mem] at hsome
  set ptr := s.readReg64 .x0; set len := s.readReg64 .x1
  set buf := s.readReg64 .x2; set n := s.readReg64 .x3
  cases hperm : (!(s.mem.canRead ptr len.toNat && s.mem.canRead buf n.toNat)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastMem.readBytes_eq hag.mem, fastReadPath_eq hag.mem, fastPathOk_eq] at hsome
    set raw := s.mem.readBytes ptr len.toNat
    cases hbad : (decide (cliPathMaxBytes ≤ len.toNat) || raw.contains 0#8) with
    | true =>
      simp only [hbad, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
      exact ⟨fastUnitResult_agrees false hag, KeepsFrozen.refl s.mem, rfl⟩
    | false =>
      simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      set p := readPath s.mem ptr len
      cases hpok : (!PathOk p) with
      | true =>
        simp only [hpok, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
        exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
      | false =>
        simp only [hpok, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
        set fs1 := fs.appendTrace [.fileChanged p]
        have hag1 : fs1.Agrees (s.appendTrace [.fileChanged p]) :=
          FastState.appendTrace_agrees hag [.fileChanged p]
        rw [FastFs.blockingAncestor?_eq hag1.fs p, FastFs.files_eq hag1.fs p,
          FastMem.readBytes_eq hag1.mem] at hsome
        cases hba : CryptoVerification.SignalSession.blockingAncestor?
            (s.appendTrace [.fileChanged p]).fs p with
        | some _ =>
          rw [hba] at hsome; dsimp only at hsome ⊢; injection hsome with hsome; subst hsome
          exact ⟨fastUnitResult_agrees false hag1, KeepsFrozen.refl s.mem, rfl⟩
        | none =>
          rw [hba] at hsome
          cases hf : (s.appendTrace [.fileChanged p]).fs.files p with
          | some ent =>
            cases ent with
            | dir =>
              rw [hf] at hsome; dsimp only at hsome ⊢; injection hsome with hsome; subst hsome
              exact ⟨fastUnitResult_agrees false hag1, KeepsFrozen.refl s.mem, rfl⟩
            | file _ =>
              rw [hf] at hsome; dsimp only at hsome ⊢; injection hsome with hsome; subst hsome
              exact ⟨fastUnitResult_agrees true
                (FastState.setFs_agrees hag1 (FastFs.setFile_agrees hag1.fs p _)),
                KeepsFrozen.refl s.mem, rfl⟩
          | none =>
            rw [hf] at hsome; dsimp only at hsome ⊢; injection hsome with hsome; subst hsome
            exact ⟨fastUnitResult_agrees true
              (FastState.setFs_agrees hag1 (FastFs.setFile_agrees hag1.fs p _)),
              KeepsFrozen.refl s.mem, rfl⟩

theorem fastWriteStdout_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastWriteStdout fs = some fs') :
    FastHookPost writeStdoutHook s fs' := by
  unfold fastWriteStdout at hsome; dsimp only at hsome
  dsimp only [FastHookPost, writeStdoutHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastMem.canRead_eq hag.mem, FastMem.readBytes_eq hag.mem] at hsome
  cases hcr : (!s.mem.canRead (s.readReg64 .x0) (s.readReg64 .x1).toNat) with
  | true =>
    simp only [hcr, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hcr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    have hag1 := FastState.appendTrace_agrees hag
      (TraceEvent.ofBytes .stdout (s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat))
    exact ⟨fastUnitResult_agrees true hag1, KeepsFrozen.refl s.mem, rfl⟩

theorem fastMemrchr_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemrchr fs = some fs') :
    FastHookPost memrchrHook s fs' := by
  unfold fastMemrchr at hsome; dsimp only at hsome
  dsimp only [FastHookPost, memrchrHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .lr,
    FastMem.canRead_eq hag.mem, FastMem.readBytes_eq hag.mem] at hsome
  set x := (s.readReg64 .x0).setWidth 8
  set ptr := s.readReg64 .x1; set len := s.readReg64 .x2
  cases hcr : (!s.mem.canRead ptr len.toNat) with
  | true =>
    simp only [hcr, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hcr, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    set bs := s.mem.readBytes ptr len.toNat
    cases hlast : ((List.range bs.length).filter fun i => bs[i]? == some x).getLast? with
    | some i =>
      rw [hlast] at hsome; injection hsome with hsome; subst hsome
      exact ⟨FastState.setPC_agrees
        (FastState.writeReg64_agrees (FastState.writeReg64_agrees hag .x0 1#64) .x1
          (BitVec.ofNat 64 i))
        (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩
    | none =>
      rw [hlast] at hsome; injection hsome with hsome; subst hsome
      exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 0#64)
        (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩

theorem fastFmtWrite_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFmtWrite fs = some fs') :
    FastHookPost fmtWriteHook0 s fs' := by
  unfold fastFmtWrite at hsome
  injection hsome with hsome; subst hsome
  dsimp only [FastHookPost, fmtWriteHook0, retHook]
  rw [FastState.readReg64_eq hag .lr]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 0#64) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

theorem fastFormatInner_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFormatInner fs = some fs') :
    FastHookPost formatInnerHook0 s fs' :=
  fastVecEmptyOk_post hag hsome

theorem fastDurationSince_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastDurationSince fs = some fs') :
    FastHookPost durationSinceExactHook s fs' := by
  unfold fastDurationSince at hsome; dsimp only at hsome
  dsimp only [FastHookPost, durationSinceExactHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x8,
    FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x2,
    FastState.readReg64_eq hag .lr, FastMem.canRead_eq hag.mem,
    FastMem.canWrite_eq hag.mem, FastMem.read32_eq hag.mem,
    FastMem.read64_eq hag.mem] at hsome
  set a := s.readReg64 .x0; set r := s.readReg64 .x8
  cases hperm : (!(s.mem.canRead a 12 && s.mem.canWrite r 24)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    have hperm_true : (s.mem.canRead a 12 && s.mem.canWrite r 24) = true := by
      revert hperm; cases (s.mem.canRead a 12 && s.mem.canWrite r 24) <;> simp
    simp only [Bool.and_eq_true] at hperm_true
    obtain ⟨hw0, hw8, hw16⟩ := canWrite_split24 hperm_true.2
    set ns1 := (s.mem.read32 (a + 8#64)).toNat
    set ns2 := ((s.readReg64 .x2).setWidth 32).toNat
    by_cases hns : ns1 < 1000000000 ∧ ns2 < 1000000000
    · simp only [hns, and_self, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      set t1 : Int := (s.mem.read64 a).toInt * 1000000000 + ns1
      set t2 : Int := (s.readReg64 .x1).toInt * 1000000000 + ns2
      set d := (t1 - t2).natAbs
      set tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      set w1 := BitVec.ofNat 64 (d / 1000000000)
      set w2 := BitVec.ofNat 32 (d % 1000000000)
      have hm3 := FastMem.write32_agrees
        (FastMem.write64_agrees (FastMem.write64_agrees hag.mem r tag) (r + 8#64) w1)
        (r + 16#64) w2
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r tag).write64 (r + 8#64) w1).write32 (r + 16#64) w2) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro addr; rw [perm_write32_eq, perm_write64_eq, perm_write64_eq]
      have kf1 := keepsFrozen_write64 hw0 tag
      have hw8' : (s.mem.write64 r tag).canWrite (r + 8#64) 8 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq s.mem r tag)]; exact hw8
      have kf2 := keepsFrozen_write64 hw8' w1
      have hw16_4 : s.mem.canWrite (r + 16#64) 4 = true := canWrite_mono_le (by decide) hw16
      have hw16' : ((s.mem.write64 r tag).write64 (r + 8#64) w1).canWrite
          (r + 16#64) 4 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq _ (r + 8#64) _),
          canWrite_of_perm_eq (perm_write64_eq s.mem r tag)]
        exact hw16_4
      have kf3 := keepsFrozen_write32 hw16' w2
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩
    · simp only [hns, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
      exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩

theorem fastTimeAdd_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastTimeAdd fs = some fs') :
    FastHookPost timeAddHook s fs' := by
  unfold fastTimeAdd at hsome; dsimp only at hsome
  dsimp only [FastHookPost, timeAddHook]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x3,
    FastState.readReg64_eq hag .lr] at hsome
  set sec := (s.readReg64 .x0).toInt + ((s.readReg64 .x2).toNat : Int)
  set ns : BitVec 32 := (s.readReg64 .x3).setWidth 32 + (s.readReg64 .x1).setWidth 32
  set carry : Bool := decide (1000000000 ≤ ns.toNat)
  set sec' := if carry then sec + 1 else sec
  set ns' := if carry then ns - 1000000000#32 else ns
  by_cases hle : sec' ≤ 2 ^ 63 - 1
  · simp only [hle, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setPC_agrees
      (FastState.writeReg64_agrees
        (FastState.writeReg64_agrees hag .x0 (BitVec.ofInt 64 sec')) .x1 (ns'.setWidth 64))
      (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩
  · simp only [hle, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩

theorem fastBlackBox_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastBlackBox fs = some fs') :
    FastHookPost blackBoxHook s fs' := by
  unfold fastBlackBox at hsome
  injection hsome with hsome; subst hsome
  dsimp only [FastHookPost, blackBoxHook, retHook]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .lr]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

theorem fastCompress256_post {F : ShaState → List (BitVec 8) → ShaState}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCompress256 F fs = some fs') :
    FastHookPost (compress256Hook F) s fs' := by
  unfold fastCompress256 at hsome; dsimp only at hsome
  have hst : (List.Vector.ofFn fun i : Fin 8 =>
      fs.mem.read32 (fs.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val))) =
      readShaState s.mem (s.readReg64 .x0) := by
    unfold readShaState
    congr 1; funext i
    rw [FastState.readReg64_eq hag .x0, FastMem.read32_eq hag.mem]
  rw [hst, FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

theorem fastPubFromSecret_post {pubKey : PubKeyFn}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastPubFromSecret pubKey fs = some fs') :
    FastHookPost (pubFromSecretHook pubKey) s fs' := by
  unfold fastPubFromSecret at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0, fastReadVec32_eq hag.mem] at hsome
  exact fastHookPost_of_eq (by unfold pubFromSecretHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x8) _ hsome)

theorem fastDiffieHellman_post {X : X25519Fn}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastDiffieHellman X fs = some fs') :
    FastHookPost (diffieHellmanHook X) s fs' := by
  unfold fastDiffieHellman at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, fastReadVec32_eq hag.mem, fastReadVec32_eq hag.mem] at hsome
  exact fastHookPost_of_eq (by unfold diffieHellmanHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x8) _ hsome)

theorem fastZeroizeSecret_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastZeroizeSecret fs = some fs') :
    FastHookPost zeroizeSecretHook s fs' := by
  unfold fastZeroizeSecret at hsome; rw [FastState.readReg64_eq hag .x0] at hsome
  exact fastHookPost_of_eq (by unfold zeroizeSecretHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x0) (List.replicate 32 0#8) hsome)

theorem codeLoaded_of_keepsFrozen {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {m0 m1 : Memory} (hcl : lib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m1) :
    lib.CodeLoaded mpl m1 :=
  fun k hk => (hcl k hk).of_keepsFrozen hkf

theorem stepsUntil_to_steps {prog : Program} {stop : State → Prop} {s0 sf : State}
    (h : StepsUntil prog stop s0 sf) : Steps prog s0 sf := by
  induction h with
  | refl s => exact .refl s
  | step _ hstep _ ih => exact .step hstep ih

private theorem findSome?_const_none {α β : Type} (xs : List α) (p : α → Bool) :
    xs.findSome? (fun x => if p x then (none : Option β) else none) = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.findSome?_cons]
    cases p x <;> exact ih

theorem externAt?_eq_none_of_no_hooks {prog : Program}
    (hext : prog.externs = fun _ => none)
    (hovr : prog.overrides = fun _ => none) (pc : BitVec 64) :
    prog.externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff?
  rw [hext, hovr, findSome?_const_none, findSome?_const_none]
  rfl

/-- Agreement between `addrs` and the `calloc`, `malloc`, and `free` entry and return-sentinel
addresses of `VerifiedLibraries.mallocngLib` at `mmpl`. -/
structure MallocngCallAddrsMatches (addrs : MallocngCallAddrs) (mmpl : MultiPlacement) : Prop where
  callocAddr_eq     : addrs.callocAddr = VerifiedLibraries.mallocngLib.fnAddr mmpl "calloc"
  callocSentinel_eq : addrs.callocSentinel = mmpl.base 2 + 1#64
  mallocAddr_eq     : addrs.mallocAddr = VerifiedLibraries.mallocngLib.fnAddr mmpl "malloc"
  mallocSentinel_eq : addrs.mallocSentinel = mmpl.base 4 + 1#64
  freeAddr_eq       : addrs.freeAddr = VerifiedLibraries.mallocngLib.fnAddr mmpl "free"
  freeSentinel_eq   : addrs.freeSentinel = mmpl.base 3 + 1#64

def mallocngCallAddrsOf (mmpl : MultiPlacement) : MallocngCallAddrs where
  callocAddr     := VerifiedLibraries.mallocngLib.fnAddr mmpl "calloc"
  callocSentinel := mmpl.base 2 + 1#64
  mallocAddr     := VerifiedLibraries.mallocngLib.fnAddr mmpl "malloc"
  mallocSentinel := mmpl.base 4 + 1#64
  freeAddr       := VerifiedLibraries.mallocngLib.fnAddr mmpl "free"
  freeSentinel   := mmpl.base 3 + 1#64

theorem mallocngCallAddrsOf_matches (mmpl : MultiPlacement) :
    MallocngCallAddrsMatches (mallocngCallAddrsOf mmpl) mmpl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lookupBlockSym_mallocng_calloc :
    lookupBlockSym "calloc" VerifiedLibraries.mallocngLib.blocks = some (2, 0) := rfl

theorem lookupBlockSym_mallocng_free :
    lookupBlockSym "free" VerifiedLibraries.mallocngLib.blocks = some (3, 0) := rfl

theorem lookupBlockSym_mallocng_malloc :
    lookupBlockSym "malloc" VerifiedLibraries.mallocngLib.blocks = some (4, 0) := rfl

private theorem isSubroutineStopFast_eq_isSubroutineStopB
    (sentinel spCall : BitVec 64) (st : ExecStatus) (pc sp : BitVec 64) :
    isSubroutineStopFast sentinel spCall st pc sp =
      isSubroutineStopB sentinel spCall st pc sp := by
  cases st <;> rfl

/-- Single-step soundness of `subStep` on hook-free `mallocngLib` block programs at `mmpl` when
frozen bytes of `m0` are preserved. -/
def SubStepSound (mmpl : MultiPlacement) (m0 : Memory)
    (subStep : FastState → Option FastState) : Prop :=
  ∀ (i : Nat) {fs fs' : FastState} {s : State},
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem →
    m0.KeepsFrozen s.mem →
    fs.Agrees s →
    subStep fs = some fs' →
    ∃ s',
      Step (VerifiedLibraries.mallocngLib.blockProgram mmpl i
        (fun _ => none) (fun _ => none) Arm64.Syscall.standard) s s' ∧
      fs'.Agrees s'

/-- Agreement preservation of `evalF` against `Program.evalInst` under `Arm64.Syscall.standard`. -/
def EvalSound (evalF : Instr → FastState → Option FastState) : Prop :=
  ∀ {prog : Program}, prog.svc = Arm64.Syscall.standard →
    ∀ {inst : Instr} {fs fs' : FastState} {s : State},
      fs.Agrees s → evalF inst fs = some fs' → fs'.Agrees (prog.evalInst inst s)

/-- Memory-fetching single-step runner for hook-free subroutines (`mallocng`). -/
def fastStepMem (evalF : Instr → FastState → Option FastState) (fs : FastState) :
    Option FastState :=
  match fs.status with
  | .Running =>
    if fs.pc.toNat % 4 == 0 && fs.mem.canExec fs.pc 4 then
      match decode (fs.mem.read32 fs.pc) with
      | some inst => evalF inst fs
      | none => none
    else none
  | _ => none

theorem fastStepMem_subStepSound {evalF : Instr → FastState → Option FastState}
    (heval : EvalSound evalF) (mmpl : MultiPlacement) (m0 : Memory) :
    SubStepSound mmpl m0 (fastStepMem evalF) := by
  intro i fs fs' s _ _ hag hstep
  unfold fastStepMem at hstep
  rw [hag.status] at hstep
  cases hrun : s.status with
  | Running =>
    rw [hrun] at hstep; dsimp only at hstep
    rw [hag.pc, FastMem.canExec_eq hag.mem, FastMem.read32_eq hag.mem] at hstep
    cases hok : (s.pc.toNat % 4 == 0 && s.mem.canExec s.pc 4) with
    | false => simp only [hok, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hstep
    | true =>
      simp only [hok, ↓reduceIte] at hstep
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ⟨hmod, hexec⟩
      cases hdec : decode (s.mem.read32 s.pc) with
      | none => rw [hdec] at hstep; cases hstep
      | some inst =>
        rw [hdec] at hstep
        set prog_i := VerifiedLibraries.mallocngLib.blockProgram mmpl i
          (fun _ => none) (fun _ => none) Arm64.Syscall.standard
        have hfetch : prog_i.fetchMem s.mem s.pc = some inst := by
          unfold Program.fetchMem
          rw [externAt?_eq_none_of_no_hooks rfl rfl s.pc]
          simp [hmod, hexec, hdec]
        exact ⟨prog_i.evalInst inst s, Step.exec hrun hfetch, heval rfl hag hstep⟩
  | Halted | Panicked | Exited _ | Signaled _ | Exception _ | OutOfMemory =>
    rw [hrun] at hstep; cases hstep

theorem fastRunSubroutineLoop_sound {mmpl : MultiPlacement} {m0 : Memory}
    {subStep : FastState → Option FastState}
    (hstep : SubStepSound mmpl m0 subStep)
    (i : Nat) {sEntry : State} :
    ∀ (fuel : Nat) {fs fsEnd : FastState} {s : State},
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem →
      m0.KeepsFrozen s.mem →
      fs.Agrees s →
      fastRunSubroutineLoop subStep (sEntry.readReg64 .lr) sEntry.sp fuel fs = some fsEnd →
      ∃ sf,
        StepsUntil (VerifiedLibraries.mallocngLib.blockProgram mmpl i
          (fun _ => none) (fun _ => none) Arm64.Syscall.standard)
          (SubroutineStop sEntry) s sf ∧
        SubroutineStop sEntry sf ∧ fsEnd.Agrees sf
  | 0, fs, fsEnd, s, _, _, hag, hloop => by
    unfold fastRunSubroutineLoop at hloop
    rw [hag.status, hag.pc, hag.sp, isSubroutineStopFast_eq_isSubroutineStopB] at hloop
    cases hstopB : isSubroutineStopB (sEntry.readReg64 .lr) sEntry.sp s.status s.pc s.sp with
    | false => simp only [hstopB, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hloop
    | true =>
      simp only [hstopB, ↓reduceIte, Option.some.injEq] at hloop; subst hloop
      exact ⟨s, .refl s, (isSubroutineStopB_eq_true_iff sEntry s).mp hstopB, hag⟩
  | fuel + 1, fs, fsEnd, s, hcl, hkf, hag, hloop => by
    unfold fastRunSubroutineLoop at hloop
    rw [hag.status, hag.pc, hag.sp, isSubroutineStopFast_eq_isSubroutineStopB] at hloop
    cases hstopB : isSubroutineStopB (sEntry.readReg64 .lr) sEntry.sp s.status s.pc s.sp with
    | true =>
      simp only [hstopB, ↓reduceIte, Option.some.injEq] at hloop; subst hloop
      exact ⟨s, .refl s, (isSubroutineStopB_eq_true_iff sEntry s).mp hstopB, hag⟩
    | false =>
      simp only [hstopB, Bool.false_eq_true, ↓reduceIte] at hloop
      have hnstop : ¬ SubroutineStop sEntry s := by
        rw [← isSubroutineStopB_eq_true_iff, hstopB]; decide
      cases hs1 : subStep fs with
      | none => rw [hs1] at hloop; cases hloop
      | some fs1 =>
        rw [hs1] at hloop
        obtain ⟨s1, hstep1, hag1⟩ := hstep i hcl hkf hag hs1
        have hkf1 : m0.KeepsFrozen s1.mem := KeepsFrozen.trans hkf hstep1.keepsFrozen
        have hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem :=
          codeLoaded_of_keepsFrozen hcl hstep1.keepsFrozen
        obtain ⟨sf, hrest, hstopf, hagf⟩ :=
          fastRunSubroutineLoop_sound hstep i fuel hcl1 hkf1 hag1 hloop
        exact ⟨sf, .step hnstop hstep1 hrest, hstopf, hagf⟩

/-- `FastHookPost` soundness of `fastCallMallocngSubroutine` against `codeROSubroutineHook` for any
exported `mallocngLib` symbol. -/
theorem fastCallMallocngSubroutine_post {mmpl : MultiPlacement} {m0 : Memory}
    {subStep : FastState → Option FastState}
    (hstep : SubStepSound mmpl m0 subStep)
    (fnName : String) (i off : Nat)
    (hlook : lookupBlockSym fnName VerifiedLibraries.mallocngLib.blocks = some (i, off))
    (fuel : Nat) {fsCall fsOut : FastState} {sCall : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem)
    (hkf0 : m0.KeepsFrozen sCall.mem)
    (hag0 : fsCall.Agrees sCall)
    (hcall : fastCallMallocngSubroutine subStep fuel
      (VerifiedLibraries.mallocngLib.fnAddr mmpl fnName) (mmpl.base i + 1#64) fsCall = some fsOut) :
    FastHookPost
      (VerifiedLibraries.mallocngLib.codeROSubroutineHook mmpl fnName
        (fun _ => none) (fun _ => none) Arm64.Syscall.standard)
      sCall fsOut := by
  unfold fastCallMallocngSubroutine at hcall
  dsimp only at hcall
  set entryAddr := VerifiedLibraries.mallocngLib.fnAddr mmpl fnName
  set sentinel := mmpl.base i + 1#64
  set sEntry := Arm64.multiCodeROHookEntry VerifiedLibraries.mallocngLib mmpl i entryAddr sCall
  have hsEntry_eq : sEntry = (sCall.writeReg64 .lr sentinel).setPC entryAddr :=
    multiCodeROHookEntry_eq_of_codeLoaded hcl
  have hagEntry : ((fsCall.writeReg64 .lr sentinel).setPC entryAddr).Agrees sEntry := by
    rw [hsEntry_eq]
    exact FastState.setPC_agrees (FastState.writeReg64_agrees hag0 .lr sentinel) entryAddr
  have hsEntry_lr : sEntry.readReg64 .lr = sentinel := by rw [hsEntry_eq]; rfl
  have hsEntry_sp : sEntry.sp = sCall.sp := by rw [hsEntry_eq]; rfl
  have hsEntry_mem : sEntry.mem = sCall.mem := by rw [hsEntry_eq]; rfl
  have hsEntry_sym : sEntry.symtab = sCall.symtab := by rw [hsEntry_eq]; rfl
  have hclEntry : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sEntry.mem := by
    rw [hsEntry_mem]; exact hcl
  have hkfEntry : m0.KeepsFrozen sEntry.mem := by
    rw [hsEntry_mem]; exact hkf0
  rw [hag0.sp, ← hsEntry_sp] at hcall
  cases hloop : fastRunSubroutineLoop subStep sentinel sEntry.sp fuel
      ((fsCall.writeReg64 .lr sentinel).setPC entryAddr) with
  | none => rw [hloop] at hcall; cases hcall
  | some fsEnd =>
    rw [hloop] at hcall; simp only [Option.some.injEq] at hcall; subst hcall
    rw [← hsEntry_lr] at hloop
    obtain ⟨sf', hsteps, hstop, hagEnd⟩ :=
      fastRunSubroutineLoop_sound hstep i fuel hclEntry hkfEntry hagEntry hloop
    have hhook_eq := codeROSubroutineHook_eq_of_stepsUntil
      VerifiedLibraries.mallocngLib mmpl fnName i off hlook
      (fun _ => none) (fun _ => none) Arm64.Syscall.standard hsteps hstop
    have hsteps_plain := stepsUntil_to_steps hsteps
    have hkf_out : sCall.mem.KeepsFrozen sf'.mem := by
      rw [← hsEntry_mem]; exact hsteps_plain.keepsFrozen
    have hsym_out : sf'.symtab = sCall.symtab := hsteps_plain.symtab_eq.trans hsEntry_sym
    have hexit_eq := multiCodeROHookExit_eq_of_codeLoaded
      (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl) (i := i) (sf' := sf') hcl hkf_out
    dsimp only [FastHookPost]
    rw [hhook_eq, hexit_eq]
    dsimp only
    rw [FastState.readReg64_eq hag0 .lr, hagEnd.pc, hagEnd.status]
    rw [← show sentinel = mmpl.base i + 1#64 from rfl]
    set lrCaller := sCall.readReg64 .lr
    by_cases hcond : sf'.pc = sentinel ∧ sf'.status = .Running
    · have hcondB : (sf'.pc == sentinel && sf'.status == .Running) = true := by
        rw [hcond.1, hcond.2, beq_self_eq_true]; rfl
      rw [hcondB]
      simp only [hcond, and_self, ↓reduceIte]
      exact ⟨FastState.writeReg64_agrees (FastState.setPC_agrees hagEnd lrCaller) .lr lrCaller,
        hkf_out, hsym_out⟩
    · have hcondB : (sf'.pc == sentinel && sf'.status == .Running) = false := by
        by_cases h1 : sf'.pc = sentinel
        · have h2 : sf'.status ≠ .Running := fun hr => hcond ⟨h1, hr⟩
          rw [h1, beq_self_eq_true, Bool.true_and]
          cases hst : sf'.status with
          | Running => exact absurd hst h2
          | Halted | Panicked | Exited _ | Signaled _ | Exception _ | OutOfMemory => rfl
        · rw [beq_eq_false_iff_ne.mpr h1]; rfl
      rw [hcondB]
      simp only [hcond, ↓reduceIte, Bool.false_eq_true]
      exact ⟨FastState.writeReg64_agrees hagEnd .lr lrCaller, hkf_out, hsym_out⟩

/-- Soundness of `fastCallMallocngSubroutine` at fuel `mallocngSubFuel` on the `"calloc"`,
`"malloc"`, and `"free"` entrypoints of `mallocngLib`. -/
def SubroutineRunnerSound (mmpl : MultiPlacement) (m0 : Memory) (addrs : MallocngCallAddrs)
    (subStep : FastState → Option FastState) : Prop :=
  ∀ (fnName : String) (entryAddr sentinel : BitVec 64),
    (fnName, entryAddr, sentinel) ∈
      [("calloc", addrs.callocAddr, addrs.callocSentinel),
       ("malloc", addrs.mallocAddr, addrs.mallocSentinel),
       ("free", addrs.freeAddr, addrs.freeSentinel)] →
    ∀ {fsCall fs1 : FastState} {sCall : State},
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem →
      m0.KeepsFrozen sCall.mem →
      fsCall.Agrees sCall →
      fastCallMallocngSubroutine subStep mallocngSubFuel entryAddr sentinel fsCall = some fs1 →
      let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mmpl fnName
        (fun _ => none) (fun _ => none) Arm64.Syscall.standard sCall
      fs1.Agrees s1 ∧ sCall.mem.KeepsFrozen s1.mem ∧ s1.symtab = sCall.symtab

theorem subroutineRunnerSound_of_subStepSound {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (haddrs : MallocngCallAddrsMatches addrs mmpl)
    (hstep : SubStepSound mmpl m0 subStep) :
    SubroutineRunnerSound mmpl m0 addrs subStep := by
  intro fnName entryAddr sentinel hmem fsCall fs1 sCall hcl hkf hag hcall
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [haddrs.callocAddr_eq, haddrs.callocSentinel_eq] at hcall
    exact fastCallMallocngSubroutine_post hstep "calloc" 2 0
      lookupBlockSym_mallocng_calloc mallocngSubFuel hcl hkf hag hcall
  · rw [haddrs.mallocAddr_eq, haddrs.mallocSentinel_eq] at hcall
    exact fastCallMallocngSubroutine_post hstep "malloc" 4 0
      lookupBlockSym_mallocng_malloc mallocngSubFuel hcl hkf hag hcall
  · rw [haddrs.freeAddr_eq, haddrs.freeSentinel_eq] at hcall
    exact fastCallMallocngSubroutine_post hstep "free" 3 0
      lookupBlockSym_mallocng_free mallocngSubFuel hcl hkf hag hcall

theorem fastRestoreCallerRegs_agrees {fsCaller fsCallee : FastState} {sCaller sCallee : State}
    (hCaller : fsCaller.Agrees sCaller) (hCallee : fsCallee.Agrees sCallee) :
    (fastRestoreCallerRegs fsCaller fsCallee).Agrees (restoreCallerRegs sCaller sCallee) := by
  simp only [fastRestoreCallerRegs, FastState.withFields_eq]
  exact ⟨hCaller.regs, hCaller.sp, hCaller.pc, hCaller.pstate, hCallee.mem, hCallee.heapIvs,
    hCallee.tpidrEl0, hCaller.fpsr, hCallee.brkStart, hCallee.brk, hCallee.physMemAvail,
    hCallee.fs, hCallee.oracle, hCallee.oracleIdx, hCallee.exclFails, hCallee.trace,
    hCallee.status, hCallee.sigAltStack⟩

private theorem fastHookPost_const {h : State → State} {s : State} {fs' : FastState}
    (hp : FastHookPost h s fs') : FastHookPost (fun _ => h s) s fs' := hp

theorem fastStepRustAlloc1_post {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (zeroed : Bool) (frameBytes size : Nat)
    {fk : FastState → BitVec 64 → Option FastState}
    {k : State → BitVec 64 → State}
    (hk : ∀ {fsKeep fsOut : FastState} {sKeep : State} (p : BitVec 64),
      m0.KeepsFrozen sKeep.mem →
      fsKeep.Agrees sKeep →
      fk fsKeep p = some fsOut →
      FastHookPost (fun _ => k sKeep p) sKeep fsOut)
    {fs fs' : FastState} {s : State}
    (hkf0 : m0.KeepsFrozen s.mem)
    (hag : fs.Agrees s)
    (hsome : fastStepRustAlloc1 subStep addrs zeroed frameBytes size fk fs = some fs') :
    FastHookPost (fun _ => stepRustAlloc1 mmpl zeroed frameBytes size k s) s fs' := by
  unfold fastStepRustAlloc1 at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, stepRustAlloc1]
  rw [hag.sp] at hsome
  set spCall := s.sp - BitVec.ofNat 64 frameBytes
  set fsCall0 := (fs.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  set sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  have hagCall0 : fsCall0.Agrees sCall0 :=
    FastState.writeReg64_agrees (FastState.writeReg64_agrees hag .sp spCall) .x0
      (BitVec.ofNat 64 size)
  set fsCall := if zeroed then fsCall0.writeReg64 .x1 1#64 else fsCall0
  set sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  have hagCall : fsCall.Agrees sCall := by
    cases zeroed
    · exact hagCall0
    · exact FastState.writeReg64_agrees hagCall0 .x1 1#64
  have hmemCall : sCall.mem = s.mem := by cases zeroed <;> simp [sCall, sCall0]
  have hsymCall : sCall.symtab = s.symtab := by cases zeroed <;> simp [sCall, sCall0]
  have hkfCall : m0.KeepsFrozen sCall.mem := by rw [hmemCall]; exact hkf0
  have hclCall : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem :=
    codeLoaded_of_keepsFrozen hcl0 hkfCall
  have hsub_post : ∀ {fs1 : FastState},
      fastCallMallocngSubroutine subStep mallocngSubFuel
        (if zeroed then addrs.callocAddr else addrs.mallocAddr)
        (if zeroed then addrs.callocSentinel else addrs.mallocSentinel) fsCall = some fs1 →
      let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mmpl
        (if zeroed then "calloc" else "malloc")
        (fun _ => none) (fun _ => none) Arm64.Syscall.standard sCall
      fs1.Agrees s1 ∧ sCall.mem.KeepsFrozen s1.mem ∧ s1.symtab = sCall.symtab := by
    intro fs1 hr
    cases zeroed with
    | true =>
      simp only [↓reduceIte] at hr ⊢
      exact hrun "calloc" addrs.callocAddr addrs.callocSentinel (by simp) hclCall hkfCall hagCall hr
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
      exact hrun "malloc" addrs.mallocAddr addrs.mallocSentinel (by simp) hclCall hkfCall hagCall hr
  cases hcall : fastCallMallocngSubroutine subStep mallocngSubFuel
      (if zeroed then addrs.callocAddr else addrs.mallocAddr)
      (if zeroed then addrs.callocSentinel else addrs.mallocSentinel) fsCall with
  | none => rw [hcall] at hsome; cases hsome
  | some fs1 =>
    rw [hcall] at hsome; dsimp only at hsome
    obtain ⟨hag1, hkf1_raw, hsym1_raw⟩ := hsub_post hcall
    set s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mmpl
      (if zeroed then "calloc" else "malloc")
      (fun _ => none) (fun _ => none) Arm64.Syscall.standard sCall
    have hkf1 : s.mem.KeepsFrozen s1.mem := by rw [← hmemCall]; exact hkf1_raw
    have hsym1 : s1.symtab = s.symtab := hsym1_raw.trans hsymCall
    rw [hag1.status] at hsome
    cases hst : (s1.status != .Running) with
    | true =>
      simp only [hst, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨hag1, hkf1, hsym1⟩
    | false =>
      simp only [hst, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      rw [FastState.readReg64_eq hag1 .x0] at hsome
      set p := s1.readReg64 .x0
      set fsKeep := fastRestoreCallerRegs fs fs1
      set sKeep := restoreCallerRegs s s1
      have hagKeep : fsKeep.Agrees sKeep := fastRestoreCallerRegs_agrees hag hag1
      cases hp0 : (p == 0#64) with
      | true =>
        simp only [hp0, ↓reduceIte, Option.some.injEq] at hsome ⊢
        subst hsome
        exact ⟨FastState.setStatus_agrees hagKeep .Panicked, hkf1, hsym1⟩
      | false =>
        simp only [hp0, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
        have hkfKeep : m0.KeepsFrozen sKeep.mem := KeepsFrozen.trans hkf0 hkf1
        obtain ⟨hagOut, hkf2, hsym2⟩ := hk p hkfKeep hagKeep hsome
        exact ⟨hagOut, KeepsFrozen.trans hkf1 hkf2, hsym2.trans hsym1⟩

theorem fastStepRustDealloc1_post {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (frameBytes : Nat) (ptr : BitVec 64)
    {fk : FastState → Option FastState}
    {k : State → State}
    (hk : ∀ {fsKeep fsOut : FastState} {sKeep : State},
      m0.KeepsFrozen sKeep.mem →
      fsKeep.Agrees sKeep →
      fk fsKeep = some fsOut →
      FastHookPost (fun _ => k sKeep) sKeep fsOut)
    {fs fs' : FastState} {s : State}
    (hkf0 : m0.KeepsFrozen s.mem)
    (hag : fs.Agrees s)
    (hsome : fastStepRustDealloc1 subStep addrs frameBytes ptr fk fs = some fs') :
    FastHookPost (fun _ => stepRustDealloc1 mmpl frameBytes ptr k s) s fs' := by
  unfold fastStepRustDealloc1 at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, stepRustDealloc1]
  rw [hag.sp] at hsome
  set spCall := s.sp - BitVec.ofNat 64 frameBytes
  set fsCall := (fs.writeReg64 .sp spCall).writeReg64 .x0 ptr
  set sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  have hagCall : fsCall.Agrees sCall :=
    FastState.writeReg64_agrees (FastState.writeReg64_agrees hag .sp spCall) .x0 ptr
  have hmemCall : sCall.mem = s.mem := by simp [sCall]
  have hsymCall : sCall.symtab = s.symtab := by simp [sCall]
  have hkfCall : m0.KeepsFrozen sCall.mem := by rw [hmemCall]; exact hkf0
  have hclCall : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem :=
    codeLoaded_of_keepsFrozen hcl0 hkfCall
  cases hcall : fastCallMallocngSubroutine subStep mallocngSubFuel addrs.freeAddr
      addrs.freeSentinel fsCall with
  | none => rw [hcall] at hsome; cases hsome
  | some fs1 =>
    rw [hcall] at hsome; dsimp only at hsome
    obtain ⟨hag1, hkf1_raw, hsym1_raw⟩ :=
      hrun "free" addrs.freeAddr addrs.freeSentinel (by simp) hclCall hkfCall hagCall hcall
    set s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mmpl "free"
      (fun _ => none) (fun _ => none) Arm64.Syscall.standard sCall
    have hkf1 : s.mem.KeepsFrozen s1.mem := by rw [← hmemCall]; exact hkf1_raw
    have hsym1 : s1.symtab = s.symtab := hsym1_raw.trans hsymCall
    rw [hag1.status] at hsome
    cases hst : (s1.status != .Running) with
    | true =>
      simp only [hst, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨hag1, hkf1, hsym1⟩
    | false =>
      simp only [hst, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      set fsKeep := fastRestoreCallerRegs fs fs1
      set sKeep := restoreCallerRegs s s1
      have hagKeep : fsKeep.Agrees sKeep := fastRestoreCallerRegs_agrees hag hag1
      have hkfKeep : m0.KeepsFrozen sKeep.mem := KeepsFrozen.trans hkf0 hkf1
      obtain ⟨hagOut, hkf2, hsym2⟩ := hk hkfKeep hagKeep hsome
      exact ⟨hagOut, KeepsFrozen.trans hkf1 hkf2, hsym2.trans hsym1⟩

private theorem fastAesEncOut_eq {E : AesKey → Block → Block}
    {fs : FastState} {s : State} (hag : fs.Agrees s) :
    fastAesEncOut E fs = aesEncOut E s := by
  have hk : fs.mem.readBytes (fs.readReg64 .x2) 32 = CryptoVerification.E2E.aesKey s := by
    unfold CryptoVerification.E2E.aesKey
    rw [FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem]
  have hiv : fs.mem.readBytes (fs.readReg64 .x4) 16 = CryptoVerification.E2E.aesIv s := by
    unfold CryptoVerification.E2E.aesIv
    rw [FastState.readReg64_eq hag .x4, FastMem.readBytes_eq hag.mem]
  have hin : fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat =
      CryptoVerification.E2E.aesInput s := by
    unfold CryptoVerification.E2E.aesInput
    rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1, FastMem.readBytes_eq hag.mem]
  exact congr3 (aesCbcEncrypt E) (congrArg bytesToKey32 hk) (congrArg bytesToBlock hiv) hin

private theorem fastAesDecOut_eq {D : AesKey → Block → Block}
    {fs : FastState} {s : State} (hag : fs.Agrees s) :
    fastAesDecOut D fs = aesDecOut D s := by
  have hk : fs.mem.readBytes (fs.readReg64 .x2) 32 = CryptoVerification.E2E.aesKey s := by
    unfold CryptoVerification.E2E.aesKey
    rw [FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem]
  have hiv : fs.mem.readBytes (fs.readReg64 .x4) 16 = CryptoVerification.E2E.aesIv s := by
    unfold CryptoVerification.E2E.aesIv
    rw [FastState.readReg64_eq hag .x4, FastMem.readBytes_eq hag.mem]
  have hin : fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat =
      CryptoVerification.E2E.aesInput s := by
    unfold CryptoVerification.E2E.aesInput
    rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1, FastMem.readBytes_eq hag.mem]
  exact congr3 (aesCbcDecrypt D) (congrArg bytesToKey32 hk) (congrArg bytesToBlock hiv) hin

private theorem fastWritePlacedVecRet_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (p : BitVec 64) (bs : List (BitVec 8)) (cap len : BitVec 64)
    (hsome : (if fs.mem.canWrite p bs.length && fs.mem.canWrite (fs.readReg64 .x8) 24 then
        some ((fs.setMem (fastWriteVecHeader (fs.mem.writeBytes p bs) (fs.readReg64 .x8) cap p len)).setPC
          (fs.readReg64 .lr))
      else none) = some fs') :
    FastHookPost
      (retHook fun st =>
        st.setMem (writeVecHeader (st.mem.writeBytes p bs) (st.readReg64 .x8) cap p len))
      s fs' := by
  dsimp only [FastHookPost, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
  set r := s.readReg64 .x8
  cases hcw : (fs.mem.canWrite p bs.length && fs.mem.canWrite r 24) with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
    simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
    have hm1 := FastMem.writeBytes_agrees hag.mem p bs
    have hm2 := fastWriteVecHeader_agrees hm1 r cap p len
    have hivs2 : HeapIntervalsAgree fs.heapIvs
        (writeVecHeader (s.mem.writeBytes p bs) r cap p len) := by
      apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
      intro a; rw [perm_writeVecHeader_eq, perm_writeBytes_eq]
    have kf1 := keepsFrozen_writeBytes bs hcw.1
    have hcwr2 : (s.mem.writeBytes p bs).canWrite r 24 = true := by
      rw [canWrite_of_perm_eq (perm_writeBytes_eq s.mem p bs)]; exact hcw.2
    have kf2 := keepsFrozen_writeVecHeader hcwr2 cap p len
    exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm2 hivs2) (s.readReg64 .lr),
      KeepsFrozen.trans kf1 kf2, rfl⟩

private theorem fastWriteBadCiphertextRet_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s)
    (hsome : (if fs.mem.canWrite (fs.readReg64 .x8) 8 &&
          fs.mem.canWrite (fs.readReg64 .x8 + 8#64) 8 then
        some ((fs.setMem ((fs.mem.write64 (fs.readReg64 .x8) errTag).write64
          (fs.readReg64 .x8 + 8#64) 1#64)).setPC (fs.readReg64 .lr))
      else none) = some fs') :
    FastHookPost
      (retHook fun st =>
        let r := st.readReg64 .x8
        st.setMem ((st.mem.write64 r errTag).write64 (r + 8#64) 1#64))
      s fs' := by
  dsimp only [FastHookPost, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
  set r := s.readReg64 .x8
  cases hcw : (fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) 8) with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
    simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
    have hm2 := FastMem.write64_agrees (FastMem.write64_agrees hag.mem r errTag) (r + 8#64) 1#64
    have hivs2 : HeapIntervalsAgree fs.heapIvs
        ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64) :=
      HeapIntervalsAgree.of_perm_eq hag.heapIvs fun addr => by rw [perm_write64_eq, perm_write64_eq]
    have hcw2 : (s.mem.write64 r errTag).canWrite (r + 8#64) 8 = true := by
      rw [canWrite_of_perm_eq (perm_write64_eq s.mem r errTag)]; exact hcw.2
    exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm2 hivs2) (s.readReg64 .lr),
      KeepsFrozen.trans (keepsFrozen_write64 hcw.1 errTag) (keepsFrozen_write64 hcw2 1#64), rfl⟩

theorem fastAesEncMallocng_post {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {E : AesKey → Block → Block}
    {fs0 fs' : FastState} {s0 : State}
    (hkf0 : m0.KeepsFrozen s0.mem)
    (hag : fs0.Agrees s0)
    (hsome : fastAesEncMallocng subStep addrs E fs0 = some fs') :
    FastHookPost (aesEncHookMallocng mmpl E) s0 fs' := by
  unfold fastAesEncMallocng at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, aesEncHookMallocng, unmodelled]
  rw [FastState.readReg64_eq hag .x3, FastState.readReg64_eq hag .x5] at hsome
  cases hkv : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) with
  | true =>
    simp only [hkv, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s0.mem, rfl⟩
  | false =>
    simp only [hkv, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x1] at hsome
    set ctLen := ((s0.readReg64 .x1).toNat / 16 + 1) * 16
    by_cases hov : 2 ^ 63 ≤ ctLen
    · simp only [hov, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
      exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s0.mem, rfl⟩
    · simp only [hov, ↓reduceIte] at hsome ⊢
      refine fastStepRustAlloc1_post hrun hcl0 true aesEncFrameBytes ctLen
        (fun {_ _} {s1} p _ hag1 hcont => ?_) hkf0 hag hsome
      rw [fastAesEncOut_eq hag1] at hcont
      exact fastHookPost_const (fastWritePlacedVecRet_post hag1 p (aesEncOut E s1) _ _ hcont)

theorem fastAesDecMallocng_post {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {D : AesKey → Block → Block}
    {fs0 fs' : FastState} {s0 : State}
    (hkf0 : m0.KeepsFrozen s0.mem)
    (hag : fs0.Agrees s0)
    (hsome : fastAesDecMallocng subStep addrs D fs0 = some fs') :
    FastHookPost (aesDecHookMallocng mmpl D) s0 fs' := by
  unfold fastAesDecMallocng at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, aesDecHookMallocng, unmodelled]
  rw [FastState.readReg64_eq hag .x3, FastState.readReg64_eq hag .x5] at hsome
  cases hkv : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) with
  | true =>
    simp only [hkv, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s0.mem, rfl⟩
  | false =>
    simp only [hkv, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x1] at hsome
    set ctLen := (s0.readReg64 .x1).toNat
    cases hct : (ctLen == 0 || ctLen % 16 != 0) with
    | true =>
      simp only [hct, ↓reduceIte] at hsome ⊢
      exact fastWriteBadCiphertextRet_post hag hsome
    | false =>
      simp only [hct, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      refine fastStepRustAlloc1_post hrun hcl0 true aesDecFrameBytes ctLen
        (fun {_ _} {s1} p hkf1 hag1 hcont => ?_) hkf0 hag hsome
      rw [fastAesDecOut_eq hag1] at hcont
      cases hdec : aesDecOut D s1 with
      | some pt =>
        rw [hdec] at hcont; dsimp only at hcont ⊢
        exact fastHookPost_const (fastWritePlacedVecRet_post hag1 p pt _ _ hcont)
      | none =>
        rw [hdec] at hcont; dsimp only at hcont ⊢
        exact fastStepRustDealloc1_post hrun hcl0 aesDecFrameBytes p
          (fun _ hag2 hcont2 => fastHookPost_const (fastWriteBadCiphertextRet_post hag2 hcont2))
          hkf1 hag1 hcont

theorem fastLibcruxHmacMallocng_post {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {F : ShaState → List (BitVec 8) → ShaState}
    {fs0 fs' : FastState} {s0 : State}
    (hkf0 : m0.KeepsFrozen s0.mem)
    (hag : fs0.Agrees s0)
    (hsome : fastLibcruxHmacMallocng subStep addrs F fs0 = some fs') :
    FastHookPost (libcruxHmacHookMallocng mmpl F) s0 fs' := by
  unfold fastLibcruxHmacMallocng at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, libcruxHmacHookMallocng, unmodelled]
  rw [FastState.readReg64_eq hag .x0] at hsome
  cases halg : ((s0.readReg64 .x0).setWidth 32 != 0#32) with
  | true =>
    simp only [halg, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s0.mem, rfl⟩
  | false =>
    simp only [halg, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x4] at hsome
    set keyLen := (s0.readReg64 .x2).toNat
    set dataLen := (s0.readReg64 .x4).toNat
    cases hov : (decide (2 ^ 32 ≤ keyLen) || decide (2 ^ 32 ≤ dataLen)) with
    | true =>
      simp only [hov, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
      exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s0.mem, rfl⟩
    | false =>
      simp only [hov, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      refine fastStepRustAlloc1_post hrun hcl0 true libcruxHmacFrameBytes 64
        (fun {_ _} {s1} pKey hkf1 hag1 hc1 => ?_) hkf0 hag hsome
      refine fastStepRustAlloc1_post hrun hcl0 false libcruxHmacFrameBytes 64
        (fun pIpad hkf2 hag2 hc2 => ?_) hkf1 hag1 hc1
      refine fastStepRustAlloc1_post hrun hcl0 false libcruxHmacFrameBytes 64
        (fun {_ _} {s3} pOpad hkf3 hag3 hc3 => ?_) hkf2 hag2 hc2
      refine fastStepRustDealloc1_post hrun hcl0 libcruxHmacFrameBytes pOpad
        (fun hkf4 hag4 hc4 => ?_) hkf3 hag3 hc3
      refine fastStepRustDealloc1_post hrun hcl0 libcruxHmacFrameBytes pIpad
        (fun hkf5 hag5 hc5 => ?_) hkf4 hag4 hc4
      refine fastStepRustDealloc1_post hrun hcl0 libcruxHmacFrameBytes pKey
        (fun hkf6 hag6 hc6 => ?_) hkf5 hag5 hc5
      refine fastStepRustAlloc1_post hrun hcl0 false libcruxHmacFrameBytes 32
        (fun {_ _} {s7} pOut _ hag7 hc7 => ?_) hkf6 hag6 hc6
      rw [FastState.readReg64_eq hag1 .x1, FastMem.readBytes_eq hag1.mem,
        FastState.readReg64_eq hag3 .x3, FastMem.readBytes_eq hag3.mem,
        FastState.readReg64_eq hag7 .x5, FastState.readReg64_eq hag7 .x6] at hc7
      set tag := hmacWith F (s1.mem.readBytes (s1.readReg64 .x1) keyLen)
        (s3.mem.readBytes (s3.readReg64 .x3) dataLen)
      set outLen := if (s7.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
        min (s7.readReg64 .x6).toNat 32 else 32
      exact fastHookPost_const (fastWritePlacedVecRet_post hag7 pOut tag 32#64
        (BitVec.ofNat 64 outLen) hc7)

private theorem listUInt8IsPrefix_iff :
    ∀ (xs ys : List UInt8), listUInt8IsPrefix xs ys = true ↔ xs <+: ys
  | [], _ => by simp [listUInt8IsPrefix]
  | _ :: _, [] => by simp [listUInt8IsPrefix]
  | a :: as, b :: bs => by
    simp only [listUInt8IsPrefix, Bool.and_eq_true, Nat.beq_eq, UInt8.toNat_inj,
      listUInt8IsPrefix_iff as bs, List.cons_prefix_cons]

private theorem strUtf8Bytes_eq_flatMap (s : String) :
    strUtf8Bytes s = s.toList.flatMap String.utf8EncodeChar := by
  have h1 : s.toByteArray = (s.toList.flatMap String.utf8EncodeChar).toByteArray := by
    rw [← List.utf8Encode.eq_1, String.utf8Encode_toList]
  have h2 := congrArg (fun b : ByteArray => b.data.toList) h1
  rw [List.data_toByteArray] at h2
  rcases s with ⟨⟨⟨bs⟩⟩, _⟩
  exact h2

private theorem utf8EncodeChar_ascii_cons_iff {a c : Char} (ha : a.toNat ≤ 127)
    {rest tail : List UInt8} :
    String.utf8EncodeChar c ++ rest = UInt8.ofNat a.toNat :: tail ↔ c = a ∧ rest = tail := by
  constructor
  · intro h
    rw [String.utf8EncodeChar.eq_def] at h
    dsimp only [Char.toNat] at h ha
    split_ifs at h with h1 h2 h3
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      rcases h with ⟨hhd, rfl⟩
      have hnat := congrArg UInt8.toNat hhd
      simp only [UInt8.toNat_ofNat'] at hnat
      rcases c with ⟨⟨⟨cv, _⟩⟩, _⟩; rcases a with ⟨⟨⟨av, _⟩⟩, _⟩
      simp at ha h1 hnat
      have heq : cv = av := by omega
      subst heq; exact ⟨rfl, rfl⟩
    all_goals
      simp only [List.cons_append, List.cons.injEq] at h
      have hnat := congrArg UInt8.toNat h.1
      simp only [UInt8.toNat_ofNat'] at hnat
      omega
  · rintro ⟨rfl, rfl⟩
    rw [String.utf8EncodeChar.eq_def]
    simp [ha]

private theorem ascii_prefix_flatMap_iff :
    ∀ (ps cs : List Char), (∀ a ∈ ps, a.toNat ≤ 127) →
      (ps.flatMap String.utf8EncodeChar <+: cs.flatMap String.utf8EncodeChar ↔ ps <+: cs)
  | [], _, _ => by simp
  | a :: as, [], hps => by
    have ha : a.toNat ≤ 127 := hps a (.head _)
    simp [String.utf8EncodeChar.eq_def, ha]
  | a :: as, c :: cs, hps => by
    have ha : a.toNat ≤ 127 := hps a (.head _)
    have has : ∀ x ∈ as, x.toNat ≤ 127 := fun x hx => hps x (.tail _ hx)
    have ha_enc : String.utf8EncodeChar a = [UInt8.ofNat a.toNat] := by
      rw [String.utf8EncodeChar.eq_def]; simp [ha]
    simp only [List.flatMap_cons, ha_enc, List.singleton_append, List.cons_prefix_cons]
    constructor
    · rintro ⟨k, hk⟩
      have hsym := utf8EncodeChar_ascii_cons_iff ha |>.mp hk.symm
      exact ⟨hsym.1.symm, (ascii_prefix_flatMap_iff as cs has).mp ⟨k, hsym.2.symm⟩⟩
    · rintro ⟨rfl, hpre⟩
      rcases (ascii_prefix_flatMap_iff as cs has).mpr hpre with ⟨k, hk⟩
      exact ⟨k, by rw [ha_enc, List.singleton_append, List.cons_append, hk]⟩

private theorem any_strUtf8Bytes_eq_contains (name : String) :
    ∀ (xs : List String),
      (xs.map strUtf8Bytes).any (fun p => listUInt8Eq (strUtf8Bytes name) p) = xs.contains name
  | [] => rfl
  | k :: rest => by
    simp only [List.map_cons, List.any_cons, List.contains_cons, listUInt8Eq_strUtf8Bytes,
      any_strUtf8Bytes_eq_contains name rest]

theorem fastIsCliPanicSymbolPlaced_eq (name : String) :
    fastIsCliPanicSymbolPlaced name = isCliPanicSymbolPlaced name := by
  unfold fastIsCliPanicSymbolPlaced fastIsCliPanicSymbolPlacedBs panicPlacedExactNamesBs
    panicPrefixBs isCliPanicSymbolPlaced
  rw [cliPanicSymbolsPlacedList_eq, any_strUtf8Bytes_eq_contains, List.contains_append]
  have hpref : listUInt8IsPrefix (strUtf8Bytes "core::panicking::") (strUtf8Bytes name) =
      name.startsWith "core::panicking::" := by
    have hascii : ∀ a ∈ "core::panicking::".toList, a.toNat ≤ 127 := by decide
    apply Bool.eq_iff_iff.mpr
    rw [listUInt8IsPrefix_iff, strUtf8Bytes_eq_flatMap, strUtf8Bytes_eq_flatMap,
      ascii_prefix_flatMap_iff _ _ hascii, String.startsWith_string_iff]
  rw [hpref]
  unfold panicExactNames isPanicSymbol
  cases cliPanicSymbolsPlaced.contains name <;>
    cases (["core::result::unwrap_failed", "core::option::unwrap_failed",
      "core::option::expect_failed", "core::slice::index::slice_start_index_len_fail",
      "core::slice::index::slice_end_index_len_fail", "core::slice::index::slice_index_order_fail",
      "core::slice::index::slice_index_fail", "alloc::raw_vec::handle_error",
      "alloc::alloc::handle_alloc_error"].contains name) <;>
    cases name.startsWith "core::panicking::" <;> rfl

/-- `FastHookPost` soundness of computable hook `fh` against `sh` whenever frozen bytes of `m0` are
preserved. -/
def PlacedHookPairSound (m0 : Memory)
    (fh : FastState → Option FastState) (sh : State → State) : Prop :=
  ∀ {fs fs' : FastState} {s : State},
    m0.KeepsFrozen s.mem → fs.Agrees s → fh fs = some fs' → FastHookPost sh s fs'

private theorem liftPureHookPairSound {m0 : Memory}
    {fh : FastState → Option FastState} {sh : State → State}
    (hp : ∀ {fs fs' : FastState} {s : State}, fs.Agrees s → fh fs = some fs' → FastHookPost sh s fs') :
    PlacedHookPairSound m0 fh sh :=
  fun _ hag hsome => hp hag hsome

private theorem lookup_isSome_of_map_fst_eq {α β γ : Type} [BEq α]
    {xs : List (α × β)} {ys : List (α × γ)}
    (hkeys : xs.map Prod.fst = ys.map Prod.fst) (k : α) :
    (xs.lookup k).isSome = (ys.lookup k).isSome := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases hkeys
  | cons x rest ih =>
    cases ys with
    | nil => cases hkeys
    | cons y yrest =>
      simp only [List.map_cons, List.cons.injEq] at hkeys
      rcases hkeys with ⟨hxy, hrest⟩
      simp only [List.lookup, hxy]; cases k == y.1 <;> [exact ih hrest; rfl]

theorem hasCliHookPlaced_eq_isSome (mmpl : MultiPlacement) (W : CliHooks) (name : String) :
    hasCliHookPlaced W name = (cliExternsPlacedSig mmpl W name).isSome := by
  unfold hasCliHookPlaced fastExternPlacedRaw? cliExternsPlacedSig cliExternsPlaced
  dsimp only
  rw [← fastIsCliPanicSymbolPlaced, fastIsCliPanicSymbolPlaced_eq, lookupStrUtf8_eq_lookup]
  cases isCliPanicSymbolPlaced name
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_map]
    exact lookup_isSome_of_map_fst_eq (fastHookTablePlaced_keys (fun _ => none) {} mmpl W) name
  · rfl

theorem fastHookTablePlaced_rel {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (W : CliHooks) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ PlacedHookPairSound m0 a.2 b.2)
      (fastHookTablePlaced subStep addrs W) (cliHookTablePlaced mmpl W) := by
  dsimp only [fastHookTablePlaced, cliHookTablePlaced, cliPqxdhHookTablePlaced, List.append_eq]
  refine
    .cons ⟨rfl, liftPureHookPairSound (@fastCompress512_post W.Q.F512)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastToEdwards_post W.Q.montToEd)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastCompress_post W.Q.compress)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastEdNeg_post W.Q.edNeg)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastTorsionFree_post W.Q.isTorsionFree)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastDsmb_post W.Q.dsmb)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastScalarMod_post W.Q.scalarMod)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastScalarWide_post W.Q.scalarWide)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastKemEncaps_post W.Q.encaps)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastKemDecaps_post W.Q.decaps)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemFromSeed_post W.Q.K)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemPk1_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemPk2_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemEncaps1_post W.Q.K)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemEncaps2_post W.Q.K)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemDecaps_post W.Q.K)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMlkemValidatePk_post W.Q.K)⟩ <|
    .cons ⟨rfl, @fastLibcruxHmacMallocng_post mmpl m0 addrs subStep hrun hcl0 W.C.F⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMemmove_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastCliBcmp_post W.bcmp)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastStrlen_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastWriteFile_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastWriteStdout_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastMemrchr_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastFromUtf8_post W.utf8Err)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastFmtWrite_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastFormatInner_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastDurationSince_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastTimeAdd_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastBlackBox_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastCompress256_post W.C.F)⟩ <|
    .cons ⟨rfl, @fastAesEncMallocng_post mmpl m0 addrs subStep hrun hcl0 W.C.E⟩ <|
    .cons ⟨rfl, @fastAesDecMallocng_post mmpl m0 addrs subStep hrun hcl0 W.C.D⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastPubFromSecret_post W.C.pubKey)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastDiffieHellman_post W.C.X)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastZeroizeSecret_post)⟩ <|
    .cons ⟨rfl, liftPureHookPairSound (@fastZeroizeSecret_post)⟩ <|
    .nil

private theorem lookup_forall2_placed_sound {m0 : Memory}
    {ft : List (String × (FastState → Option FastState))}
    {st : List (String × (State → State))}
    (hrel : List.Forall₂ (fun a b => a.1 = b.1 ∧ PlacedHookPairSound m0 a.2 b.2) ft st)
    (name : String) :
    match ft.lookup name, st.lookup name with
    | some fh, some sh => PlacedHookPairSound m0 fh sh
    | none, none => True
    | _, _ => False := by
  induction hrel with
  | nil => trivial
  | @cons a b _ _ hab _ ih =>
    rcases a with ⟨fn, fh⟩; rcases b with ⟨sn, sh⟩; rcases hab with ⟨rfl, hps⟩
    simp only [List.lookup]; cases name == fn <;> [exact ih; exact hps]

/-- Every successful `fastExecExternPlaced` dispatch realizes the corresponding `cliExternsPlacedSig`
hook and preserves `FastState.Agrees`, `KeepsFrozen`, and `symtab`. -/
theorem fastExecExternPlaced_exists_sound {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {W : CliHooks} {name : String} {fs fs' : FastState} {s : State}
    (hkf0 : m0.KeepsFrozen s.mem)
    (hag : fs.Agrees s)
    (hsome : fastExecExternPlaced subStep addrs W name fs = some fs') :
    ∃ h, cliExternsPlacedSig mmpl W name = some h ∧
      fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab := by
  unfold fastExecExternPlaced fastExternPlacedRaw? at hsome
  dsimp only at hsome
  rw [← fastIsCliPanicSymbolPlaced, fastIsCliPanicSymbolPlaced_eq, lookupStrUtf8_eq_lookup] at hsome
  unfold cliExternsPlacedSig cliExternsPlaced
  cases hpan : isCliPanicSymbolPlaced name with
  | true =>
    simp only [hpan, ↓reduceIte, Option.map_eq_some_iff, Option.map_some] at hsome ⊢
    obtain ⟨fs1, hfs1, rfl⟩ := hsome
    exact ⟨abortOnPanic panicked, rfl, fastAbortOnPanic_post (fastPanicked_post hag hfs1)⟩
  | false =>
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    have hlk := lookup_forall2_placed_sound (fastHookTablePlaced_rel hrun hcl0 W) name
    cases hfl : (fastHookTablePlaced subStep addrs W).lookup name with
    | none => rw [hfl] at hsome; cases hsome
    | some fh =>
      rw [hfl] at hsome hlk; dsimp only at hsome
      cases hsl : (cliHookTablePlaced mmpl W).lookup name with
      | none => rw [hsl] at hlk; exact False.elim hlk
      | some sh =>
        rw [hsl] at hlk
        simp only [Option.map_eq_some_iff, Option.map_some] at hsome ⊢
        obtain ⟨fs1, hfs1, rfl⟩ := hsome
        exact ⟨abortOnPanic sh, rfl, fastAbortOnPanic_post (hlk hkf0 hag hfs1)⟩

theorem fastExecExternPlaced_sound {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {W : CliHooks} {name : String} {fs fs' : FastState} {s : State} {h : State → State}
    (hkf0 : m0.KeepsFrozen s.mem)
    (hag : fs.Agrees s)
    (hsome : fastExecExternPlaced subStep addrs W name fs = some fs')
    (hext : cliExternsPlacedSig mmpl W name = some h) :
    fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab := by
  obtain ⟨h', hext', hpost⟩ := fastExecExternPlaced_exists_sound hrun hcl0 hkf0 hag hsome
  rw [hext] at hext'; injection hext' with heq; subst heq; exact hpost

theorem fastExecExternPlaced_compHooks0_exists_sound {mmpl : MultiPlacement} {m0 : Memory}
    {addrs : MallocngCallAddrs} {subStep : FastState → Option FastState}
    (hrun : SubroutineRunnerSound mmpl m0 addrs subStep)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    {name : String} {fs fs' : FastState} {s : State}
    (hkf0 : m0.KeepsFrozen s.mem)
    (hag : fs.Agrees s)
    (hsome : fastExecExternPlaced subStep addrs compHooks0 name fs = some fs') :
    ∃ h, cliExternsPlacedSig mmpl compHooks0 name = some h ∧
      fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab :=
  fastExecExternPlaced_exists_sound hrun hcl0 hkf0 hag hsome

end Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound
