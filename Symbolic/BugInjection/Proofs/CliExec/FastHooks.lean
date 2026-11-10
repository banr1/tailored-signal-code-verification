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
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

/-!
# Closure-Free Extern Hook Dispatcher

Lifts the extern hooks in `cliExternsAbortOnPanic W` (`cliHookTable W` and `isCliPanicSymbol`)
to closure-free `FastState`. Each lifted hook preserves `FastState.Agrees`, `Memory.KeepsFrozen`,
and `symtab` (`fastExecExtern_sound`).
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastHooks

set_option autoImplicit false

open Arm64 Arm64.Memory ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.E2E
open CryptoVerification.LibsignalSpqrV1 (mlkemFromSeedName mlkemPk1Name mlkemPk2Name
  mlkemEncaps1Name mlkemEncaps2Name mlkemDecapsName mlkemValidatePkName libcruxHmacName)
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

export Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState FastHookPost)

def fastPanicked (fs : FastState) : Option FastState := some (fs.setStatus .Panicked)

theorem fastPanicked_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastPanicked fs = some fs') :
    FastHookPost Rust.panicked s fs' := by
  injection hsome with hsome; subst hsome
  exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩

def fastHookNoop (fs : FastState) : Option FastState := some (fs.setPC (fs.readReg64 .lr))

theorem fastHookNoop_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastHookNoop fs = some fs') :
    FastHookPost hookNoop s fs' := by
  injection hsome with hsome; subst hsome
  dsimp only [FastHookPost, hookNoop, retHook, id]
  rw [FastState.readReg64_eq hag .lr]
  exact ⟨FastState.setPC_agrees hag (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩

def fastAlloc (fs : FastState) : Option FastState :=
  let sz := (fs.readReg64 .x0).toNat; let al := (fs.readReg64 .x1).toNat
  match fastBumpAlloc fs.heapIvs sz al with
  | some (p, ivs') =>
    some (((fs.setMemAndIvs (fs.mem.mapFresh p sz Perm.rw) ivs').writeReg64 .x0 p).setPC
      (fs.readReg64 .lr))
  | none => some (fastAllocFail fs)

theorem fastAlloc_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastAlloc fs = some fs') :
    FastHookPost allocHook0 s fs' := by
  unfold fastAlloc at hsome; dsimp only at hsome
  dsimp only [FastHookPost, allocHook0, allocReq, bumpThen]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1] at hsome
  set sz := (s.readReg64 .x0).toNat; set al := (s.readReg64 .x1).toNat
  cases hba : fastBumpAlloc fs.heapIvs sz al with
  | none =>
    rw [hba] at hsome; injection hsome with hsome; subst hsome
    rw [fastBumpAlloc_none_sound hag.heapIvs hba]; exact fastAllocFail_post hag
  | some pair =>
    rcases pair with ⟨p, ivs'⟩
    rw [hba] at hsome; injection hsome with hsome; subst hsome
    obtain ⟨hbump, hivs1⟩ := fastBumpAlloc_some_sound hag.heapIvs hba
    rw [hbump, FastState.readReg64_eq hag .lr]; dsimp only [retHook]
    have hm1 := FastMem.mapFresh_agrees hag.mem p sz Perm.rw
    exact ⟨FastState.setPC_agrees
      (FastState.writeReg64_agrees (FastState.setMemAndIvs_agrees hag hm1 hivs1) .x0 p)
      (s.readReg64 .lr), keepsFrozen_mapFresh s.mem p sz Perm.rw, rfl⟩

def fastRealloc (fs : FastState) : Option FastState :=
  let bs := fs.mem.readBytes (fs.readReg64 .x0)
    (min (fs.readReg64 .x1).toNat (fs.readReg64 .x3).toNat)
  let sz := (fs.readReg64 .x3).toNat; let al := (fs.readReg64 .x2).toNat
  match fastBumpAlloc fs.heapIvs sz al with
  | some (q, ivs') =>
    let fm1 := fs.mem.mapFresh q sz Perm.rw
    if fm1.canWrite q bs.length then
      some (((fs.setMemAndIvs (fm1.writeBytes q bs) ivs').writeReg64 .x0 q).setPC (fs.readReg64 .lr))
    else none
  | none => some (fastAllocFail fs)

theorem fastRealloc_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastRealloc fs = some fs') :
    FastHookPost reallocHook0 s fs' := by
  unfold fastRealloc at hsome; dsimp only at hsome
  dsimp only [FastHookPost, reallocHook0, reallocReq, bumpThen]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x3,
    FastMem.readBytes_eq hag.mem] at hsome
  set bs := s.mem.readBytes (s.readReg64 .x0)
    (min (s.readReg64 .x1).toNat (s.readReg64 .x3).toNat)
  set sz := (s.readReg64 .x3).toNat; set al := (s.readReg64 .x2).toNat
  cases hba : fastBumpAlloc fs.heapIvs sz al with
  | none =>
    rw [hba] at hsome; injection hsome with hsome; subst hsome
    rw [fastBumpAlloc_none_sound hag.heapIvs hba]; exact fastAllocFail_post hag
  | some pair =>
    rcases pair with ⟨q, ivs'⟩
    rw [hba] at hsome; dsimp only at hsome
    obtain ⟨hbump, hivs1⟩ := fastBumpAlloc_some_sound hag.heapIvs hba
    rw [hbump]; dsimp only [retHook]
    set fm1 := fs.mem.mapFresh q sz Perm.rw
    cases hcw : fm1.canWrite q bs.length with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
      have hm1 := FastMem.mapFresh_agrees hag.mem q sz Perm.rw
      simp only [fm1, FastMem.canWrite_eq hm1] at hcw
      rw [FastState.readReg64_eq hag .lr]
      have hm2 := FastMem.writeBytes_agrees hm1 q bs
      have hivs2 := HeapIntervalsAgree.of_perm_eq hivs1 (perm_writeBytes_eq _ q bs)
      exact ⟨FastState.setPC_agrees
        (FastState.writeReg64_agrees (FastState.setMemAndIvs_agrees hag hm2 hivs2) .x0 q)
        (s.readReg64 .lr),
        KeepsFrozen.trans (keepsFrozen_mapFresh s.mem q sz Perm.rw)
          (keepsFrozen_writeBytes bs hcw), rfl⟩

def fastAllocZeroed (fs : FastState) : Option FastState :=
  let sz := (fs.readReg64 .x0).toNat; let al := (fs.readReg64 .x1).toNat
  match fastBumpAlloc fs.heapIvs sz al with
  | some (p, ivs') =>
    let fm1 := fs.mem.mapFresh p sz Perm.rw; let zs := List.replicate sz 0#8
    if fm1.canWrite p zs.length then
      some (((fs.setMemAndIvs (fm1.writeBytes p zs) ivs').writeReg64 .x0 p).setPC (fs.readReg64 .lr))
    else none
  | none => some (fastAllocFail fs)

theorem fastAllocZeroed_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastAllocZeroed fs = some fs') :
    FastHookPost allocZeroedHook0 s fs' := by
  unfold fastAllocZeroed at hsome; dsimp only at hsome
  dsimp only [FastHookPost, allocZeroedHook0, allocReq, bumpThen]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1] at hsome
  set sz := (s.readReg64 .x0).toNat; set al := (s.readReg64 .x1).toNat
  cases hba : fastBumpAlloc fs.heapIvs sz al with
  | none =>
    rw [hba] at hsome; injection hsome with hsome; subst hsome
    rw [fastBumpAlloc_none_sound hag.heapIvs hba]; exact fastAllocFail_post hag
  | some pair =>
    rcases pair with ⟨p, ivs'⟩
    rw [hba] at hsome; dsimp only at hsome
    obtain ⟨hbump, hivs1⟩ := fastBumpAlloc_some_sound hag.heapIvs hba
    rw [hbump]; dsimp only [retHook]
    set fm1 := fs.mem.mapFresh p sz Perm.rw; set zs := List.replicate sz 0#8
    cases hcw : fm1.canWrite p zs.length with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
      have hm1 := FastMem.mapFresh_agrees hag.mem p sz Perm.rw
      simp only [fm1, FastMem.canWrite_eq hm1] at hcw
      rw [FastState.readReg64_eq hag .lr]
      have hm2 := FastMem.writeBytes_agrees hm1 p zs
      have hivs2 := HeapIntervalsAgree.of_perm_eq hivs1 (perm_writeBytes_eq _ p zs)
      exact ⟨FastState.setPC_agrees
        (FastState.writeReg64_agrees (FastState.setMemAndIvs_agrees hag hm2 hivs2) .x0 p)
        (s.readReg64 .lr),
        KeepsFrozen.trans (keepsFrozen_mapFresh s.mem p sz Perm.rw)
          (keepsFrozen_writeBytes zs hcw), rfl⟩

def fastMemset (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x0)
    (List.replicate (fs.readReg64 .x2).toNat ((fs.readReg32 .x1).truncate 8)) fs

theorem fastMemset_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemset fs = some fs') :
    FastHookPost hookMemset s fs' := by
  unfold fastMemset at hsome
  rw [FastState.readReg64_eq hag .x0, FastState.readReg32_eq hag .x1,
    FastState.readReg64_eq hag .x2] at hsome
  exact fastWriteBytesRet_retHook_post hag (s.readReg64 .x0) _ hsome

def fastMemcpy (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x0)
    (fs.mem.readBytes (fs.readReg64 .x1) (fs.readReg64 .x2).toNat) fs

theorem fastMemcpy_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemcpy fs = some fs') :
    FastHookPost hookMemcpy s fs' := by
  unfold fastMemcpy at hsome
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem] at hsome
  exact fastWriteBytesRet_retHook_post hag (s.readReg64 .x0) _ hsome

def fastCliBcmp (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64)
    (fs : FastState) : Option FastState :=
  let n := (fs.readReg64 .x2).toNat
  some ((fs.writeReg64 .x0 (bcmp (fs.mem.readBytes (fs.readReg64 .x0) n)
    (fs.mem.readBytes (fs.readReg64 .x1) n))).setPC (fs.readReg64 .lr))

theorem fastCliBcmp_post {bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCliBcmp bcmp fs = some fs') :
    FastHookPost (cliBcmpHook bcmp) s fs' := by
  injection hsome with hsome; subst hsome
  dsimp only [FastHookPost, cliBcmpHook, retHook]
  rw [FastState.readReg64_eq hag .lr, FastState.readReg64_eq hag .x2,
    FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastMem.readBytes_eq hag.mem, FastMem.readBytes_eq hag.mem]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastStrlen (fs : FastState) : Option FastState :=
  match fastStrlenScan fs.mem (fs.readReg64 .x0) 0 strlenFuel with
  | some (some len) => some ((fs.writeReg64 .x0 (BitVec.ofNat 64 len)).setPC (fs.readReg64 .lr))
  | some none => some (fs.setStatus (.Exception "strlen: no readable NUL"))
  | none => none

open Classical in
theorem fastStrlen_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastStrlen fs = some fs') :
    FastHookPost strlenHook s fs' := by
  unfold fastStrlen at hsome
  dsimp only [FastHookPost, strlenHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0] at hsome
  set p := s.readReg64 .x0
  cases hscan : fastStrlenScan fs.mem p 0 strlenFuel with
  | none => rw [hscan] at hsome; cases hsome
  | some res =>
    cases res with
    | some len =>
      rw [hscan] at hsome; injection hsome with hsome; subst hsome
      obtain ⟨hex, hfind⟩ := fastStrlenScan_some_sound hag.mem hscan
      simp only [hex, ↓reduceDIte, hfind, FastState.readReg64_eq hag .lr]
      exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
        KeepsFrozen.refl s.mem, rfl⟩
    | none =>
      rw [hscan] at hsome; injection hsome with hsome; subst hsome
      have hno := fastStrlenScan_none_sound hag.mem hscan
      simp only [hno, ↓reduceDIte]
      exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩

def fastVecErr (fs : FastState) : Option FastState :=
  let r := fs.readReg64 .x8
  if fs.mem.canWrite r 8 then
    some ((fs.setMem (fs.mem.write64 r (BitVec.allOnes 64))).setPC (fs.readReg64 .lr))
  else none

theorem fastVecErr_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastVecErr fs = some fs') :
    FastHookPost vecErr s fs' := by
  unfold fastVecErr at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, vecErr, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
  set r := s.readReg64 .x8
  cases hcw : fs.mem.canWrite r 8 with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
    subst hsome
    rw [FastMem.canWrite_eq hag.mem] at hcw
    have hall : (BitVec.allOnes 64 : BitVec 64) = -1#64 := rfl
    have hm1 := FastMem.write64_agrees hag.mem r (BitVec.allOnes 64)
    have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs
      (perm_write64_eq s.mem r (BitVec.allOnes 64))
    exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
      keepsFrozen_write64 hcw _, rfl⟩

def fastVecEmptyOk (fs : FastState) : Option FastState :=
  let r := fs.readReg64 .x8
  if fs.mem.canWrite r 24 then
    some ((fs.setMem (fastWriteVecHeader fs.mem r 0#64 1#64 0#64)).setPC (fs.readReg64 .lr))
  else none

theorem fastVecEmptyOk_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastVecEmptyOk fs = some fs') :
    FastHookPost vecEmptyOk s fs' := by
  unfold fastVecEmptyOk at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, vecEmptyOk, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
  set r := s.readReg64 .x8
  cases hcw : fs.mem.canWrite r 24 with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
    subst hsome
    rw [FastMem.canWrite_eq hag.mem] at hcw
    have hm1 := fastWriteVecHeader_agrees hag.mem r 0#64 1#64 0#64
    have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs
      (perm_writeVecHeader_eq s.mem r 0#64 1#64 0#64)
    exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
      keepsFrozen_writeVecHeader hcw 0#64 1#64 0#64, rfl⟩

def fastVecOk (bs : List (BitVec 8)) (fs : FastState) : Option FastState :=
  if bs.isEmpty then fastVecEmptyOk fs
  else fastReturnFreshVecU8 bs fs

theorem fastVecOk_post {bs : List (BitVec 8)} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastVecOk bs fs = some fs') :
    FastHookPost (vecOk bs) s fs' := by
  unfold fastVecOk at hsome
  dsimp only [FastHookPost, vecOk]
  cases he : bs.isEmpty with
  | true =>
    simp only [he, ↓reduceIte] at hsome ⊢
    exact fastVecEmptyOk_post hag hsome
  | false =>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    exact fastReturnFreshVecU8_post hag bs hsome

def fastUnitResult (ok : Bool) (fs : FastState) : FastState :=
  (fs.writeReg64 .x0 (if ok then 0#64 else 1#64)).setPC (fs.readReg64 .lr)

theorem fastUnitResult_agrees (ok : Bool) {fs : FastState} {s : State} (hag : fs.Agrees s) :
    (fastUnitResult ok fs).Agrees (unitResult ok s) := by
  dsimp only [fastUnitResult, unitResult, retHook]
  rw [FastState.readReg64_eq hag .lr]
  exact FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr)

def fastReadPath (fm : FastMem) (ptr len : BitVec 64) : String :=
  String.ofList ((fm.readBytes ptr len.toNat).map fun b => Char.ofNat b.toNat)

theorem fastReadPath_eq {fm : FastMem} {m : Memory} (hm : fm.Agrees m) (ptr len : BitVec 64) :
    fastReadPath fm ptr len = readPath m ptr len := by
  simp only [fastReadPath, readPath, FastMem.readBytes_eq hm]

def fastReadFile (fs : FastState) : Option FastState :=
  let ptr := fs.readReg64 .x0
  let len := fs.readReg64 .x1
  if !(fs.mem.canRead ptr len.toNat && fs.mem.canWrite (fs.readReg64 .x8) 24) then
    some (fs.setStatus (.Exception "read_file: unreadable path or unwritable result"))
  else
    let raw := fs.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      fastVecErr fs
    else
      let p := fastReadPath fs.mem ptr len
      if !fastPathOk p then
        some (fs.setStatus (.Exception "read_file: path outside the model"))
      else
        match fs.fs.blockingAncestor? p with
        | some (some _) => fastVecErr fs
        | some none => fastVecEmptyOk fs
        | none =>
          match fs.fs.files p with
          | some (.file bs) =>
            if bs.length ≤ fileCapBytes then fastVecOk bs fs else fastVecErr fs
          | some .dir => fastVecErr fs
          | none => fastVecEmptyOk fs

theorem fastReadFile_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastReadFile fs = some fs') :
    FastHookPost readFileHook s fs' := by
  unfold fastReadFile at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, readFileHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x8, FastMem.canRead_eq hag.mem,
    FastMem.canWrite_eq hag.mem] at hsome
  set ptr := s.readReg64 .x0
  set len := s.readReg64 .x1
  cases hperm : (!(s.mem.canRead ptr len.toNat && s.mem.canWrite (s.readReg64 .x8) 24)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastMem.readBytes_eq hag.mem, fastReadPath_eq hag.mem, fastPathOk_eq] at hsome
    set raw := s.mem.readBytes ptr len.toNat
    cases hbad : (decide (cliPathMaxBytes ≤ len.toNat) || raw.contains 0#8) with
    | true =>
      simp only [hbad, ↓reduceIte] at hsome ⊢
      exact fastVecErr_post hag hsome
    | false =>
      simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      set p := readPath s.mem ptr len
      cases hpok : (!PathOk p) with
      | true =>
        simp only [hpok, ↓reduceIte, Option.some.injEq] at hsome ⊢
        subst hsome
        exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
      | false =>
        simp only [hpok, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
        rw [FastFs.blockingAncestor?_eq hag.fs p, FastFs.files_eq hag.fs p] at hsome
        cases hba : CryptoVerification.SignalSession.blockingAncestor? s.fs p with
        | some o =>
          cases o with
          | some _ =>
            rw [hba] at hsome; dsimp only at hsome ⊢
            exact fastVecErr_post hag hsome
          | none =>
            rw [hba] at hsome; dsimp only at hsome ⊢
            exact fastVecEmptyOk_post hag hsome
        | none =>
          rw [hba] at hsome; dsimp only at hsome ⊢
          cases hf : s.fs.files p with
          | some ent =>
            cases ent with
            | file bs =>
              rw [hf] at hsome; dsimp only at hsome ⊢
              by_cases hcap : bs.length ≤ fileCapBytes
              · simp only [hcap, ↓reduceIte] at hsome ⊢
                exact fastVecOk_post hag hsome
              · simp only [hcap, ↓reduceIte] at hsome ⊢
                exact fastVecErr_post hag hsome
            | dir =>
              rw [hf] at hsome; dsimp only at hsome ⊢
              exact fastVecErr_post hag hsome
          | none =>
            rw [hf] at hsome; dsimp only at hsome ⊢
            exact fastVecEmptyOk_post hag hsome

def fastWriteFile (fs : FastState) : Option FastState :=
  let ptr := fs.readReg64 .x0
  let len := fs.readReg64 .x1
  let buf := fs.readReg64 .x2
  let n := fs.readReg64 .x3
  if !(fs.mem.canRead ptr len.toNat && fs.mem.canRead buf n.toNat) then
    some (fs.setStatus (.Exception "write_file: unreadable path or bytes"))
  else
    let raw := fs.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      some (fastUnitResult false fs)
    else
      let p := fastReadPath fs.mem ptr len
      if !fastPathOk p then
        some (fs.setStatus (.Exception "write_file: path outside the model"))
      else
        let fs1 := fs.appendTrace [.fileChanged p]
        match fs1.fs.blockingAncestor? p, fs1.fs.files p with
        | some _, _ => some (fastUnitResult false fs1)
        | none, some .dir => some (fastUnitResult false fs1)
        | none, _ =>
          some (fastUnitResult true
            (fs1.setFs (fs1.fs.setFile p (some (.file (fs1.mem.readBytes buf n.toNat))))))

theorem fastWriteFile_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastWriteFile fs = some fs') :
    FastHookPost writeFileHook s fs' := by
  unfold fastWriteFile at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, writeFileHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x3,
    FastMem.canRead_eq hag.mem, FastMem.canRead_eq hag.mem] at hsome
  set ptr := s.readReg64 .x0
  set len := s.readReg64 .x1
  set buf := s.readReg64 .x2
  set n := s.readReg64 .x3
  cases hperm : (!(s.mem.canRead ptr len.toNat && s.mem.canRead buf n.toNat)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastMem.readBytes_eq hag.mem, fastReadPath_eq hag.mem, fastPathOk_eq] at hsome
    set raw := s.mem.readBytes ptr len.toNat
    cases hbad : (decide (cliPathMaxBytes ≤ len.toNat) || raw.contains 0#8) with
    | true =>
      simp only [hbad, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨fastUnitResult_agrees false hag, KeepsFrozen.refl s.mem, rfl⟩
    | false =>
      simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      set p := readPath s.mem ptr len
      cases hpok : (!PathOk p) with
      | true =>
        simp only [hpok, ↓reduceIte, Option.some.injEq] at hsome ⊢
        subst hsome
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
          rw [hba] at hsome; dsimp only at hsome ⊢
          injection hsome with hsome; subst hsome
          exact ⟨fastUnitResult_agrees false hag1, KeepsFrozen.refl s.mem, rfl⟩
        | none =>
          rw [hba] at hsome
          cases hf : (s.appendTrace [.fileChanged p]).fs.files p with
          | some ent =>
            cases ent with
            | dir =>
              rw [hf] at hsome; dsimp only at hsome ⊢
              injection hsome with hsome; subst hsome
              exact ⟨fastUnitResult_agrees false hag1, KeepsFrozen.refl s.mem, rfl⟩
            | file _ =>
              rw [hf] at hsome; dsimp only at hsome ⊢
              injection hsome with hsome; subst hsome
              exact ⟨fastUnitResult_agrees true
                (FastState.setFs_agrees hag1 (FastFs.setFile_agrees hag1.fs p _)),
                KeepsFrozen.refl s.mem, rfl⟩
          | none =>
            rw [hf] at hsome; dsimp only at hsome ⊢
            injection hsome with hsome; subst hsome
            exact ⟨fastUnitResult_agrees true
              (FastState.setFs_agrees hag1 (FastFs.setFile_agrees hag1.fs p _)),
              KeepsFrozen.refl s.mem, rfl⟩

def fastReadStdin (fs : FastState) : Option FastState :=
  if !fs.mem.canWrite (fs.readReg64 .x8) 24 then
    some (fs.setStatus (.Exception "read_stdin: unwritable result"))
  else
    match fs.fs.getFd 0#64 with
    | some e =>
      if e.kind == .stdio && e.accMode.canRead then
        let rest := fs.fs.stdin.drop e.offset
        if rest.length ≤ stdinCapBytes then
          fastVecOk rest (fs.setFs (fs.fs.setFd 0#64 (some { e with offset := e.offset + rest.length })))
        else
          fastVecErr (fs.setFs (fs.fs.setFd 0#64 (some { e with offset := e.offset + (stdinCapBytes + 1) })))
      else
        some (fs.setStatus (.Exception "read_stdin: file descriptor 0 is not readable standard input"))
    | none =>
      some (fs.setStatus (.Exception "read_stdin: file descriptor 0 is closed"))

theorem fastReadStdin_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastReadStdin fs = some fs') :
    FastHookPost readStdinHook s fs' := by
  unfold fastReadStdin at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, readStdinHook, unmodelled]
  rw [FastState.readReg64_eq hag .x8, FastMem.canWrite_eq hag.mem] at hsome
  cases hcw : (!s.mem.canWrite (s.readReg64 .x8) 24) with
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hcw, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastFs.getFd_eq hag.fs 0#64] at hsome
    cases hfd : s.fs.fds 0#64 with
    | none =>
      rw [hfd] at hsome; dsimp only at hsome ⊢
      injection hsome with hsome; subst hsome
      exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
    | some e =>
      rw [hfd] at hsome; dsimp only at hsome ⊢
      cases hok : (e.kind == .stdio && e.accMode.canRead) with
      | false =>
        simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome ⊢
        subst hsome
        exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
      | true =>
        simp only [hok, ↓reduceIte] at hsome ⊢
        rw [hag.fs.2.1] at hsome
        set rest := s.fs.stdin.drop e.offset
        by_cases hcap : rest.length ≤ stdinCapBytes
        · simp only [hcap, ↓reduceIte] at hsome ⊢
          have hag1 := FastState.setFs_agrees hag
            (FastFs.setFd_agrees hag.fs 0#64 (some { e with offset := e.offset + rest.length }))
          exact fastVecOk_post hag1 hsome
        · simp only [hcap, ↓reduceIte] at hsome ⊢
          have hag1 := FastState.setFs_agrees hag
            (FastFs.setFd_agrees hag.fs 0#64 (some { e with offset := e.offset + (stdinCapBytes + 1) }))
          exact fastVecErr_post hag1 hsome

def fastWriteStdout (fs : FastState) : Option FastState :=
  let buf := fs.readReg64 .x0
  let n := fs.readReg64 .x1
  if !fs.mem.canRead buf n.toNat then
    some (fs.setStatus (.Exception "write_stdout: unreadable bytes"))
  else
    some (fastUnitResult true (fs.appendTrace (TraceEvent.ofBytes .stdout (fs.mem.readBytes buf n.toNat))))

theorem fastWriteStdout_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastWriteStdout fs = some fs') :
    FastHookPost writeStdoutHook s fs' := by
  unfold fastWriteStdout at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, writeStdoutHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastMem.canRead_eq hag.mem, FastMem.readBytes_eq hag.mem] at hsome
  set buf := s.readReg64 .x0
  set n := s.readReg64 .x1
  cases hcr : (!s.mem.canRead buf n.toNat) with
  | true =>
    simp only [hcr, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hcr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    have hag1 := FastState.appendTrace_agrees hag
      (TraceEvent.ofBytes .stdout (s.mem.readBytes buf n.toNat))
    exact ⟨fastUnitResult_agrees true hag1, KeepsFrozen.refl s.mem, rfl⟩

def fastMemrchr (fs : FastState) : Option FastState :=
  let x := (fs.readReg64 .x0).setWidth 8
  let ptr := fs.readReg64 .x1
  let len := fs.readReg64 .x2
  if !fs.mem.canRead ptr len.toNat then
    some (fs.setStatus (.Exception "memrchr: unreadable bytes"))
  else
    let bs := fs.mem.readBytes ptr len.toNat
    let lr := fs.readReg64 .lr
    match ((List.range bs.length).filter fun i => bs[i]? == some x).getLast? with
    | some i =>
      some (((fs.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)).setPC lr)
    | none =>
      some ((fs.writeReg64 .x0 0#64).setPC lr)

theorem fastMemrchr_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMemrchr fs = some fs') :
    FastHookPost memrchrHook s fs' := by
  unfold fastMemrchr at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, memrchrHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .lr,
    FastMem.canRead_eq hag.mem, FastMem.readBytes_eq hag.mem] at hsome
  set x := (s.readReg64 .x0).setWidth 8
  set ptr := s.readReg64 .x1
  set len := s.readReg64 .x2
  cases hcr : (!s.mem.canRead ptr len.toNat) with
  | true =>
    simp only [hcr, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
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

def fastFromUtf8 (err : List (BitVec 8) → BitVec 64 × BitVec 16)
    (fs : FastState) : Option FastState :=
  let ptr := fs.readReg64 .x0
  let len := fs.readReg64 .x1
  let r := fs.readReg64 .x8
  if !(fs.mem.canRead ptr len.toNat && fs.mem.canWrite r 24) then
    some (fs.setStatus (.Exception "from_utf8: unreadable bytes or unwritable result"))
  else
    let bs := fs.mem.readBytes ptr len.toNat
    let lr := fs.readReg64 .lr
    if fastCheckUtf8 bs then
      let fm' := ((fs.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64 (r + 16#64) len
      some ((fs.setMem fm').setPC lr)
    else
      let e := err bs
      let fm' := ((fs.mem.write64 r 1#64).write64 (r + 8#64) e.1).write16 (r + 16#64) e.2
      some ((fs.setMem fm').setPC lr)

open Classical in
theorem fastFromUtf8_post {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFromUtf8 err fs = some fs') :
    FastHookPost (fromUtf8Hook err) s fs' := by
  unfold fastFromUtf8 at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, fromUtf8Hook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr,
    FastMem.canRead_eq hag.mem, FastMem.canWrite_eq hag.mem,
    FastMem.readBytes_eq hag.mem] at hsome
  set ptr := s.readReg64 .x0
  set len := s.readReg64 .x1
  set r := s.readReg64 .x8
  cases hperm : (!(s.mem.canRead ptr len.toNat && s.mem.canWrite r 24)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    have hperm_true : (s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) = true := by
      revert hperm; cases (s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) <;> simp
    simp only [Bool.and_eq_true] at hperm_true
    obtain ⟨hw0, hw8, hw16⟩ := canWrite_split24 hperm_true.2
    set bs := s.mem.readBytes ptr len.toNat
    cases hutf : fastCheckUtf8 bs with
    | true =>
      simp only [hutf, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      have huok : Utf8Ok bs := (fastCheckUtf8_iff bs).mp hutf
      simp only [huok, ↓reduceIte]
      have hm1 := FastMem.write64_agrees hag.mem r 0#64
      have hm2 := FastMem.write64_agrees hm1 (r + 8#64) ptr
      have hm3 := FastMem.write64_agrees hm2 (r + 16#64) len
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64 (r + 16#64) len) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro a; rw [perm_write64_eq, perm_write64_eq, perm_write64_eq]
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        keepsFrozen_writeVecHeader hperm_true.2 0#64 ptr len, rfl⟩
    | false =>
      simp only [hutf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      have hnuok : ¬ Utf8Ok bs := (fastCheckUtf8_eq_false_iff bs).mp hutf
      simp only [hnuok, ↓reduceIte]
      have hm1 := FastMem.write64_agrees hag.mem r 1#64
      have hm2 := FastMem.write64_agrees hm1 (r + 8#64) (err bs).1
      have hm3 := FastMem.write16_agrees hm2 (r + 16#64) (err bs).2
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).write16 (r + 16#64) (err bs).2) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro a; rw [perm_write16_eq, perm_write64_eq, perm_write64_eq]
      have kf1 := keepsFrozen_write64 hw0 1#64
      have hw8' : (s.mem.write64 r 1#64).canWrite (r + 8#64) 8 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq s.mem r 1#64)]; exact hw8
      have kf2 := keepsFrozen_write64 hw8' (err bs).1
      have hw16_2 : s.mem.canWrite (r + 16#64) 2 = true :=
        canWrite_mono_le (by decide) hw16
      have hw16' : ((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).canWrite
          (r + 16#64) 2 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq _ (r + 8#64) _),
          canWrite_of_perm_eq (perm_write64_eq s.mem r 1#64)]
        exact hw16_2
      have kf3 := keepsFrozen_write16 hw16' (err bs).2
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩

def fastFmtWrite (fs : FastState) : Option FastState :=
  some ((fs.writeReg64 .x0 0#64).setPC (fs.readReg64 .lr))

theorem fastFmtWrite_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFmtWrite fs = some fs') :
    FastHookPost fmtWriteHook0 s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, fmtWriteHook0, retHook]
  rw [FastState.readReg64_eq hag .lr]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 0#64) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastFormatInner (fs : FastState) : Option FastState :=
  fastVecEmptyOk fs

theorem fastFormatInner_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFormatInner fs = some fs') :
    FastHookPost formatInnerHook0 s fs' :=
  fastVecEmptyOk_post hag hsome

def fastDurationSince (fs : FastState) : Option FastState :=
  let a := fs.readReg64 .x0
  let r := fs.readReg64 .x8
  if !(fs.mem.canRead a 12 && fs.mem.canWrite r 24) then
    some (fs.setStatus (.Exception "duration_since: unreadable self or unwritable result"))
  else
    let ns1 := (fs.mem.read32 (a + 8#64)).toNat
    let ns2 := ((fs.readReg64 .x2).setWidth 32).toNat
    if ns1 < 1000000000 ∧ ns2 < 1000000000 then
      let t1 : Int := (fs.mem.read64 a).toInt * 1000000000 + ns1
      let t2 : Int := (fs.readReg64 .x1).toInt * 1000000000 + ns2
      let d := (t1 - t2).natAbs
      let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      let fm' := ((fs.mem.write64 r tag).write64 (r + 8#64)
        (BitVec.ofNat 64 (d / 1000000000))).write32 (r + 16#64)
        (BitVec.ofNat 32 (d % 1000000000))
      some ((fs.setMem fm').setPC (fs.readReg64 .lr))
    else
      some (fs.setStatus (.Exception "duration_since: tv_nsec out of range"))

theorem fastDurationSince_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastDurationSince fs = some fs') :
    FastHookPost durationSinceExactHook s fs' := by
  unfold fastDurationSince at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, durationSinceExactHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x8,
    FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x2,
    FastState.readReg64_eq hag .lr, FastMem.canRead_eq hag.mem,
    FastMem.canWrite_eq hag.mem, FastMem.read32_eq hag.mem,
    FastMem.read64_eq hag.mem] at hsome
  set a := s.readReg64 .x0
  set r := s.readReg64 .x8
  cases hperm : (!(s.mem.canRead a 12 && s.mem.canWrite r 24)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
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
    · simp only [hns] at hsome ⊢
      injection hsome with hsome; subst hsome
      set t1 : Int := (s.mem.read64 a).toInt * 1000000000 + ns1
      set t2 : Int := (s.readReg64 .x1).toInt * 1000000000 + ns2
      set d := (t1 - t2).natAbs
      set tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      set w1 := BitVec.ofNat 64 (d / 1000000000)
      set w2 := BitVec.ofNat 32 (d % 1000000000)
      have hm1 := FastMem.write64_agrees hag.mem r tag
      have hm2 := FastMem.write64_agrees hm1 (r + 8#64) w1
      have hm3 := FastMem.write32_agrees hm2 (r + 16#64) w2
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r tag).write64 (r + 8#64) w1).write32 (r + 16#64) w2) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro addr; rw [perm_write32_eq, perm_write64_eq, perm_write64_eq]
      have kf1 := keepsFrozen_write64 hw0 tag
      have hw8' : (s.mem.write64 r tag).canWrite (r + 8#64) 8 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq s.mem r tag)]; exact hw8
      have kf2 := keepsFrozen_write64 hw8' w1
      have hw16_4 : s.mem.canWrite (r + 16#64) 4 = true :=
        canWrite_mono_le (by decide) hw16
      have hw16' : ((s.mem.write64 r tag).write64 (r + 8#64) w1).canWrite
          (r + 16#64) 4 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq _ (r + 8#64) _),
          canWrite_of_perm_eq (perm_write64_eq s.mem r tag)]
        exact hw16_4
      have kf3 := keepsFrozen_write32 hw16' w2
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩
    · simp only [hns, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩

def fastTimeAdd (fs : FastState) : Option FastState :=
  let sec := (fs.readReg64 .x0).toInt + ((fs.readReg64 .x2).toNat : Int)
  let ns : BitVec 32 := (fs.readReg64 .x3).setWidth 32 + (fs.readReg64 .x1).setWidth 32
  let carry : Bool := decide (1000000000 ≤ ns.toNat)
  let sec' := if carry then sec + 1 else sec
  let ns' := if carry then ns - 1000000000#32 else ns
  if sec' ≤ 2 ^ 63 - 1 then
    some (((fs.writeReg64 .x0 (BitVec.ofInt 64 sec')).writeReg64 .x1 (ns'.setWidth 64)).setPC
      (fs.readReg64 .lr))
  else
    some (fs.setStatus .Panicked)

theorem fastTimeAdd_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastTimeAdd fs = some fs') :
    FastHookPost timeAddHook s fs' := by
  unfold fastTimeAdd at hsome
  dsimp only at hsome
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
  · simp only [hle, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setPC_agrees
      (FastState.writeReg64_agrees
        (FastState.writeReg64_agrees hag .x0 (BitVec.ofInt 64 sec')) .x1 (ns'.setWidth 64))
      (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩
  · simp only [hle, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩

def fastBlackBox (fs : FastState) : Option FastState :=
  some ((fs.writeReg64 .x0 (((fs.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC
    (fs.readReg64 .lr))

theorem fastBlackBox_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastBlackBox fs = some fs') :
    FastHookPost LibsignalSession.blackBoxHook s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, LibsignalSession.blackBoxHook, retHook]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .lr]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastCompress256 (F : ShaState → List (BitVec 8) → ShaState) (fs : FastState) :
    Option FastState :=
  let x0 := fs.readReg64 .x0
  let st : ShaState := List.Vector.ofFn fun i : Fin 8 =>
    fs.mem.read32 (x0 + BitVec.ofNat 64 (4 * i.val))
  let bs := fs.mem.readBytes (fs.readReg64 .x1) (64 * (fs.readReg64 .x2).toNat)
  fastWriteBytesRet x0 (LibsignalHmac.shaStateBytes ((chunks64 bs).foldl F st)) fs

theorem fastCompress256_post {F : ShaState → List (BitVec 8) → ShaState}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCompress256 F fs = some fs') :
    FastHookPost (LibsignalHmac.compress256Hook F) s fs' := by
  unfold fastCompress256 at hsome
  dsimp only at hsome
  have hst : (List.Vector.ofFn fun i : Fin 8 =>
      fs.mem.read32 (fs.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val))) =
      LibsignalHmac.readShaState s.mem (s.readReg64 .x0) := by
    unfold LibsignalHmac.readShaState
    congr 1; funext i
    rw [FastState.readReg64_eq hag .x0, FastMem.read32_eq hag.mem]
  rw [hst, FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

private theorem congr3 {α β γ δ : Type} (f : α → β → γ → δ)
    {a1 a2 : α} {b1 b2 : β} {c1 c2 : γ} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) :
    f a1 b1 c1 = f a2 b2 c2 := by subst ha; subst hb; subst hc; rfl

private theorem fastHookPost_of_eq {h1 h2 : State → State} {s : State} {fs' : FastState}
    (heq : h1 s = h2 s) (hp : FastHookPost h1 s fs') : FastHookPost h2 s fs' := by
  unfold FastHookPost at hp ⊢; rw [← heq]; exact hp

def fastAesEncOut (E : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) : List (BitVec 8) :=
  aesCbcEncrypt E (bytesToKey32 (fs.mem.readBytes (fs.readReg64 .x2) 32))
    (CBC.bytesToBlock (fs.mem.readBytes (fs.readReg64 .x4) 16))
    (fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat)

def fastAesEnc (E : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) : Option FastState :=
  if fs.readReg64 .x3 != 32#64 || fs.readReg64 .x5 != 16#64 then
    let r := fs.readReg64 .x8
    if fs.mem.canWrite r 8 then
      some ((fs.setMem (fs.mem.write64 r errTag)).setPC (fs.readReg64 .lr))
    else none
  else if 2 ^ 63 ≤ ((fs.readReg64 .x1).toNat / 16 + 1) * 16 then
    some (fs.setStatus .Panicked)
  else
    fastReturnFreshVecU8 (fastAesEncOut E fs) fs

private theorem fastAesEncOut_eq {E : CBC.AesKey → CBC.Block → CBC.Block}
    {fs : FastState} {s : State} (hag : fs.Agrees s) :
    fastAesEncOut E fs = aesEncOut E s := by
  have hk : fs.mem.readBytes (fs.readReg64 .x2) 32 = aesKey s := by
    unfold aesKey; rw [FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem]
  have hiv : fs.mem.readBytes (fs.readReg64 .x4) 16 = aesIv s := by
    unfold aesIv; rw [FastState.readReg64_eq hag .x4, FastMem.readBytes_eq hag.mem]
  have hin : fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat = aesInput s := by
    unfold aesInput
    rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1, FastMem.readBytes_eq hag.mem]
  exact congr3 (aesCbcEncrypt E) (congrArg bytesToKey32 hk) (congrArg CBC.bytesToBlock hiv) hin

theorem fastAesEnc_post {E : CBC.AesKey → CBC.Block → CBC.Block}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastAesEnc E fs = some fs') :
    FastHookPost (aesEncHook0 E) s fs' := by
  unfold fastAesEnc at hsome
  dsimp only [FastHookPost, aesEncHook0]
  rw [FastState.readReg64_eq hag .x3, FastState.readReg64_eq hag .x5] at hsome
  cases hkv : (s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64) with
  | true =>
    simp only [hkv, ↓reduceIte] at hsome ⊢
    dsimp only [retHook]
    rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr] at hsome
    set r := s.readReg64 .x8
    cases hcw : fs.mem.canWrite r 8 with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
      rw [FastMem.canWrite_eq hag.mem] at hcw
      have hm1 := FastMem.write64_agrees hag.mem r errTag
      have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_write64_eq s.mem r errTag)
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
        keepsFrozen_write64 hcw errTag, rfl⟩
  | false =>
    simp only [hkv, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x1] at hsome
    by_cases hov : 2 ^ 63 ≤ ((s.readReg64 .x1).toNat / 16 + 1) * 16
    · simp only [hov, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
      exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩
    · simp only [hov, ↓reduceIte] at hsome ⊢
      exact fastHookPost_of_eq (congrArg (fun bs => returnFreshVecU8 bs s) (fastAesEncOut_eq hag))
        (fastReturnFreshVecU8_post hag (fastAesEncOut E fs) hsome)

def fastAesDecOut (D : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) :
    Option (List (BitVec 8)) :=
  aesCbcDecrypt D (bytesToKey32 (fs.mem.readBytes (fs.readReg64 .x2) 32))
    (CBC.bytesToBlock (fs.mem.readBytes (fs.readReg64 .x4) 16))
    (fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat)

private theorem fastAesDecOut_eq {D : CBC.AesKey → CBC.Block → CBC.Block}
    {fs : FastState} {s : State} (hag : fs.Agrees s) :
    fastAesDecOut D fs = aesDecOut D s := by
  have hk : fs.mem.readBytes (fs.readReg64 .x2) 32 = aesKey s := by
    unfold aesKey; rw [FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem]
  have hiv : fs.mem.readBytes (fs.readReg64 .x4) 16 = aesIv s := by
    unfold aesIv; rw [FastState.readReg64_eq hag .x4, FastMem.readBytes_eq hag.mem]
  have hin : fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat = aesInput s := by
    unfold aesInput
    rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1, FastMem.readBytes_eq hag.mem]
  exact congr3 (aesCbcDecrypt D) (congrArg bytesToKey32 hk) (congrArg CBC.bytesToBlock hiv) hin

def fastAesDec (D : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) : Option FastState :=
  let ctLen := (fs.readReg64 .x1).toNat
  let r := fs.readReg64 .x8
  let lr := fs.readReg64 .lr
  if ctLen == 0 || ctLen % 16 != 0 then
    if fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) 8 then
      some ((fs.setMem ((fs.mem.write64 r errTag).write64 (r + 8#64) 1#64)).setPC lr)
    else none
  else if fs.readReg64 .x3 != 32#64 || fs.readReg64 .x5 != 16#64 then
    if fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) 8 then
      some ((fs.setMem ((fs.mem.write64 r errTag).write64 (r + 8#64) 0#64)).setPC lr)
    else none
  else if 2 ^ 63 ≤ ctLen then
    some (fs.setStatus .Panicked)
  else
    match fastAesDecOut D fs with
    | some pt =>
      if (fastBumpAlloc fs.heapIvs ctLen 1).isNone then
        some (fastAllocPanic fs)
      else
        fastReturnFreshVecU8 pt fs
    | none =>
      match fastBumpAlloc fs.heapIvs ctLen 1 with
      | some (p, ivs') =>
        let fm1 := fs.mem.mapFresh p ctLen Perm.rw
        if fm1.canWrite r 8 && fm1.canWrite (r + 8#64) 8 then
          let fm2 := (fm1.write64 r errTag).write64 (r + 8#64) 1#64
          some ((fs.setMemAndIvs fm2 ivs').setPC lr)
        else none
      | none => some (fastAllocPanic fs)

theorem fastAesDec_post {D : CBC.AesKey → CBC.Block → CBC.Block}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastAesDec D fs = some fs') :
    FastHookPost (aesDecHook0 D) s fs' := by
  unfold fastAesDec at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, aesDecHook0]
  rw [FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x8,
    FastState.readReg64_eq hag .lr] at hsome
  set ctLen := (s.readReg64 .x1).toNat
  set r := s.readReg64 .x8
  cases hct : (ctLen == 0 || ctLen % 16 != 0) with
  | true =>
    simp only [hct, ↓reduceIte] at hsome ⊢
    dsimp only [retHook]
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
  | false =>
    simp only [hct, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x3, FastState.readReg64_eq hag .x5] at hsome
    cases hkv : (s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64) with
    | true =>
      simp only [hkv, ↓reduceIte] at hsome ⊢
      dsimp only [retHook]
      cases hcw : (fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) 8) with
      | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
      | true =>
        simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
        simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
        have hm2 := FastMem.write64_agrees (FastMem.write64_agrees hag.mem r errTag) (r + 8#64) 0#64
        have hivs2 : HeapIntervalsAgree fs.heapIvs
            ((s.mem.write64 r errTag).write64 (r + 8#64) 0#64) :=
          HeapIntervalsAgree.of_perm_eq hag.heapIvs fun addr => by rw [perm_write64_eq, perm_write64_eq]
        have hcw2 : (s.mem.write64 r errTag).canWrite (r + 8#64) 8 = true := by
          rw [canWrite_of_perm_eq (perm_write64_eq s.mem r errTag)]; exact hcw.2
        exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm2 hivs2) (s.readReg64 .lr),
          KeepsFrozen.trans (keepsFrozen_write64 hcw.1 errTag) (keepsFrozen_write64 hcw2 0#64), rfl⟩
    | false =>
      simp only [hkv, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
      by_cases hov : 2 ^ 63 ≤ ctLen
      · simp only [hov, ↓reduceIte, Option.some.injEq] at hsome ⊢; subst hsome
        exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩
      · simp only [hov, ↓reduceIte] at hsome ⊢
        cases hdec : fastAesDecOut D fs with
        | some pt =>
          rw [hdec] at hsome; dsimp only at hsome
          have hdec' : aesDecOut D s = some pt := (fastAesDecOut_eq hag).symm.trans hdec
          rw [hdec']; dsimp only
          cases hba : fastBumpAlloc fs.heapIvs ctLen 1 with
          | none =>
            rw [hba] at hsome
            simp only [Option.isNone, ↓reduceIte, Option.some.injEq] at hsome
            subst hsome
            rw [fastBumpAlloc_none_sound hag.heapIvs hba]
            dsimp only [Option.isNone, ↓reduceIte]
            exact fastAllocPanic_post hag
          | some pair =>
            rcases pair with ⟨p, ivs'⟩
            rw [hba] at hsome
            simp only [Option.isNone, Bool.false_eq_true, ↓reduceIte] at hsome
            rw [(fastBumpAlloc_some_sound hag.heapIvs hba).1]
            simp only [Option.isNone, Bool.false_eq_true, ↓reduceIte]
            exact fastReturnFreshVecU8_post hag pt hsome
        | none =>
          rw [hdec] at hsome; dsimp only at hsome
          have hdec' : aesDecOut D s = none := (fastAesDecOut_eq hag).symm.trans hdec
          rw [hdec']; dsimp only [bumpThen]
          cases hba : fastBumpAlloc fs.heapIvs ctLen 1 with
          | none =>
            rw [hba] at hsome; injection hsome with hsome; subst hsome
            rw [fastBumpAlloc_none_sound hag.heapIvs hba]
            exact fastAllocPanic_post hag
          | some pair =>
            rcases pair with ⟨p, ivs'⟩
            rw [hba] at hsome; dsimp only at hsome
            obtain ⟨hbump, hivs1⟩ := fastBumpAlloc_some_sound hag.heapIvs hba
            rw [hbump]; dsimp only
            set fm1 := fs.mem.mapFresh p ctLen Perm.rw
            cases hcw : (fm1.canWrite r 8 && fm1.canWrite (r + 8#64) 8) with
            | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
            | true =>
              simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome; subst hsome
              simp only [Bool.and_eq_true] at hcw
              have hm1 := FastMem.mapFresh_agrees hag.mem p ctLen Perm.rw
              have hcw1_s : (s.mem.mapFresh p ctLen Perm.rw).canWrite r 8 = true := by
                rw [← FastMem.canWrite_eq hm1]; exact hcw.1
              have hcw2_s : (s.mem.mapFresh p ctLen Perm.rw).canWrite (r + 8#64) 8 = true := by
                rw [← FastMem.canWrite_eq hm1]; exact hcw.2
              have hm2 := FastMem.write64_agrees (FastMem.write64_agrees hm1 r errTag) (r + 8#64) 1#64
              have hivs2 : HeapIntervalsAgree ivs'
                  (((s.mem.mapFresh p ctLen Perm.rw).write64 r errTag).write64 (r + 8#64) 1#64) :=
                HeapIntervalsAgree.of_perm_eq hivs1 fun a => by rw [perm_write64_eq, perm_write64_eq]
              have hag_ret : ((fs.setMemAndIvs ((fm1.write64 r errTag).write64 (r + 8#64) 1#64) ivs').setPC
                  (s.readReg64 .lr)).Agrees
                  (retHook (fun st =>
                    let r := st.readReg64 .x8
                    st.setMem ((st.mem.write64 r errTag).write64 (r + 8#64) 1#64))
                    (s.setMem (s.mem.mapFresh p ctLen Perm.rw))) := by
                unfold retHook
                exact FastState.setPC_agrees (FastState.setMemAndIvs_agrees hag hm2 hivs2)
                  (s.readReg64 .lr)
              have kf1 := keepsFrozen_mapFresh s.mem p ctLen Perm.rw
              have kf2 := keepsFrozen_write64 hcw1_s errTag
              have hcw2' : ((s.mem.mapFresh p ctLen Perm.rw).write64 r errTag).canWrite
                  (r + 8#64) 8 = true := by
                rw [canWrite_of_perm_eq (perm_write64_eq _ r errTag)]; exact hcw2_s
              have kf3 := keepsFrozen_write64 hcw2' 1#64
              exact ⟨hag_ret, KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩

def fastPubFromSecret (pubKey : PubKeyFn) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (pubKey (fastReadVecN fs.mem (fs.readReg64 .x0) 32)).toList fs

theorem fastPubFromSecret_post {pubKey : PubKeyFn}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastPubFromSecret pubKey fs = some fs') :
    FastHookPost (LibsignalTripleRatchet.pubFromSecretHook pubKey) s fs' := by
  unfold fastPubFromSecret at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0, fastReadVec32_eq hag.mem] at hsome
  exact fastHookPost_of_eq (by unfold LibsignalTripleRatchet.pubFromSecretHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x8) _ hsome)

def fastDiffieHellman (X : Ratchet.X25519Fn) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (X (fastReadVecN fs.mem (fs.readReg64 .x0) 32) (fastReadVecN fs.mem (fs.readReg64 .x1) 32)).toList fs

theorem fastDiffieHellman_post {X : Ratchet.X25519Fn}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastDiffieHellman X fs = some fs') :
    FastHookPost (LibsignalTripleRatchet.diffieHellmanHook X) s fs' := by
  unfold fastDiffieHellman at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, fastReadVec32_eq hag.mem, fastReadVec32_eq hag.mem] at hsome
  exact fastHookPost_of_eq (by unfold LibsignalTripleRatchet.diffieHellmanHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x8) _ hsome)

def fastZeroizeSecret (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x0) (List.replicate 32 0#8) fs

theorem fastZeroizeSecret_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastZeroizeSecret fs = some fs') :
    FastHookPost LibsignalTripleRatchet.zeroizeSecretHook s fs' := by
  unfold fastZeroizeSecret at hsome; rw [FastState.readReg64_eq hag .x0] at hsome
  exact fastHookPost_of_eq (by unfold LibsignalTripleRatchet.zeroizeSecretHook retHook; rfl)
    (fastWriteBytesRet_retHook_post hag (s.readReg64 .x0) (List.replicate 32 0#8) hsome)

/-- States that `fh` establishes `FastHookPost sh` whenever it succeeds on an agreeing `FastState`. -/
def HookPairSound (fh : FastState → Option FastState) (sh : State → State) : Prop :=
  ∀ {fs fs' : FastState} {s : State}, fs.Agrees s → fh fs = some fs' → FastHookPost sh s fs'

def fastHookTable (W : CliHooks) : List (String × (FastState → Option FastState)) :=
  [(compress512Name, fastCompress512 W.Q.F512), (toEdwardsName, fastToEdwards W.Q.montToEd),
   (compressName, fastCompress W.Q.compress), (edNegName, fastEdNeg W.Q.edNeg),
   (torsionFreeName, fastTorsionFree W.Q.isTorsionFree), (dsmbName, fastDsmb W.Q.dsmb),
   (scalarModName, fastScalarMod W.Q.scalarMod), (scalarWideName, fastScalarWide W.Q.scalarWide),
   (kemEncapsName, fastKemEncaps W.Q.encaps), (kemDecapsName, fastKemDecaps W.Q.decaps),
   (mlkemFromSeedName, fastMlkemFromSeed W.Q.K), (mlkemPk1Name, fastMlkemPk1),
   (mlkemPk2Name, fastMlkemPk2), (mlkemEncaps1Name, fastMlkemEncaps1 W.Q.K),
   (mlkemEncaps2Name, fastMlkemEncaps2 W.Q.K), (mlkemDecapsName, fastMlkemDecaps W.Q.K),
   (mlkemValidatePkName, fastMlkemValidatePk W.Q.K), (libcruxHmacName, fastLibcruxHmac W.C.F),
   ("__rustc::__rust_no_alloc_shim_is_unstable_v2", fastHookNoop),
   ("__rustc::__rust_alloc", fastAlloc), ("__rustc::__rust_dealloc", fastHookNoop),
   ("__rustc::__rust_realloc", fastRealloc), ("__rustc::__rust_alloc_zeroed", fastAllocZeroed),
   ("memset", fastMemset), ("memmove", fastMemcpy), ("memcpy", fastMemcpy),
   ("bcmp", fastCliBcmp W.bcmp), ("strlen", fastStrlen),
   (readFileName, fastReadFile), (writeFileName, fastWriteFile),
   (readStdinName, fastReadStdin), (writeStdoutName, fastWriteStdout),
   ("core::slice::memchr::memrchr", fastMemrchr),
   ("core::str::converts::from_utf8", fastFromUtf8 W.utf8Err),
   ("core::fmt::write", fastFmtWrite), ("alloc::fmt::format::format_inner", fastFormatInner),
   ("<std::time::SystemTime>::duration_since", fastDurationSince),
   ("<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add", fastTimeAdd),
   ("subtle::black_box::<u8>", fastBlackBox),
   ("sha2::sha256::compress256", fastCompress256 W.C.F),
   ("signal_crypto::aes_cbc::aes_256_cbc_encrypt", fastAesEnc W.C.E),
   ("signal_crypto::aes_cbc::aes_256_cbc_decrypt", fastAesDec W.C.D),
   ("<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
     fastPubFromSecret W.C.pubKey),
   ("<x25519_dalek::x25519::StaticSecret>::diffie_hellman", fastDiffieHellman W.C.X),
   ("<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop", fastZeroizeSecret),
   ("<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop", fastZeroizeSecret)]

theorem fastHookTable_rel (W : CliHooks) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ HookPairSound a.2 b.2)
      (fastHookTable W) (cliHookTable W) := by
  dsimp only [fastHookTable, cliHookTable, pqxdhHookTable, spqrHookTable, List.append_eq]
  refine .cons ⟨rfl, @fastCompress512_post W.Q.F512⟩ <| .cons ⟨rfl, @fastToEdwards_post W.Q.montToEd⟩ <|
    .cons ⟨rfl, @fastCompress_post W.Q.compress⟩ <| .cons ⟨rfl, @fastEdNeg_post W.Q.edNeg⟩ <|
    .cons ⟨rfl, @fastTorsionFree_post W.Q.isTorsionFree⟩ <| .cons ⟨rfl, @fastDsmb_post W.Q.dsmb⟩ <|
    .cons ⟨rfl, @fastScalarMod_post W.Q.scalarMod⟩ <| .cons ⟨rfl, @fastScalarWide_post W.Q.scalarWide⟩ <|
    .cons ⟨rfl, @fastKemEncaps_post W.Q.encaps⟩ <| .cons ⟨rfl, @fastKemDecaps_post W.Q.decaps⟩ <|
    .cons ⟨rfl, @fastMlkemFromSeed_post W.Q.K⟩ <| .cons ⟨rfl, @fastMlkemPk1_post⟩ <|
    .cons ⟨rfl, @fastMlkemPk2_post⟩ <| .cons ⟨rfl, @fastMlkemEncaps1_post W.Q.K⟩ <|
    .cons ⟨rfl, @fastMlkemEncaps2_post W.Q.K⟩ <| .cons ⟨rfl, @fastMlkemDecaps_post W.Q.K⟩ <|
    .cons ⟨rfl, @fastMlkemValidatePk_post W.Q.K⟩ <| .cons ⟨rfl, @fastLibcruxHmac_post W.C.F⟩ <|
    .cons ⟨rfl, @fastHookNoop_post⟩ <| .cons ⟨rfl, @fastAlloc_post⟩ <|
    .cons ⟨rfl, @fastHookNoop_post⟩ <| .cons ⟨rfl, @fastRealloc_post⟩ <|
    .cons ⟨rfl, @fastAllocZeroed_post⟩ <| .cons ⟨rfl, @fastMemset_post⟩ <|
    .cons ⟨rfl, @fastMemcpy_post⟩ <| .cons ⟨rfl, @fastMemcpy_post⟩ <|
    .cons ⟨rfl, @fastCliBcmp_post W.bcmp⟩ <| .cons ⟨rfl, @fastStrlen_post⟩ <|
    .cons ⟨rfl, @fastReadFile_post⟩ <| .cons ⟨rfl, @fastWriteFile_post⟩ <|
    .cons ⟨rfl, @fastReadStdin_post⟩ <| .cons ⟨rfl, @fastWriteStdout_post⟩ <|
    .cons ⟨rfl, @fastMemrchr_post⟩ <| .cons ⟨rfl, @fastFromUtf8_post W.utf8Err⟩ <|
    .cons ⟨rfl, @fastFmtWrite_post⟩ <|
    .cons ⟨rfl, @fastFormatInner_post⟩ <| .cons ⟨rfl, @fastDurationSince_post⟩ <|
    .cons ⟨rfl, @fastTimeAdd_post⟩ <| .cons ⟨rfl, @fastBlackBox_post⟩ <|
    .cons ⟨rfl, @fastCompress256_post W.C.F⟩ <| .cons ⟨rfl, @fastAesEnc_post W.C.E⟩ <|
    .cons ⟨rfl, @fastAesDec_post W.C.D⟩ <| .cons ⟨rfl, @fastPubFromSecret_post W.C.pubKey⟩ <|
    .cons ⟨rfl, @fastDiffieHellman_post W.C.X⟩ <| .cons ⟨rfl, @fastZeroizeSecret_post⟩ <|
    .cons ⟨rfl, @fastZeroizeSecret_post⟩ <| .nil

private theorem lookup_forall2_sound
    {ft : List (String × (FastState → Option FastState))}
    {st : List (String × (State → State))}
    (hrel : List.Forall₂ (fun a b => a.1 = b.1 ∧ HookPairSound a.2 b.2) ft st) (name : String) :
    match ft.lookup name, st.lookup name with
    | some fh, some sh => HookPairSound fh sh | none, none => True | _, _ => False := by
  induction hrel with
  | nil => trivial
  | @cons a b _ _ hab _ ih =>
    rcases a with ⟨fn, fh⟩; rcases b with ⟨sn, sh⟩; rcases hab with ⟨rfl, hps⟩
    simp only [List.lookup]; cases name == fn <;> [exact ih; exact hps]

/-- Looks up the `FastState` hook for `name` prior to `abortOnPanic` wrapping. -/
def fastExternRaw? (W : CliHooks) (name : String) : Option (FastState → Option FastState) :=
  let bs := strUtf8Bytes name
  if fastIsImagePanicSymbolBs bs then some fastPanicked else lookupStrUtf8 bs (fastHookTable W)

/-- Executes the hooked extern symbol `name` on `fs` with `abortOnPanic` wrapping. -/
def fastExecExtern (W : CliHooks) (name : String) (fs : FastState) : Option FastState :=
  (fastExternRaw? W name).bind fun fh => (fh fs).map FastState.abortOnPanic

abbrev fastExecExtern0 : String → FastState → Option FastState := fastExecExtern compHooks0

/-- Returns `true` iff `name` is handled by `cliExternsAbortOnPanic W`. -/
def hasCliHook (W : CliHooks) (name : String) : Bool := (fastExternRaw? W name).isSome

private theorem not_isImagePanicSymbol_capacityOverflow1 :
    isImagePanicSymbol "<hashbrown::raw::Fallibility>::capacity_overflow#1" = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol]

private theorem not_isImagePanicSymbol_allocErr1 :
    isImagePanicSymbol "<hashbrown::raw::Fallibility>::alloc_err#1" = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol]

/-- `isCliPanicSymbol` coincides with `isImagePanicSymbol` because neither entry of
`deadCliHashbrownPanicNames` satisfies `isImagePanicSymbol`. -/
theorem isCliPanicSymbol_eq_isImagePanicSymbol (name : String) :
    isCliPanicSymbol name = isImagePanicSymbol name := by
  cases h : isImagePanicSymbol name with
  | false => simp [isCliPanicSymbol, h]
  | true =>
    have hc : name ≠ "<hashbrown::raw::Fallibility>::capacity_overflow#1" := by
      rintro rfl
      rw [not_isImagePanicSymbol_capacityOverflow1] at h
      cases h
    have ha : name ≠ "<hashbrown::raw::Fallibility>::alloc_err#1" := by
      rintro rfl
      rw [not_isImagePanicSymbol_allocErr1] at h
      cases h
    simp [isCliPanicSymbol, deadCliHashbrownPanicNames, h, hc, ha]

theorem hasCliHook_eq_isSome (W : CliHooks) (name : String) :
    hasCliHook W name = ((cliExternsAbortOnPanic W) name).isSome := by
  unfold hasCliHook fastExternRaw? cliExternsAbortOnPanic cliExterns withCliPanics
  dsimp only
  rw [isCliPanicSymbol_eq_isImagePanicSymbol, ← fastIsImagePanicSymbol,
    fastIsImagePanicSymbol_eq, lookupStrUtf8_eq_lookup]
  cases isImagePanicSymbol name
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact match (fastHookTable W).lookup name, (cliHookTable W).lookup name,
        lookup_forall2_sound (fastHookTable_rel W) name with
      | none, none, _ => rfl | some _, some _, _ => rfl
      | none, some _, h => False.elim h | some _, none, h => False.elim h
  · rfl

theorem fastExecExtern_exists_sound {W : CliHooks} {name : String}
    {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastExecExtern W name fs = some fs') :
    ∃ h, cliExternsAbortOnPanic W name = some h ∧
      fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab := by
  unfold fastExecExtern fastExternRaw? at hsome
  dsimp only at hsome
  rw [← fastIsImagePanicSymbol, fastIsImagePanicSymbol_eq, lookupStrUtf8_eq_lookup] at hsome
  unfold cliExternsAbortOnPanic cliExterns withCliPanics
  simp only [isCliPanicSymbol_eq_isImagePanicSymbol]
  cases hpan : isImagePanicSymbol name with
  | true =>
    simp only [hpan, ↓reduceIte, Option.bind_some, Option.map_eq_some_iff, Option.map_some] at hsome ⊢
    obtain ⟨fs1, hfs1, rfl⟩ := hsome
    exact ⟨abortOnPanic Rust.panicked, rfl, fastAbortOnPanic_post (fastPanicked_post hag hfs1)⟩
  | false =>
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    have hlk := lookup_forall2_sound (fastHookTable_rel W) name
    cases hfl : (fastHookTable W).lookup name with
    | none => rw [hfl] at hsome; cases hsome
    | some fh =>
      rw [hfl] at hsome hlk
      cases hsl : (cliHookTable W).lookup name with
      | none => rw [hsl] at hlk; exact False.elim hlk
      | some sh =>
        rw [hsl] at hlk
        simp only [Option.bind_some, Option.map_eq_some_iff, Option.map_some] at hsome ⊢
        obtain ⟨fs1, hfs1, rfl⟩ := hsome
        exact ⟨abortOnPanic sh, rfl, fastAbortOnPanic_post (hlk hag hfs1)⟩

/-- Soundness of `fastExecExtern` against `cliExternsAbortOnPanic W`: preserves state agreement,
frozen memory, and the symbol table. -/
theorem fastExecExtern_sound {W : CliHooks} {name : String}
    {fs fs' : FastState} {s : State} {h : State → State}
    (hag : fs.Agrees s) (hsome : fastExecExtern W name fs = some fs')
    (hext : cliExternsAbortOnPanic W name = some h) :
    fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab := by
  obtain ⟨h', hext', hpost⟩ := fastExecExtern_exists_sound hag hsome
  rw [hext] at hext'; injection hext' with heq; subst heq; exact hpost

theorem fastExecExtern0_exists_sound {name : String} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastExecExtern0 name fs = some fs') :
    ∃ h, cliExternsAbortOnPanic compHooks0 name = some h ∧
      fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab :=
  fastExecExtern_exists_sound hag hsome

theorem fastExecExtern0_sound {name : String} {fs fs' : FastState} {s : State} {h : State → State}
    (hag : fs.Agrees s) (hsome : fastExecExtern0 name fs = some fs')
    (hext : cliExternsAbortOnPanic compHooks0 name = some h) :
    fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab :=
  fastExecExtern_sound hag hsome hext

end Symbolic.BugInjection.Proofs.CliExec.FastHooks
