/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Inner Loop B Entry Step (`M+0x9e8 .. M+0xa60`, Block `617`)

Verifies `m5_loop_b_write_entry_placed` on Block `617` under `[LibsignalPlacement]`, dispatching
empty vs. non-empty entry names in Loop B (`d.path = []`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.LoopDrop

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1600000 in
theorem m5_loop_b_write_entry_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr v40 v48 v58 v458 v460 v468 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {done rest : List (List (BitVec 8) × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = [])
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hs : InMainPlaced CodeOk s0 s 0x9e8)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hfiles : commitFiles io.wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest) ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool ∗ anyHeap)
    (herr : ∀ (se : State) (errE : M5ErrEntryPlaced),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp (mainOom s0))
    (hcont_a60 : ∀ (s_end : State) (F' : FsFiles),
      (done ++ e :: rest).length ≤ curCap.toNat →
      curCap.toNat * 48 < 2 ^ 63 →
      InMainPlaced CodeOk s0 s_end 0xa60 →
      s_end.fs.files = F' →
      io.wr s.fs.files e.1 e.2 = some F' →
      tr0 <+: s_end.trace →
      ProcessOutcome.traceStreamBytes .stdout s_end.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      s_end.readReg64 (.gpr 19#5) = buf →
      s_end.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s_end.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s_end.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s_end.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s_end
        (vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest) ∗
          m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
            curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  rcases (show e.1 = [] ∨ 0 < e.1.length by cases e.1 <;> simp) with he0 | hpos
  · let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    have hne_cur : ((storesDirs g)[k]'(by simp [hk])).changed ≠ [] := by rw [hsplit]; simp
    have he_mem : e ∈ ((storesDirs g)[k]'(by simp [hk])).changed := by
      rw [hsplit]; exact List.mem_append_right _ (.head _)
    have ⟨he_ok, he_lt⟩ : io.pathOk e.1 ∧ e.1.length < 2 ^ 32 := by
      simpa only [hdpath, pathOf_nil] using dir_entry_path_ok_len hk hpaths he_mem
    have hbit63a : (BitVec.ofNat 64 e.1.length).getLsbD 63 = false :=
      ofNat_getLsbD_63_false (by m5_omega)
    have hbit63b : (BitVec.ofNat 64 e.1.length)[63] = false :=
      ofNat_getElem_63_false (by m5_omega)
    refine SepWPp.weaken_pre hP ?_
    rw [vecBuf_borrow_eq A curCap curPtr done e rest]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun c1 => ?_
    refine SepWPp.exists_elim fun p1 => ?_
    refine SepWPp.exists_elim fun c2 => ?_
    refine SepWPp.exists_elim fun p2 => ?_
    rw [entryBorrowRest_pure A curCap curPtr done e rest c1 p1 c2 p2]
    have hpure_front :
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          (⌜e.2.length < 2 ^ 63 ∧
            (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
            entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2)) =
        ⌜e.2.length < 2 ^ 63 ∧
          (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2) := by
      ac_rfl
    rw [hpure_front]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨he2_lt63, hle_tot, hcap_lt⟩ => ?_
    have he2_toNat : (BitVec.ofNat 64 e.2.length).toNat = e.2.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
    let invFrame : SepProp :=
      entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 ∗
        m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          v40 v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗ anyHeap
    have hunb_loop :
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ invFrame) ⊢
        vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest) ∗
          m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
      dsimp only [invFrame]
      have hord :
          vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗
            (entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 ∗
              m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                v40 v48 v58 v458 v460 v468 ∗
              m5WorkRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
              ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗ anyHeap) =
          (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2) ∗
          (m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
              v40 v48 v58 v458 v460 v468 ∗
            m5WorkRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
            ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) := by ac_rfl
      rw [hord]
      exact sepConj_mono_left (vecBuf_unborrow A curCap curPtr done e rest c1 p1 c2 p2)
    have to_err_mem : ∀ (errE : M5ErrEntryPlaced),
        errE.heap A ∗
          (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ invFrame) ⊢
        m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE := by
      intro errE
      refine Entails.trans (sepConj_mono_right hunb_loop) ?_
      have hexit := m5Work_exit_to_err_placed A fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g hk v40 v48 v58 v458 v460 v468
      dsimp only [m5ErrMemPlaced, fsp]
      rw [← hsplit]
      have hord :
          errE.heap A ∗
            (vecBuf A 48 8 (dirEntryAt A) curCap curPtr ((storesDirs g)[k]'(by simp [hk])).changed ∗
              m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
                (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                v40 v48 v58 v458 v460 v468 ∗
              m5WorkRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
                outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
              ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              A.pool ∗ anyHeap) =
          (m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
              v40 v48 v58 v458 v460 v468 ∗
            m5WorkRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
          (errE.heap A ∗
            vecBuf A 48 8 (dirEntryAt A) curCap curPtr ((storesDirs g)[k]'(by simp [hk])).changed ∗
            ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ anyHeap) := by ac_rfl
      rw [hord]
      exact Entails.trans (sepConj_mono_left hexit) (Entails.of_eq (by ac_rfl))
    have off_m24 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-24#64) =
        (curPtr + BitVec.ofNat 64 (done.length * 48)) + 16#64 := by rw [BitVec.add_assoc]; rfl
    have off_m32 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-32#64) =
        (curPtr + BitVec.ofNat 64 (done.length * 48)) + 8#64 := by rw [BitVec.add_assoc]; rfl
    have off_m8 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-8#64) =
        (curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64 := by rw [BitVec.add_assoc]; rfl
    have off_hdr2 :
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) =
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) ↦₆₄ c2) ∗
          (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) ↦₆₄ p2) ∗
          ((((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64) ↦₆₄
            BitVec.ofNat 64 e.2.length) := by
      unfold vecHeader
      have ha : ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) + 8#64 =
          (curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64 := by rw [BitVec.add_assoc]; rfl
      have hb : ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) + 16#64 =
          ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64 := by
        simp only [BitVec.add_assoc]; rfl
      rw [ha, hb]
    have hpc := hs.pc; have hrun := hs.run
    have hlen0 : BitVec.ofNat 64 e.1.length = 0#64 := by simp [he0]
    refine m5_run_placed hs.inv (mid := lsρ lsWriteFileSym)
      (P0 := (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 16#64) ↦₆₄
          BitVec.ofNat 64 e.1.length) ∗
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) ↦₆₄ p2) ∗
        ((((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64) ↦₆₄
          BitVec.ofNat 64 e.2.length))
      (F := ((curPtr + BitVec.ofNat 64 (done.length * 48)) ↦₆₄ c1) ∗
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 8#64) ↦₆₄ p1) ∗
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) ↦₆₄ c2) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ invFrame)
      (by rw [off_hdr2]; unfold vecHeader; dsimp only [invFrame, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm hrunm hinv_m
    refine m5_call_write_file_placed hio hstk_hook hstk64 hpcm hrunm hinv_m
      (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
      (retOff := 0xa5c) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (pathA := 1#64) (path := []) (buf := p2) (bs := e.2)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]; try rfl)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]; exact he2_toNat)
      (by decide) (by simpa [he0] using he_ok)
      (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ A.pool ∗ invFrame)
      (by rw [pointsToBytes_nil, emp_sepConj, off_hdr2]; unfold vecHeader; exact Entails.of_eq (by ac_rfl))
      ?_
    intro sm hsm hwr htrm houtm hcsm
    simp only [arm64_norm] at hwr htrm houtm
    have hpcs_m := hsm.pc; have hruns_m := hsm.run
    cases hwr_eq : io.wr s.fs.files [] e.2 with
    | none =>
      rw [hwr_eq] at hwr; rcases hwr with ⟨hx0_m, _⟩
      apply m5_seq_placed hsm.inv (mid := mPcPlaced 0xbf4)
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
      intro hpcm2 hrunm2 hinv_m2
      have herr_st : M5LoopErrPlaced CodeOk io F0 tr0 g s0 _ n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed .bf4 :=
        { hk := hk, hne := hne_cur, errRegs := trivial
          base := hsm.mk_step (by simpa only [mPcPlaced_eq_blkPl, M5ErrEntryPlaced.pcOff] using hpcm2) hrunm2 (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv_m2 (by simp only [calleeSavedVRegs, arm64_norm])
          x19 := by simp only [arm64_norm, hcsm.1, hx19]
          x24 := by simp only [arm64_norm, hcsm.2.2.2.2.2.1, hx24]
          x20 := by simp only [arm64_norm, hcsm.2.1, hx20]
          commitNone := commitFiles_entry_err hk hsplit hfiles
            (by simpa only [hdpath, pathOf_nil, he0] using hwr_eq)
          trace := by simp only [arm64_norm]; exact htr0.trans htrm
          stdout := by simp only [arm64_norm, houtm, hstdout] }
      refine SepWPp.weaken_pre ?_ (herr _ .bf4 herr_st)
      refine Entails.trans ?_ (to_err_mem .bf4)
      dsimp only [M5ErrEntryPlaced.heap]; rw [pointsToBytes_nil]; exact Entails.of_eq (by ac_rfl)
    | some F' =>
      rw [hwr_eq] at hwr; rcases hwr with ⟨hx0_m, hfs_m⟩
      apply m5_seq_placed hsm.inv (mid := mPcPlaced 0xa60)
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
      intro hpcm2 hrunm2 hinv_m2
      refine SepWPp.weaken_pre
        (by rw [pointsToBytes_nil, emp_sepConj]; exact Entails.trans (Entails.of_eq (by ac_rfl)) hunb_loop)
        (hcont_a60 _ F' hle_tot hcap_lt
          (hsm.mk_step (by simpa only [mPcPlaced_eq_blkPl] using hpcm2) hrunm2 (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m2 (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hfs_m])
          (by simpa only [he0] using hwr_eq)
          (by simp only [arm64_norm]; exact htr0.trans htrm)
          (by simp only [arm64_norm, houtm, hstdout])
          (by simp only [arm64_norm, hcsm.1, hx19])
          (by simp only [arm64_norm, hcsm.2.1, hx20])
          (by simp only [arm64_norm, hcsm.2.2.2.2.2.1, hx24])
          (by simp only [arm64_norm, hcsm.2.2.2.2.2.2.1, hx25])
          (by simp only [arm64_norm, hcsm.2.2.2.2.2.2.2.1, hx26]))
  · exact m5_loop_b_write_nonempty_placed (curPtr := curPtr) hA hc hio hs0tr hpanic hstk_ext hstk_hook hstk64
      hk hpaths hdpath hpos hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout
      hP herr hcont_a60

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
