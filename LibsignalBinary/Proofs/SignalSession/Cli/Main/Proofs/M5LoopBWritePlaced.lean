/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Inner Loop B Non-Empty Entry Write (`M+0x9e8 .. M+0xa48`, Block `617`)

Verifies `m5_loop_b_write_nonempty_placed` on Block `617` under `[LibsignalPlacement]`, allocating
the path copy and invoking `write_file` for a non-empty entry name when `d.path = []`.
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
/-- Extract pure length/capacity bounds from `entryBorrowRest` without unfolding its frame in callers. -/
theorem entryBorrowRest_pure (A : RustAlloc) (curCap curPtr : BitVec 64)
    (done : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (c1 p1 c2 p2 : BitVec 64) :
    entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 =
      ⌜e.2.length < 2 ^ 63 ∧
        (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
        entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 := by
  apply Entails.antisymm
  · unfold entryBorrowRest
    apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
    exact Entails.pure_right ⟨Nat.lt_of_le_of_lt h2.1 h2.2.1, h3.1, h3.2.1⟩
      (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
  · apply Entails.pure_left; intro _; exact Entails.refl _

set_option maxHeartbeats 1600000 in
/-- Execute `M+0x9e8 .. M+0xa48` for a single non-empty entry `e` of `Dir k` (`d.path = []`), handing
either write failure to `herr` (`0xbdc`) or write success to `hcont_a60` at `M+0xa60` together
with `(done ++ e :: rest).length ≤ curCap.toNat`. -/
theorem m5_loop_b_write_nonempty_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
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
    (hpos : 0 < e.1.length)
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
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
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
        (curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64 := by m5_bv_omega
    have hb : ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) + 16#64 =
        ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64 := by m5_bv_omega
    rw [ha, hb]
  have hpc := hs.pc; have hrun := hs.run
  have he1_beq0 : (BitVec.ofNat 64 e.1.length == 0#64) = false :=
    ofNat_beq_zero_false hpos (by m5_omega)
  have he1_toNat : (BitVec.ofNat 64 e.1.length).toNat = e.1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  have hlay1 : LayoutOk e.1.length 1 := ⟨hpos, ⟨0, rfl⟩, by m5_omega⟩
  refine m5_run_placed hs.inv (mid := lsρ lsRustNoAllocShimSymCli)
    (P0 := (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 8#64) ↦₆₄ p1) ∗
      (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length))
    (F := ((curPtr + BitVec.ofNat 64 (done.length * 48)) ↦₆₄ c1) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ invFrame)
    (by unfold vecHeader; dsimp only [invFrame, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm1 hrunm1 hinv_m1
  refine m5_call_shim_placed hA hstk_ext hstk64 hpcm1 hrunm1 hinv_m1
    (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
    (retOff := 0x9fc) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ A.pool ∗ invFrame)
    (by unfold vecHeader; exact Entails.of_eq (by ac_rfl)) ?_
  intro s1 hs1 hfs1 htr1 hcsm1
  have hpc1 := hs1.pc; have hrun1 := hs1.run
  have r21_1 : s1.readReg64 (.gpr 21#5) = p1 := by simp only [hcsm1.2.2.1, arm64_norm]
  have r25_1 : s1.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
    hcsm1.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
  have r23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length := by
    simp only [hcsm1.2.2.2.2.1, arm64_norm]
  apply m5_seq_placed hs1.inv (mid := lsρ lsRustAllocSymCli)
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm2 hrunm2 hinv_m2
  refine m5_call_alloc_placed hA hs0tr hstk_ext hstk64 hlay1 hpcm2 hrunm2 hinv_m2
    (by simp only [arm64_norm, hs1.sp]) (by simp only [arm64_norm, hs1.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs1.vregs]) hs1.spAligned
    (retOff := 0xa08) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, r23_1, he1_toNat]) (by simp only [arm64_norm]; try rfl)
    (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame)
    (Entails.of_eq (by ac_rfl)) ?_ ?_
  · intro s2 hs2 hx0_2 haf2
    have hpc2 := hs2.pc; have hrun2 := hs2.run
    apply m5_seq_placed hs2.inv (mid := mPcPlaced 0xba8)
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
    intro hpcm3 hrunm3 hinv_m3
    exact m5_oom_ba8_placed hc hpanic hs0tr
      (hs2.mk_step (by simpa only [mPcPlaced_eq_blkPl] using hpcm3) hrunm3
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m3 (by simp only [calleeSavedVRegs, arm64_norm]))
      (allocFailedIn_of_prefix haf2 (by simp only [arm64_norm]; exact List.prefix_refl _))
  · intro s2 hs2 htmp_ne hfs2 htr2 hcsm2
    let tmpPtr := s2.readReg64 .x0
    have htmp_beq : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne htmp_ne
    have hpc2 := hs2.pc; have hrun2 := hs2.run
    have r21_2 : s2.readReg64 (.gpr 21#5) = p1 := hcsm2.2.2.1.trans (by simp only [arm64_norm, r21_1])
    have r25_2 : s2.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
      hcsm2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_1])
    have r23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
      hcsm2.2.2.2.2.1.trans (by simp only [arm64_norm, r23_1])
    apply m5_seq_placed hs2.inv (mid := lsρ memcpyName)
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm3 hrunm3 hinv_m3
    refine m5_call_memcpy_placed hA hstk_ext hstk64 hpcm3 hrunm3 hinv_m3
      (by simp only [arm64_norm, hs2.sp]) (by simp only [arm64_norm, hs2.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs2.vregs]) hs2.spAligned
      (retOff := 0xa24) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (dst := tmpPtr) (src := p1) (bs := e.1)
      (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm, r21_2])
      (by simp only [arm64_norm, r23_2, he1_toNat])
      (F := A.pool ∗ A.live tmpPtr e.1.length 1 ∗
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p2 ↦ₛ e.2) ∗ invFrame)
      (by dsimp only [tmpPtr]; exact Entails.of_eq (by ac_rfl)) ?_
    intro s3 hs3 hfs3 htr3 hcsm3
    have hpc3 := hs3.pc; have hrun3 := hs3.run
    have r25_3 : s3.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
      hcsm3.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_2])
    have r22_3 : s3.readReg64 (.gpr 22#5) = tmpPtr :=
      hcsm3.2.2.2.1.trans (by simp only [arm64_norm]; try rfl)
    have r23_3 : s3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
      hcsm3.2.2.2.2.1.trans (by simp only [arm64_norm, r23_2])
    refine m5_run_placed hs3.inv (mid := lsρ lsWriteFileSym)
      (P0 := (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) ↦₆₄ p2) ∗
        ((((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64) ↦₆₄
          BitVec.ofNat 64 e.2.length))
      (F := (tmpPtr ↦ₛ e.1) ∗ (p1 ↦ₛ e.1) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ A.live tmpPtr e.1.length 1 ∗
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) ↦₆₄ c2) ∗
        (p2 ↦ₛ e.2) ∗ invFrame)
      (by rw [off_hdr2]; exact Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm4 hrunm4 hinv_m4
    refine m5_call_write_file_placed hio hstk_hook hstk64 hpcm4 hrunm4 hinv_m4
      (by simp only [arm64_norm, hs3.sp]) (by simp only [arm64_norm, hs3.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs3.vregs]) hs3.spAligned
      (retOff := 0xa34) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (pathA := tmpPtr) (path := e.1) (buf := p2) (bs := e.2)
      (by simp only [arm64_norm, r22_3]) (by simp only [arm64_norm, r23_3, he1_toNat])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, he2_toNat])
      he_lt he_ok
      (F := A.live tmpPtr e.1.length 1 ∗
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ A.pool ∗ invFrame)
      (by rw [off_hdr2]; exact Entails.of_eq (by ac_rfl)) ?_
    intro s4 hs4 hwr4 htr4 hout4 hcsm4
    have hfs_chain : s3.fs.files = s.fs.files := by simp only [hfs3, arm64_norm, hfs2, hfs1]
    simp only [arm64_norm, hfs_chain] at hwr4
    have htr_chain : tr0 <+: s4.trace := by
      have h3t : s3.trace = s.trace := by simp only [htr3, arm64_norm, htr2, htr1]
      have h4t : s3.trace <+: s4.trace := by simpa only [arm64_norm] using htr4
      exact htr0.trans (h3t ▸ h4t)
    have hout_chain : ProcessOutcome.traceStreamBytes .stdout s4.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 := by
      have h3t : s3.trace = s.trace := by simp only [htr3, arm64_norm, htr2, htr1]
      simpa only [arm64_norm, h3t, hstdout] using hout4
    have r19_4 : s4.readReg64 (.gpr 19#5) = buf := by
      simp only [hcsm4.1, arm64_norm, hcsm3.1, hcsm2.1, hcsm1.1, hx19]
    have r20_4 : s4.readReg64 (.gpr 20#5) =
        BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length := by
      simp only [hcsm4.2.1, arm64_norm, hcsm3.2.1, hcsm2.2.1, hcsm1.2.1, hx20]
    have r22_4 : s4.readReg64 (.gpr 22#5) = tmpPtr :=
      hcsm4.2.2.2.1.trans (by simp only [arm64_norm, r22_3])
    have r23_4 : s4.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
      hcsm4.2.2.2.2.1.trans (by simp only [arm64_norm, r23_3])
    have r24_4 : s4.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
      simp only [hcsm4.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.1,
        hcsm2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.1, hx24]
    have r25_4 : s4.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
      hcsm4.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_3])
    have r26_4 : s4.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) := by
      simp only [hcsm4.2.2.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.2.2.1,
        hcsm2.2.2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.2.2.1, hx26]
    have hpc4 := hs4.pc; have hrun4 := hs4.run
    cases hwr_eq : io.wr s.fs.files e.1 e.2 with
    | none =>
      rw [hwr_eq] at hwr4; rcases hwr4 with ⟨hx0_4, _⟩
      apply m5_seq_placed hs4.inv (mid := mPcPlaced 0xbdc)
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
      intro hpcm5 hrunm5 hinv_m5
      let errBdc := M5ErrEntryPlaced.bdc (BitVec.ofNat 64 e.1.length) tmpPtr e.1
      have herr_st : M5LoopErrPlaced CodeOk io F0 tr0 g s0 _ n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed errBdc :=
        { hk := hk, hne := hne_cur
          errRegs := ⟨by simp only [arm64_norm, r22_4], by simp only [arm64_norm, r23_4],
            ofNat_ne_zero hpos (by m5_omega)⟩
          base := hs4.mk_step (by simpa only [mPcPlaced_eq_blkPl, errBdc, M5ErrEntryPlaced.pcOff] using hpcm5) hrunm5
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv_m5 (by simp only [calleeSavedVRegs, arm64_norm])
          x19 := by simp only [arm64_norm, r19_4]
          x24 := by simp only [arm64_norm, r24_4]
          x20 := by simp only [arm64_norm, r20_4]
          commitNone := commitFiles_entry_err hk hsplit hfiles
            (by simpa only [hdpath, pathOf_nil] using hwr_eq)
          trace := by simp only [arm64_norm]; exact htr_chain
          stdout := by simp only [arm64_norm, hout_chain] }
      refine SepWPp.weaken_pre ?_ (herr _ errBdc herr_st)
      refine Entails.trans ?_ (to_err_mem errBdc)
      dsimp only [errBdc, M5ErrEntryPlaced.heap]
      have hord :
          (tmpPtr ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ stackAt fsp (stk - mainFrameSize) ∗
            (A.live tmpPtr e.1.length 1 ∗
              vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
              vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                (BitVec.ofNat 64 e.2.length) ∗
              (p1 ↦ₛ e.1) ∗ A.pool ∗ invFrame) =
          (A.live tmpPtr e.1.length 1 ∗ (tmpPtr ↦ₛ e.1)) ∗
            (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
              vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                (BitVec.ofNat 64 e.2.length) ∗
              (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
              stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ invFrame) := by ac_rfl
      rw [hord]
      exact sepConj_mono_left (ownedBytes_of_live_bytes A tmpPtr e.1 hpos (by m5_omega) htmp_ne)
    | some F' =>
      rw [hwr_eq] at hwr4; rcases hwr4 with ⟨hx0_4, hfs_4⟩
      apply m5_seq_placed hs4.inv (mid := lsρ lsRustDeallocSymCli)
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
        (by simp only [arm64_norm, *])
      intro hpcm5 hrunm5 hinv_m5
      refine m5_call_dealloc_placed hA hstk_ext hstk64 hlay1 hpcm5 hrunm5 hinv_m5
        (by simp only [arm64_norm, hs4.sp]) (by simp only [arm64_norm, hs4.fp])
        (by simp only [calleeSavedVRegs, arm64_norm, hs4.vregs]) hs4.spAligned
        (retOff := 0xa48) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
        (ptr := tmpPtr) (by simp only [arm64_norm, r22_4])
        (by simp only [arm64_norm, r23_4, he1_toNat]) (by simp only [arm64_norm]; try rfl)
        (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame)
        (by
          have hord :
              (tmpPtr ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ stackAt fsp (stk - mainFrameSize) ∗
                (A.live tmpPtr e.1.length 1 ∗
                  vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
                    (BitVec.ofNat 64 e.1.length) ∗
                  vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                    (BitVec.ofNat 64 e.2.length) ∗
                  (p1 ↦ₛ e.1) ∗ A.pool ∗ invFrame) =
              (tmpPtr ↦ₛ e.1) ∗
                (A.live tmpPtr e.1.length 1 ∗ A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
                  vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
                    (BitVec.ofNat 64 e.1.length) ∗
                  vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                    (BitVec.ofNat 64 e.2.length) ∗
                  (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame) := by ac_rfl
          rw [hord]
          exact Entails.trans (sepConj_mono_left (bytes_entails_memRegion tmpPtr e.1))
            (Entails.of_eq (by ac_rfl))) ?_
      intro s5 hs5 hfs5 htr5 hcsm5
      have hpc5 := hs5.pc; have hrun5 := hs5.run
      apply m5_seq_placed hs5.inv (mid := mPcPlaced 0xa60)
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
      intro hpcm6 hrunm6 hinv_m6
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hunb_loop)
        (hcont_a60 _ F' hle_tot hcap_lt
          (hs5.mk_step (by simpa only [mPcPlaced_eq_blkPl] using hpcm6) hrunm6
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m6 (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hfs5, hfs_4])
          hwr_eq
          (by simp only [arm64_norm]; exact htr5 ▸ htr_chain)
          (by simp only [arm64_norm, htr5, hout_chain])
          (by simp only [arm64_norm, hcsm5.1, r19_4])
          (by simp only [arm64_norm, hcsm5.2.1, r20_4])
          (by simp only [arm64_norm, hcsm5.2.2.2.2.2.1, r24_4])
          (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.1, r25_4])
          (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.2.1, r26_4]))

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
