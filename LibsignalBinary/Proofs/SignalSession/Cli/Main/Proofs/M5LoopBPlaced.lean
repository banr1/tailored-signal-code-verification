/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBStepPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Inner Loop B Induction (`M+0x9e8 .. M+0xa68`, Block `617`)

Verifies `m5_loop_b_one_placed` and `m5_loop_b_entries_placed` on Block `617` under
`[LibsignalPlacement]`, committing all `(name, bs)` entries of a `Dir` when `d.path = []`.
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

private theorem bv_mul48_sub48 (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) - 48#64 = BitVec.ofNat 64 (n * 48) := by
  have heq : (n + 1) * 48 = n * 48 + 48 := by omega
  rw [heq, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel (BitVec.ofNat 64 (n * 48)) 48#64

private theorem bv_mul48_add_neg48 (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) + (-48#64) = BitVec.ofNat 64 (n * 48) := by
  rw [← BitVec.sub_eq_add_neg]
  exact bv_mul48_sub48 n

private theorem bv_mul48_beq0_false {α : Type} (e' : α) (rest' : List α)
    (hle : (e' :: rest').length * 48 < 2 ^ 64) :
    (BitVec.ofNat 64 ((e' :: rest').length * 48) == 0#64) = false :=
  ofNat_beq_zero_false (by simp only [List.length_cons]; omega) hle

private theorem addr_advance_entry {α : Type} (curPtr : BitVec 64) (done : List α) (e : α) :
    curPtr + BitVec.ofNat 64 (done.length * 48) + 88#64 =
      curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
  have hlen_add : (done ++ [e]).length * 48 = done.length * 48 + 48 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen_add, BitVec.ofNat_add]; bv_omega

private theorem addr_advance_entry' {α : Type} (curPtr : BitVec 64) (done : List α) (e : α) :
    (curPtr + BitVec.ofNat 64 (done.length * 48) + 40#64) + 48#64 =
      curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
  have hlen_add : (done ++ [e]).length * 48 = done.length * 48 + 48 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen_add, BitVec.ofNat_add]; bv_omega

set_option maxHeartbeats 1600000 in
/-- Single iteration of inner Loop B (`d.path = []`) for head entry `e` and tail `rest`. -/
theorem m5_loop_b_one_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {rest done : List (List (BitVec 8) × List (BitVec 8))}
    {s0 s : State} {v40 v48 v58 v458 v460 v468 : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
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
    (herr : ∀ (se : State) (errE : M5ErrEntryPlaced),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp (mainOom s0))
    (hnext : ∀ sf : State,
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp (mainOom s0))
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
    (hmore : ∀ (s' : State) (P' : SepProp),
      rest ≠ [] →
      ((storesDirs g)[k]'(by simp [hk])).changed = (done ++ [e]) ++ rest →
      InMainPlaced CodeOk s0 s' 0x9e8 →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P' ⊢ vecBuf A 48 8 (dirEntryAt A) curCap curPtr ((done ++ [e]) ++ rest) ∗
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
        A.pool ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s' P' Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have hne_cur : ((storesDirs g)[k]'(by simp [hk])).changed ≠ [] := by
    intro h0; rw [hsplit] at h0; simp at h0
  refine m5_loop_b_write_entry_placed (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr)
    (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
    (out := out) (inp := inp) (ps := ps)
    hA hc hio hs0tr hpanic hstk_ext hstk_hook hstk64
    hk hpaths hdpath
    hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP herr ?_
  intro s_end F' hle_tot hcap_lt hse hfse hwr_ok htre hstdoute r19 r20 r24 r25 r26
  have hfiles_next :
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some F' :=
    commitFiles_entry_ok hk hfiles (by simpa only [hdpath, pathOf_nil] using hwr_ok)
  have hpce := hse.pc; have hrune := hse.run
  cases rest with
  | nil =>
    apply m5_seq_placed hse.inv (mid := mPcPlaced 0xa6c)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl]; try m5_bv_omega)
      (by simp only [arm64_norm, hrune])
    intro hpcm hrunm hinv_m
    have hfiles_k1 : commitFiles io.wr F0 (writesBefore g (k + 1)) = some F' := by
      rwa [writesBefore_entry_done hk hsplit] at hfiles_next
    apply m5_after_entries_placed (CodeOk := CodeOk) (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      (out := out) (inp := inp) (ps := ps)
      hA hstk_ext hstk64 hk hne_cur
    · exact hse.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
    · simp only [arm64_norm, r19]
    · simp only [arm64_norm, r20]
    · simp only [arm64_norm, r24]
    · simp only [arm64_norm, hfse, hfiles_k1]
    · simp only [arm64_norm]; exact htre
    · simp only [arm64_norm, hstdoute]
    · rw [← hsplit]; exact Entails.refl _
    · exact hnext
  | cons e' rest' =>
    have hrem_lt : (e' :: rest').length * 48 < 2 ^ 64 := by
      simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
    have htot_lt64 : (e :: e' :: rest').length * 48 < 2 ^ 64 := by
      simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
    have hne48 : BitVec.ofNat 64 ((e :: e' :: rest').length * 48) ≠ 48#64 := by
      intro heq
      have h1 : ((e :: e' :: rest').length * 48) % 2 ^ 64 = 48 := congrArg BitVec.toNat heq
      rw [Nat.mod_eq_of_lt htot_lt64] at h1
      simp only [List.length_cons] at h1; omega
    have hsub_eq1 :
        BitVec.ofNat 64 ((e :: e' :: rest').length * 48) - 48#64 =
          BitVec.ofNat 64 ((e' :: rest').length * 48) :=
      bv_mul48_sub48 (e' :: rest').length
    have hsub_eq2 :
        BitVec.ofNat 64 ((e :: e' :: rest').length * 48) + (-48#64) =
          BitVec.ofNat 64 ((e' :: rest').length * 48) :=
      bv_mul48_add_neg48 (e' :: rest').length
    have hx25_next := addr_advance_entry curPtr done e
    have hx25_next' := addr_advance_entry' curPtr done e
    apply m5_seq_placed hse.inv (mid := mPcPlaced 0x9e8)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl, hsub_eq1, hsub_eq2, bv_mul48_beq0_false e' rest' hrem_lt]; try m5_bv_omega)
      (by simp only [arm64_norm, hrune])
    intro hpcm hrunm hinv_m
    apply hmore
    · exact List.cons_ne_nil _ _
    · simp only [List.append_assoc, List.singleton_append]; exact hsplit
    · exact hse.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
    · simp only [arm64_norm, r19]
    · simp only [arm64_norm, r20]
    · simp only [arm64_norm, r24]
    · simp only [arm64_norm, r25, hx25_next, hx25_next']
    · simp only [arm64_norm, r26, hsub_eq1, hsub_eq2]
    · simp only [arm64_norm, hfse, hfiles_next]
    · simp only [arm64_norm]; exact htre
    · simp only [arm64_norm, hstdoute]
    · simp only [List.append_assoc, List.singleton_append]; exact Entails.refl _

/-- Commits all remaining entries `rest ≠ []` of `Dir k` (`d.path = []`) starting at `M+0x9e8` with
`done` already committed (`curEntries = done ++ rest`). -/
theorem m5_loop_b_entries_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop}
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
    (herr : ∀ (se : State) (errE : M5ErrEntryPlaced),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp (mainOom s0))
    (hnext : ∀ sf : State,
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp (mainOom s0)) :
    ∀ (rest done : List (List (BitVec 8) × List (BitVec 8)))
      (s : State) (v40 v48 v58 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x9e8 →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ rest) ∗
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
        A.pool ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  intro rest; induction rest with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ hne_r; intros
    exact (hne_r rfl).elim
  | cons e rest ih =>
    intro done s v40 v48 v58 v458 v460 v468 P _ hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP
    exact m5_loop_b_one_placed (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (out := out) (inp := inp) (ps := ps)
      (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      hA hc hio hs0tr hpanic hstk_ext hstk_hook hstk64
      hk hpaths hdpath herr hnext hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP
      fun s' P' => ih (done ++ [e]) s' v40 v48 v58 v458 v460 v468 P'

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
