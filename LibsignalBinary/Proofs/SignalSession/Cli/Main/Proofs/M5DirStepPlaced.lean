/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Single-`Dir` Commit Step for `main` Hop M5 (Block `617`)

Verifies inner Loop A entry induction (`m5_loop_a_entries_placed`) and single-directory commit
dispatch (`m5_dir_step_placed`, `M+0x8b8 → AtM5LoopPlaced (k + 1)`) on Block `617` under
`[LibsignalPlacement]`.
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

attribute [local irreducible] SepWPp Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Inner Loop A Wrapper (`m5_loop_a_entries_placed`) & Single `Dir` Dispatch (`m5_dir_step_placed`) -/

/-- Commits all remaining entries `rest ≠ []` of `Dir k` (`d.path ≠ []`) starting at `M+0x8fc` with
`done` already committed (`curEntries = done ++ rest`) and `(dPathPtr ↦ᵣ d.path)` in frame. -/
theorem m5_loop_a_entries_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr dPathPtr v58 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hd_ne : ((storesDirs g)[k]'(by simp [hk])).path ≠ [])
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
      (s : State) (v48 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x8fc →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      s.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
        vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ rest) ∗
        m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
          curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  intro rest; induction rest with
  | nil => intro _ _ _ _ _ _ _ hne_r; intros; exact (hne_r rfl).elim
  | cons e rest ih =>
    intro done s v48 v458 v460 v468 P _ hsplit hs hx19 hx20 hx24 hx26 hx27 hx28 hfiles htr0 hstdout hP
    exact m5_loop_a_one_placed (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr)
      (out := out) (inp := inp) (ps := ps)
      (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      hA hc hio hs0tr hpanic hstk_ext hstk_hook hstk_res hstk64
      hk hpaths hd_ne herr hnext hsplit hs hx19 hx20 hx24 hx26 hx27 hx28 hfiles htr0 hstdout hP
      fun s' v48' v458' v460' v468' P' => ih (done ++ [e]) s' v48' v458' v460' v468' P'

set_option maxHeartbeats 1600000 in
/-- Execute one `Dir k` (`k < 8`) iteration of `main`'s outer M5 loop (`M+0x8b8`), advancing to
`AtM5LoopPlaced (k + 1)` (or exiting via `herr` on `write_file` failure or `Qp` on OOM). -/
theorem m5_dir_step_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k)
    (herr : ∀ (se : State) (errE : M5ErrEntryPlaced) (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp (mainOom s0))
    (hnext : ∀ sf : State,
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  let dAddr := (s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64
  have hstk_ext : mainFrameSize + extHookStack ≤ stk := by m5_omega
  have hstk_hook : mainFrameSize + hookStack ≤ stk := by m5_omega
  have hstk_res : mainFrameSize + resStack ≤ stk := by m5_omega
  have hbase : InMainPlaced CodeOk s0 s 0x8b8 := by simpa [hk] using hs.base
  change k < (storesDirs g).length at hk
  have hpc := hbase.pc; have hrun := hbase.run
  have hx19 := hs.x19; have hx23 := hs.x23; have hx25 := hs.x25
  have hx24 := hs.x24; have hx26 := hs.x26
  have hk_add1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hdAddr_eq : dAddr = fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k) := by
    dsimp only [fsp, dAddr, mainFrameSize]; m5_bv_omega
  have hoff16 : (dAddr + 8#64) + 8#64 = dAddr + 16#64 := by rw [BitVec.add_assoc]; rfl
  have hsp40 : (s.sp + 32#64) + 8#64 = s.sp + 40#64 := by rw [BitVec.add_assoc]; rfl
  have hsp56 : (s.sp + 48#64) + 8#64 = s.sp + 56#64 := by rw [BitVec.add_assoc]; rfl
  have hx25_cell : ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄ (s0.sp - 792#64)) =
      ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄ (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) :=
    congrArg _ (by dsimp only [mainFrameSize]; rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl)
  dsimp only [m5LoopMemPlaced]
  rw [locals_m5LoopCellsPlaced_pop A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g hk,
    ← hdAddr_eq, dirAt_unpack A dAddr ((storesDirs g)[k]'hk)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun dPathPtr => ?_; refine SepWPp.exists_elim fun curCap => ?_
  refine SepWPp.exists_elim fun curPtr => ?_
  rw [vecBuf_pure_keep A curCap curPtr ((storesDirs g)[k]'hk).changed]
  have hpure_top :
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((((dAddr ↦₆₄ curCap) ∗ ((dAddr + 0x08#64) ↦₆₄ curPtr) ∗
            ((dAddr + 0x10#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length) ∗
            ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
            ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          (⌜((storesDirs g)[k]'hk).changed.length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
            vecBuf A 48 8 (dirEntryAt A) curCap curPtr ((storesDirs g)[k]'hk).changed)) ∗
          m5DirPopRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap =
      ⌜((storesDirs g)[k]'hk).changed.length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
      (((dAddr ↦₆₄ curCap) ∗ ((dAddr + 0x08#64) ↦₆₄ curPtr) ∗
          ((dAddr + 0x10#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length) ∗
          ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        vecBuf A 48 8 (dirEntryAt A) curCap curPtr ((storesDirs g)[k]'hk).changed ∗
        m5DirPopRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) := by ac_rfl
  rw [hpure_top]
  refine SepWPp.pure_elim fun ⟨hle_chg, hcap_lt⟩ => ?_
  have hcap_add1_ne' : curCap + 1#64 ≠ 0#64 := by
    intro h
    have hlt64 : curCap.toNat + 1 < 2 ^ 64 := by m5_omega
    have hto : (curCap + 1#64).toNat = curCap.toNat + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hlt64
    rw [h] at hto; simp at hto
  have hcap_add1_ne : (curCap + 1#64 == 0#64) = false := beq_false_of_ne hcap_add1_ne'
  cases hchg : ((storesDirs g)[k]'hk).changed with
  | nil =>
    refine m5_run_placed hbase.inv (mid := mPcPlaced 0xabc)
      (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
        ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
        (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
          BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length))
      (F := ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
        ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ vecBuf A 48 8 (dirEntryAt A) curCap curPtr [] ∗
        m5DirPopRestPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
      (by rw [← hoff16]; dsimp only [dAddr]; exact Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl]) (by simp only [arm64_norm, hrun])
    intro hpcm hrunm hinv_m
    have hfiles_k1 : commitFiles io.wr F0 (writesBefore g (k + 1)) = some s.fs.files := by
      have hw0 : ((storesDirs g)[k]'hk).writes = [] := by
        unfold DirGhost.writes; simp [hchg]
      rw [writesBefore_succ hk, hw0, List.append_nil]; exact hs.files
    refine m5_buf_dealloc_placed (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (out := out) (inp := inp) (ps := ps)
      hc.allocFs hstk_ext hstk64 hk hcap_lt
      (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx23, hk_add1]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hfiles_k1])
      (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
      (by
        dsimp only [dAddr] at hoff16 ⊢
        rw [hoff16]
        have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
          (BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length)
          dPathPtr (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
        dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
        have hord :
            ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                  BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length)) ∗
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
              (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
              vecBuf A 48 8 (dirEntryAt A) curCap curPtr [] ∗
              m5DirPopRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
              ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              A.pool ∗ anyHeap =
            (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                  BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                  BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
              m5DirPopRestPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
            ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
            vecBuf A 48 8 (dirEntryAt A) curCap curPtr [] ∗
            (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool) := by
          ac_rfl
        rw [hord]
        refine Entails.trans
          (sepConj_mono (sepConj_mono_left hhdr)
            (sepConj_mono (sep_anyHeap_absorb _)
              (sepConj_mono_left (vecBuf_nil_dealloc A curCap curPtr)))) ?_
        rw [hdAddr_eq, locals_m5LoopCellsPlaced_push A _ outCap outPtr (BitVec.ofNat 64 out.length)
          inCap inPtr g hk]
        dsimp only [m5LoopMemPlaced]
        exact Entails.of_eq (by ac_rfl))
      hnext
  | cons e0 rest0 =>
    have hpos_chg : 0 < (e0 :: rest0).length := by simp
    have hchg_lt : (e0 :: rest0).length < 2 ^ 58 := by rw [← hchg]; m5_omega
    have hchg_ne0 : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
      ofNat_beq_zero_false hpos_chg (by m5_omega)
    have hchg_ne0' : BitVec.ofNat 64 (e0 :: rest0).length ≠ 0#64 := by
      intro heq; rw [heq] at hchg_ne0; cases hchg_ne0
    have hmul48 : BitVec.ofNat 64 (e0 :: rest0).length * 48#64 =
        BitVec.ofNat 64 ((e0 :: rest0).length * 48) :=
      (BitVec.ofNat_mul (e0 :: rest0).length 48).symm
    have hcarve := m5DirPopRest_carve_scratch_placed A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g hk
    refine SepWPp.weaken_pre
      (sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_left hcarve) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun v20 => ?_; refine SepWPp.exists_elim fun v28 => ?_
    refine SepWPp.exists_elim fun v30 => ?_; refine SepWPp.exists_elim fun v38 => ?_
    refine SepWPp.exists_elim fun v40 => ?_; refine SepWPp.exists_elim fun v48 => ?_
    refine SepWPp.exists_elim fun v58 => ?_; refine SepWPp.exists_elim fun v458 => ?_
    refine SepWPp.exists_elim fun v460 => ?_; refine SepWPp.exists_elim fun v468 => ?_
    by_cases hdpath : ((storesDirs g)[k]'hk).path = []
    · have hdpath0 : BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length = 0#64 := by simp [hdpath]
      refine m5_run_placed hbase.inv (mid := mPcPlaced 0x9e8)
        (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
          (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
            BitVec.ofNat 64 (e0 :: rest0).length) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
            BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
          ((s.sp + 0x20#64) ↦₆₄ v20) ∗ (((s.sp + 0x20#64) + 0x08#64) ↦₆₄ v28) ∗
          ((s.sp + 0x30#64) ↦₆₄ v30) ∗ (((s.sp + 0x30#64) + 0x08#64) ↦₆₄ v38))
        (F := ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((fsp + 0x40#64) ↦₆₄ v40) ∗ ((fsp + 0x48#64) ↦₆₄ v48) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
          ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
          m5DirWorkMidPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
        (by unfold m5ScratchPlaced; rw [← hoff16]; dsimp only [dAddr, fsp]; rw [← hbase.sp, ← hsp40, ← hsp56]; exact Entails.of_eq (by ac_rfl)) ?_
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl]) (by simp only [arm64_norm, hrun])
      intro hpcm hrunm hinv_m
      exact m5_loop_b_entries_placed (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
        (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
        (buf := buf) (curCap := curCap) (curPtr := curPtr) (out := out) (inp := inp) (ps := ps)
        hc.allocFs hc hio hs0tr hpanic hstk_ext hstk_hook hstk64 hk hpaths hdpath
        (fun se errE hE => herr se errE curCap curPtr ((storesDirs g)[k]'hk).changed hE) hnext
        (e0 :: rest0) [] _ v40 v48 v58 v458 v460 v468 _ (List.cons_ne_nil _ _) hchg
        (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hchg])
        (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ubfm_lsl1_nat, ubfm_lsl1_bv, shl4_lsl1_nat, hmul48])
        (by simp only [arm64_norm, List.map_nil, List.append_nil]; exact hs.files)
        (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
        (by
          dsimp only [dAddr] at hoff16 ⊢
          rw [hoff16, hsp40, hsp56, hbase.sp, hx25_cell]
          have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
            (BitVec.ofNat 64 (e0 :: rest0).length) dPathPtr
            (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
          dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
          have hord :
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                    BitVec.ofNat 64 (e0 :: rest0).length) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                    BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x20#64) ↦₆₄ curCap) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x28#64) ↦₆₄ curPtr) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄
                    (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x38#64) ↦₆₄
                    BitVec.ofNat 64 (k + 1))) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x40#64) ↦₆₄ v40) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x48#64) ↦₆₄ v48) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x58#64) ↦₆₄ v58) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x458#64) ↦₆₄ v458) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x460#64) ↦₆₄ v460) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x468#64) ↦₆₄ v468) ∗
                (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
                m5DirWorkMidPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                  (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
                ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                argsBuf A (BitVec.ofNat 64 n) buf ps ∗
                mainSaved s0 ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                A.pool ∗ anyHeap =
              (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                    BitVec.ofNat 64 (e0 :: rest0).length) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                    BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
                m5DirWorkMidPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                  (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
              ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
              (vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
                m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
                  (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                  v40 v48 v58 v458 v460 v468 ∗
                ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                argsBuf A (BitVec.ofNat 64 n) buf ps ∗
                mainSaved s0 ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool) := by
            unfold m5ScratchPlaced; ac_rfl
          rw [hord]
          refine Entails.trans
            (sepConj_mono (sepConj_mono_left hhdr) (sepConj_mono_left (sep_anyHeap_absorb _))) ?_
          rw [hdAddr_eq, m5DirWorkMid_finish_placed A _ outCap outPtr (BitVec.ofNat 64 out.length)
            inCap inPtr g hk, List.nil_append]
          exact Entails.of_eq (by ac_rfl))
    · have hpos_dp : 0 < ((storesDirs g)[k]'hk).path.length := List.length_pos_of_ne_nil hdpath
      have he0_mem : e0 ∈ ((storesDirs g)[k]'hk).changed := by rw [hchg]; exact .head _
      have ⟨_, hp_lt32⟩ := dir_entry_path_ok_len hk hpaths he0_mem
      have hplen := pathOf_ne_nil hdpath e0.1
      have hd_lt32 : ((storesDirs g)[k]'hk).path.length < 2 ^ 32 := by
        have hlen_eq : (pathOf ((storesDirs g)[k]'hk).path e0.1).length =
            ((storesDirs g)[k]'hk).path.length + 1 + e0.1.length := by
          rw [hplen]; simp; omega
        m5_omega
      have hdp_ne0 : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length == 0#64) = false :=
        ofNat_beq_zero_false hpos_dp (by m5_omega)
      have hdp_ne0' : BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length ≠ 0#64 := by
        intro heq; rw [heq] at hdp_ne0; cases hdp_ne0
      have hdp_b63a : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length).getLsbD 63 = false :=
        ofNat_getLsbD_63_false (by m5_omega)
      have hdp_b63b : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)[63] = false :=
        ofNat_getElem_63_false (by m5_omega)
      refine m5_run_placed hbase.inv (mid := mPcPlaced 0x8fc)
        (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
          (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
            BitVec.ofNat 64 (e0 :: rest0).length) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
            BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
          ((s.sp + 0x20#64) ↦₆₄ v20) ∗ (((s.sp + 0x20#64) + 0x08#64) ↦₆₄ v28) ∗
          ((s.sp + 0x30#64) ↦₆₄ v30) ∗ (((s.sp + 0x30#64) + 0x08#64) ↦₆₄ v38) ∗
          ((s.sp + 0x40#64) ↦₆₄ v40))
        (F := ((fsp + 0x48#64) ↦₆₄ v48) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
          ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
          ((fsp + 0x468#64) ↦₆₄ v468) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
          m5DirWorkMidPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
        (by unfold m5ScratchPlaced; rw [← hoff16]; dsimp only [dAddr, fsp]; rw [← hbase.sp, ← hsp40, ← hsp56]; exact Entails.of_eq (by ac_rfl)) ?_
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl]) (by simp only [arm64_norm, hrun])
      intro hpcm hrunm hinv_m
      exact m5_loop_a_entries_placed (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
        (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
        (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr) (v58 := v58)
        (out := out) (inp := inp) (ps := ps)
        hc.allocFs hc hio hs0tr hpanic hstk_ext hstk_hook hstk_res hstk64 hk hpaths hdpath
        (fun se errE hE => herr se errE curCap curPtr ((storesDirs g)[k]'hk).changed hE) hnext
        (e0 :: rest0) [] _ v48 v458 v460 v468 _ (List.cons_ne_nil _ _) hchg
        (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hchg])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, ubfm_lsl1_nat, ubfm_lsl1_bv, shl4_lsl1_nat, hmul48])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, List.map_nil, List.append_nil]; exact hs.files)
        (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
        (by
          dsimp only [dAddr] at hoff16 ⊢
          rw [hoff16, hsp40, hsp56, hbase.sp, hx25_cell]
          have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
            (BitVec.ofNat 64 (e0 :: rest0).length) dPathPtr
            (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
          dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
          have hord :
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                    BitVec.ofNat 64 (e0 :: rest0).length) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                    BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x20#64) ↦₆₄ curCap) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x28#64) ↦₆₄ curPtr) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄
                    (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x38#64) ↦₆₄
                    BitVec.ofNat 64 (k + 1)) ∗
                  ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x40#64) ↦₆₄ dPathPtr)) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x48#64) ↦₆₄ v48) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x58#64) ↦₆₄ v58) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x458#64) ↦₆₄ v458) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x460#64) ↦₆₄ v460) ∗
                ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x468#64) ↦₆₄ v468) ∗
                (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
                m5DirWorkMidPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                  (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
                ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                argsBuf A (BitVec.ofNat 64 n) buf ps ∗
                mainSaved s0 ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                A.pool ∗ anyHeap =
              (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                    BitVec.ofNat 64 (e0 :: rest0).length) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                  ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                    BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
                m5DirWorkMidPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                  (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
              ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                vecBuf A 48 8 (dirEntryAt A) curCap curPtr (e0 :: rest0) ∗
                m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
                  (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                  dPathPtr v48 v58 v458 v460 v468 ∗
                ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                argsBuf A (BitVec.ofNat 64 n) buf ps ∗
                mainSaved s0 ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                A.pool ∗ anyHeap) := by
            unfold m5ScratchPlaced; ac_rfl
          rw [hord]
          refine Entails.trans (sepConj_mono_left (sepConj_mono_left hhdr)) ?_
          rw [hdAddr_eq, m5DirWorkMid_finish_placed A _ outCap outPtr (BitVec.ofNat 64 out.length)
            inCap inPtr g hk, List.nil_append]
          exact Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
