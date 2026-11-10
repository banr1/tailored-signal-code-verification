/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import ProofLib.ProgramReflection
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.CodeLayout

/-!
# Relocatable `[LibsignalPlacement]` Mid-Segment Proofs for `Chain::clone` (Block `524`)

Epilogue (`+736 → ret`), `message_keys` loop and empty fast path (`+260 .. +732`), and
`chain_key = none` join (`+244 .. +256`) on `(blkPC_524).rebase (blkPl_524).base H`.
-/

@[expose] public section

namespace CryptoVerification.Cli.LibsignalE2E.Pqxdh.Reloc.ChainClone4

open Arm64 ProofLib ProofLib.ProgramReflection
open Arm64.Obj CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight memRegion_cells allocFailedIn_of_eq sessionShimSpec sessionMemcpySpec
open CryptoVerification.HookTrace
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone hiding chain_clone_placed_ok_of_hooks chain_clone_placed_ok senderChain_clone_placed_ok_of_hooks senderChain_clone_placed_ok calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_setPC calleeSavedVRegs_setPState calleeSavedVRegs_setMem
open ChainCloneRegReadSimp
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Mid-Segment Proofs on Block `524` -/

theorem chain_clone_placed_epilogue [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_524).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

theorem panic_at_handle_error_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ((blkPC_524).rebase (blkPl_524).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := by
  rw [ls_externAt?_of_mem, hpanic]

theorem chain_clone_placed_panic_800 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_panic_812 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_panic_824 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_panic_836 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_panic_848 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_panic_860 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_placed_mk_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (blkPl_524).base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (blkPl_524).base + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic824 := fun s P => chain_clone_placed_panic_824 (A := A)
    (H := H) (Q := Q) hpanic x s0 s P R
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (660))
    wp_steps
    wp_call hshim ()
    have htr_sf : sf.trace = s0.trace := by reg_chain
    wp_compact
    wp_steps
    wp_call halloc (mkg.seed.length, 1)
    rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
    wp_compact
    apply SepWP.done ‹_› ‹_›
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (824))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine hpanic824 _ _ ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace_oom
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod, htrace1⟩ => ?_
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (404))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
          (sf_1.readReg64 (Reg.gpr 0#5))
        refine SepWPp.weaken_pre
          (fold_iter_messageKeys A gk mkg srcCur
            (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
            hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
        rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
        cases rem' with
        | nil =>
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (688))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · refine SepWPp.weaken_pre ?_
              (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
                arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
              exact Entails.refl _
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (408))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
              simp at htot ⊢; omega
            refine SepWPp.weaken_pre ?_
              (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
                (messageKeyAt A (gk, mkg) srcCur ∗
                  messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_)
            · exact Entails.of_eq (by ac_rfl)
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
            · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
                (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
              rw [List.map_cons, List.zip_cons_cons,
                arrayAt_cons (x := (gk, mkg)),
                arrayAt_cons (x := (gk', (gk, mkg).2)),
                ptr_off_add_104] at hdone
              dsimp only at hdone
              simp only [sepConj_assoc] at hdone
              refine SepWPp.weaken_pre ?_ hdone
              exact Entails.of_eq (by ac_rfl)

theorem chain_clone_placed_mks_nil [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (blkPl_524).base + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hep := fun s' => chain_clone_placed_epilogue (A := A) (H := H) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPp.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

theorem chain_clone_placed_mks_nonempty [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_524).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic860 := fun s P => chain_clone_placed_panic_860 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_placed_mk_loop (A := A) (H := H)
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      hshim halloc hmemcpy hpanic x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_placed_epilogue (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [sessionShimSpec] at hshim
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (308))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  wp_compact
  wp_steps
  wp_call halloc (104 * x.gc.2.messageKeys.length, 8)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (860))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic860 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod8, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (408))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.weaken_pre ?_
        (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
          (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A x.gc x.src ∗
            ((s0.sp - 208#64) ↦₆₄ x28) ∗
            ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
            ((s0.sp - 196#64) ↦₃₂ w27) ∗
            ((s0.sp - 192#64) ↦₆₄ x25) ∗
            ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
            ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
            ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            savedRegsCore s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
      · rw [hzip_len, BitVec.add_zero]
        exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm, hzip_len]
      · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      · exact htrace1
      · simp only [wp_norm]; assumption
      · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
        have hsp_l_align : sf_l.spAligned = true := by
          rw [State.spAligned, hsp_l]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
          (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
          map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
          sepConj_assoc]
        apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (736))
        wp_steps
        refine SepWP.done ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · refine SepWPp.weaken_pre ?_
            (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
              simp [hklen]
            have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
              rw [hzip'_len]; exact hpos
            have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
              rw [hzip'_len]; exact hmax
            have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
              hzip'_pos hzip'_max hoom64
            rw [hzip'_len] at hbuf_eq
            rw [hbuf_eq,
                chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
                spillSlotsExist_eq_struct s0.sp,
                savedRegsOnStack_eq_core s0]
            have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
            have hsr_fold :
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0) ⊢
                (∃∗ p : BitVec 64 × BitVec 32,
                  ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                  ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                  savedRegsCore s0) := by
              apply Entails.sepExists_right (v11', w12b')
              dsimp only
              exact Entails.refl _
            have hsrc_fold :
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ⊢
                (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                    x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) :=
              Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
            have hgroup_pre :
                (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  chainMkSourceFrame A x.gc x.src ∗
                  ((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  savedRegsCore s0) =
                (memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                    arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                    arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                    chainMkSourceFrame A x.gc x.src) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  (((s0.sp - 208#64) ↦₆₄ x28) ∗
                    ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                    ((s0.sp - 196#64) ↦₃₂ w27) ∗
                    ((s0.sp - 192#64) ↦₆₄ x25) ∗
                    ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                    ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                    ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                    ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                    ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  (((s0.sp - 120#64) ↦₆₄ v11') ∗
                    ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                    savedRegsCore s0)) := by
              ac_rfl
            rw [hgroup_pre]
            exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right hsr_fold))))))))))))
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · unfold State.readReg32; simp only [wp_norm, htrunc32]
          · exact htr_l
          · simp only [wp_norm]; exact hvregs_l

theorem chain_clone_placed_ck_none [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (blkPl_524).base + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_placed_mks_nil (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_placed_mks_nonempty (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hmks_nil hmks_ne ⊢
  rw [chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (732))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + bv% (260))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption

end CryptoVerification.Cli.LibsignalE2E.Pqxdh.Reloc.ChainClone4
