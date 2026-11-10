/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ReceiverChainsPart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: `receiver_chains` Entry and `pending_pre_key`

Completes Field 5 (`receiver_chains`, `+0x23c / +0x150 → +0x240 / +0x1dc`) and clones Field 6
(`pending_pre_key`, `+0x240 / +0x1dc → +0x250 ∨ +0x288`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1 hiding
  allocFailedIn_of_eq srk_length_pos ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false sepWPp_pure_mid
  vecU8At_eq_of_nil vecU8At_eq_of_pos vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPpX_pure_2nd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B) Q Qp) :
    SepWPpX img prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

private theorem sepWPpX_pure_3rd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPpX img prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

private theorem stackAt_chainCloneX_eq_alloc (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
      stackAt sp extHookStack := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 chainCloneStackX)
    (b' := sp - BitVec.ofNat 64 extHookStack) (n := 208) (k := extHookStack)
    rfl (by dsimp [chainCloneStackX, extHookStack]; bv_arith) (by decide)

theorem sc_receiverChains {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hcc : ChainCloneLocal1Ok img A ext)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x23c#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x150#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x240#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1dc#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStackX ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (A := A) (img := img) (ext := ext) hA
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  have hpanic := sc_panic_0x498 (img := img) (A := A) (ext := ext) (ret := ret) (Q := Q) x s0
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x150 56
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x23c 4
  clear hfn
  cases hrc_eq : x.s.state.receiverChains with
  | nil =>
    clear hshim halloc hpanic hcc
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPpX.of_sepWP (mid := entry + bv% (576))
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    refine SepWPpX.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hsub := sc_receiverChains_loop (img := img) (A := A)
      (ext := ext) hcc x R s0 ret Q
    clear hcc
    have hne : x.s.state.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
          ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPpX.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPpX_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨hpos_mul, hpow2, hsz_le63⟩
      rw [stackAt_chainCloneX_eq_alloc s.sp]
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      wpx_of_sepWP (mid := entry + bv% (364))
      wpx_steps
      wpx_call hshim ()
      clear hshim
      wpx_steps
      wpx_call halloc ((rc :: rcs_tl).length * 104, 8)
      clear halloc
      wpx_clear_invs
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · clear hsub hnext
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPpX_pure_3rd fun htrace => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (1176))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
      · clear hpanic
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (392))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        have hsf_sp : sf.sp = s.sp := by sc_close2
        have hsf1_sp : sf_1.sp = s.sp := by sc_close2
        set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        refine SepWPpX.weaken_pre
          (P' := A.pool ∗
                  arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (sf_1.sp + 0xf8#64) 104 ∗
                  stackAt sf_1.sp chainCloneStackX ∗
                  (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                    ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                    segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr
                      ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
          (by rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainCloneX_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl)) ?_
        refine hsub ptr' rcs_tl _
          rc g gs_tl x.G.chainsPtr 0#64 _
          hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2)
          (by sc_close2)
          (by sc_close2) (by sc_close2)
          (by dsimp only [ptr']; sc_close2)
          (by sc_close2)
          (by sc_close2)
          (by sc_close2)
          fun s2 gs' hgs' henc' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
        clear hsub
        dsimp only [Reg.x19, Reg.x25, Reg.x26] at hx19_2 hx25_2 hx26_2
        simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
          State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2
        rw [hsf1_sp] at hsp2 hx21_2 hx29_2
        rw [hptr_zero]
        refine SepWPpX.weaken_pre ?_
          (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
            (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
            (by rw [hgs_eq, hrc_eq]; exact henc')
            hpc2 hrun2 (by sc_close2) hspA2
            (by sc_close2) hx21_2 (by sc_close2)
            (by sc_close2) hx27_2 hx29_2 htr2 hvregs2)
        dsimp only [State.setPC, State.setPState, State.writeReg64]
        simp only [hgs_eq, hrc_eq, hsf1_sp]
        have hreasm :=
          segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
            ((g :: gs_tl).zip (rc :: rcs_tl))
        have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs']
        have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
        have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
        have hnew_buf := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
        rw [hnew_len] at hnew_buf
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                  arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                A.pool ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStackX ∗ F)
          (Entails.of_eq (by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
        exact Entails.of_eq (by ac_rfl)

/-! ## 2. Field 6: `pending_pre_key` (`+0x240 / +0x1dc → +0x250 ∨ +0x288`) -/

theorem sc_pendingPreKey_200_pos {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x200#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp extHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
        ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
        (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗
        ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗
        ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (A := A) (img := img) (ext := ext) hA
  have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [scMemcpySpec] at hmemcpy
  have hpanic := sc_panic_0x4b0 (img := img) (A := A) (ext := ext) (ret := ret) (Q := Q) x s0
  have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
  have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x200 44
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x280 8
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  wpx_of_sepWP (mid := entry + bv% (532))
  wpx_steps
  wpx_call hshim ()
  clear hshim
  wpx_steps
  wpx_call halloc (gp.vec.bytes.length, 1)
  clear halloc
  wpx_clear_invs
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpX_pure_3rd fun htrace => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1200))
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    wpx_of_sepWP (mid := entry + bv% (648))
    wpx_steps
    wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
    clear hmemcpy
    wpx_steps
    wpx_clear_invs
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close2
    have hsf1_sp : sf_1.sp = s.sp := by sc_close2
    refine SepWPpX.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw0 tw1 tw3
        (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length ∧
        ∃ tw4' : BitVec 32,
          gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
    have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108,
        htail_eq,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Field 6 (`+0x240 / +0x1dc → +0x250 ∨ +0x288`): clones `pending_pre_key`
into `x28 = pendCap'`, `[sp + 0x20] = pendPtr'`, `w23 = w23'`, `w24 = w24'`,
`[sp + 0x18] = v18'`, and `[sp + 0x2c] = v2c'`. -/
theorem sc_pendingPreKey {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x240#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1dc#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp extHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp extHookStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x1dc 36
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x240 16
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x278 16
  clear hfn
  cases hpend : x.G.pending with
  | none =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.s.state.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPpX.of_sepWP (mid := entry + bv% (592))
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPpX.of_sepWP (mid := entry + bv% (592))
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gp =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, htail_val, htail_pts⟩ := exists_tail24_decomp htail
    have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
    have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
    have h110 : x.src + 0xf8#64 + BitVec.ofNat 64 24 = x.src + 0x110#64 := by bv_arith
    have h114 : x.src + 0x110#64 + 4#64 = x.src + 0x114#64 := by bv_arith
    have h118 : x.src + 0x110#64 + 8#64 = x.src + 0x118#64 := by bv_arith
    have h120 : x.src + 0x110#64 + 16#64 = x.src + 0x120#64 := by bv_arith
    have h124 : x.src + 0x110#64 + 20#64 = x.src + 0x124#64 := by bv_arith
    have htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
        (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
          ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
          ((x.src + 0x124#64) ↦₃₂ tw4)) := by
      rw [h110, htail_pts (x.src + 0x110#64), h114, h118, h120, h124]
    rw [htail_eq]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ tw4' : BitVec 32,
            gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.s.state.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        unfold tripleRatchetProgAtExt at *
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
        examples_hide_fetches
        apply SepWPpX.of_sepWP (mid := entry + bv% (648))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPpX.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        unfold tripleRatchetProgAtExt at *
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
        examples_hide_fetches
        apply SepWPpX.of_sepWP (mid := entry + bv% (648))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPpX.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_200 : State) =>
        sc_pendingPreKey_200_pos (img := img) (A := A)
          (ext := ext) hA (x := x) (R := R) (s0 := s0) (s := s_200) (ret := ret) (Q := Q)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v18 := v18) (v20 := v20) (F := F)
          htail htail_eq htail_val hpos hlen_le hcap_lt hptr
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      suffices h_at_200 : ∀ s_200 : State,
          s_200.pc = entry + bv% (512) →
          s_200.status = .Running →
          s_200.sp = s.sp →
          s_200.spAligned = true →
          s_200.readReg64 .x19 = s.readReg64 .x19 →
          (s_200.readReg64 .x23).truncate 32 = tw0 →
          (s_200.readReg64 .x24).truncate 32 = tw1 →
          s_200.readReg64 .x25 = x.src →
          s_200.readReg64 .x26 = s.readReg64 .x26 →
          s_200.readReg64 .x27 = s.readReg64 .x27 →
          s_200.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length →
          s_200.readReg64 .x29 = s.readReg64 .x29 →
          s_200.trace = s0.trace →
          calleeSavedVRegs s_200 = calleeSavedVRegs s0 →
          SepWPpX img prog ret s_200
            (A.pool ∗
              ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
              ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
              ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              ((x.src + 0x110#64) ↦₃₂ tw0) ∗
              ((x.src + 0x114#64) ↦₃₂ tw1) ∗
              ((x.src + 0x118#64) ↦₆₄ td2) ∗
              ((x.src + 0x120#64) ↦₃₂ tw3) ∗
              ((x.src + 0x124#64) ↦₃₂ tw4) ∗
              ((s_200.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s_200.sp + 0x20#64) ↦₆₄ v20) ∗
              ((s_200.sp + 0x2c#64) ↦₃₂ tw3) ∗
              stackAt s_200.sp extHookStack ∗ F)
            Q (scPanicPost A x R s0) by
        clear hsub
        by_cases hrc : x.s.state.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpX.of_sepWP (mid := entry + bv% (512))
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpX.of_sepWP (mid := entry + bv% (512))
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      intro s_200 hpc200 hrun200 hsp200 hspA200 hx19_200 hx23_200 hx24_200 hx25_200 hx26_200 hx27_200 hx28_200 hx29_200 htr200 hvregs200
      refine hsub s_200 hpc200 hrun200 hspA200 hx23_200 hx24_200 hx25_200 hx28_200 htr200 hvregs200
        fun s1 pendCap' pendPtr' v18' w23' w24' v2c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp200]
      exact hnext s1 pendCap' pendPtr' v18' w23' w24' v2c'
        hpc1 hrun1 (hsp1.trans hsp200) hspA1
        (hx19_1.trans hx19_200) hx23_1 hx24_1 hx25_1
        (hx26_1.trans hx26_200) (hx27_1.trans hx27_200) hx28_1 (hx29_1.trans hx29_200) htr1 hvregs1

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
