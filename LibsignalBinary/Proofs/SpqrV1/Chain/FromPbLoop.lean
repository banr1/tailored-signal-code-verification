/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoin
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Loop Error Cleanup & Cell Helpers for `<spqr::chain::Chain>::from_pb` (`0x600fc .. 0x6038c`)

Proves the loop scratch frame and error cleanup blocks (`+380`, `+452`, `+520`, `+644`, `+780`)
of the in-place `ChainEpoch::from_pb` conversion loop at `0x600fc` (`+136`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L36
open Lean Elab Tactic ProofLib ProofLib.CodeLookup in
elab "code_fetches_sym " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout

theorem rustDealloc_rel_fromPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr "__rustc::__rust_dealloc" =
      (dropProgAtExt b ext).fnAddr chainFromPbName +
        bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc") := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff "__rustc::__rust_dealloc") =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainFromPbName) +
      bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")
  rw [show libsignalSessionCode.fnOff "__rustc::__rust_dealloc" = num% (ls_off% "__rustc::__rust_dealloc") from (ls_stub% "__rustc::__rust_dealloc"),
      show libsignalSessionCode.fnOff chainFromPbName = num% (ls_off% "<spqr::chain::Chain>::from_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")]
  bv_omega

end CryptoVerification.SpqrV1.Layout.L36

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L36
open FromPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Loop Scratch Frame and Arithmetic Helpers -/

/-- The 96-byte scratch region `[s0.sp - 192#64 .. s0.sp - 96#64)` during the conversion loop. -/
def loopScratchAt (s0 : State) (x : ChainFromPbCall) (sp0_val : BitVec 64) : SepProp :=
  ((s0.sp - 192#64) ↦₆₄ sp0_val) ∗
  ((s0.sp - 184#64) ↦₆₄ (x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))) ∗
  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
  ((s0.sp - 168#64) ↦₆₄ x.pb.currentEpoch) ∗
  ((s0.sp - 160#64) ↦₆₄ x.pb.sendEpoch) ∗
  memRegion (s0.sp - 152#64) 4 ∗
  ((s0.sp - 148#64) ↦₃₂ x.pb.direction) ∗
  ((s0.sp - 144#64) ↦₆₄ x.pbPtr) ∗
  ((s0.sp - 136#64) ↦₆₄ x.out) ∗
  ((s0.sp - 128#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
  ((s0.sp - 120#64) ↦₆₄ x.gPb.nextRoot.cap) ∗
  ((s0.sp - 112#64) ↦₆₄ x.gPb.linksCap) ∗
  ((s0.sp - 104#64) ↦₆₄ x.gPb.linksPtr)

theorem loopScratchAt_entails_joinScratchAt (s0 : State) (x : ChainFromPbCall)
    (sp0_val : BitVec 64) :
    loopScratchAt s0 x sp0_val ⊢ joinScratchAt s0 x.gPb x.pb sp0_val := by
  unfold loopScratchAt joinScratchAt
  rw [ProofLib.memRegion_split' (b := s0.sp - 144#64) (n := 8) (k := 24) (b' := s0.sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 136#64) (n := 8) (k := 16) (b' := s0.sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 128#64) (n := 8) (k := 8) (b' := s0.sp - 120#64) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (Entails.refl _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                        (Entails.refl _)))))))))))

@[simp, arm64_norm, wp_norm]
theorem ofNat_mul_112_add_112 (n : Nat) :
    BitVec.ofNat 64 (n * 112) + 112#64 = BitVec.ofNat 64 ((n + 1) * 112) := by
  rw [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]

@[simp, arm64_norm, wp_norm]
theorem add_curPtr_112 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 (n * 112) + 112#64 = ptr + BitVec.ofNat 64 ((n + 1) * 112) := by
  rw [BitVec.add_assoc, ofNat_mul_112_add_112]

theorem ofNat_mul_112_beq_false {a b : Nat} (hne : a ≠ b)
    (ha : a * 112 < 2 ^ 63) (hb : b * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (a * 112) == BitVec.ofNat 64 (b * 112)) = false := by
  have ha64 : a * 112 < 18446744073709551616 := by omega
  have hb64 : b * 112 < 18446744073709551616 := by omega
  rw [beq_eq_false_iff_ne]
  intro heq
  have htn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64] at htn
  omega

theorem recv_none_unpack_at_56 (A : RustAlloc) (g : EpochDirectionPBGhost) (cur : BitVec 64) :
    optEpochDirectionPBAt A g (cur + 56#64) none =
      (∃∗ u1 : BitVec 64, (cur + 64#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (cur + 72#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (cur + 80#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (cur + 88#64) ↦₆₄ u4) ∗
      ((cur + 56#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (cur + 96#64) 16 := by
  rw [optEpochDirectionPBAt_none_unpack]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem recv_none_cells_entails_memRegion_56 (cur u0 u1 u2 u3 u4 : BitVec 64) :
    ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 ⊢
      memRegion (cur + 56#64) 56 := by
  have h := optEpochDirectionPB_none_cells_entails_memRegion_56 (cur + 56#64) u0 u1 u2 u3 u4
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

def recvDirPBCellsAt56 (cur : BitVec 64) (g : EpochDirectionPBGhost) (d : EpochDirectionPB) : SepProp :=
  ((cur + 56#64) ↦₆₄ g.next.cap) ∗
  ((cur + 64#64) ↦₆₄ g.next.ptr) ∗
  ((cur + 72#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
  ((cur + 80#64) ↦₆₄ g.prev.cap) ∗
  ((cur + 88#64) ↦₆₄ g.prev.ptr) ∗
  ((cur + 96#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
  ((cur + 104#64) ↦₃₂ d.ctr) ∗
  memRegion (cur + 108#64) 4

theorem epochDirPBCellsAt_56_eq (cur : BitVec 64) (g : EpochDirectionPBGhost) (d : EpochDirectionPB) :
    epochDirPBCellsAt (cur + 56#64) g d = recvDirPBCellsAt56 cur g d := by
  unfold epochDirPBCellsAt recvDirPBCellsAt56
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem recvDirPBCellsAt56_entails_memRegion_56 (cur : BitVec 64) (g : EpochDirectionPBGhost)
    (d : EpochDirectionPB) :
    recvDirPBCellsAt56 cur g d ⊢ memRegion (cur + 56#64) 56 := by
  rw [← epochDirPBCellsAt_56_eq]
  exact epochDirPBCellsAt_entails_memRegion_56 (cur + 56#64) g d

/-! ## Error Cleanup Helpers (`+520`, `+452`, `+780`, `+380`, `+644`) -/

set_option maxHeartbeats 800000 in
/-- Error cleanup at `0x6027c` (`+520`) when `curPB.recv = none` (`x20 = 0xffffffffffffffff#64`). -/
theorem fromPb_loop_err_520_none {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err A b ext hdealloc x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `0x6027c` (`+520`) when `curPB.recv = some recvPb`. -/
theorem fromPb_loop_err_520_some {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (rncap rnptr rpcap rpptr sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err A b ext hdealloc x s0
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Layout.L36.rustDealloc_rel_fromPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hrn_cmn := add_one_beq_zero_of_lt_pow63 hrn_lt
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at herr hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 596#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x12 = rpptr ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = rpcap) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (rnptr, rncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx12_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1⟩
    refine seq_clean (mid := entry + 792#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
        sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hrp : rpcap = 0
      · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
        simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        wp_done
      · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
        have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hrpb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (rpptr, rpcap.toNat, 1)
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx0_2, hx11_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2⟩
      exact herr s2 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx0_2 hx11_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Deallocate `sendPb.next` and `sendPb.prev` at `0x60238 .. 0x6027c` (`+452 .. +520`). -/
theorem fromPb_loop_err_452_to_520 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (F : SepProp) (x : ChainFromPbCall) (s0 s : State)
    (sncap snptr spcap spptr x9_val x12_val x19_val x20_val x23_val x26_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = x12_val) (hx19 : s.readReg64 .x19 = x19_val)
    (hx20 : s.readReg64 .x20 = x20_val) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x23_val) (hx24 : s.readReg64 .x24 = sncap)
    (hx26 : s.readReg64 .x26 = x26_val) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr) :
    SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr chainFromPbName + 520#64) s
      (F ∗ vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fun sm Pm =>
        (Pm ⊢ F ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x12 = x12_val ∧ sm.readReg64 .x19 = x19_val ∧
        sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x26 = x26_val) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Layout.L36.rustDealloc_rel_fromPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 488#64)
    (P_mid := F ∗ vecCapPtrDealloc A spcap spptr ∗ A.pool ∗
      loopScratchAt s0 x x9_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = x12_val ∧ sm.readReg64 .x19 = x19_val ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x26 = x26_val ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (snptr, sncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1, hx27_1, hx28_1⟩
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hsp_cap : spcap = 0
    · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
      simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
      have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hspb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (spptr, spcap.toNat, 1)
      wp_steps; rw [hsp1]; wp_done

set_option maxHeartbeats 800000 in
/-- Tail bridge at `0x60380` (`+780 .. +792`) into `fromPb_join_err`. -/
theorem fromPb_loop_err_780 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err A b ext hdealloc x s0
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `0x601f0` (`+380`) when `curPB.recv = none`. -/
theorem fromPb_loop_err_380 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 380#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = snptr) (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h780 := @fromPb_loop_err_780 A b ext hdealloc x s0
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Layout.L36.rustDealloc_rel_fromPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at h780 hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 408#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (snptr, sncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx23_1, hx27_1, hx28_1⟩
    refine seq_clean (mid := entry + 780#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsp_cap : spcap = 0
      · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
        rw [hsp_cap] at hx27_1
        simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
        have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hspb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (spptr, spcap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx11_2, hx19_2, hx20_2, hx23_2, hx27_2⟩
      exact h780 s2 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx11_2
        hx19_2 hx20_2 hx23_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Deallocate `recvPb.next` and `recvPb.prev` at `0x602f8 .. 0x60334` (`+644 .. +704`). -/
theorem fromPb_loop_err_644_to_704 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (F : SepProp) (x : ChainFromPbCall) (s0 s : State)
    (convLen : Nat) (rncap rnptr rpcap rpptr x21_val x22_val x24_val x27_val x28_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = x21_val) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = x24_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convLen * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = x27_val)
    (hx28 : s.readReg64 .x28 = x28_val) :
    SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr chainFromPbName + 704#64) s
      (F ∗ vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fun sm Pm =>
        (Pm ⊢ F ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x21 = x21_val ∧ sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convLen * 112) ∧
        sm.readReg64 .x24 = x24_val ∧ sm.readReg64 .x27 = x27_val ∧
        sm.readReg64 .x28 = x28_val) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Layout.L36.rustDealloc_rel_fromPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 676#64)
    (P_mid := F ∗ vecCapPtrDealloc A rpcap rpptr ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = x22_val ∧ sm.readReg64 .x24 = x24_val ∧
      sm.readReg64 .x25 = BitVec.ofNat 64 (convLen * 112) ∧
      sm.readReg64 .x26 = rpcap ∧ sm.readReg64 .x27 = x27_val ∧
      sm.readReg64 .x28 = x28_val) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (rnptr, rncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx21_1, hx22_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hrp : rpcap = 0
    · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
      simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
      have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrpb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc_raw (rpptr, rpcap.toNat, 1)
      wp_steps; rw [hsp1]; wp_done

set_option maxHeartbeats 800000 in
/-- Error cleanup at `0x602f8` (`+644`) when `curPB.recv = some recvPb` fails `tst`. -/
theorem fromPb_loop_err_644 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x22_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = snptr) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_644_to_704 A b ext hdealloc F_frame
    x s0 s convEpochs.length rncap rnptr rpcap rpptr snptr x22_val sncap spcap spptr sp0_val
    hsp0_align hrn_lt hrn_ne hrp_lt hrp_ne hpc hrun hsp htr hfp hx11 hx12 hx19 hx20 hx21 hx22
    hx24 hx25 hx26 hx27 hx28
  refine seq_clean (mid := (dropProgAtExt b ext).fnAddr chainFromPbName + 704#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x21 = snptr ∧ sm.readReg64 .x22 = x22_val ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = sncap ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1⟩
    refine SepWP.weaken_pre (Entails.of_eq (by
      dsimp only [F_frame]; ac_rfl :
      F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack =
      memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)) ?_
    have h780 := @fromPb_loop_err_780 A b ext hdealloc x s0
    have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr chainFromPbName + (bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc"))) (rustDeallocSpec A) :=
      sub_ok_of_addr_eq (CryptoVerification.SpqrV1.Layout.L36.rustDealloc_rel_fromPb b ext) hdealloc
    have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 192#64 hsp0_align (by decide)
    code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
    dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at h780 hdealloc_raw hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::chain::Chain>::from_pb" = entry
    examples_hide_fetches
    refine seq_clean (mid := entry + 732#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsn : sncap = 0
      · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
        simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
        have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (snptr, sncap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx11_2, hx20_2, hx22_2, hx23_2, hx27_2, hx28_2⟩
      refine seq_clean (mid := entry + 780#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          arrayAt (chainEpochPBAt A) 112
            (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x x22_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x19 = 0#64 ∧
          sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
          sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
          sm.readReg64 .x27 = 0#64) ?_ ?_
      · unfold vecCapPtrDealloc loopScratchAt
        by_cases hsp_cap : spcap = 0
        · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
          rw [hsp_cap] at hx27_2
          simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps; wp_done
        · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
          have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
          simp only [hspb, Bool.false_eq_true, ↓reduceIte]
          rw [stackAt_subStack_split_allocHook s0.sp]
          wp_steps
          wp_call hdealloc_raw (spptr, spcap.toNat, 1)
          wp_steps; rw [hsp2]; wp_done
      · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx11_3, hx19_3, hx20_3, hx23_3, hx27_3⟩
        exact h780 s3 convG convEpochs remG remPB x22_val hsp0_align hfromPb_eq hconv_len hrem_len
          hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hfp3 hx11_3
          hx19_3 hx20_3 hx23_3 hx27_3

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_none {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr x9_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520 A b ext hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val (s.readReg64 .x12) (s.readReg64 .x19)
    0xffffffffffffffff#64 (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (s.readReg64 .x26) sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 rfl rfl hx20 hx21
    hx23 hx24 rfl hx27 hx28
  refine seq_clean (mid := (dropProgAtExt b ext).fnAddr chainFromPbName + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
      sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = s.readReg64 .x26) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, _, _, hx20_1, hx23_1, _⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_none hdealloc x s0 s1 convG convEpochs remG remPB x9_val
        hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx20_1 hx23_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_some {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x9_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap) (hx26 : s.readReg64 .x26 = rpcap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520 A b ext hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val rpptr rnptr rncap
    (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) rpcap sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 hx12 hx19 hx20 hx21
    hx23 hx24 hx26 hx27 hx28
  refine seq_clean (mid := (dropProgAtExt b ext).fnAddr chainFromPbName + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x19 = rnptr ∧
      sm.readReg64 .x20 = rncap ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = rpcap) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_some hdealloc x s0 s1 convG convEpochs remG remPB
        rncap rnptr rpcap rpptr x9_val hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len
        hl_le hl_lt hl_ne hn_le hn_lt hn_ne hrn_lt hrn_ne hrp_lt hrp_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hx26_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

/-! ## Cell Repacking and `memRegion 112` Collapse Helpers -/

def mkChainEpochFromPb (sendPb recvPb : EpochDirectionPB) : ChainEpoch :=
  { send := { ctr := sendPb.ctr, next := sendPb.next, prev := { data := sendPb.prev } }
    recv := { ctr := recvPb.ctr, next := recvPb.next, prev := { data := recvPb.prev } } }

theorem repack_cur_chainEpochAt (A : RustAlloc) (cur : BitVec 64)
    (curG : ChainEpochPBGhost) (sendPb recvPb : EpochDirectionPB)
    (hsn1 : sendPb.next.length ≤ curG.send.next.cap.toNat)
    (hsn2 : curG.send.next.cap.toNat < 2 ^ 63) (hsn3 : curG.send.next.ptr ≠ 0)
    (hsp1 : sendPb.prev.length ≤ curG.send.prev.cap.toNat)
    (hsp2 : curG.send.prev.cap.toNat < 2 ^ 63) (hsp3 : curG.send.prev.ptr ≠ 0)
    (hrn1 : recvPb.next.length ≤ curG.recv.next.cap.toNat)
    (hrn2 : curG.recv.next.cap.toNat < 2 ^ 63) (hrn3 : curG.recv.next.ptr ≠ 0)
    (hrp1 : recvPb.prev.length ≤ curG.recv.prev.cap.toNat)
    (hrp2 : curG.recv.prev.cap.toNat < 2 ^ 63) (hrp3 : curG.recv.prev.ptr ≠ 0) :
    epochDirPBCellsAt cur curG.send sendPb ∗
      vecU8BufAt A curG.send.next.cap curG.send.next.ptr sendPb.next ∗
      vecU8BufAt A curG.send.prev.cap curG.send.prev.ptr sendPb.prev ∗
      recvDirPBCellsAt56 cur curG.recv recvPb ∗
      vecU8BufAt A curG.recv.next.cap curG.recv.next.ptr recvPb.next ∗
      vecU8BufAt A curG.recv.prev.cap curG.recv.prev.ptr recvPb.prev ⊢
      chainEpochAt A (toChainEpochGhost curG, mkChainEpochFromPb sendPb recvPb) cur := by
  rw [← epochDirPBCellsAt_56_eq]
  unfold chainEpochAt toChainEpochGhost mkChainEpochFromPb
  dsimp only
  have hsend := epochDirPBCellsAt_repack_ced A cur curG.send sendPb hsn1 hsn2 hsn3 hsp1 hsp2 hsp3
  have hrecv := epochDirPBCellsAt_repack_ced A (cur + 56#64) curG.recv recvPb hrn1 hrn2 hrn3 hrp1 hrp2 hrp3
  rw [show
    epochDirPBCellsAt cur curG.send sendPb ∗
      vecU8BufAt A curG.send.next.cap curG.send.next.ptr sendPb.next ∗
      vecU8BufAt A curG.send.prev.cap curG.send.prev.ptr sendPb.prev ∗
      epochDirPBCellsAt (cur + 56#64) curG.recv recvPb ∗
      vecU8BufAt A curG.recv.next.cap curG.recv.next.ptr recvPb.next ∗
      vecU8BufAt A curG.recv.prev.cap curG.recv.prev.ptr recvPb.prev =
    (epochDirPBCellsAt cur curG.send sendPb ∗
      vecU8BufAt A curG.send.next.cap curG.send.next.ptr sendPb.next ∗
      vecU8BufAt A curG.send.prev.cap curG.send.prev.ptr sendPb.prev) ∗
    (epochDirPBCellsAt (cur + 56#64) curG.recv recvPb ∗
      vecU8BufAt A curG.recv.next.cap curG.recv.next.ptr recvPb.next ∗
      vecU8BufAt A curG.recv.prev.cap curG.recv.prev.ptr recvPb.prev) by ac_rfl]
  exact sepConj_mono hsend hrecv

theorem sendCells_recvNone_entails_memRegion_112 (cur : BitVec 64)
    (gs : EpochDirectionPBGhost) (ds : EpochDirectionPB) (u0 u1 u2 u3 u4 : BitVec 64) :
    epochDirPBCellsAt cur gs ds ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 ⊢
      memRegion cur 112 :=
  Entails.trans
    (sepConj_mono (epochDirPBCellsAt_entails_memRegion_56 cur gs ds)
      (recv_none_cells_entails_memRegion_56 cur u0 u1 u2 u3 u4))
    (memRegion_56_56_to_112 cur)

theorem sendCells_recvCells_entails_memRegion_112 (cur : BitVec 64)
    (gs gr : EpochDirectionPBGhost) (ds dr : EpochDirectionPB) :
    epochDirPBCellsAt cur gs ds ∗ recvDirPBCellsAt56 cur gr dr ⊢ memRegion cur 112 :=
  Entails.trans
    (sepConj_mono (epochDirPBCellsAt_entails_memRegion_56 cur gs ds)
      (recvDirPBCellsAt56_entails_memRegion_56 cur gr dr))
    (memRegion_56_56_to_112 cur)

theorem sendNone_recvNone_entails_memRegion_112 (cur : BitVec 64)
    (s0_w s1 s2 s3 s4 u0 u1 u2 u3 u4 : BitVec 64) :
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 ⊢
      memRegion cur 112 := by
  rw [show
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 =
    ((cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16) ∗
    (((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16) by ac_rfl]
  exact Entails.trans
    (sepConj_mono (optEpochDirectionPB_none_cells_entails_memRegion_56 cur s0_w s1 s2 s3 s4)
      (recv_none_cells_entails_memRegion_56 cur u0 u1 u2 u3 u4))
    (memRegion_56_56_to_112 cur)

theorem sendNone_recvCells_entails_memRegion_112 (cur : BitVec 64)
    (s0_w s1 s2 s3 s4 : BitVec 64) (gr : EpochDirectionPBGhost) (dr : EpochDirectionPB) :
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      recvDirPBCellsAt56 cur gr dr ⊢
      memRegion cur 112 := by
  rw [show
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      recvDirPBCellsAt56 cur gr dr =
    ((cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16) ∗
    recvDirPBCellsAt56 cur gr dr by ac_rfl]
  exact Entails.trans
    (sepConj_mono (optEpochDirectionPB_none_cells_entails_memRegion_56 cur s0_w s1 s2 s3 s4)
      (recvDirPBCellsAt56_entails_memRegion_56 cur gr dr))
    (memRegion_56_56_to_112 cur)

theorem sendNone_recvSome_entails_err520 (A : RustAlloc) (cur : BitVec 64)
    (s0_w s1 s2 s3 s4 : BitVec 64) (gr : EpochDirectionPBGhost) (dr : EpochDirectionPB)
    (hrn1 : dr.next.length ≤ gr.next.cap.toNat) (hrn2 : gr.next.cap.toNat < 2 ^ 63)
    (hrp1 : dr.prev.length ≤ gr.prev.cap.toNat) (hrp2 : gr.prev.cap.toNat < 2 ^ 63) :
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      recvDirPBCellsAt56 cur gr dr ∗
      vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev ⊢
      memRegion cur 112 ∗
      vecCapPtrDealloc A gr.next.cap gr.next.ptr ∗
      vecCapPtrDealloc A gr.prev.cap gr.prev.ptr := by
  rw [show
    (cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      recvDirPBCellsAt56 cur gr dr ∗
      vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev =
    ((cur ↦₆₄ s0_w) ∗ ((cur + 8#64) ↦₆₄ s1) ∗ ((cur + 16#64) ↦₆₄ s2) ∗
      ((cur + 24#64) ↦₆₄ s3) ∗ ((cur + 32#64) ↦₆₄ s4) ∗ memRegion (cur + 40#64) 16 ∗
      recvDirPBCellsAt56 cur gr dr) ∗
    (vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev) by ac_rfl]
  exact sepConj_mono
    (sendNone_recvCells_entails_memRegion_112 cur s0_w s1 s2 s3 s4 gr dr)
    (sepConj_mono
      (vecU8BufAt_entails_dealloc A gr.next.cap gr.next.ptr dr.next hrn1 hrn2)
      (vecU8BufAt_entails_dealloc A gr.prev.cap gr.prev.ptr dr.prev hrp1 hrp2))

theorem sendSome_recvNone_entails_err (A : RustAlloc) (cur : BitVec 64)
    (gs : EpochDirectionPBGhost) (ds : EpochDirectionPB) (u0 u1 u2 u3 u4 : BitVec 64)
    (hsn1 : ds.next.length ≤ gs.next.cap.toNat) (hsn2 : gs.next.cap.toNat < 2 ^ 63)
    (hsp1 : ds.prev.length ≤ gs.prev.cap.toNat) (hsp2 : gs.prev.cap.toNat < 2 ^ 63) :
    epochDirPBCellsAt cur gs ds ∗
      vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 ⊢
      memRegion cur 112 ∗
      vecCapPtrDealloc A gs.next.cap gs.next.ptr ∗
      vecCapPtrDealloc A gs.prev.cap gs.prev.ptr := by
  rw [show
    epochDirPBCellsAt cur gs ds ∗
      vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16 =
    (epochDirPBCellsAt cur gs ds ∗
      ((cur + 56#64) ↦₆₄ u0) ∗ ((cur + 64#64) ↦₆₄ u1) ∗ ((cur + 72#64) ↦₆₄ u2) ∗
      ((cur + 80#64) ↦₆₄ u3) ∗ ((cur + 88#64) ↦₆₄ u4) ∗ memRegion (cur + 96#64) 16) ∗
    (vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev) by ac_rfl]
  exact sepConj_mono
    (sendCells_recvNone_entails_memRegion_112 cur gs ds u0 u1 u2 u3 u4)
    (sepConj_mono
      (vecU8BufAt_entails_dealloc A gs.next.cap gs.next.ptr ds.next hsn1 hsn2)
      (vecU8BufAt_entails_dealloc A gs.prev.cap gs.prev.ptr ds.prev hsp1 hsp2))

theorem sendSome_recvSome_entails_err (A : RustAlloc) (cur : BitVec 64)
    (gs gr : EpochDirectionPBGhost) (ds dr : EpochDirectionPB)
    (hsn1 : ds.next.length ≤ gs.next.cap.toNat) (hsn2 : gs.next.cap.toNat < 2 ^ 63)
    (hsp1 : ds.prev.length ≤ gs.prev.cap.toNat) (hsp2 : gs.prev.cap.toNat < 2 ^ 63)
    (hrn1 : dr.next.length ≤ gr.next.cap.toNat) (hrn2 : gr.next.cap.toNat < 2 ^ 63)
    (hrp1 : dr.prev.length ≤ gr.prev.cap.toNat) (hrp2 : gr.prev.cap.toNat < 2 ^ 63) :
    epochDirPBCellsAt cur gs ds ∗
      vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev ∗
      recvDirPBCellsAt56 cur gr dr ∗
      vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev ⊢
      memRegion cur 112 ∗
      vecCapPtrDealloc A gs.next.cap gs.next.ptr ∗
      vecCapPtrDealloc A gs.prev.cap gs.prev.ptr ∗
      vecCapPtrDealloc A gr.next.cap gr.next.ptr ∗
      vecCapPtrDealloc A gr.prev.cap gr.prev.ptr := by
  rw [show
    epochDirPBCellsAt cur gs ds ∗
      vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev ∗
      recvDirPBCellsAt56 cur gr dr ∗
      vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev =
    (epochDirPBCellsAt cur gs ds ∗ recvDirPBCellsAt56 cur gr dr) ∗
    (vecU8BufAt A gs.next.cap gs.next.ptr ds.next ∗
      vecU8BufAt A gs.prev.cap gs.prev.ptr ds.prev ∗
      vecU8BufAt A gr.next.cap gr.next.ptr dr.next ∗
      vecU8BufAt A gr.prev.cap gr.prev.ptr dr.prev) by ac_rfl]
  exact sepConj_mono
    (sendCells_recvCells_entails_memRegion_112 cur gs gr ds dr)
    (sepConj_mono
      (vecU8BufAt_entails_dealloc A gs.next.cap gs.next.ptr ds.next hsn1 hsn2)
      (sepConj_mono
        (vecU8BufAt_entails_dealloc A gs.prev.cap gs.prev.ptr ds.prev hsp1 hsp2)
        (sepConj_mono
          (vecU8BufAt_entails_dealloc A gr.next.cap gr.next.ptr dr.next hrn1 hrn2)
          (vecU8BufAt_entails_dealloc A gr.prev.cap gr.prev.ptr dr.prev hrp1 hrp2))))

/-! ## Relocatable `[LibsignalPlacement]` Error Cleanup Helpers (Block `364`) -/

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = none` (`x20 = 0xffffffffffffffff#64`). -/
theorem fromPb_loop_err_520_none_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = some recvPb`. -/
theorem fromPb_loop_err_520_some_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (rncap rnptr rpcap rpptr sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hrn_cmn := add_one_beq_zero_of_lt_pow63 hrn_lt
  dsimp only [BitVec.ofNat_eq_ofNat] at herr hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 596#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x12 = rpptr ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = rpcap) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (rnptr, rncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx12_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1⟩
    refine seq_clean (mid := (blkPl_364).base + 792#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
        sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hrp : rpcap = 0
      · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
        simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        wp_done
      · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
        have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hrpb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (rpptr, rpcap.toNat, 1)
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx0_2, hx11_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2⟩
      exact herr s2 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx0_2 hx11_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Deallocate `sendPb.next` and `sendPb.prev` at `+452 .. +520`. -/
theorem fromPb_loop_err_452_to_520_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (F : SepProp) (x : ChainFromPbCall) (s0 s : State)
    (sncap snptr spcap spptr x9_val x12_val x19_val x20_val x23_val x26_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = x12_val) (hx19 : s.readReg64 .x19 = x19_val)
    (hx20 : s.readReg64 .x20 = x20_val) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x23_val) (hx24 : s.readReg64 .x24 = sncap)
    (hx26 : s.readReg64 .x26 = x26_val) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) ((blkPl_364).base + 520#64) s
      (F ∗ vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fun sm Pm =>
        (Pm ⊢ F ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x12 = x12_val ∧ sm.readReg64 .x19 = x19_val ∧
        sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x26 = x26_val) := by
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  refine seq_clean (mid := (blkPl_364).base + 488#64)
    (P_mid := F ∗ vecCapPtrDealloc A spcap spptr ∗ A.pool ∗
      loopScratchAt s0 x x9_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = x12_val ∧ sm.readReg64 .x19 = x19_val ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x26 = x26_val ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (snptr, sncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1, hx27_1, hx28_1⟩
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hsp_cap : spcap = 0
    · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
      simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
      have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hspb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (spptr, spcap.toNat, 1)
      wp_steps; rw [hsp1]; wp_done

set_option maxHeartbeats 800000 in
/-- Tail bridge at `+780 .. +792` into `fromPb_join_err_placed`. -/
theorem fromPb_loop_err_780_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_placed _ A H hdealloc hchain_slice hproto_slice x s0
  dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+380` when `curPB.recv = none`. -/
theorem fromPb_loop_err_380_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 380#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = snptr) (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h780 := @fromPb_loop_err_780_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [BitVec.ofNat_eq_ofNat] at h780 hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 408#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (snptr, sncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx23_1, hx27_1, hx28_1⟩
    refine seq_clean (mid := (blkPl_364).base + 780#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsp_cap : spcap = 0
      · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
        rw [hsp_cap] at hx27_1
        simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
        have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hspb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (spptr, spcap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx11_2, hx19_2, hx20_2, hx23_2, hx27_2⟩
      exact h780 s2 convG convEpochs remG remPB sp0_val hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx11_2
        hx19_2 hx20_2 hx23_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Deallocate `recvPb.next` and `recvPb.prev` at `+644 .. +704`. -/
theorem fromPb_loop_err_644_to_704_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (F : SepProp) (x : ChainFromPbCall) (s0 s : State)
    (convLen : Nat) (rncap rnptr rpcap rpptr x21_val x22_val x24_val x27_val x28_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = x21_val) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = x24_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convLen * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = x27_val)
    (hx28 : s.readReg64 .x28 = x28_val) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) ((blkPl_364).base + 704#64) s
      (F ∗ vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fun sm Pm =>
        (Pm ⊢ F ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x21 = x21_val ∧ sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convLen * 112) ∧
        sm.readReg64 .x24 = x24_val ∧ sm.readReg64 .x27 = x27_val ∧
        sm.readReg64 .x28 = x28_val) := by
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  refine seq_clean (mid := (blkPl_364).base + 676#64)
    (P_mid := F ∗ vecCapPtrDealloc A rpcap rpptr ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = x22_val ∧ sm.readReg64 .x24 = x24_val ∧
      sm.readReg64 .x25 = BitVec.ofNat 64 (convLen * 112) ∧
      sm.readReg64 .x26 = rpcap ∧ sm.readReg64 .x27 = x27_val ∧
      sm.readReg64 .x28 = x28_val) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (rnptr, rncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx21_1, hx22_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hrp : rpcap = 0
    · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
      simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
      have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrpb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (rpptr, rpcap.toNat, 1)
      wp_steps; rw [hsp1]; wp_done

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+644` when `curPB.recv = some recvPb` fails `tst`. -/
theorem fromPb_loop_err_644_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x22_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = snptr) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_644_to_704_placed _ A H hdealloc F_frame
    x s0 s convEpochs.length rncap rnptr rpcap rpptr snptr x22_val sncap spcap spptr sp0_val
    hsp0_align hrn_lt hrn_ne hrp_lt hrp_ne hpc hrun hsp htr hfp hx11 hx12 hx19 hx20 hx21 hx22
    hx24 hx25 hx26 hx27 hx28
  refine seq_clean (mid := (blkPl_364).base + 704#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x21 = snptr ∧ sm.readReg64 .x22 = x22_val ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = sncap ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1⟩
    refine SepWP.weaken_pre (Entails.of_eq (by
      dsimp only [F_frame]; ac_rfl :
      F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack =
      memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)) ?_
    have h780 := @fromPb_loop_err_780_placed _ A H hdealloc hchain_slice hproto_slice x s0
    have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 192#64 hsp0_align (by decide)
    dsimp only [BitVec.ofNat_eq_ofNat] at h780 hdealloc hpc1 ⊢
    refine seq_clean (mid := (blkPl_364).base + 732#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsn : sncap = 0
      · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
        simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
        have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (snptr, sncap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx11_2, hx20_2, hx22_2, hx23_2, hx27_2, hx28_2⟩
      refine seq_clean (mid := (blkPl_364).base + 780#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          arrayAt (chainEpochPBAt A) 112
            (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x x22_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x19 = 0#64 ∧
          sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
          sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
          sm.readReg64 .x27 = 0#64) ?_ ?_
      · unfold vecCapPtrDealloc loopScratchAt
        by_cases hsp_cap : spcap = 0
        · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
          rw [hsp_cap] at hx27_2
          simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps; wp_done
        · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
          have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
          simp only [hspb, Bool.false_eq_true, ↓reduceIte]
          rw [stackAt_subStack_split_allocHook s0.sp]
          wp_steps
          wp_call hdealloc (spptr, spcap.toNat, 1)
          wp_steps; rw [hsp2]; wp_done
      · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx11_3, hx19_3, hx20_3, hx23_3, hx27_3⟩
        exact h780 s3 convG convEpochs remG remPB x22_val hsp0_align hfromPb_eq hconv_len hrem_len
          hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hfp3 hx11_3
          hx19_3 hx20_3 hx23_3 hx27_3

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_none_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr x9_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ A H hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val (s.readReg64 .x12) (s.readReg64 .x19)
    0xffffffffffffffff#64 (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (s.readReg64 .x26) sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 rfl rfl hx20 hx21
    hx23 hx24 rfl hx27 hx28
  refine seq_clean (mid := (blkPl_364).base + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
      sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = s.readReg64 .x26) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, _, _, hx20_1, hx23_1, _⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_none_placed hdealloc hchain_slice hproto_slice x s0 s1 convG convEpochs remG remPB x9_val
        hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx20_1 hx23_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_some_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x9_val sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap) (hx26 : s.readReg64 .x26 = rpcap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ A H hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val rpptr rnptr rncap
    (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) rpcap sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 hx12 hx19 hx20 hx21
    hx23 hx24 hx26 hx27 hx28
  refine seq_clean (mid := (blkPl_364).base + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x19 = rnptr ∧
      sm.readReg64 .x20 = rncap ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = rpcap) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_some_placed hdealloc hchain_slice hproto_slice x s0 s1 convG convEpochs remG remPB
        rncap rnptr rpcap rpptr x9_val hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len
        hl_le hl_lt hl_ne hn_le hn_lt hn_ne hrn_lt hrn_ne hrp_lt hrp_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hx26_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

end CryptoVerification.SpqrV1.ChainProofs
