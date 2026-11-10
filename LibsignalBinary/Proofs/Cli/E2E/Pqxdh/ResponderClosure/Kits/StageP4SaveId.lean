/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P4.1 Segments: `IdentityKeyStore::save_identity`

Basic-block `SepWP` segments (`+0x34dc → saveShim`, `+0x3564 → savePoll`, `+0x6c → saveFutDrop`,
`+0x2ec → kyberMarkUsedShimAddr` / `+0x550`) and error-slot bijection helpers for Substage P4.1 on
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_0_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_32_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.setWidth_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.append_1_32_getElem_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## Basic-block `SepWP` segments for Substage P4.1 -/

set_option maxHeartbeats 800000 in
/-- `+0x34dc → saveIdentityShimAddr`: checks empty `previous_states` (`sp + 0x3c8..0x3d8`),
    copies the 24-byte `ptext` `Vec<u8>` from `sp + 0x278..0x290` into `coroPtr + 0x280..0x298`,
    and dispatches `id_store.save_identity(remote_addr, remote_ik)` via `[idStoreVt + 0x28]`. -/
theorem p4_seg1a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr idStorePtr idStoreVt saveIdentityShimAddr
    remoteAddrPtr remoteIkPtr ptextMid0 ptextMid1
    u_250 u_258 u_coro284 u_coro28c v_3d0 : BitVec 64)
    (ptextHead ptextTail u_260 u_coro280 u_coro294 : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext) saveIdentityShimAddr s
      (((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x280#64) ↦₃₂ u_coro280) ∗
       ((coroPtr + 0x284#64) ↦₆₄ u_coro284) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ u_coro28c) ∗
       ((coroPtr + 0x294#64) ↦₃₂ u_coro294) ∗
       ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
       ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x250#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x258#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x260#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
          ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = remoteIkPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3564#64) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34dc 0x34e4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3500 0x3504
  closure_fetches_range_cli b (Rust.withPanics ext) 0x351c 0x3560
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0x3564 → saveIdentityPollAddr` via `+0x005c..+0x0068`: stores `(saveIdFutPtr, saveIdFutVt)`
    at `coroPtr + 0x2c8..0x2d0` and polls `save_identity` into `sp + 0x3e0..0x410`. -/
theorem p4_seg1b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr saveIdFutPtr saveIdFutVt saveIdentityPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3564#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = saveIdFutPtr)
    (hx1 : s.readReg64 .x1 = saveIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAtExt b ext) saveIdentityPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6c#64) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3564 0x356c
  closure_fetches_range_cli b (Rust.withPanics ext) 0x5c 0x68
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = saveIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = saveIdFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0x006c → saveIdentityDropAddr` via `+0x02bc..+0x02e8` for any ready tag `w0`
    (`w0 + 3#64 ≠ 0#64`, covering both `Ok` (`-2`) and `Err` (`0x800000000000001A`)):
    copies `sp + 0x3ec..0x410` into `sp + 0x2b0..0x2d4`, sets `x22 := w_3e8`, `x28 := w0`,
    and calls `drop_in_place` (`[saveIdFutVt + 0x0]`) on `saveIdFutPtr`. -/
theorem p4_seg1c_gen_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt saveIdentityDropAddr w0
    w_3ec w_3f4 w_3fc w_404 u_2b0 u_2b8 u_2c0 u_2c8 : BitVec 64)
    (w_3e8 w_40c u_2d0 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : saveIdentityDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext) saveIdentityDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
       (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
       stagingCellsAt (s.sp + 0x2b0#64) u_2b0 u_2b8 u_2c0 u_2c8 u_2d0 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
          stagingCellsAt (s.sp + 0x2b0#64) w_3ec w_3f4 w_3fc w_404 w_40c ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = saveIdFutPtr ∧
        s1.readReg64 .x22 = w_3e8.zeroExtend 64 ∧
        s1.readReg64 .x23 = saveIdFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2ec#64) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (saveIdentityDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  closure_fetches_range_cli b (Rust.withPanics ext) 0x6c 0x74
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2bc 0x2e8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- `+0x02ec → kyberMarkUsedShimAddr` (`Ok` arm, `x28 = -2`) under `StageP4Alloc`. -/
theorem p4_seg1d_ok_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr msgPtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr
    saveIdFutPtr saveIdFutVt futSize futAlign u_2ac u_2b4 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext) kyberMarkUsedShimAddr s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
       ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
       ((coroPtr + 0x2ac#64) ↦₆₄ u_2ac) ∗
       ((coroPtr + 0x2b4#64) ↦₆₄ u_2b4) ∗
       ((coroPtr + 0x2bc#64) ↦₃₂ u_2bc) ∗
       ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
       ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x2ac#64) ↦₃₂ opkIdIsSome) ∗
          ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
          ((coroPtr + 0x2b4#64) ↦₃₂ 1#32) ∗
          ((coroPtr + 0x2b8#64) ↦₃₂ kyberPreKeyId) ∗
          ((coroPtr + 0x2bc#64) ↦₃₂ signedPreKeyId) ∗
          ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x3 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x350#64) := by
  have hdealloc := dealloc_at_closure_p4 hA
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hopk_beq : (opkIdIsSome - 2#32 == 0#32) = false := beq_eq_false_iff_ne.mpr hopk_ne2
  have hpair_298 : ∀ R : SepProp,
      ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ (((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗ R) =
      ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗ R := by
    intro R; rw [← sepConj_assoc]
    exact congrArg (· ∗ R) (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        pointsTo32_pair_eq (coroPtr + 0x298#64) opkIdIsSome opkId)
  rw [hpair_298]
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2ec 0x34c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  have hsplit_2ac :
      ((coroPtr + 684#64) ↦₆₄ (opkId ++ opkIdIsSome)) =
      ((coroPtr + 684#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 688#64) ↦₃₂ opkId) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq (coroPtr + 684#64) opkIdIsSome opkId).symm
  have hsplit_2b4 :
      ((coroPtr + 692#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) =
      ((coroPtr + 692#64) ↦₃₂ 1#32) ∗ ((coroPtr + 696#64) ↦₃₂ kyberPreKeyId) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq (coroPtr + 692#64) 1#32 kyberPreKeyId).symm
  refine ⟨Entails.of_eq (by rw [hsplit_2ac, hsplit_2b4]; ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p4_seg1d_ok_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr msgPtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr
    saveIdFutPtr saveIdFutVt futSize futAlign u_2ac u_2b4 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext) kyberMarkUsedShimAddr s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
       ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
       ((coroPtr + 0x2ac#64) ↦₆₄ u_2ac) ∗
       ((coroPtr + 0x2b4#64) ↦₆₄ u_2b4) ∗
       ((coroPtr + 0x2bc#64) ↦₃₂ u_2bc) ∗
       ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
       ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x2ac#64) ↦₃₂ opkIdIsSome) ∗
          ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
          ((coroPtr + 0x2b4#64) ↦₃₂ 1#32) ∗
          ((coroPtr + 0x2b8#64) ↦₃₂ kyberPreKeyId) ∗
          ((coroPtr + 0x2bc#64) ↦₃₂ signedPreKeyId) ∗
          ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x3 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x350#64) :=
  p4_seg1d_ok_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr msgPtr kyberStorePtr kyberStoreVt
    kyberMarkUsedShimAddr saveIdFutPtr saveIdFutVt futSize futAlign u_2ac u_2b4
    opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc hsize_nz hopk_ne2 hpc hrun hsp
    hx19 hx21 hx23 hx28

/-- `+0x02ec → +0x0550` (`Err` arm, `w0 + 2#64 ≠ 0#64`) under `StageP4Alloc`. -/
theorem p4_seg1d_err_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x2b0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := dealloc_at_closure_p4 hA
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hw0_beq : (w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_ok
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2ec 0x304
  closure_fetches_range_cli b (Rust.withPanics ext) 0x544 0x54c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps
  wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p4_seg1d_err_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x2b0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) :=
  p4_seg1d_err_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr saveIdFutPtr saveIdFutVt
    futSize futAlign w0 hsize_nz hw0_ne_ok hpc hrun hsp hx19 hx21 hx23 hx28

/-! ## `SepWPp` call combinators and error-slot bijections -/

/-- `SepWPp.bind_sepWP_frame` refined to pass `Steps prog s s1` to the continuation. -/
theorem SepWPp.bind_sepWP_frame_steps {prog : Program} {mid ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q1 Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s T Q1)
    (hP : P = T ∗ F)
    (hnext : ∀ s1 P1, s1.pc = mid → s1.status = .Running → Steps prog s s1 →
      Q1 s1 P1 → SepWPp prog ret s1 (P1 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨s1, hsteps1, ⟨hpc1, hrun1, P1, hm1, hQ1⟩ | ⟨_, hoom⟩⟩
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps2, hout⟩ := hnext s1 P1 hpc1 hrun1 hsteps1 hQ1 R hm1 (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Inject read-only `.rodata` points-to atoms extracted from `img.FrozenLoaded s` into a `SepWPp`
precondition at zero spatial cost. -/
theorem SepWPp.intro_ro {prog : Program} {ret : BitVec 64} {s : State}
    {R_ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {M : SepProp}, s.mem ⊨ M → s.mem ⊨ R_ro ∗ M)
    (h : SepWPp prog ret s (R_ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (R_ro ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact hro hm
  exact h R hm' hL

/-- Layout-independent unpack of a right-associated 5-word + `errTailAt`-shaped
`SignalProtocolError` poll slot (`savePollOutAt ... (.error ())` or `storePollOutAt ... (.error ())`)
into `pollCellsAt`. -/
theorem fiveWords_tail_eq_exists_pollCells (p w0 w1 w2 w3 w4 strAddr : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
      ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
      memRegion (p + 0x28#64) 8 =
    ∃∗ w5 : BitVec 64,
      pollCellsAt p w0 (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) ∗ (strAddr ↦ᵣ storeHookStr) := by
  rw [ProofLib.memRegion_eight (p + 0x28#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w5 => ?_)
  rw [← speWordsAt_eq_pollCellsAt p w0 w1 w2 w3 w4 w5]
  unfold speWordsAt; ac_rfl

/-- Layout-independent repack of `pollCellsAt outPtr ... ∗ (strAddr ↦ᵣ storeHookStr)` back into a
right-associated 5-word + `errTailAt` `SignalProtocolError` return slot. -/
theorem pollCells_entails_fiveWords_tail (outPtr w0 w1 w2 w3 w4 w5 strAddr : BitVec 64) :
    pollCellsAt outPtr w0 (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) ∗ (strAddr ↦ᵣ storeHookStr) ⊢
      (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
        ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
        memRegion (outPtr + 0x28#64) 8 := by
  rw [← speWordsAt_eq_pollCellsAt outPtr w0 w1 w2 w3 w4 w5]
  have hswap : speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗ (strAddr ↦ᵣ storeHookStr) =
      (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
        ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
        ((outPtr + 0x28#64) ↦₆₄ w5) := by
    unfold speWordsAt; ac_rfl
  rw [hswap]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _))))))

/-- Layout-independent existential unpack + repack of a 5-word + `errTailAt` poll slot into
    `pollCellsAt` with explicit witness terms. -/
theorem fiveWords_tail_unpack_repack {w0_tag : BitVec 64}
    (p w0 w1 w2 w3 w4 strAddr : BitVec 64) (hw0 : w0 = w0_tag) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
      ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
      memRegion (p + 0x28#64) 8 ⊢
    ∃∗ w0' : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
    ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
      ⌜w0' = w0_tag ∧
        (∀ outPtr : BitVec 64,
          pollCellsAt outPtr w0' o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
            (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
              ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗
              (strAddr ↦ᵣ storeHookStr) ∗ memRegion (outPtr + 0x28#64) 8)⌝ ∗
      pollCellsAt p w0' o1 o2 o3 o4 o5 o6 ∗ H_err := by
  rw [fiveWords_tail_eq_exists_pollCells p w0 w1 w2 w3 w4 strAddr]
  refine Entails.sepExists_elim fun w5 => ?_
  let o1 := w1.extractLsb' 0 32
  let o2 := w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32
  let o3 := w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32
  let o4 := w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32
  let o5 := w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32
  let o6 := w5.extractLsb' 32 32
  let H_err : SepProp := strAddr ↦ᵣ storeHookStr
  refine Entails.sepExists_right w0
    (Entails.sepExists_right o1 (Entails.sepExists_right o2 (Entails.sepExists_right o3
    (Entails.sepExists_right o4 (Entails.sepExists_right o5 (Entails.sepExists_right o6
    (Entails.sepExists_right H_err ?_)))))))
  refine Entails.pure_right ⟨hw0, fun outPtr => ?_⟩ (Entails.refl _)
  exact pollCells_entails_fiveWords_tail outPtr w0 w1 w2 w3 w4 w5 strAddr

/-- Prefix-generalized `.inImage img` subroutine call combinator for `SepWPp` under `PanicOomProp s0`,
accepting an entailment-style precondition splitter `hpre` so `withEnvPre` and `withLogOff` specs
need no manual pure-conjunction reassociation. -/
theorem SepWPp.call_inImage_pre_oom_prefix {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) :=
    inImage_pre_intro hF hsym (hpre R hm)
  obtain ⟨sm, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right
  · dsimp only [Spec.inImage] at _hoom_post
    rw [hoom_false] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) hsteps
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [Spec.inImage] at hpost
    rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_prefix htr⟩)⟩
  · dsimp only [Spec.inImage] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-- Read-only `.rodata` vtable bundle for `ikit`'s `save_identity` dispatch, poll, and drop. -/
def saveIdVtablesAt {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
  ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
  ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff))

theorem saveIdVtablesAt_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} (hvt : IdentityVtablesOk img ikit)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ saveIdVtablesAt ikit ∗ P := by
  unfold saveIdVtablesAt
  simp only [sepConj_assoc]
  exact hvt.saveSlot hF (hvt.saveFutDrop hF
    (hvt.saveFutSize hF (hvt.saveFutAlign hF (hvt.saveFutPoll hF hP))))

theorem memRegion24_eq_unaligned_cells (p : BitVec 64) :
    memRegion p 24 =
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 32,
        (p ↦₃₂ u0) ∗ ((p + 0x4#64) ↦₆₄ u1) ∗ ((p + 0xc#64) ↦₆₄ u2) ∗ ((p + 0x14#64) ↦₃₂ u3) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 4) (k := 20)
        (b' := p + 0x4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x4#64) (n := 8) (k := 12)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0xc#64) (n := 8) (k := 4)
        (b' := p + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four p,
      ProofLib.memRegion_eight (p + 0x4#64),
      ProofLib.memRegion_eight (p + 0xc#64),
      ProofLib.memRegion_four (p + 0x14#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion20_eq_cells (p : BitVec 64) :
    memRegion p 20 =
      ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 0x8#64) ↦₆₄ u1) ∗ ((p + 0x10#64) ↦₃₂ u2) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 12)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 8) (k := 4)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x8#64),
      ProofLib.memRegion_four (p + 0x10#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells20_entails_memRegion20 (p w0 w1 : BitVec 64) (w2 : BitVec 32) :
    (p ↦₆₄ w0) ∗ ((p + 0x8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₃₂ w2) ⊢ memRegion p 20 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 12)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 8) (k := 4)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))

theorem memRegion16_eq_cells (p : BitVec 64) :
    memRegion p 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 0x8#64) ↦₆₄ u1) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 8)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells16_entails_memRegion16 (p w0 w1 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 0x8#64) ↦₆₄ w1) ⊢ memRegion p 16 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 8)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

/-- Call `futDropSpec` (`emp → ⌜sf.trace = s.trace⌝`, no panic/exit/OOM) inside `SepWPp`. -/
theorem SepWPp.call_futDrop {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry futDropSpec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      Steps prog s sf →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ futDropSpec.pre () s ∗ (P ∗ R) := by
    dsimp only [futDropSpec]; rw [emp_sepConj]; exact hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall () (P ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ |
    ⟨_, hpost⟩
  · dsimp only [futDropSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm htrm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) hsteps
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-- Advance `FsAt` across any execution segment that appends no trace events. -/
theorem FsAt.of_steps_nil {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s s' : State}
    (h : FsAt envOk Q P s) (hst : Steps P s s') (htr : s'.trace = s.trace) :
    FsAt envOk Q P s' :=
  h.of_steps hst (evs := []) (by rw [htr, List.append_nil]) (fun _ => NoFsEv.nil)

/-- Unpack `savePollOutAt b p (.ok c)` into `pollCellsAt p (-2) ...`. -/
theorem savePollOk_eq_exists_pollCells (b p : BitVec 64) (c : IdentityChange) :
    savePollOutAt b p (.ok c) =
      ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64, ∃∗ o4 : BitVec 64,
      ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        pollCellsAt p 0xfffffffffffffffe#64
          (if c == .replacedExisting then 1#32 else 0#32) o2 o3 o4 o5 o6 := by
  dsimp only [savePollOutAt]
  rw [memRegion36_eq_exists_stagingCells (p + 0xc#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o6 => congrArg sepExists (funext fun o5 =>
    congrArg sepExists (funext fun o4 => congrArg sepExists (funext fun o3 =>
    congrArg sepExists (funext fun o2 => ?_)))))
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Layout-independent unpack + repack of `savePollOutAt b p (.error ())` into `pollCellsAt`. -/
theorem savePollErr_unpack_repack (b p : BitVec 64) :
    savePollOutAt b p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢ savePollOutAt b outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err := by
  dsimp only [savePollOutAt, errTailAt]
  simp only [sepConj_assoc]
  exact fiveWords_tail_unpack_repack p _ _ _ _ _ _ rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
