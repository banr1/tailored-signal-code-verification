/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrap
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlaced

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

set_option maxHeartbeats 1200000 in
theorem stageP1_ok_kit_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (hkit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec kit)))
    (hkit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitLoadPollPlacedSpecSE kit Scope encRecord)))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec ikit)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitTrustPollPlacedSpecI ikit)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hstack_lt : stageP1CallStack kit ikit ≤ 2 ^ 64)
    (hext_load : extHookStack ≤ loadCallStack kit)
    (_hext_trust : extHookStack ≤ trustCallStack ikit)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 b_4f2 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s0)
    (hpc : s0.pc = stageP1EntryPlaced)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x868#64) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗
       ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1CallStack kit ikit))
      (fun sf P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
          (P_f ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              p1LoadedRecordAt Scope A coroPtr opt ∗
              ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
              ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
              ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
              ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              FromRecordCallees.lsLogOff ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt sp (stageP1CallStack kit ikit))) ∧
        sf.sp = sp ∧
        sf.readReg64 .x8 = kyberStorePtr ∧
        sf.readReg64 .x9 = msgPtr ∧
        sf.readReg64 .x10 = kyberStoreVt ∧
        sf.readReg64 .x11 = preKeyStorePtr ∧
        sf.readReg64 .x12 = remoteAddrPtr ∧
        sf.readReg64 .x13 = preKeyStoreVt ∧
        sf.readReg64 .x14 = localAddrPtr ∧
        sf.readReg64 .x15 = idStorePtr ∧
        sf.readReg64 .x16 = ikit.id_vt ∧
        sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        sf.readReg64 .x24 = spkStoreVt ∧
        sf.readReg64 .x25 = sp + 0x210#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = s0.sp - 0x60#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := p1_seg1_vregs_wp_ext_placed ext s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (0#64 + kit.loadShimOff) v_sp0
    hpc hrun hsp_align hx0 hx1 hx2
  rw [hsp_def] at hstep1
  refine bind_sepWP_steps_frame_placed hcrl hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hcrl1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit_x_ext_placed (ikit := ikit)
    peer hdealloc hmemcpy hkit_shim hkit_poll hkit_drop hext_load hload_le haddr_ss hload_ok s0 s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hcrl1 hfs1_kit hpc1 hrun1 hsp1_align htr1
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  have hload_ex := SepWPp.mono_run hload fun s6 P_m h =>
    let ⟨⟨opt, hrel, htr6, hent⟩, hregs⟩ := h
    Exists.intro opt (And.intro (And.intro hrel (And.intro htr6 hregs)) hent)
  refine bind_sepWPp_exists_frame hload_ex (by sep_focus)
    fun opt s6 hsteps16 hpc6 hrun6 hregs6 => ?_
  rcases hregs6 with ⟨hrel_load, htr6, hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, hx29_6, hx30_6, hvregs6, hcrl6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have htrust := stageP1_trust_ok_kit_x_ext_placed
    peer remoteIdKey hdealloc hikit_shim hikit_poll hikit_drop htrust_le haddr_id htrust_true s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_4f2
    hcrl6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  rw [hsp6] at htrust
  simp only [BitVec.add_assoc] at htrust
  have htrust_re := SepWPp.mono_run htrust fun sf P_f h =>
    let ⟨hrel_t, htr_f, hent, hregs⟩ := h
    And.intro hent (And.intro hrel_t (And.intro htr_f hregs))
  refine SepWPp.bind_sepWPp_steps_frame htrust_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hrel_trust, htr_f, hsp_f,
    hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f,
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f, hvregsf, hcrlf⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) := by
    rw [htr_f, htr6, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs6, hvregs1]
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hsp_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f,
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f,
    by rw [hx29_f, hx29_6, hx29_1], hvregs_full, hcrlf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlaced
