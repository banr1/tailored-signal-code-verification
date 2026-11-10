/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Ok
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsTrapA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustTrap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedTrap

/-!
# Stage P1 Untrusted-Identity Composition over `trTrapProgAt` and `tripleRatchetProgAtExt`

Proves full entry-to-`s0.readReg64 .x30` untrusted-identity composition (`stageP1_untrusted_ok_kit_trap`
and `stageP1_untrusted_ok_kit_x_ext`) preserving `calleeSavedVRegs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 1200000 in
private theorem stageP1_untrusted_from_trust_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hA : AllocHooks A abs)
    (hikit : IdentityStoreKitOkIE img ikit (trTrapExterns C abs))
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 s6 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv6 : ImgCallInv img s6)
    (hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (trTrapProgAt img.base C abs) s6)
    (hpc6 : s6.pc = img.base + ikit.trustShimOff)
    (hrun6 : s6.status = .Running)
    (hsp6_eq : s6.sp = sp)
    (hsp_saved : sp + 0xcd0#64 = s0.sp)
    (hsp6_align : (s6.sp &&& 15#64 == 0#64) = true)
    (htr6_pre : s0.trace <+: s6.trace)
    (hx0_6 : s6.readReg64 .x0 = idStorePtr)
    (hx1_6 : s6.readReg64 .x1 = remoteAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = (directionByte .receiving).zeroExtend 64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_6 : s6.readReg64 .x26 = outPtr)
    (hx27_6 : s6.readReg64 .x27 = ctxPtr)
    (hx30_6 : s6.readReg64 .x30 =
      (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s6
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt s0.sp s0 ∗
       memRegion outPtr 48 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            cells (coroPtr + 0x398#64) 2 ∗
            ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x3e0#64) 368 ∗
            cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            kit.storeAt sessStorePtr st ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt sp (stageP1UntrustedCallStack kit ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sf.trace = s6.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s6 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_le : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit_trap (ist := ist)
    peer remoteIdKey hA hikit htrust_le haddr_id s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_trap htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine SepWPp.bind_sepWPp_steps_frame htrust (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hinvm⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6_eq]; exact hsp6_align
  have htrm_pre : s0.trace <+: sm.trace := by
    rcases htr6_pre with ⟨pre, hpre⟩
    exact ⟨pre ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false),
      by rw [htrm, ← hpre, List.append_assoc]⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt))
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit_trap
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hA herr_le s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hb hinvm hpcm hrunm hspm_align htrm_pre hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  have herr_re := SepWPp.mono_run herr fun sf P_f h =>
    let ⟨htrf, hent, hregs⟩ := h
    And.intro hent (And.intro htrf hregs)
  refine SepWPp.bind_sepWPp_steps_frame herr_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcs_f, hvregsf_m, hFf, hsymf⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hrel_trust, htrf.trans htrm, hspf, hcs_f, hvregsf_m.trans hvregsm, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
set_option maxHeartbeats 1200000 in
/-- Full Stage P1 + untrusted-identity exit over `trTrapProgAt img.base C abs`,
`SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns C abs)`, and
`IdentityStoreKitOkIE img ikit (trTrapExterns C abs)`, preserving `calleeSavedVRegs`. -/
theorem stageP1_untrusted_ok_kit_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hA : AllocHooks A abs)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns C abs))
    (hikit : IdentityStoreKitOkIE img ikit (trTrapExterns C abs))
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs) s0)
    (hpc : s0.pc =
      (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       memRegion outPtr 48 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
       ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
       ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
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
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
              ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
              ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              logOff img ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hp1_le
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := p1_seg1_vregs_wp_trap
    img.base C abs s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (img.base + kit.loadShimOff) v_sp0
    hpc hrun hsp_align hx0 hx1 hx2
  rw [hsp_def] at hstep1
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit_trap (ikit := ikit)
    peer hA hkit hload_le haddr_ss hload_ok s0 s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hb hinv1 hfs1_kit hpc1 hrun1 hsp1_align htr1
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  have hload_ex := SepWPp.mono_run hload fun s6 P_m h =>
    let ⟨⟨opt, hrel, htr6, hent⟩, hregs⟩ := h
    Exists.intro opt (And.intro (And.intro hrel (And.intro htr6 hregs)) hent)
  refine bind_sepWPp_exists_frame hload_ex (by sep_focus)
    fun opt s6 hsteps16 hpc6 hrun6 hregs6 => ?_
  rcases hregs6 with ⟨hrel_load, htr6, hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, _, hx30_6, hvregs6, hF6, hsym6⟩
  have hinv6 : ImgCallInv img s6 := ⟨hF6, hsym6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  have htail := stageP1_untrusted_from_trust_trap
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hA hikit hstack_lt haddr_id htrust_false s0 s6
    sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6 hsp_saved hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  simp only [BitVec.add_assoc] at htail
  refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hrel_trust, htrf_6, hspf, hcs_f, hvregsf_6, hFf, hsymf⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) := by
    rw [htrf_6, htr6, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_6, hvregs6, hvregs1]
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hspf, hcs_f, hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Full Stage P1 + untrusted-identity exit over `tripleRatchetProgAtExt img.base ext`,
`SessionOnlyKitOkSE kit Scope encRecord ext`, and `IdentityStoreKitOkIE img ikit ext`,
preserving `calleeSavedVRegs`. -/
theorem stageP1_untrusted_ok_kit_ext {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hAh : AllocHooks A abs)
    (_hA : AllocContracts img.base A ext)
    (hT : TrapsOnly (trTrapProgAt img.base C abs) (tripleRatchetProgAtExt img.base ext))
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s0)
    (hpc : s0.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       memRegion outPtr 48 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
       ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
       ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
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
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
              ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
              ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              logOff img ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hfn := fnAddr_trTrap_eq_ext img.base C abs ext
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hp1_le
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := SepWP.of_trapsOnly hT (p1_seg1_vregs_wp_trap
    img.base C abs s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (img.base + kit.loadShimOff) v_sp0
    (by rwa [hfn]) hrun hsp_align hx0 hx1 hx2)
  rw [hsp_def, hfn] at hstep1
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit_ext (ikit := ikit)
    peer hAh hT hkit hload_le haddr_ss hload_ok s0 s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hb hinv1 hfs1_kit hpc1 hrun1 hsp1_align htr1
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  have hload_ex := SepWPp.mono_run hload fun s6 P_m h =>
    let ⟨⟨opt, hrel, htr6, hent⟩, hregs⟩ := h
    Exists.intro opt (And.intro (And.intro hrel (And.intro htr6 hregs)) hent)
  refine bind_sepWPp_exists_frame hload_ex (by sep_focus)
    fun opt s6 hsteps16 hpc6 hrun6 hregs6 => ?_
  rcases hregs6 with ⟨hrel_load, htr6, hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, _, hx30_6, hvregs6, hF6, hsym6⟩
  have hinv6 : ImgCallInv img s6 := ⟨hF6, hsym6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  have htail := stageP1_untrusted_from_trust_ext
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hAh hT hikit hstack_lt haddr_id htrust_false s0 s6
    sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6 hsp_saved hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  simp only [BitVec.add_assoc] at htail
  refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hrel_trust, htrf_6, hspf, hcs_f, hvregsf_6, hFf, hsymf⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) := by
    rw [htrf_6, htr6, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_6, hvregs6, hvregs1]
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hspf, hcs_f, hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Contract-backed (`AllocContractsX`) Stage P1 Untrusted interface on `tripleRatchetProgAtExt`.
Requires `2 * extHookStack ≤ loadCallStack kit` (`32,768` B) because `<String as Clone>::clone` is
real code (`48`-byte prologue frame) calling `.inImage img` `shim`/`memcpy` contracts with
`extHookStack` (`16,384` B): real `String::clone` frame (`48` B) + `shim`/`memcpy` hook stack
(`16,384` B) ≤ `32,768` B. -/
def StageP1UntrustedXExtStmt : Prop :=
  ∀ {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    AllocContractsX img A ext →
    AllocHooks A ext →
    SessionOnlyKitOkSE kit Scope encRecord ext →
    IdentityStoreKitOkIE img ikit ext →
    stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
    2 * extHookStack ≤ loadCallStack kit →
    kit.addrOk peer.val →
    ikit.addrOk peer.val →
    (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 : BitVec 8),
      img.base &&& 0xfff#64 = 0#64 →
      ImgCallInv img s0 →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (tripleRatchetProgAtExt img.base ext) s0 →
      s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0xa90#64) 6 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         memRegion outPtr 48 ∗
         ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
         ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
         ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
         ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
         ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
         ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
         ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
         ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
         logOff img ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt A peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         A.pool ∗
         stackAt sp (stageP1UntrustedCallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))),
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
            sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
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
                memRegion (coroPtr + 0xe0#64) 368 ∗
                cells (coroPtr + 0x250#64) 6 ∗
                ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x370#64) 36 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                cells (sp + 0xa90#64) 6 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
                ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
                ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
                ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
                ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
                ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
                ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
                ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
                ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
                ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
                ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
                logOff img ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
                protocolAddressAt A peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                A.pool ∗
                stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
          sf.sp = s0.sp ∧
          ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
        (PanicOomProp s0)

set_option maxHeartbeats 1200000 in
/-- Full Stage P1 Untrusted-Identity Composition over `tripleRatchetProgAtExt` under
`AllocContractsX` (`entry -> s0.readReg64 .x30`) with `calleeSavedVRegs sf = calleeSavedVRegs s0`. -/
theorem stageP1_untrusted_ok_kit_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hAc : AllocContractsX img A ext)
    (hAh : AllocHooks A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (hext_load : 2 * extHookStack ≤ loadCallStack kit)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s0)
    (hpc : s0.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       memRegion outPtr 48 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
       ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
       ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
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
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
              ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
              ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              logOff img ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hp1_le
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := p1_seg1_vregs_wp_ext img.base ext s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (img.base + kit.loadShimOff) v_sp0
    hpc hrun hsp_align hx0 hx1 hx2
  rw [hsp_def] at hstep1
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit_x_ext (ikit := ikit)
    peer hAc hAh hkit (Nat.le_trans (by decide) hext_load) hload_le haddr_ss hload_ok s0 s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hb hinv1 hfs1_kit hpc1 hrun1 hsp1_align htr1
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  have hload_ex := SepWPp.mono_run hload fun s6 P_m h =>
    let ⟨⟨opt, hrel, htr6, hent⟩, hregs⟩ := h
    Exists.intro opt (And.intro (And.intro hrel (And.intro htr6 hregs)) hent)
  refine bind_sepWPp_exists_frame hload_ex (by sep_focus)
    fun opt s6 hsteps16 hpc6 hrun6 hregs6 => ?_
  rcases hregs6 with ⟨hrel_load, htr6, hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, _, hx30_6, hvregs6, hF6, hsym6⟩
  have hinv6 : ImgCallInv img s6 := ⟨hF6, hsym6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  have htail := stageP1_untrusted_from_trust_x_ext
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hAc hAh hikit hstack_lt hext_load haddr_id htrust_false s0 s6
    sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6 hsp_saved hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  simp only [BitVec.add_assoc] at htail
  refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hrel_trust, htrf_6, hspf, hcs_f, hvregsf_6, hFf, hsymf⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) := by
    rw [htrf_6, htr6, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_6, hvregs6, hvregs1]
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hspf, hcs_f, hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem stageP1_untrusted_ok_x_ext : StageP1UntrustedXExtStmt :=
  fun peer remoteIdKey hAc hAh hkit hikit hstack_lt hext_load =>
    stageP1_untrusted_ok_kit_x_ext peer remoteIdKey hAc hAh hkit hikit hstack_lt hext_load

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
