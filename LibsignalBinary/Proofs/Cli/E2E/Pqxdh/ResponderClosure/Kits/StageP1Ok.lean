/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Load
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Trust
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1

/-!
# Stage P1 Trusted-Identity Composition on Store Kits

Proves `stageP1_ok_kit` (`entry → entry + 0x868#64`) by composing coroutine frame entry,
`stageP1_load_ok_kit`, and `stageP1_trust_ok_kit`, threading `FsAt` via `kit.Quiet`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem bind_sepWPp_exists_frame {α : Type} {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : α → SepProp}
    {Q_regs : α → State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ a : α, Q_regs a sm ∧ (P_m ⊢ P_stage_post a))
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (a : α) (sm : State), Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs a sm →
      SepWPp prog ret sm (P_stage_post a ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, a, hregs, hent⟩ | ⟨hpan, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post a ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext a sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 2800000 in
/-- Kit-generic Full Stage P1 Composition (`entry -> entry + 0x0868`):
composing `p1_seg1_wp` (`entry -> img.base + kit.loadShimOff`), `stageP1_load_ok_kit`
(`img.base + kit.loadShimOff -> img.base + ikit.trustShimOff`), and `stageP1_trust_ok_kit`
(`img.base + ikit.trustShimOff -> entry + 0x0868`). -/
theorem stageP1_ok_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hA : AllocHooks A abs)
    (hkit : SessionOnlyKitOkS kit Scope C encRecord ctl abs)
    (hikit : IdentityStoreKitOkI img ikit C ctl abs)
    (hstack_lt : stageP1CallStack kit ikit ≤ 2 ^ 64)
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
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s0)
    (hpc : s0.pc =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64) s0
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
              ikit.identityAt idStorePtr (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
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
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg1_wp
    img.base C ctl abs s0 outPtr coroPtr ctxPtr
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
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit (ikit := ikit)
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
    hx19_6, hx21_6, hx26_6, hx27_6, hx29_6, hx30_6, hF6, hsym6⟩
  have hinv6 : ImgCallInv img s6 := ⟨hF6, hsym6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have htrust := stageP1_trust_ok_kit
    peer remoteIdKey hA hikit htrust_le haddr_id htrust_true s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_4f2
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
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
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f, hFf, hsymf⟩
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
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hsp_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f,
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f,
    by rw [hx29_f, hx29_6, hx29_1], hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
