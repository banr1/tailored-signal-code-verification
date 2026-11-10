/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEnc
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOk
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMem

/-!
# `segSignal` `OTR::encrypt` Call (`Enc` → `Ret`)

Frames the stack and heap state around `bl OTR::encrypt` in `segSignal` and proves
`segSignal_enc_to_ret_pf` (and `segSignal_enc_to_ret_pf_trap`) returning to `+0x3a4`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.tapeAfter_zero_entails_tapeAt (ctl cur : BitVec 64) (rest : List (BitVec 8))
    (hrest : rest.length < 2 ^ 63) :
    CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 ⊢ CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest := by
  unfold CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2 CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2
  have hcur : cur + BitVec.ofNat 64 0 = cur := BitVec.add_zero cur
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero rest.length
  rw [hcur, hlen]
  exact Entails.pure_right hrest (Entails.refl _)

/-- Frame around `OTR::encrypt` at `segSignal`. -/
private def segSignalEncCallFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (_img : Obj.Image)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
  memRegion x.ret 248 ∗
  protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_pre_unpack {ss_vt id_vt : BitVec 64} {Q : List (BitVec 8) → Prop}
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (img : Obj.Image) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hQ : Q otr.pqrState) (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = sp + 0x580#64) (hx1 : s.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s.readReg64 .x2 = x.ptA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hx4 : s.readReg64 .x4 = 0#64) (hx5 : s.readReg64 .x5 = x.remA)
    (hpt : x.ptext.length < 2 ^ 32) (hrest : x.rest.length < 2 ^ 63)
    (hm : s.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R) :
    ∃ g : RecordGhost,
      s.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img).pre (segSignalEncGhost sp pqCap pqPtr otr x) s ∗
        (segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R) := by
  unfold takenSlots CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  refine ⟨g, ?_⟩
  have htape := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.tapeAfter_zero_entails_tapeAt img.base x.cur x.rest hrest
  have hm_rearr : s.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
      (otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗
        logOff img ∗
        stackAt sp rootStack ∗
        A.pool ∗
        segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R) := by
    unfold segSignalEncCallFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  have hx3_nat : (s.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage segSignalEncGhost optAddrAt
  dsimp only
  rw [hsp, emp_sepConj]
  have hpure :
      (⌜Q otr.pqrState⌝ : SepProp) ∗
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
        s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
        ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
        s.readReg64 .x5 = x.remA⌝ ∗
      (CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        (otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          logOff img ∗
          stackAt sp rootStack ∗
          A.pool ∗
          segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R)) =
      ((⌜Q otr.pqrState⌝ ∗
        (⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
            s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
            x.ptext.length < 2 ^ 32 ∧
            s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
            ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
            s.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
          logOff img ∗
          stackAt sp rootStack ∗
          A.pool)) ∗
        (segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R)) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  refine ⟨hQ, ⟨hfl, hsym⟩,
    ⟨hx0, hx1, hx2, hx3_nat, hpt, hx4, (by intro h; cases h), hx5⟩, hm_tape⟩

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_post_pack {ss_vt id_vt : BitVec 64} {Q : List (BitVec 8) → Prop}
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (img : Obj.Image) (x : WithStoresEncGhost) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s sm : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hpost : sm.mem ⊨
      ((CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img).post (segSignalEncGhost sp pqCap pqPtr otr x) s sm ∗
        segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0) ∗ R) :
    (segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace ∧
    (sm.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ R) := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage at hpost
  dsimp only at hpost
  rw [segSignalEncGhost_model, hsp] at hpost
  unfold segSignalEncGhost optAddrAt at hpost
  dsimp only at hpost
  rw [emp_sepConj] at hpost
  have h1 : sm.mem ⊨ ⌜(segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace⌝ ∗
      (((∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ stackAt sp rootStack ∗ A.pool ∗
        segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨hne, htr, ?_⟩
  unfold segSignalEncCallFrame at hmem
  have hmem_rearr : sm.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
        stackAt sp rootStack) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ encSavedRegs s0.sp s0 ∗ A.pool ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack rootStack] at hmem_rearr
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_rearr

/-- **Enc → Ret** (`bl OTR::encrypt` returns to `+0x3a4`): `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q` on
`segSignalEncGhost sp pqCap pqPtr otr x`, `Q otr.pqrState` from `EncEnv.q_otr`, panic via
`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_panic_bridge`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_to_ret_pf_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName := by
    rw [hs_pc, hentry, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.otrEnc_addr_eq_trap]
  have hQ : Q otr.pqrState := env.q_otr hcur hsc hfrom
  obtain ⟨g, hm_pre⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_pre_unpack C A ctl S img x sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp hQ hfl hsym hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call_trap env.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x)
    hs_pc' hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_panic_bridge hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm hL1 hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have ⟨hflm, hsymm⟩ := Pf.SegFrom.callInv_steps hfl hsym hsteps12 hL1
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal hsm_sp
  have hsm_x19 : sm.readReg64 .x19 = x.ret := (hcsm.1).trans hx19
  have hsm_x20 : sm.readReg64 .x20 = sp + 0x58#64 := (hcsm.2.1).trans hx20
  have hsm_x25 : sm.readReg64 .x25 = sp + 0x580#64 := (hcsm.2.2.2.2.2.2.1).trans hx25
  have hsm_x26 : sm.readReg64 .x26 = sp + 0x9d0#64 := (hcsm.2.2.2.2.2.2.2.1).trans hx26
  have hsm_x28 : sm.readReg64 .x28 = sp + 0x4a0#64 := (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsm_x29 : sm.readReg64 .x29 = s0.sp - 0x60#64 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hsm_vregs : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  obtain ⟨hne, hsm_tr, hm_ret⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_post_pack C A ctl S img x g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next_trap ⟨hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
    ⟨hsm_run, hsm_sp', hal0, hsm_al, hsm_x29, hsm_x19, hflm, hsymm, hsm_vregs⟩,
    hsm_tr.trans htr, hsm_x20, hsm_x25, hsm_x26, hsm_x28,
    hpt, hrest, hloc, hnow, hstk, g, hm_ret⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_to_ret_pf {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName := by
    rw [hs_pc, hentry, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.otrEnc_addr_eq]
  have hQ : Q otr.pqrState := env.q_otr hcur hsc hfrom
  obtain ⟨g, hm_pre⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_pre_unpack C A ctl S img x sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp hQ hfl hsym hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call env.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x)
    hs_pc' hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_panic_bridge hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm hL1 hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have ⟨hflm, hsymm⟩ := Pf.SegFrom.callInv_steps hfl hsym hsteps12 hL1
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal hsm_sp
  have hsm_x19 : sm.readReg64 .x19 = x.ret := (hcsm.1).trans hx19
  have hsm_x20 : sm.readReg64 .x20 = sp + 0x58#64 := (hcsm.2.1).trans hx20
  have hsm_x25 : sm.readReg64 .x25 = sp + 0x580#64 := (hcsm.2.2.2.2.2.2.1).trans hx25
  have hsm_x26 : sm.readReg64 .x26 = sp + 0x9d0#64 := (hcsm.2.2.2.2.2.2.2.1).trans hx26
  have hsm_x28 : sm.readReg64 .x28 = sp + 0x4a0#64 := (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsm_x29 : sm.readReg64 .x29 = s0.sp - 0x60#64 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hsm_vregs : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  obtain ⟨hne, hsm_tr, hm_ret⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_post_pack C A ctl S img x g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next ⟨hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
    ⟨hsm_run, hsm_sp', hal0, hsm_al, hsm_x29, hsm_x19, hflm, hsymm, hsm_vregs⟩,
    hsm_tr.trans htr, hsm_x20, hsm_x25, hsm_x26, hsm_x28,
    hpt, hrest, hloc, hnow, hstk, g, hm_ret⟩

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
