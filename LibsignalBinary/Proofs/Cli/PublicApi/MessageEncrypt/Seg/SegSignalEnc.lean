/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnack
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEnc
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# `segSignal` Argument Setup Before `OTR::encrypt` (`+0x348..+0x3a0`)

Defines `SegSignalEncStateV` at the `OTR::encrypt` entry (`lr = +0x3a4`) and proves
`segSignal_ack_to_enc` (and `segSignal_ack_to_enc_trap`).
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

set_option maxRecDepth 200000

/-- **Enc** (`OTR::encrypt`'s entry, `lr = +0x3a4`, parameterized by session-store kit `kit` and
initial state `st0`): `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc` done. Memory: Ack's slots, the scratch in `cmScratch` form (key / OTR
pointer spills), the 120-byte sret `sp+0x580` free (tag and copied junk forgotten), the junk copy at
`sp+0x870` forgotten. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧ sess.pendingPreKey = none ∧
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) ∧
  s.readReg64 Reg.lr = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x3a4#64 ∧ encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
  s.readReg64 .x2 = x.ptA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length ∧
  s.readReg64 .x4 = 0#64 ∧ s.readReg64 .x5 = x.remA ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
      memRegion (sp + 0x5f8#64) 0x588) ∗
    memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

/-- **Ack → Enc** (`+0x348..+0x3a0`): `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ack_to_enc_trap {A : RustAlloc} {img : Obj.Image}
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
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalAckStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
        R0 s0 s') := by
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx23, hx25, hx26, hx27, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  change s.mem ⊨
    (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) at hm
  unfold curScratch encSpillsAtV at hm
  have hscr : memRegion sp 0x50 =
      memRegion sp 0x38 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
        memRegion (sp + 0x48#64) 8 := by
    rw [segSignal_memRegion_cut sp (sp + 0x38#64) 0x50 0x38 0x18 rfl rfl (by decide),
      segSignal_memRegion_cut (sp + 0x38#64) (sp + 0x40#64) 0x18 8 0x10 (by bv_omega) rfl (by decide),
      segSignal_memRegion_cut (sp + 0x40#64) (sp + 0x48#64) 0x10 8 8 (by bv_omega) rfl (by decide)]
  have h584 : memRegion (sp + 0x584#64) 84 =
      memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗ memRegion (sp + 0x590#64) 8 ∗
        memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗
        memRegion (sp + 0x5a4#64) 8 ∗ memRegion (sp + 0x5ac#64) 8 ∗
        memRegion (sp + 0x5b4#64) 8 ∗ memRegion (sp + 0x5bc#64) 4 ∗
        memRegion (sp + 0x5c0#64) 24 := by
    rw [show (84 : Nat) = 4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + 24)))))))) from rfl,
      show sp + 0x584#64 = sp + BitVec.ofNat 64 0x584 from rfl,
      mr_cut_add sp 0x584 4 _ (by decide),
      mr_cut_add sp (0x584 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  have h5d8 : memRegion (sp + 0x5d8#64) 0x5a8 =
      memRegion (sp + 0x5d8#64) 32 ∗ memRegion (sp + 0x5f8#64) 0x278 ∗
        memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
        memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗
        memRegion (sp + 0x890#64) 4 ∗ memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x5a8 : Nat) = 32 + (0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec)))))) from rfl,
      show sp + 0x5d8#64 = sp + BitVec.ofNat 64 0x5d8 from rfl,
      mr_cut_add sp 0x5d8 32 _ (by decide),
      mr_cut_add sp (0x5d8 + 32) 0x278 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [hscr, h584, h5d8] at hm
  obtain ⟨u38, hm⟩ := segSignal_peel8 (sp + 0x38#64) (by sep_focus) hm
  obtain ⟨u40, hm⟩ := segSignal_peel8 (sp + 0x40#64) (by sep_focus) hm
  obtain ⟨u48, hm⟩ := segSignal_peel8 (sp + 0x48#64) (by sep_focus) hm
  obtain ⟨a0, hm⟩ := segSignal_peel4 (sp + 0x584#64) (by sep_focus) hm
  obtain ⟨a1, hm⟩ := segSignal_peel8 (sp + 0x588#64) (by sep_focus) hm
  obtain ⟨a2, hm⟩ := segSignal_peel8 (sp + 0x590#64) (by sep_focus) hm
  obtain ⟨a3, hm⟩ := segSignal_peel4 (sp + 0x598#64) (by sep_focus) hm
  obtain ⟨c0, hm⟩ := segSignal_peel8 (sp + 0x59c#64) (by sep_focus) hm
  obtain ⟨c1, hm⟩ := segSignal_peel8 (sp + 0x5a4#64) (by sep_focus) hm
  obtain ⟨c2, hm⟩ := segSignal_peel8 (sp + 0x5ac#64) (by sep_focus) hm
  obtain ⟨c3, hm⟩ := segSignal_peel8 (sp + 0x5b4#64) (by sep_focus) hm
  obtain ⟨c4, hm⟩ := segSignal_peel4 (sp + 0x5bc#64) (by sep_focus) hm
  obtain ⟨e0, hm⟩ := segSignal_peel8 (sp + 0x870#64) (by sep_focus) hm
  obtain ⟨e1, hm⟩ := segSignal_peel8 (sp + 0x878#64) (by sep_focus) hm
  obtain ⟨e2, hm⟩ := segSignal_peel8 (sp + 0x880#64) (by sep_focus) hm
  obtain ⟨e3, hm⟩ := segSignal_peel8 (sp + 0x888#64) (by sep_focus) hm
  obtain ⟨e4, hm⟩ := segSignal_peel4 (sp + 0x890#64) (by sep_focus) hm
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64 := by
    rw [hs_pc, hentry]
  have hm4 := segSignal_focusR' (T := ((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗
        ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap hm4 (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc_trap hs_pc' hrun hsp hal hx23 hx25 hx27) ?_
  intro s3 Pm3 hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28,
      hs3_x29, hs3_vregs, hlr, hPm3⟩
  have ⟨hfl3, hsym3⟩ := SegFrom.callInv_steps hfl hsym hsteps hL
  have hs3_al : s3.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hPost := Entails.trans hPm3
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo32_entails_memRegion _ _)))))))))))))))))))))
  have hm7 := Satisfies.mono (sepConj_mono_left hPost) hm5
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next_trap ?_
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV
  refine ⟨hcur, hsc, hfrom, hrem, hnone, by rw [hs3_pc, hentry], by rw [hlr, hentry],
    ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hfl3, hsym3,
      hs3_vregs.trans hvregs⟩,
    hs3_tr.trans htr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x20.trans hx20, hs3_x25.trans hx25,
    hs3_x26.trans hx26, hs3_x28.trans hx28, hpt, hrest, hloc, hnow, hstk, ?_⟩
  rw [← hsp0]
  have h580g : memRegion (sp + 0x580#64) 120 =
      memRegion (sp + 0x580#64) 4 ∗ memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗
        memRegion (sp + 0x590#64) 8 ∗ memRegion (sp + 0x598#64) 4 ∗
        memRegion (sp + 0x59c#64) 8 ∗ memRegion (sp + 0x5a4#64) 8 ∗
        memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗
        memRegion (sp + 0x5bc#64) 4 ∗ memRegion (sp + 0x5c0#64) 24 ∗
        memRegion (sp + 0x5d8#64) 32 := by
    rw [show (120 : Nat) = 4 + (4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + (24 + 32))))))))))
        from rfl,
      show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
      mr_cut_add sp 0x580 4 _ (by decide),
      mr_cut_add sp (0x580 + 4) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 4) 24 _ (by decide)]
  have h5f8g : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x278 ∗ memRegion (sp + 0x870#64) 8 ∗
        memRegion (sp + 0x878#64) 8 ∗ memRegion (sp + 0x880#64) 8 ∗
        memRegion (sp + 0x888#64) 8 ∗ memRegion (sp + 0x890#64) 4 ∗
        memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x588 : Nat) = 0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec))))) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x278 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [h580g, h5f8g]
  unfold cmScratch encSpillsAtV
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ack_to_enc {A : RustAlloc} {img : Obj.Image}
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
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalAckStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
        R0 s0 s') := by
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx23, hx25, hx26, hx27, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  change s.mem ⊨
    (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) at hm
  unfold curScratch encSpillsAtV at hm
  have hscr : memRegion sp 0x50 =
      memRegion sp 0x38 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
        memRegion (sp + 0x48#64) 8 := by
    rw [segSignal_memRegion_cut sp (sp + 0x38#64) 0x50 0x38 0x18 rfl rfl (by decide),
      segSignal_memRegion_cut (sp + 0x38#64) (sp + 0x40#64) 0x18 8 0x10 (by bv_omega) rfl (by decide),
      segSignal_memRegion_cut (sp + 0x40#64) (sp + 0x48#64) 0x10 8 8 (by bv_omega) rfl (by decide)]
  have h584 : memRegion (sp + 0x584#64) 84 =
      memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗ memRegion (sp + 0x590#64) 8 ∗
        memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗
        memRegion (sp + 0x5a4#64) 8 ∗ memRegion (sp + 0x5ac#64) 8 ∗
        memRegion (sp + 0x5b4#64) 8 ∗ memRegion (sp + 0x5bc#64) 4 ∗
        memRegion (sp + 0x5c0#64) 24 := by
    rw [show (84 : Nat) = 4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + 24)))))))) from rfl,
      show sp + 0x584#64 = sp + BitVec.ofNat 64 0x584 from rfl,
      mr_cut_add sp 0x584 4 _ (by decide),
      mr_cut_add sp (0x584 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  have h5d8 : memRegion (sp + 0x5d8#64) 0x5a8 =
      memRegion (sp + 0x5d8#64) 32 ∗ memRegion (sp + 0x5f8#64) 0x278 ∗
        memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
        memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗
        memRegion (sp + 0x890#64) 4 ∗ memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x5a8 : Nat) = 32 + (0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec)))))) from rfl,
      show sp + 0x5d8#64 = sp + BitVec.ofNat 64 0x5d8 from rfl,
      mr_cut_add sp 0x5d8 32 _ (by decide),
      mr_cut_add sp (0x5d8 + 32) 0x278 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [hscr, h584, h5d8] at hm
  obtain ⟨u38, hm⟩ := segSignal_peel8 (sp + 0x38#64) (by sep_focus) hm
  obtain ⟨u40, hm⟩ := segSignal_peel8 (sp + 0x40#64) (by sep_focus) hm
  obtain ⟨u48, hm⟩ := segSignal_peel8 (sp + 0x48#64) (by sep_focus) hm
  obtain ⟨a0, hm⟩ := segSignal_peel4 (sp + 0x584#64) (by sep_focus) hm
  obtain ⟨a1, hm⟩ := segSignal_peel8 (sp + 0x588#64) (by sep_focus) hm
  obtain ⟨a2, hm⟩ := segSignal_peel8 (sp + 0x590#64) (by sep_focus) hm
  obtain ⟨a3, hm⟩ := segSignal_peel4 (sp + 0x598#64) (by sep_focus) hm
  obtain ⟨c0, hm⟩ := segSignal_peel8 (sp + 0x59c#64) (by sep_focus) hm
  obtain ⟨c1, hm⟩ := segSignal_peel8 (sp + 0x5a4#64) (by sep_focus) hm
  obtain ⟨c2, hm⟩ := segSignal_peel8 (sp + 0x5ac#64) (by sep_focus) hm
  obtain ⟨c3, hm⟩ := segSignal_peel8 (sp + 0x5b4#64) (by sep_focus) hm
  obtain ⟨c4, hm⟩ := segSignal_peel4 (sp + 0x5bc#64) (by sep_focus) hm
  obtain ⟨e0, hm⟩ := segSignal_peel8 (sp + 0x870#64) (by sep_focus) hm
  obtain ⟨e1, hm⟩ := segSignal_peel8 (sp + 0x878#64) (by sep_focus) hm
  obtain ⟨e2, hm⟩ := segSignal_peel8 (sp + 0x880#64) (by sep_focus) hm
  obtain ⟨e3, hm⟩ := segSignal_peel8 (sp + 0x888#64) (by sep_focus) hm
  obtain ⟨e4, hm⟩ := segSignal_peel4 (sp + 0x890#64) (by sep_focus) hm
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64 := by
    rw [hs_pc, hentry]
  have hm4 := segSignal_focusR' (T := ((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗
        ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP hm4 (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc hs_pc' hrun hsp hal hx23 hx25 hx27) ?_
  intro s3 Pm3 hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28,
      hs3_x29, hs3_vregs, hlr, hPm3⟩
  have ⟨hfl3, hsym3⟩ := SegFrom.callInv_steps hfl hsym hsteps hL
  have hs3_al : s3.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hPost := Entails.trans hPm3
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo32_entails_memRegion _ _)))))))))))))))))))))
  have hm7 := Satisfies.mono (sepConj_mono_left hPost) hm5
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next ?_
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalEncStateV
  refine ⟨hcur, hsc, hfrom, hrem, hnone, by rw [hs3_pc, hentry], by rw [hlr, hentry],
    ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hfl3, hsym3,
      hs3_vregs.trans hvregs⟩,
    hs3_tr.trans htr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x20.trans hx20, hs3_x25.trans hx25,
    hs3_x26.trans hx26, hs3_x28.trans hx28, hpt, hrest, hloc, hnow, hstk, ?_⟩
  rw [← hsp0]
  have h580g : memRegion (sp + 0x580#64) 120 =
      memRegion (sp + 0x580#64) 4 ∗ memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗
        memRegion (sp + 0x590#64) 8 ∗ memRegion (sp + 0x598#64) 4 ∗
        memRegion (sp + 0x59c#64) 8 ∗ memRegion (sp + 0x5a4#64) 8 ∗
        memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗
        memRegion (sp + 0x5bc#64) 4 ∗ memRegion (sp + 0x5c0#64) 24 ∗
        memRegion (sp + 0x5d8#64) 32 := by
    rw [show (120 : Nat) = 4 + (4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + (24 + 32))))))))))
        from rfl,
      show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
      mr_cut_add sp 0x580 4 _ (by decide),
      mr_cut_add sp (0x580 + 4) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 4) 24 _ (by decide)]
  have h5f8g : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x278 ∗ memRegion (sp + 0x870#64) 8 ∗
        memRegion (sp + 0x878#64) 8 ∗ memRegion (sp + 0x880#64) 8 ∗
        memRegion (sp + 0x888#64) 8 ∗ memRegion (sp + 0x890#64) 4 ∗
        memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x588 : Nat) = 0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec))))) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x278 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [h580g, h5f8g]
  unfold cmScratch encSpillsAtV
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
