/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: Post-Loop Required-Field Presence Checks (`+0x460..+0x5b4`)

Defines the 96-byte stack spill layout `seg1SpillsAtW` and the presence-check exit states
(`PresenceOkState` at `+0x5b4`, `BkNoneTailState` at `+0x5e0`, `IkNoneTailState` at `+0x61c`,
`MsgNoneTailState` at `+0x66c`, `SpkNoneTailState` at `+0x678`), and proves the presence
checks for `base_key`, `identity_key`, `message`, and `signed_pre_key_id`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (memRegion96_seg1_unpack post_memRegion48_split8)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (words5At words5At_entails_memRegion)
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.call_noPanic_tryFromX := @Wire.SepWPp.call_noPanic_tryFrom

open Lean Meta Elab Tactic in
local elab "pksm_fetches " b:term:max H:term:max hfn:ident
    k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat
    (← `(ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
    "pksm_fetches"
  let offLit := Syntax.mkNumLit (toString off)
  evalTactic (← `(tactic|
    responder_wire_fetches_from $b $H $hfn $offLit $k0 $len))

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_W5aPresence : True := trivial

/-! ## 1. Spills and Frozen Exit States (`section W5aExits`) -/

/-- Stack spill layout at `sp' + 16 .. sp' + 112` (96 bytes) after `+0x574`. -/
def seg1SpillsAtW (sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
  ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
  ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
  ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
  ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
  ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)

section W5aExits

/-- Common register/machine state across the presence checks (`+0x57c .. +0x5b4`) and
presence-failure exits (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`). -/
def PresenceErrTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = x24 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Exit state at `+0x5e0` (`1504`) when `m.baseKey = none`. -/
abbrev BkNoneTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64)
    (spkTag : BitVec 32) (vb : BitVec 8) (sf : State) : Prop :=
  PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
    (spkTag.zeroExtend 64) vb sf

/-- Memory layout at `+0x5e0` (`1504`) when `m.baseKey = none`
(only `sp' + 96 = msgPtr`, `sp' + 104 = ikPtr`, and `[sp' + 312] = 0x8000000000000002` have been
written before the branch at `+0x550`). -/
def BkNoneTailMem (A : RustAlloc)
    (sp' kyberCap kyberPtr kyberLen bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) : SepProp :=
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
  vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
  optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
  vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
  vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
  vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
  ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
  ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
  ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
  ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)

/-- Exit state at `+0x61c` (`1564`) when `m.identityKey = none` (`x23 = noneCap`). -/
abbrev IkNoneTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr msgCap x24 : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr noneCap msgCap x24 vb sf

/-- Exit state at `+0x66c` (`1644`) when `m.message = none` (`x26 = noneCap`). -/
abbrev MsgNoneTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap x24 : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap noneCap x24 vb sf

/-- Exit state at `+0x678` (`1656`) when `m.signedPreKeyId = none` (`x24 = 0#64`). -/
abbrev SpkNoneTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap 0#64 vb sf

/-- Frozen Ok state at `+0x5b4` (`1460`) when
all 4 required fields (`baseKey`, `identityKey`, `message`, `signedPreKeyId`) are `some`. -/
abbrev PresenceOkState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap 1#64 vb sf

end W5aExits

/-! ## 2. Separation-Logic Helpers for -/

theorem vecU8Buf_cap_lt_len (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ Wire.vecU8Buf A cap ptr bs := by
  dsimp only [Wire.vecU8Buf]; refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h, emp_sepConj, emp_sepConj]; exact Entails.refl _

/-- For any `optVecU8Buf A cap ptr len opt`, the dead niche check `cap + 2 != 0` at `+0x4e8` holds. -/
theorem optVecU8Buf_cap_add2_ne (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢
      ⌜(cap + 2#64 != 0#64) = true⌝ ∗ optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    dsimp only [optVecU8Buf]; refine Entails.pure_left_only fun hcap => ?_
    have hne : (cap + 2#64 != 0#64) = true := by subst hcap; decide
    rw [pure_true_emp hne, emp_sepConj, pure_true_emp hcap]; exact Entails.refl _
  | some bs =>
    dsimp only [optVecU8Buf]; refine Entails.pure_left fun hlen => ?_
    refine Entails.trans (vecU8Buf_cap_lt_len A cap ptr bs) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
    have hne : (cap + 2#64 != 0#64) = true := cap_add2_ne_of_lt hlt
    rw [pure_true_emp hne, emp_sepConj, pure_true_emp hlen, emp_sepConj]; exact Entails.refl _

/-- Bridge `Wire.vecU8Buf` to upstream `Wire.deallocSlot` via `optVecU8Buf_entails_deallocSlot`,
recording `cap ≠ noneCap` for the `cbz` dealloc checks in `ErrTailB`. -/
theorem vecU8Buf_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans (vecU8Buf_cap_lt_len A cap ptr bs) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  refine Entails.trans ?_ (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

theorem post_headers_entails_memRegion80W (sp' ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64)
    (regTag regVal opkT opkV spkTag spkVal kpkTag kpkVal : BitVec 32) :
    vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗ vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
    ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ∗
    ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
    ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ⊢
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 := by
  have h1 := vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr ikLen
  have h2 := vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen
  have h3 : ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ⊢ memRegion (sp' + 408#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 408#64) regTag regVal
  have h4 : ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ⊢ memRegion (sp' + 416#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 416#64) opkT opkV
  have h5 : ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ⊢ memRegion (sp' + 424#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 424#64) spkTag spkVal
  have h6 : ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ⊢ memRegion (sp' + 432#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 432#64) kpkTag kpkVal
  rw [show (72 : Nat) = 24 + (24 + (8 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 360#64) 24 48 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64) 24 24 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64 + 24#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64 + 24#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q := memRegion (sp' + 360#64) 24 ∗ memRegion (sp' + 384#64) 24 ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗ memRegion (sp' + 424#64) 8 ∗
      memRegion (sp' + 432#64) 8) ?_ (by apply entails_of_eq; ac_rfl)
  rw [← sepConj_assoc ((sp' + 408#64) ↦₃₂ regTag), ← sepConj_assoc ((sp' + 416#64) ↦₃₂ opkT),
      ← sepConj_assoc ((sp' + 424#64) ↦₃₂ spkTag)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))

/-! ## 3. (`+0x460 .. +0x5b4`): Presence Checks of `baseKey`, `identityKey`, `message`, `signedPreKeyId` -/

/-- Presence check (`m.baseKey = none`): from loop exit `+0x460` (`1120`) with `x24 = 0`, branches at `+0x550`
to the error-tail entry `+0x5e0` (`1504`) in `BkNoneTailState` with `BkNoneTailMem`. -/
theorem post_bk_none_to_5e0_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitState img s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64) s
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal))
      (fun sf Pf =>
        BkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ BkNoneTailMem A sp' kyberCap kyberPtr kyberLen bkPtr bkLen
          ikCap ikPtr ikLen msgCap msgPtr msgLen
          regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hF, hsym, htr⟩
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1120 24
  pksm_fetches img.base H hfn 1256 8
  pksm_fetches img.base H hfn 1316 48
  clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (optVecU8Buf_cap_add2_ne A kyberCap kyberPtr kyberLen kyberOpt))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hky_ne => ?_
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    by simp [h29, arm64_norm], by simp [arm64_norm], by simp [h27, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [h22, arm64_norm], by simp [h21, arm64_norm], by simp [h20, arm64_norm],
    by simp [h19, arm64_norm]⟩, ?_⟩
  dsimp only [BkNoneTailMem, vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-- Presence check (`m.baseKey = some bk`): from loop exit `+0x460` (`1120`) with `x24 = 0`, spills fields
to `sp' + 16..112` (`seg1SpillsAtW`) and executes `drop_in_place<SignalProtocolError>` #1,
reaching `+0x57c` (`1404`). -/
theorem post_bk_some_to_57c_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDropSpe : DropSpeOkX img A ext) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk : List (BitVec 8)}
    (hst : PreKeyLoopExitState img s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
          (spkTag.zeroExtend 64) vb sf ∧
        bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧
        (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
            regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hF, hsym, htr⟩
  have hcallSpe := dropSpe_ok_at_prekeyX hDropSpe; clear hDropSpe
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1120 24
  pksm_fetches img.base H hfn 1256 8
  pksm_fetches img.base H hfn 1316 88
  clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallSpe hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp')
      (sepConj_mono_right (sepConj_mono (optVecU8Buf_cap_add2_ne A kyberCap kyberPtr kyberLen kyberOpt)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_lt_len A bkCap bkPtr bk)))))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w16 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w24 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w32 => SepWPp.exists_pre fun w40 =>
    SepWPp.exists_pre fun w48 => SepWPp.exists_pre fun w52 =>
    SepWPp.exists_pre fun w56 => SepWPp.exists_pre fun w68 =>
    SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
    SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
    SepWPp.exists_pre fun w104 => ?_
  refine SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
        ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hky_ne => SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := fnEntry + bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr kyberLen bkCap bkPtr (BitVec.ofNat 64 bk.length)
  have hhdr80 := post_headers_entails_memRegion80W sp' ikCap ikPtr ikLen msgCap msgPtr msgLen
    regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (P' := (speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗
      stackAt s.sp Getters.dropSpeStackX) ∗
      (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
          (Prost.skipFieldStackX 100 - Getters.dropSpeStackX)))
    (by
      rw [hspe, hstackSpe, hsp_eq]; dsimp only [seg1SpillsAtW]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length)) ∗
        (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool ∗ stackAt sp' Getters.dropSpeStackX ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
            (Prost.skipFieldStackX 100 - Getters.dropSpeStackX)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) (by apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.call_noPanic_tryFromX (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := fnEntry + bv% (1404)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
        regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
      optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗
      memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_cs, h29, arm64_norm], by simp [hx28_cs, arm64_norm],
    by simp [hx27_cs, h27, arm64_norm], by simp [hx26_cs, arm64_norm],
    by simp [hx25_cs, arm64_norm], by simp [hx24_cs, arm64_norm],
    by simp [hx23_cs, arm64_norm], by simp [hx22_cs, h22, arm64_norm],
    by simp [hx21_cs, h21, arm64_norm], by simp [hx20_cs, h20, arm64_norm],
    by simp [hx19_cs, h19, arm64_norm]⟩, hbk_le, hbk_lt, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-- Presence check (`m.identityKey = none`): from `+0x57c` (`1404`) with `x23 = noneCap`, branches at `+0x584`
to the error-tail entry `+0x61c` (`1564`) in `IkNoneTailState`. -/
theorem post_ik_none_to_61c_wpW {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : IkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        IkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1404 12; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

/-- Presence check (`m.identityKey = some ik`): from `+0x57c` (`1404`) with `ikCap.toNat < 2 ^ 63`,
executes `drop_in_place<SignalProtocolError>` #2, reaching `+0x590` (`1424`). -/
theorem post_ik_some_to_590_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDropSpe : DropSpeOkX img A ext) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := dropSpe_ok_at_prekeyX hDropSpe; clear hDropSpe
  have hik_eq := cap_add1_eq_of_lt hik_lt
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1404 20; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallSpe hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    SepWPp.of_sepWP_frozen hF hsym
      (mid := fnEntry + bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := fnEntry + bv% (1424)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-- Presence check (`m.message = none`): from `+0x590` (`1424`) with `x26 = noneCap`, branches at `+0x598`
to the error-tail entry `+0x66c` (`1644`) in `MsgNoneTailState`. -/
theorem post_msg_none_to_66c_wpW {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : MsgNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        MsgNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1424 12; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

/-- Presence check (`m.message = some msg`): from `+0x590` (`1424`) with `msgCap.toNat < 2 ^ 63`,
executes `drop_in_place<SignalProtocolError>` #3, reaching `+0x5a4` (`1444`). -/
theorem post_msg_some_to_5a4_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDropSpe : DropSpeOkX img A ext) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64)
    (hrun : s.status = .Running) (hmsg_lt : msgCap.toNat < 2 ^ 63) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1444#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := dropSpe_ok_at_prekeyX hDropSpe; clear hDropSpe
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1424 20; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallSpe hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    SepWPp.of_sepWP_frozen hF hsym
      (mid := fnEntry + bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := fnEntry + bv% (1444)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-- Presence check (`m.signedPreKeyId = none`, `x24 = 0`): from `+0x5a4` (`1444`), branches at `+0x5a8`
to the error-tail entry `+0x678` (`1656`) in `SpkNoneTailState`. -/
theorem post_spk_none_to_678_wpW {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : SpkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        SpkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1444 8; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

/-- Presence check (`m.signedPreKeyId = some spkId`, `x24 = 1`): from `+0x5a4` (`1444`),
executes `drop_in_place<SignalProtocolError>` #4, reaching `+0x5b4` (`1460`) in
`PresenceOkState`. -/
theorem post_spk_some_to_5b4_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDropSpe : DropSpeOkX img A ext) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := dropSpe_ok_at_prekeyX hDropSpe; clear hDropSpe
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1444 16; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallSpe hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = fnEntry
  examples_hide_fetches
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    SepWPp.of_sepWP_frozen hF hsym
      (mid := fnEntry + bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := fnEntry + bv% (1460)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-- Composed Presence check (`+0x460 → +0x5b4`, dec `1120 → 1460`) when all 4 required fields
are `some` (`m.baseKey = some bk`, `m.identityKey = some ik`, `m.message = some msg`,
`m.signedPreKeyId = some spkId`): reaches `+0x5b4` (`1460`)
in `PresenceOkState`. -/
theorem post_seg1_xok_to_5b4_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDropSpe : DropSpeOkX img A ext) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {vb : BitVec 8} {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk ik msg : List (BitVec 8)}
    (hst : PreKeyLoopExitState img s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        bkCap.toNat < 2 ^ 63 ∧ ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧
        (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
            ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
            regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (vecU8Buf_cap_lt_len A ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_lt_len A msgCap msgPtr msg)))))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜ik.length ≤ ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0⌝ ∗
      ⌜msg.length ≤ msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0⌝ ∗
      ((memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun ⟨_, hik_lt, _⟩ => SepWPp.pure_pre fun ⟨_, hmsg_lt, _⟩ => ?_
  let tailF := seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
      ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
      regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg
  refine SepWPp.bind (Qm := fun s1 P1 =>
      PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s1 ∧
      bkCap.toNat < 2 ^ 63 ∧
      (P1 ⊢ (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
            ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
            regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        (Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg)))
    (SepWPp.frame_tryFrom (post_bk_some_to_57c_wpW hDropSpe hst hpc hrun hx24)
      fun s1 P1 ⟨hst1, _, hbk_lt, hent1⟩ =>
        ⟨by simpa [PresenceOkState, PresenceErrTailState] using hst1, hbk_lt, sepConj_mono_left hent1⟩) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hbk_lt, hent1⟩
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF)
    (Entails.trans hent1 (by dsimp only [tailF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.bind (Qm := fun s2 P2 =>
      PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s2 ∧
      (P2 ⊢ (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF))
    (SepWPp.frame_tryFrom (post_ik_some_to_590_wpW hDropSpe hst1 hpc1 hrun1 hik_lt)
      fun s2 P2 ⟨hst2, hent2⟩ => ⟨hst2, sepConj_mono_left hent2⟩) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, hent2⟩
  refine SepWPp.mono_pre hent2 ?_
  refine SepWPp.bind (Qm := fun s3 P3 =>
      PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
      (P3 ⊢ (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF))
    (SepWPp.frame_tryFrom (post_msg_some_to_5a4_wpW hDropSpe hst2 hpc2 hrun2 hmsg_lt)
      fun s3 P3 ⟨hst3, hent3⟩ => ⟨hst3, sepConj_mono_left hent3⟩) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, hent3⟩
  refine SepWPp.mono_pre hent3 ?_
  refine SepWPp.frame_tryFrom (post_spk_some_to_5b4_wpW hDropSpe hst3 hpc3 hrun3)
    fun sf Pf ⟨hst4, hent4⟩ => ⟨hst4, hbk_lt, hik_lt, hmsg_lt, ?_⟩
  refine Entails.trans (sepConj_mono_left hent4) ?_
  dsimp only [tailF]; apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
