/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome

/-!
# `PreKeySignalMessage::try_from`: `base_key` Deserialization (`+0x5b4 → +0x684` / `+0x7a8`)

Defines the exit states `BaseKeyOkState` (`+0x684`) and `DeserErrTailState` /
`DeserErrTailStateE` (`+0x7a8`), and proves the `PublicKey::deserialize` `Ok` and `Err`
branches (`+0x5b4..+0x5dc`, `+0x700..+0x714`, `+0x790..+0x7a8`) together with the
deallocation-slot bridge to `+0x7a8`.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

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

theorem L1_PksmWire_W5aBaseKey : True := trivial

/-! ## 1. Callee Wrapper and Frozen Exit States (`BaseKeyOkState`, `DeserErrTailState`, `DeserErrTailStateE`) -/

/-- `PublicKey::deserialize` at `preKeyTryFromName + (ls_off% deserializeName - ls_off% preKeyTryFromName)`
(`+0x5bc` call target) on `contractProg img.base ext` via `deserializeFull_ok_at_contractProg`. -/
theorem deserializeFull_ok_at_prekeyX {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% deserializeName - ls_off% preKeyTryFromName))
      ((deserializeFullSpec img.base).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (deserializeFull_ok_at_contractProg (b := img.base) (ext := ext)
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (k := num% (ls_off% deserializeName - ls_off% preKeyTryFromName)) (by decide))

/-- Frozen Ok exit state at `+0x684` (`1668`) when `PublicKey.deserialize bk = .ok pk`:
includes `ecKeyParses bk = true`, `pkOf bk = pk`, and
`(pkOf bk).bytes.toList = (bk.take 33).drop 1`. -/
def BaseKeyOkState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (bk : List (BitVec 8)) (pk : PublicKey) (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

section W5aExits

/-- Exit state at `+0x7a8` (`1960`) when
`PublicKey.deserialize bk = .error e`. -/
def DeserErrTailState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Exact-`SignalProtocolError` exit state at `+0x7a8` (`1960`), pinning
`speWordsOf e (sf.readReg64 .x9) (sf.readReg64 .x8) (sf.readReg64 .x10)` verbatim for
`ErrTailB.entry_7a8_wpE`. -/
def DeserErrTailStateE (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (e : SignalProtocolError) (sf : State) : Prop :=
  DeserErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
  speWordsOf e (sf.readReg64 .x9) (sf.readReg64 .x8) (sf.readReg64 .x10)

end W5aExits

/-! ## 2. (`+0x5b4 .. +0x5dc`, `+0x700 .. +0x714`, `+0x790 .. +0x7a8`): `PublicKey::deserialize(baseKey)` -/

/-- `PublicKey::deserialize(base_key)` call (`+0x5b4 .. +0x5c0`, dec `1460 .. 1472`): calls `PublicKey::deserialize`
on `bk` via `deserializeFull_ok_at_prekeyX`, producing
`deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15`. -/
theorem post_deser_bk_call_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (bk : List (BitVec 8))
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1472#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img)
      (fun sf Pf =>
        PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallDeser := deserializeFull_ok_at_prekeyX (img := img) (ext := ext)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Buf_entails_slice_rest A bkCap bkPtr bk))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre (P' :=
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ (bkPtr ↦ₛ bk) ∗ vecU8BufRest A bkCap bkPtr bk ∗ logOff img))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_len_lt : bk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbk_le hbk_lt
  have hbk_toNat : (BitVec.ofNat 64 bk.length).toNat = bk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let H := Rust.withPanics ext
  have hfn :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1460 12; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallDeser hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% deserializeName - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have h48_split := post_memRegion48_split33_15 sp'
  have hlog := logOff_eq img
  refine SepWPp.call_noPanic_tryFromX (bkPtr, bk, sp' + 312#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 1472#64) (by simp [arm64_norm])
    (T := (bkPtr ↦ₛ bk) ∗ memRegion (sp' + 312#64) 33 ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
    (φ := bkPtr = bkPtr ∧ (BitVec.ofNat 64 bk.length).toNat = bk.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ bk.length < 2 ^ 63 ∧ (img.base &&& 0xfff#64) = 0#64)
    (by simp [deserializeFullSpec, arm64_norm]) ⟨rfl, hbk_toNat, rfl, hbk_len_lt, hb⟩
    (by rw [h48_split, hlog]; sep_focus) ?_
  clear hcallDeser
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [deserializeFullSpec]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A bkCap bkPtr bk
  rw [← hlog]
  refine Entails.trans (Q :=
      ((bkPtr ↦ₛ bk) ∗ vecU8BufRest A bkCap bkPtr bk) ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
        memRegion (sp' + 345#64) 15 ∗ logOff img))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Entails.trans (sepConj_mono_left hrepack) (by apply entails_of_eq; ac_rfl)

/-- `PublicKey::deserialize(base_key)` `Ok` branch (`+0x5c0 .. +0x5c4 → +0x684`, dec `1472 .. 1476 → 1668`):
when `PublicKey.deserialize bk = .ok pk`, branches to `+0x684` (`1668`) in
`BaseKeyOkState`:
`((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗ memRegion (sp' + 345#64) 15`
(and `(pkOf bk).bytes.toList = (bk.take 33).drop 1` under `ecKeyParses bk = true`). -/
theorem post_deser_bk_ok_to_684_wpW {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64) s
      (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hec : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hdeser
  have hpkOf : pkOf bk = pk := pkOf_of_deserialize_ok hdeser
  have hbytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hec
  have hpk_bytes : pk.bytes.toList = (bk.take 33).drop 1 := by rw [← hpkOf, hbytes]
  rw [hdeser]; dsimp only [deserializeResult33At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  let H := Rust.withPanics ext
  have hfn :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1472 8; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩, hec, hpkOf, hbytes,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, ?_⟩
  rw [hpk_bytes]; exact Entails.refl _

/-- `PublicKey::deserialize(base_key)` `Err` branch (`+0x5c0 .. +0x5dc`, `+0x700 .. +0x714`, `+0x790 .. +0x7a4 → +0x7a8`,
dec `1472 .. 1500`, `1792 .. 1812`, `1936 .. 1956 → 1960`):
when `PublicKey.deserialize bk = .error e`, steps all three error kinds (`noKeyTypeIdentifier`,
`badKeyType t`, `badKeyLength n`) to the error-tail entry `+0x7a8` (`1960`) in
`DeserErrTailStateE` (preserving `speWordsOf e`). -/
theorem post_deser_bk_err_to_7a8_wpE {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        DeserErrTailStateE img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  rw [herr]
  let H := Rust.withPanics ext
  have hfn :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1472 32
  pksm_fetches img.base H hfn 1792 24
  pksm_fetches img.base H hfn 1936 16
  clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_end hF hsym ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_base (sp' + 312#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | badKeyType t =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_end hF hsym ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyType (sp' + 312#64) t
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | badKeyLength n =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_end hF hsym ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]; bv_bits⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyLength (sp' + 312#64) n
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | _ =>
    dsimp only [deserializeResult33At]
    exact SepWPp.pure_pre fun hfalse => False.elim hfalse

/-- Weakened `DeserErrTailState` corollary of `post_deser_bk_err_to_7a8_wpE`. -/
theorem post_deser_bk_err_to_7a8_wpW {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        DeserErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15))
      (tryFromQp s0) := by
  intro R hm hL
  rcases post_deser_bk_err_to_7a8_wpE herr hst hpc hrun R hm hL with
    ⟨sf, hs, ⟨hpc', hrun', Pf, hmf, ⟨⟨hdst, _⟩, hent⟩, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc', hrun', Pf, hmf, ⟨hdst, hent⟩, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

/-- Composed `base_key` `Ok` step (`+0x5b4 → +0x684`, dec `1460 → 1668`) from `PresenceOkState` when
`PublicKey.deserialize bk = .ok pk`: reaches `+0x684` (`1668`) in
`BaseKeyOkState`. -/
theorem post_deser_bk_ok_full_to_684_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img)
      (fun sf Pf =>
        BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img))
      (tryFromQp s0) := by
  refine SepWPp.bind (post_deser_bk_call_wpW hb bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img
  refine SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_ok_to_684_wpW hdeser hst1 hpc1 hrun1)
    fun sf Pf ⟨hbst, hent2⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; ac_rfl

/-- Composed `base_key` `Err` step (`+0x5b4 → +0x7a8`, dec `1460 → 1960`) from `PresenceOkState` when
`PublicKey.deserialize bk = .error e`: reaches `+0x7a8` (`1960`) in `DeserErrTailStateE`. -/
theorem post_deser_bk_err_full_to_7a8_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img)
      (fun sf Pf =>
        DeserErrTailStateE img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img))
      (tryFromQp s0) := by
  refine SepWPp.bind (post_deser_bk_call_wpW hb bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img
  refine SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_err_to_7a8_wpE herr hst1 hpc1 hrun1)
    fun sf Pf ⟨hdst, hent2⟩ => ⟨hdst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; ac_rfl

/-- Weakened `DeserErrTailState` corollary of `post_deser_bk_err_full_to_7a8_wpE`. -/
theorem post_deser_bk_err_full_to_7a8_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img)
      (fun sf Pf =>
        DeserErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img))
      (tryFromQp s0) := by
  intro R hm hL
  rcases post_deser_bk_err_full_to_7a8_wpE hb herr hst hpc hrun R hm hL with
    ⟨sf, hs, ⟨hpc', hrun', Pf, hmf, ⟨⟨hdst, _⟩, hent⟩, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc', hrun', Pf, hmf, ⟨hdst, hent⟩, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

/-! ## 3. Dealloc-Slot Bridge (`*_wpE` / `*_wpW`), Join Frame -/

section D12JoinFrames

private theorem w5a_vec_ne_noneCap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ⌜cap ≠ noneCap⌝ ∗ Wire.vecU8Buf A cap ptr bs := by
  refine Entails.trans (vecU8Buf_entails_slice_rest A cap ptr bs)
    (Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  exact slice_rest_entails_vecU8Buf A cap ptr bs

private theorem w5a_vec_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans ?_
    (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

private theorem w5a_vec_ne_and_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active :=
  Entails.trans (w5a_vec_ne_noneCap A cap ptr bs)
    (sepConj_mono_right (w5a_vec_entails_deallocSlot A cap ptr bs))

/-- Dealloc-slot bridge (`+0x5b4 → +0x7a8`, dec `1460 → 1960`)**: steps
`post_deser_bk_err_full_to_7a8_wpE` and bridges `Wire.vecU8Buf` for `msg`, `ik`, `bk` and
`optVecU8Buf` for `kyberOpt` into `DeserErrTailStateE`, `msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap`,
and the exact consumer pre-shape of `ErrTailB.entry_7a8_wpE` (`memRegion sret 248 ∗ ...`). -/
theorem post_deser_bk_err_dealloc_to_7a8_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen
      bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {vb : BitVec 8}
    {bk ik msg : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
        (memRegion sret 248 ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        DeserErrTailStateE img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (∃ x8v x9v x10v : BitVec 64,
          sf.readReg64 .x8 = x8v ∧ sf.readReg64 .x9 = x9v ∧ sf.readReg64 .x10 = x10v ∧
          speWordsOf e x9v x8v x10v) ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          memRegion sret 248 ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ logOff img))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_vec_ne_noneCap A bkCap bkPtr bk)))))
      (sepConj_mono_right
        (sepConj_mono (w5a_vec_ne_and_deallocSlot A msgCap msgPtr msg)
          (sepConj_mono_right (sepConj_mono_left (w5a_vec_ne_and_deallocSlot A ikCap ikPtr ik)))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
        (memRegion sret 248 ∗
          (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hmsg_ne =>
    SepWPp.pure_pre fun hik_ne =>
    SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_err_full_to_7a8_wpE hb herr hst hpc hrun)
    fun sf Pf ⟨hdstE, hent⟩ =>
      ⟨hdstE, ⟨_, _, _, rfl, rfl, rfl, hdstE.2⟩, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_vec_entails_deallocSlot A bkCap bkPtr bk))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hky)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

/-- Word-level dealloc-slot bridge (`+0x5b4 → +0x7a8`, dec `1460 → 1960`) matching `ErrTailB.entry_7a8_wpX`
with native stack budget `Prost.skipFieldStackX 100` and exact `DeserErrTailStateE`. -/
theorem post_deser_bk_err_dealloc_to_7a8_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64) {s0 s : State}
    {sp' sret len ptr0 w0 w1 w2 kyberCap kyberPtr kyberLen
      bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {vb : BitVec 8}
    {bk ik msg : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64) s
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        DeserErrTailStateE img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (∃ x8v x9v x10v : BitVec 64,
          sf.readReg64 .x8 = x8v ∧ sf.readReg64 .x9 = x9v ∧ sf.readReg64 .x10 = x10v ∧
          speWordsOf e x9v x8v x10v) ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ logOff img))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_vec_ne_noneCap A bkCap bkPtr bk)))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (w5a_vec_ne_and_deallocSlot A msgCap msgPtr msg)
          (sepConj_mono_right (sepConj_mono_left (w5a_vec_ne_and_deallocSlot A ikCap ikPtr ik)))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hmsg_ne =>
    SepWPp.pure_pre fun hik_ne =>
    SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_err_full_to_7a8_wpE hb herr hst hpc hrun)
    fun sf Pf ⟨hdstE, hent⟩ =>
      ⟨hdstE, ⟨_, _, _, rfl, rfl, rfl, hdstE.2⟩, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_vec_entails_deallocSlot A bkCap bkPtr bk))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hky)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

theorem deserErrTailStateE_nonvacuous (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (hst : PostEpilogueState img s0 sp' s0) :
    ∃ sf : State,
      DeserErrTailStateE img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb
        .noKeyTypeIdentifier sf := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  refine ⟨(((((((((((s0.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 1#64).writeReg64 .x23 ikCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret).writeReg64 .x9 (speWord 7), ?_⟩
  refine ⟨⟨⟨by tryFromPost_sp [hsp0], by tryFromPost_sp_align hal,
      by simpa [Obj.Image.FrozenLoaded, arm64_norm] using hF,
      by simp [hsym, arm64_norm], by simp [arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
    by simp [speWordsOf, speWord, arm64_norm]⟩

end D12JoinFrames

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
