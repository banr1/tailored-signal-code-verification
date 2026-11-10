/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsg
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Pack

/-!
# `PreKeySignalMessage::try_from`: `+0x8c0` `Ok` Packing, Deallocation, and Epilogue (`PreKey8c0OkW`)

Proves `preKey8c0OkW_proof` (`+0x8c0 → +0x970 → +0x504 → ret`) by chaining
`preKey_pack_8c0_to_970_dealloc_res_wpX`, `deallocChain_970_wpX`, `epilogue_504_wpX`,
and `w8bPack_okPost`.
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

/-! ## 1. Pure & Region Helpers -/

/-- `identRegId` of the `registration_id` cells is `m.registrationId.getD 0`. -/
theorem w8bPack_regId {opt : Option (BitVec 32)} {regTag regVal : BitVec 32}
    (h : w8bOptU32Cells opt (regTag, regVal)) :
    identRegId regTag regVal = opt.getD 0#32 := by
  cases opt with
  | none => cases (h : regTag = 0#32); rfl
  | some v => obtain ⟨h1, h2⟩ := (h : regTag = 1#32 ∧ regVal = v); subst h1; subst h2; rfl

/-- The `pre_key_id` cells give Pack's `hopkTag` and `hopkVal`. -/
theorem w8bPack_opk {opt : Option (BitVec 32)} {opkTag opkVal : BitVec 32}
    (h : w8bOptU32Cells opt (opkTag, opkVal)) :
    (opkTag = if opt.isSome then 1#32 else 0#32) ∧ (∀ v, opt = some v → opkVal = v) := by
  cases opt with
  | none => exact ⟨by rw [show opkTag = 0#32 from h]; rfl, fun _ hv => nomatch hv⟩
  | some v =>
    obtain ⟨h1, h2⟩ := (h : opkTag = 1#32 ∧ opkVal = v)
    exact ⟨by rw [show opkTag = 1#32 from h1]; rfl, fun _ hv => by cases hv; exact h2⟩

/-- Unpacks a 32-byte vector into four 64-bit words using kernel-checked `pointsTo64_eq_bytes8`. -/
theorem w8b_exists_words4_of_vector32 (v : List.Vector (BitVec 8) 32) :
    ∃ ik0 ik1 ik2 ik3 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ v.toList) =
        (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
    b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8,
    b23 ++ b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16,
    b31 ++ b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24,
    fun a => ?_⟩
  change (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) = _
  rw [ReceiveRatchetFrom.pointsTo64_eq_bytes8 a b0 b1 b2 b3 b4 b5 b6 b7,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 8#64) b8 b9 b10 b11 b12 b13 b14 b15,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 16#64) b16 b17 b18 b19 b20 b21 b22 b23,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 24#64) b24 b25 b26 b27 b28 b29 b30 b31]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- 7-way split of `memRegion sp' 296` for epilogue refolding. -/
theorem w8b_memRegion296_full_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 12 ∗
      memRegion (sp' + 12#64) 4 ∗
      memRegion (sp' + 16#64) 96 ∗
      memRegion (sp' + 112#64) 32 ∗
      memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 176#64) 112 ∗
      memRegion (sp' + 288#64) 8 := by
  rw [show (296 : Nat) = 12 + (4 + (96 + (32 + (32 + (112 + 8))))) by decide,
    Prost.memRegion_split sp' 12 284 (by decide),
    Prost.memRegion_split (sp' + 12#64) 4 280 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64) 96 184 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64) 32 152 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64) 32 120 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64 + 32#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Packs the 96-byte spill region `sp' + 16 .. 112` into `memRegion (sp' + 16) 96`. -/
theorem w8b_spills96_entails_memRegion (sp' : BitVec 64)
    (w16 w20 w24 w28 w48 w52 w56 w60 w68 : BitVec 32)
    (w32 w40 w72 w80 w88 w96 w104 : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
    ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
    ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
    ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
    ((sp' + 56#64) ↦₃₂ w56) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
    memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
    ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
    ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
    ((sp' + 104#64) ↦₆₄ w104) ⊢
      memRegion (sp' + 16#64) 96 := by
  rw [show (96 : Nat) =
      4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 +
        (4 + (4 + (4 + (4 + (8 + (8 + (8 + (8 + 8)))))))))))))))
      by decide,
    Prost.memRegion_split (sp' + 16#64) 4 92 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 52 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 48 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 44 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 40 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64) 8 32 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono (pointsTo32_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (pointsTo64_entails_memRegion _ _))))))))))))))))

/-! ## 2. The Untouched Residue -/

/-- The part of `w8bRowSPost ∗ w8bRowSFrame` at `+0x8c0` that `Pack` does not read or
write: passed as Pack's `frame`, refolded for the epilogue. -/
def w8bPackJunk (img : Obj.Image) (s0 : State) (sp' ptr : BitVec 64)
    (regTag regVal : BitVec 32) (ik msg bytes : List (BitVec 8)) (kyberLen : BitVec 64) :
    SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗ spUnused112 sp' ∗
    logOff img ∗
    memRegion sp' 12 ∗ memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 312#64) 120 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
    (ptr ↦ₛ bytes)

/-! ## 3. Regrouping -/

theorem w8bPack_open3 {φ1 φ2 φ3 : Prop} {P1 P2 P3 : Bool → SepProp} {F Q : SepProp}
    (h : ∀ a1 a2 a3 : Bool, φ1 → φ2 → φ3 → (P1 a1 ∗ P2 a2 ∗ P3 a3 ∗ F ⊢ Q)) :
    (⌜φ1⌝ ∗ ∃∗ a1 : Bool, P1 a1) ∗ (⌜φ2⌝ ∗ ∃∗ a2 : Bool, P2 a2) ∗
      (⌜φ3⌝ ∗ ∃∗ a3 : Bool, P3 a3) ∗ F ⊢ Q := by
  refine Entails.trans (Entails.of_eq (Q := ⌜φ1⌝ ∗ ⌜φ2⌝ ∗ ⌜φ3⌝ ∗ (∃∗ a1 : Bool, P1 a1) ∗
    (∃∗ a2 : Bool, P2 a2) ∗ (∃∗ a3 : Bool, P3 a3) ∗ F) (by ac_rfl)) ?_
  refine Entails.pure_left fun h1 => ?_
  refine Entails.pure_left fun h2 => ?_
  refine Entails.pure_left fun h3 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun a3 => ?_
  refine Entails.sepExists_elim fun a2 => ?_
  refine Entails.sepExists_elim fun a1 => ?_
  exact h a1 a2 a3 h1 h2 h3

/-- `+0x8c0` state → Pack's pre (`R_heap := emp`, `frame := w8bPackJunk`,
`stackSz := Prost.skipFieldStackX 100`), with the three `Vec<u8>` slots opened to `deallocSlot`s. -/
theorem w8bPack_pre_open (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen
      serBoxPtr : BitVec 64)
    (regTag regVal opkTag opkVal sid kpkVal regId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8) (body : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey)
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (hb : bytes = vb :: body)
    (hreg : identRegId regTag regVal = regId)
    (hipk : ∀ a : BitVec 64, (a ↦ₛ ipk.bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) :
    w8bRowSPost A sp' serBoxPtr bytes innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ∗
      w8bRowSFrame img A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal sid kpkVal
        b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk ⊢
    ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      (((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
          emp)) ∗
        (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          w8bPackJunk img s0 sp' ptr regTag regVal ik msg bytes kyberLen)) := by
  subst hb hreg
  unfold w8bRowSPost w8bRowSFrame w8bRowSRest w8bPackJunk
  rw [hipk (sp' + 144#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hik := Entails.trans (slice_rest_to_vecU8Buf A ikCap ikPtr ik)
    (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
  have hbk := vecU8Buf_entails_deallocSlot A bkCap bkPtr bk
  have hmsg := vecU8Buf_entails_deallocSlot A msgCap msgPtr msg
  refine Entails.trans (Q := ((ikPtr ↦ₛ ik) ∗ vecU8Rest A ikCap ikPtr ik) ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ _)
    (by sep_frame) ?_
  refine Entails.trans (sepConj_mono hik (sepConj_mono hbk (sepConj_mono_left hmsg))) ?_
  refine w8bPack_open3 fun ikAct bkAct msgAct hik_ne hbk_ne hmsg_ne => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  rw [pure_sepConj_of_true (φ := msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap)
    ⟨hmsg_ne, hik_ne, hbk_ne⟩, sepConj_emp]
  apply entails_of_eq; ac_rfl

/-- After `deallocChain_970_wpX`: its `ErrTailQ` frame, plus the Pack residue (`Q_res`, the spill
cells, `memRegion (sp' + 176) 112`, `w8bPackJunk`), regroups to `epilogue_504_wpX`'s pre. -/
theorem w8bPack_epi_regroup (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (ptr bkCap bkPtr msgPtr ikPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal sid kpkVal regId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 ik0 ik1 ik2 ik3 : BitVec 64) (ik msg bytes : List (BitVec 8))
    (Q_res : SepProp) :
    (((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikPtr) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100) ∗
        (Q_res ∗
          ((s0.sp - 608#64 + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((s0.sp - 608#64 + 16#64) ↦₃₂ kpkVal) ∗
          ((s0.sp - 608#64 + 20#64) ↦₃₂ opkTag) ∗
          ((s0.sp - 608#64 + 24#64) ↦₃₂ opkVal) ∗
          ((s0.sp - 608#64 + 28#64) ↦₃₂ sid) ∗
          ((s0.sp - 608#64 + 56#64) ↦₃₂ regId) ∗
          ((s0.sp - 608#64 + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((s0.sp - 608#64 + 72#64) ↦₆₄ w15) ∗
          ((s0.sp - 608#64 + 112#64) ↦₆₄ w23) ∗ ((s0.sp - 608#64 + 120#64) ↦₈ b31) ∗
          ((s0.sp - 608#64 + 128#64) ↦₃₂ w9) ∗ ((s0.sp - 608#64 + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (s0.sp - 608#64 + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((s0.sp - 608#64 + 144#64) ↦₆₄ ik0) ∗ ((s0.sp - 608#64 + 152#64) ↦₆₄ ik1) ∗
          ((s0.sp - 608#64 + 160#64) ↦₆₄ ik2) ∗ ((s0.sp - 608#64 + 168#64) ↦₆₄ ik3) ∗
          memRegion (s0.sp - 608#64 + 176#64) 112 ∗
          w8bPackJunk img s0 (s0.sp - 608#64) ptr regTag regVal ik msg bytes kyberLen)) ⊢
      stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        Q_res ∗ (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  generalize s0.sp - 608#64 = sp'
  unfold w8bPackJunk
  have hm12 := pointsTo32_entails_memRegion (sp' + 12#64) (b7.zeroExtend 32)
  have hm96 := w8b_spills96_entails_memRegion sp' kpkVal opkTag opkVal sid regTag regVal regId
    (BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) (b8.zeroExtend 32)
    (BitVec.ofNat 64 msg.length) kyberLen w15 bkPtr bkCap msgPtr ikPtr
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  have hm144 :
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ⊢
        memRegion (sp' + 144#64) 32 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words4_entails_memRegion32 (sp' + 144#64) ik0 ik1 ik2 ik3
  have h152 : memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 120 ∗
        memRegion (sp' + 432#64) 8 ∗ memRegion (sp' + 440#64) 8 := by
    rw [show (152 : Nat) = 16 + (120 + (8 + 8)) by decide,
      Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64) 120 16 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64 + 120#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [stackAt_sub_split sp' (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide),
    w8b_memRegion296_full_split sp', h152]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono hm12 (sepConj_mono hm96
        (sepConj_mono hm112 (sepConj_mono_left hm144)))))))
  simp only [sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-! ## 4. Post -/

/-- The Ok epilogue post (`sp`, callee-saved, trace, `RunCompose.pksmResAt`) meets
`(pksmTryFromSpec A img).post` (Ok twin of `W8bAssembly.w8b_errPost`). -/
theorem w8bPack_okPost {img : Obj.Image} {A : RustAlloc} {x : RunCompose.PksmGhost} {s0 sf : State}
    {Pf : SepProp}
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      sf.trace = s0.trace ∧
      (Pf ⊢ RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf) := by
  obtain ⟨hsp, hcs, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpec, Spec.inImage]
  rw [pure_sepConj_of_true htr]
  apply entails_of_eq; ac_rfl

/-! ## 5. `+0x8c0` `Ok` Continuation -/

/-- the `+0x8c0` (`2240`) Ok edge returns with `(pksmTryFromSpec A img).post`. -/
theorem preKey8c0OkW_proof {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext) :
    PreKey8c0OkW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId _pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal _kpkTag kpkVal kyberBoxPtr kyberBoxLen
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1
    verHi56 clonePtr hx hge3 hle4 _hlen hdec hbk hik hmsg hsid hreg hopk _hkpk hpkD _hkyb hpkB
    hikD hinner hrk hst _hbkCap _hikCap _hmsgCap hpc hrun
  have hvlt := vb.isLt
  simp only [BitVec.lt_def, vb_lsr4_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    at hge3 hle4
  have hlo : 0x30 ≤ vb.toNat := by omega
  have hhi : vb.toNat ≤ 0x4f := by omega
  have hbk_ok : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hpkD
  have hpkb1 : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hbk_ok
  have hik_ok : ecKeyParses ik = true := ecKeyParses_of_deserialize_ok hikD
  have hikpk : pkOf ik = ipk := pkOf_of_deserialize_ok hikD
  obtain ⟨ik0, ik1, ik2, ik3, hipk⟩ := w8b_exists_words4_of_vector32 ipk.bytes
  have hikw : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3) := by
    rw [hikpk]; exact hipk
  obtain ⟨hopkTag, hopkVal⟩ := w8bPack_opk hopk
  have hregId := w8bPack_regId hreg
  have hBridge := sret_cells_entails_pksmResAt A x.ret vb (b1 :: bs1) m bk ik msg spkId innerMsg
    msgG clonePtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3
    opkTag opkVal kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 emp hlo hhi hdec hbk hik
    hmsg hsid hbk_ok hik_ok hinner hopkTag hopkVal (hpkb1.trans hpkB) hrk hikw
  rw [hx] at hst
  refine SepWPp.mono_pre
    (w8bPack_pre_open img A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr
      msgCap msgPtr kyberBoxPtr kyberBoxLen clonePtr regTag regVal opkTag opkVal spkId kpkVal
      (m.registrationId.getD 0#32) p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb (b1 :: bs1)
      m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes ipk innerMsg msgG rk0 rk1 rk2 rk3
      addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3 hx hregId hipk) ?_
  refine SepWPp.exists_pre fun msgAct => SepWPp.exists_pre fun ikAct =>
    SepWPp.exists_pre fun bkAct => ?_
  refine SepWPp.bind
    (preKey_pack_8c0_to_970_dealloc_res_wpX (msgAct := msgAct) (ikAct := ikAct) (bkAct := bkAct)
      (R_heap := emp) hopkTag hBridge hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  refine SepWPp.mono_pre hent1 ?_
  refine SepWPp.bind (deallocChain_970_wpX hC msgAct ikAct bkAct hst1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _, hent2⟩
  refine SepWPp.mono_post
    (SepWPp.mono_pre
      (Entails.trans hent2
        (w8bPack_epi_regroup img A s0 x.ptr bkCap bkPtr msgPtr ikPtr kyberLen regTag
          regVal opkTag opkVal spkId kpkVal (m.registrationId.getD 0#32)
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 ik0 ik1 ik2 ik3
          ik msg x.bytes
          (RunCompose.pksmResAt A x.ret (Pksm.pksmParse (vb :: b1 :: bs1)))))
      (epilogue_504_wpX (A := A) (x := x)
        (R := RunCompose.pksmResAt A x.ret (Pksm.pksmParse (vb :: b1 :: bs1)))
        hst2 hpc2 hrun2)) ?_
  intro sf' Pf _ _ hq
  obtain ⟨hsp, hcs, htr, hent⟩ := hq
  rw [← hx] at hent
  exact w8bPack_okPost ⟨hsp, hcs, htr, hent⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
