/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6ExitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` `IdentityKey::try_from` Stage (`+0x830 → +0x864 / +0x978`)

Proves `preKey_ident_ok_830_to_864_placed_wpX` and `preKey_ident_err_830_to_978_placed_wpE` on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev ikw_SepWPp := @Wire.SepWPp
private abbrev ikw_done := @Wire.SepWP.done
private abbrev ikw_pure_pre := @Wire.SepWPp.pure_pre
private abbrev ikw_exists_pre := @Wire.SepWPp.exists_pre
private abbrev ikw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev ikw_of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev ikw_call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem ikw_identRegId_tst (regTag : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) =
      (regTag &&& 1#32 == 0#32) := by
  apply congrArg (· == 0#32)
  bv_bits

private theorem ikw_identRegId_csel (regTag regVal : BitVec 32) :
    (if ¬(BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) = true then
        BitVec.truncate 64 regVal else 0#64) = (identRegId regTag regVal).zeroExtend 64 := by
  rw [ikw_identRegId_tst]
  unfold identRegId
  by_cases h : regTag &&& 1#32 = 0#32 <;> simp [h]

private theorem ikw_words3_to_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion24_words3 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

private theorem ikw_errWords5_memRegion8_entails_speAt (A : RustAlloc) (fn : List (BitVec 8))
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : PublicKey.deserialize ik = .error e)
    (sp' w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
      memRegion (sp' + 352#64) 8 ⊢
      speAt A fn (sp' + 312#64) e := by
  have hm24 := ikw_words3_to_memRegion24 (sp' + 328#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hm32 :
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8 ⊢
      memRegion (sp' + 328#64) 32 := by
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (sp' + 328#64) 24 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact sepConj_mono_left (by simpa only [sepConj_assoc] using hm24)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    ikErrWords_entails_speAt hik A fn (sp' + 312#64)

/-- (``+0x830 → +0x864`, `2096 → 2148`, `[LibsignalPlacement]``): from `KyberOkStatePlaced`
at `+0x830`, loads the `identity_key` slice (`ptr @ sp' + 104`, `len @ sp' + 56`), computes
`w27 = registration_id.unwrap_or_default()`, calls `IdentityKey::try_from` into `sp' + 312`,
copies the 32 key bytes to `sp' + 144`, and (`PublicKey.deserialize ik = .ok ipk`) falls through
`b.ne +0x978` to `IdentOkStatePlaced` at `+0x864`. -/
theorem preKey_ident_ok_830_to_864_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {vb : BitVec 8} {regTag regVal : BitVec 32}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik : PublicKey.deserialize ik = .ok ipk) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    ikw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2148#64) s
      (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        lsLogOff ∗ stackAt sp' S)
      (fun sf Pf =>
        IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          (identRegId regTag regVal) bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
          ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
          memRegion (sp' + 352#64) 8 ∗
          lsLogOff ∗ stackAt sp' S))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallIk := hC.identityKeyOk
  clear hC
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  refine ikw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsmpl.base 116) ?_
  wp_steps
  refine ikw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ikw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ik, ipk, sp' + 312#64) hcallIk
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp [arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize ik = .ok ipk)
    (by simp [identityKeyTryFromSliceOkPlacedSpec, hsp_eq, arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [identityKeyTryFromSliceOkPlacedSpec]
  rw [sepConj_assoc]
  refine ikw_pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  obtain ⟨ik0, ik1, ik2, ik3, -, hipk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ipk.bytes)
  rw [memRegion32_words4 (sp' + 144#64), hipk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine ikw_exists_pre fun _ => ikw_exists_pre fun _ =>
    ikw_exists_pre fun _ => ikw_exists_pre fun _ => ?_
  refine ikw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine ikw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
  have h27_2 : s2.readReg64 .x27 = (identRegId regTag regVal).zeroExtend 64 := by
    rw [← ikw_identRegId_csel]
    simp [hx27_2, arm64_norm]
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik,
    by simp [h29_2, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [h27_2, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [h24_2, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  rw [← hsp2, hsp2_eq, hipk (sp' + 144#64), hipk (sp' + 320#64), hstackIk]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl

/-- (``+0x830 → +0x978`, `2096 → 2424`, `[LibsignalPlacement]``): `PublicKey.deserialize ik = .error e` writes `(ikErrWords e)` at `sp' + 312`, loads
`x8 := (ikErrWords e).1`, copies `sp' + 320 .. 352` into `sp' + 144 .. 176`, and takes
`b.ne +0x978` into `IdentErrStatePlaced`, keeping exact `speAt A fn (sp' + 312#64) e` at the callee
result slot together with `sf.readReg64 .x8` and the hoisted word `(ikErrWords e).2` at `sp' + 144`. -/
theorem preKey_ident_err_830_to_978_placed_wpE [LibsignalPlacement]
    (A : RustAlloc) (fn : List (BitVec 8))
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {regTag regVal : BitVec 32}
    {ik : List (BitVec 8)} {e : SignalProtocolError} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hik : PublicKey.deserialize ik = .error e) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx19 : s.readReg64 .x19 = sret) :
    ikw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2424#64) s
      (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        lsLogOff ∗ stackAt sp' S)
      (fun sf Pf =>
        IdentErrStatePlaced s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
        sf.readReg64 .x8 = (ikErrWords e).1 ∧
        (Pf ⊢ ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
          speAt A fn (sp' + 312#64) e ∗
          lsLogOff ∗ stackAt sp' S))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallIk := hC.identityKeyWordsErr
  clear hC
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  refine ikw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsmpl.base 116) ?_
  wp_steps
  refine ikw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ikw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ik, e, sp' + 312#64) hcallIk
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp [arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize ik = .error e)
    (by simp [identityKeyTryFromSliceWordsErrPlacedSpec, hsp_eq, arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [identityKeyTryFromSliceWordsErrPlacedSpec]
  rw [sepConj_assoc]
  refine ikw_pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [memRegion24_words3 (sp' + 328#64), memRegion32_words4 (sp' + 144#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine ikw_exists_pre fun _ => ikw_exists_pre fun _ =>
    ikw_exists_pre fun _ => ikw_exists_pre fun _ =>
    ikw_exists_pre fun w4 => ikw_exists_pre fun w3 => ikw_exists_pre fun w2 => ?_
  have hne : ((ikErrWords e).1 + 2#64 != 0#64) = true := by
    rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩ <;>
      (dsimp only [ikErrWords, speWord]; decide)
  refine ikw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine ikw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [h29_2, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx19_2, hx19, arm64_norm]⟩,
    by simp [arm64_norm], ?_⟩
  rw [← hsp2, hsp2_eq]
  have hm24 := ikw_words3_to_memRegion24 (sp' + 152#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hspe := ikw_errWords5_memRegion8_entails_speAt A fn hik sp' w2 w3 w4
  refine Entails.trans
    (Q := ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
      ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗
      (((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
      (((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
        ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8) ∗
      lsLogOff ∗ (memRegion (sp' - BitVec.ofNat 64 S) (S - 96) ∗ stackAt sp' 96))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hstackIk]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm24 (sepConj_mono_left hspe)))))))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
