/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `[LibsignalPlacement]` `SessionRecord::deserialize` Loop (Block `46`)

Verifies relocatable `.base` framing (`mergeFieldQPlacedOkW_base`), loop entry
(`deserLoopEntryQ_placed_okW`), loop iteration (`deserLoopIterQ_placed_okW`), loop exit
(`deserLoopExitQ_placed_ok_of_memcpy`), and full loop assembly (`deserializeExactQPlacedW_ok`,
`deserializeBodyQPlacedW_ok`, `recordDeserializeOpen_placed_of_exactQ`) on `lsProg_46 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord CanonSession allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Hooks2.DeserLoopEntryGExt
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

section Placed

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_succ_sub_one_loopIter

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopWP (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopWP (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopWP (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopWP (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopWP (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopWP (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopWP (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopWP (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local simp, local arm64_norm]
private theorem int64_toBitVec_mk_loopWP (u : UInt64) : ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl
@[local simp, local arm64_norm]
private theorem uint64_toBitVec_mk_loopWP (v : BitVec 64) : ({ toBitVec := v } : UInt64).toBitVec = v := rfl
@[local simp, local arm64_norm]
private theorem bitVec_toFin_mk_64_loopWP (n : Nat) (h : n < 18446744073709551616 := by decide) :
    ({ toFin := ⟨n, h⟩ } : BitVec 64) = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm

theorem L1_B3DeserQ_LoopW_Placed : True := trivial

/-! ## Relocatable `.base` framing -/

/-- Any `MergeFieldGenPlacedOkW H P` (tags 1..9) lifts directly to
`MergeFieldQPlacedOkW H (fun fl => ∃ f, P f ∧ fl = .base f)`. -/
theorem mergeFieldQPlacedOkW_base [LibsignalPlacement] (H : LibsignalHooks)
    {P : GenField → Prop} (hBase : MergeFieldGenPlacedOkW H P) :
    MergeFieldQPlacedOkW H (fun fl => ∃ f, P f ∧ fl = .base f) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcrl, hpre'⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  simp only [mergeFieldQRawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, ⟨f, hPf, hfl⟩, hok, hfresh, hlen⟩, hmem⟩
  rcases x with ⟨ss, ⟨vbase, vext⟩, fld, bufSlot, curSlot, p, rest⟩
  dsimp only at hfl hx0 hx1 hx2 hx3 hx4 hok hfresh hlen hmem
  subst hfl
  rcases hfresh with ⟨hvext, hfresh_f⟩
  dsimp only at hvext hfresh_f
  subst hvext
  let xG : MergeFieldGenGhost := ⟨ss, vbase, f, bufSlot, curSlot, p, rest⟩
  have hpreG : s0.mem ⊨ (mergeFieldGenPlacedSpecW P).pre xG s0 ∗ R := by
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [mergeFieldGenRawSpecW, xG, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hPf, hok, hfresh_f, hlen⟩, ?_⟩
    rw [← prostSSGQAt_empty A0 ss vbase]
    exact hmem
  refine hBase.mono_outcome xG R s0 hpc hrun hpreG hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [mergeFieldGenPlacedSpecW, mergeFieldQPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    simp only [mergeFieldGenRawSpecW, mergeFieldQRawSpecW, xG, SSGQ.apply] at hpost ⊢
    rw [prostSSGQAt_empty A0 ss (vbase.apply f)]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

/-! ## Relocatable loop entry -/

/-- Relocatable `SessionRecord::deserialize` loop entry (`+0x000` → `+0x254`, `k = 0`) on
`lsProg_46 H` for `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem deserLoopEntryQ_placed_okW [LibsignalPlacement] (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeQPlacedSpecW.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepQPlacedW H x R s0 s0 (DeserLoopQPlacedW x R s0 0) := by
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [deserializeQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx8, hr⟩, hm0⟩
  rw [sepConj_assoc, sepConj_assoc] at hm0
  have heq := encodeRecord_eq_recFieldsQ x.r hr
  have hlt : (encodeRecord x.r).length < 2 ^ 62 :=
    Nat.lt_trans (encodeRecord_length_ltQ hr) (by decide)
  intro hL0
  obtain ⟨s', hst, hout⟩ :=
    deserLoopEntry_raw_placed_ok H hC.1 x.p x.out (encodeRecord x.r)
      ((recFieldsQ x.r).flatMap GenFieldQ.enc) R s0 hpc hrun hx0 hx1 hx8 hal hcrl0 heq hlt hm0 hL0
  refine ⟨s', hst, ?_⟩
  rcases hout with hok | hpan
  · refine Or.inl ?_
    have hss0 : ssgqAfter x.r 0 = ⟨SSG.empty, ExtraGQ.empty⟩ := rfl
    simpa only [DeserLoopQPlacedW, List.drop_zero, hss0, deserLocalsQ_base] using hok
  · exact Or.inr hpan

/-! ## Relocatable loop iteration -/

private def keyByte_diterQP (fl : GenFieldQ) : BitVec 8 :=
  BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)

private theorem enc_eq_keyByte_cons_diterQP (fl : GenFieldQ) :
    fl.enc = keyByte_diterQP fl :: fl.payload := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem drop_flatMap_enc_diterQP {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r).drop k).flatMap GenFieldQ.enc =
      (recFieldsQ r)[k].enc ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

private theorem ssgqAfter_succ_diterQP {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    ssgqAfter r (k + 1) = (ssgqAfter r k).apply (recFieldsQ r)[k] := by
  simp only [ssgqAfter, List.take_succ_eq_append_getElem hk,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

private def preBytes_diterQP (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++
    ((recFieldsQ r).take k).flatMap GenFieldQ.enc

private def curPtr_diterQP (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) :
    BitVec 64 :=
  p + BitVec.ofNat 64 (preBytes_diterQP r k).length

private theorem encodeRecord_eq_preBytes_append_diterQP {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    encodeRecord r = preBytes_diterQP r k ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
  have hs : (recFieldsQ r).flatMap GenFieldQ.enc =
      ((recFieldsQ r).take k).flatMap GenFieldQ.enc ++
        ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFieldsQ r hr, preBytes_diterQP,
    List.append_assoc, List.append_assoc, ← hs, ← List.append_assoc]

private theorem rem_length_lt_diterQP {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length < 2 ^ 33 := by
  have h1 := encodeRecord_length_ltQ hr
  rw [encodeRecord_eq_preBytes_append_diterQP hr k, List.length_append] at h1
  omega

private theorem payload_rest_length_lt_diterQP {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length < 2 ^ 33 := by
  have h := rem_length_lt_diterQP hr k
  rw [drop_flatMap_enc_diterQP hk, enc_eq_keyByte_cons_diterQP, List.cons_append, List.length_cons] at h
  omega

private theorem encodeRecord_sub_rem_length_diterQP {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (encodeRecord r).length - (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length =
      (preBytes_diterQP r k).length := by
  rw [encodeRecord_eq_preBytes_append_diterQP hr k, List.length_append]
  omega

private theorem sliceCursorAfter_split_key_diterQP (L p : BitVec 64)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
        (((recFieldsQ r).drop k).flatMap GenFieldQ.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_diterQP p r k) ∗
        ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64
          (((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length + 1)) ∗
        (curPtr_diterQP p r k ↦₈ keyByte_diterQP (recFieldsQ r)[k]) ∗
        ((curPtr_diterQP p r k + 1#64) ↦ₛ
          ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) ∗
        (p ↦ₛ preBytes_diterQP r k) := by
  unfold Prost.sliceCursorAfter
  have hsub := encodeRecord_sub_rem_length_diterQP hr k
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc =
      keyByte_diterQP (recFieldsQ r)[k] ::
        ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
    rw [drop_flatMap_enc_diterQP hk, enc_eq_keyByte_cons_diterQP, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_diterQP r k) ∗
        (curPtr_diterQP p r k ↦₈ keyByte_diterQP (recFieldsQ r)[k]) ∗
        ((curPtr_diterQP p r k + 1#64) ↦ₛ
          ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_diterQP hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_diterQP, pointsToBytes_cons]
  rw [hsub, ← curPtr_diterQP, show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega,
    hbs_split, hrem, List.length_cons]
  ac_rfl

private theorem sliceCursorAfter_unsplit_key_diterQP (L p : BitVec 64)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_diterQP p r k + 1#64)
        ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)
        (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) ∗
      (curPtr_diterQP p r k ↦₈ keyByte_diterQP (recFieldsQ r)[k]) ∗
      (p ↦ₛ preBytes_diterQP r k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
  let fl := (recFieldsQ r)[k]
  let rest := ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_diterQP fl :: (fl.payload ++ rest) := by
    rw [drop_flatMap_enc_diterQP hk, enc_eq_keyByte_cons_diterQP, List.cons_append]
  have hbs_eq : encodeRecord r = preBytes_diterQP r k ++ (keyByte_diterQP fl :: (fl.payload ++ rest)) := by
    rw [encodeRecord_eq_preBytes_append_diterQP hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by
    rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length =
      (preBytes_diterQP r k).length + 1 + fl.payload.length := by
    rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_diterQP p r k + 1#64 + BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) =
      p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_diterQP, BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_diterQP r k) ∗ (curPtr_diterQP p r k ↦₈ keyByte_diterQP fl) ∗
        ((curPtr_diterQP p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_diterQP, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter
  rw [hptr, hbs_pts]
  ac_rfl

private theorem deserLocalsQ_decomp_diterQP (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) :
    deserLocalsQ L p bs rest v =
      Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
        prostSSGQAt A0 (L + 0x420#64) v ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        deserFixed_loopIter L := by
  unfold deserLocalsQ deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1
  generalize memRegion (L + 0x578#64) 0x170 = m2
  generalize memRegion (L + 0x6f0#64) 0x20 = m3
  ac_rfl

private theorem keyByte_diterQP_bounds (fl : GenFieldQ) :
    (keyByte_diterQP fl).toNat < 128 ∧
    0 < (keyByte_diterQP fl).toNat / 8 ∧
    (keyByte_diterQP fl).toNat % 8 < 6 ∧
    (keyByte_diterQP fl).toNat / 8 = fl.tag ∧
    (keyByte_diterQP fl).toNat % 8 = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp [keyByte_diterQP, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt, WireType.toNat]

/-- Relocatable `SessionRecord::deserialize` one-field loop iteration (`k → k + 1`) on `lsProg_46 H`
for `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem deserLoopIterQ_placed_okW [LibsignalPlacement] (H : LibsignalHooks)
    (hMF : MergeFieldQPlacedOkW H (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (hk : k < (recFieldsQ x.r).length) (hs : DeserLoopQPlacedW x R s0 k s) :
    DeserStepQPlacedW H x R s0 s (fun s' => DeserLoopQPlacedW x R s0 (k + 1) s') := by
  obtain ⟨hpc, hrun, htr, hcrl, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFieldsQ x.r)[k]
  let rest := ((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_diterQP x.p x.r k
  have hpc_entry : s.pc = (blkPl_46).base + 596#64 := hpc
  have hn_lt33 : payRest.length < 2 ^ 33 := payload_rest_length_lt_diterQP hr hk
  have hn_lt62 : payRest.length < 2 ^ 62 := Nat.lt_trans hn_lt33 (by decide)
  obtain ⟨hkb_lt, htag_pos, hwt_lt, hkb_tag, hkb_wt⟩ := keyByte_diterQP_bounds fl
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_diterQP x.r k) ∗
      prostSSGQAt A0 (L + 0x420#64) (ssgqAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_diterQP fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsQ L x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsQ_decomp_diterQP, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_diterQP L x.p hr hk,
      stackAt_deserCallee_split_loopIterW L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_254_to_2e8_placed_loopIter_kb L curPtr (keyByte_diterQP fl) payRest.length s
      (post := fun sm Pm =>
        sm.pc = lsmpl.base 15 ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (blkPl_46).base + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 ((keyByte_diterQP fl).toNat / 8) ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 ((keyByte_diterQP fl).toNat % 8) ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_diterQP fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hkb_lt htag_pos hwt_lt hn_lt62
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  rw [hkb_tag] at hx1m
  rw [hkb_wt] at hx2m
  have hcrl_m : LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hLm : (lsProg_46 H).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 15)
      (mergeFieldQPlacedSpecW (fun _ => True)) :=
    ls_call_ro_of_block (callerProg := lsProg_46 H) hMF
  let g : MergeFieldQGhost :=
    ⟨L + 0x420#64, ssgqAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_diterQP fl) ∗
      (x.p ↦ₛ preBytes_diterQP x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFieldsQ_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgqAfter x.r k) := recFieldsQ_fresh x.r hr k hk
  have hpre_mf : sm.mem ⊨ (mergeFieldQPlacedSpecW (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl_m, ?_⟩
    dsimp only [mergeFieldQRawSpecW, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hn_lt62⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (lsProg_46 H).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2ec_placed_loopIter s2
        (P := prostSSGQAt A0 (L + 0x420#64) ((ssgqAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStackX)
        (post := fun sf P_f =>
          sf.pc = (blkPl_46).base + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGQAt A0 (L + 0x420#64) ((ssgqAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStackX))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (lsProg_46 H) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf,
      ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)),
       htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩,
      hcrl.of_keepsFrozen hsteps_all.keepsFrozen,
      hsp_sf, hal_sf,
      hx29f.trans (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29m),
      hx19f.trans (hcs2.1.trans (hx19m.trans hx19)),
      hx20f.trans (hcs2.2.1.trans hx20m),
      hx23f.trans (hcs2.2.2.2.2.1.trans hx23m), ?_⟩
    change sf.mem ⊨ deserLocalsQ L x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc) (ssgqAfter x.r (k + 1)) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [deserLocalsQ_decomp_diterQP, deserOutRegion_eq_loopIter,
      ssgqAfter_succ_diterQP hk, ← sliceCursorAfter_unsplit_key_diterQP L x.p hr hk,
      stackAt_deserCallee_split_loopIterW L, ← sep_perm3_loopIter]
    rw [hspm_L] at hmf
    exact hmf
  · refine ⟨s2, hsteps1.trans hsteps2, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW, deserializeQPlacedSpecW, deserializeQRawSpecW, allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr.1] at ha
    rw [htrm.1, htr.1] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim

/-! ## Relocatable loop exit -/

@[local arm64_norm]
private theorem int64_raw_toBitVec_dexitQP (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm

private theorem w0_add_one_ne_zero_dexitQP {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    w0 + 1#64 ≠ 0#64 := by unfold noneCap at h; bv_omega
private theorem w0_add_one_beq_zero_dexitQP {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    (w0 + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; exact w0_add_one_ne_zero_dexitQP h

private def deserSavedAtL_dexitQP (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSaved_eq_atL_dexitQP (s0 : State) :
    deserSaved s0 = deserSavedAtL_dexitQP (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_dexitQP deserSpL
  rw [show s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 by bv_omega]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem sliceCursorAfter_nil_dexitQP (L p : BitVec 64) (bs : List (BitVec 8)) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs [] =
      ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold Prost.sliceCursorAfter
  rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, List.length_nil, Nat.sub_zero]

private theorem memRegion_3f8_split_dexitQP (L : BitVec 64) :
    memRegion L 0x3f8 =
      memRegion L 8 ∗ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 3 * 336) (by decide) rfl (by decide),
    memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 3 * 336) (n := 336) (k := 2 * 336) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 2 * 336) (n := 336) (k := 336) (by decide) (by bv_omega) (by decide)]

private theorem memRegion_out_split_dexitQP (out : BitVec 64) :
    memRegion out 368 = ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
      (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360) (by decide) rfl (by decide),
    memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336) (by decide) (by bv_omega) (by decide),
    ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem satisfies_memRegion_out_split_dexitQP {m : Memory} {out : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64,
      m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗
        ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_out_split_dexitQP out] at h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩
  exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem deserSavedAtL_entails_memRegion_dexitQP (L : BitVec 64) (s0 : State) :
    deserSavedAtL_dexitQP L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_dexitQP
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) :
      memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 =
        memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n)) (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide), join 32 (by decide), join 40 (by decide),
    join 48 (by decide), join 56 (by decide), join 64 (by decide), join 72 (by decide), join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_locals_entails_memRegion_dexitQP (L c0 w0 : BitVec 64) (s0 : State)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
      ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQP L s0 ⊢ memRegion L 0x770 := by
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by
    rw [← hrest]; exact ProofLib.pointsToBytes_entails_memRegion a rest
  refine Entails.trans (sepConj_mono_right (sepConj_mono (hb (L + 8#64)) (sepConj_mono (hb (L + 0x158#64)) (sepConj_mono (hb (L + 0x2a8#64))
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (hb (L + 0x428#64)) (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_right (deserSavedAtL_entails_memRegion_dexitQP L s0))))))))))))))) ?_
  have join (n k : Nat) (h : n + k ≤ 2 ^ 64) :
      memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
    (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
  simp only [← sepConj_assoc]
  rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide), join 1016 8 (by decide), join 1024 8 (by decide),
    join 1032 8 (by decide), join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide), join 1064 336 (by decide),
    join 1400 0x170 (by decide), join 1768 8 (by decide), join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_dexitQP (s0 : State) (c0 w0 : BitVec 64)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗ (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQP L s0) ⊢ stackAt s0.sp recDeserializeStack := by
  intro L
  refine Entails.trans (sepConj_mono_right (dexit_locals_entails_memRegion_dexitQP L c0 w0 s0 rest hrest)) ?_
  unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by
    dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]; bv_omega
  rw [h1, memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L)
    (N := recDeserializeStack) (n := deserCalleeStack) (k := recDeserializeStack - deserCalleeStack) (by decide)
    (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega) (by decide)]
  exact Entails.refl _

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeReg64_dexitQP {pl : Obj.MultiPlacement} (s : State) (r : Reg) (v : BitVec 64) :
    LibsignalCodeLoaded pl (s.writeReg64 r v).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeReg32_dexitQP {pl : Obj.MultiPlacement} (s : State) (r : Reg) (v : BitVec 32) :
    LibsignalCodeLoaded pl (s.writeReg32 r v).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_setPC_dexitQP {pl : Obj.MultiPlacement} (s : State) (pc : BitVec 64) :
    LibsignalCodeLoaded pl (s.setPC pc).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_setPState_dexitQP {pl : Obj.MultiPlacement} (s : State) (ps : PState) :
    LibsignalCodeLoaded pl (s.setPState ps).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeVReg128_dexitQP {pl : Obj.MultiPlacement} (s : State) (idx : BitVec 5) (v : BitVec 128) :
    LibsignalCodeLoaded pl (s.writeVReg128 idx v).mem = LibsignalCodeLoaded pl s.mem := rfl

private theorem of_sepWP_lscl_dexitQP {pl : Obj.MultiPlacement} {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (hcl.of_keepsFrozen hsteps.keepsFrozen)).elim hmm
        (hsteps.codeLoaded hL) with ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

set_option maxHeartbeats 800000 in
private theorem dexit_sepWP_placed_dexitQP [LibsignalPlacement]
    {H : LibsignalHooks}
    (hmc_ok : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)))
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = deserPlacedPC 0x254#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = L)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw0 : w0 ≠ noneCap)
    (hrest : rest.length = 336)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_46 H) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_dexitQP L s0)
      (fun sf P_f =>
        sf.sp = L + 0x770#64 ∧
        sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗
          ((out + 0x20#64) ↦ₛ rest) ∗
          stackAt L deserCalleeStack ∗
          deserSavedAtL_dexitQP L s0)) := by
  subst hsp
  dsimp only [deserPlacedPC] at hpc
  have hw0_ne := w0_add_one_ne_zero_dexitQP hw0
  have hw0_beq := w0_add_one_beq_zero_dexitQP hw0
  unfold deserSavedAtL_dexitQP
  wp_steps
  wp_call hmc_ok (s.sp + 8#64, s.sp + 0x428#64, rest)
  wp_steps
  wp_call hmc_ok (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  wp_steps
  wp_call hmc_ok (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  apply of_sepWP_lscl_dexitQP (mid := lsρ "memcpy") (by assumption)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_c4
  wp_call hmc_ok (out + 0x20#64, s.sp + 0x158#64, rest)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; ac_rfl

/-- Relocatable `SessionRecord::deserialize` loop exit (`k = |recFieldsQ x.r|` → return) on
`lsProg_46 H` from `memcpy` at `deserCalleeStack`. -/
theorem deserLoopExitQ_placed_ok_of_memcpy [LibsignalPlacement] (H : LibsignalHooks)
    (hmc_ok : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (hs : DeserLoopQPlacedW x R s0 (recFieldsQ x.r).length s) :
    DeserStepQPlacedW H x R s0 s (DeserRetQAtW x R s0) := by
  let _ := hr
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hcrl, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  let L := deserSpL s0.sp
  let v := ssgqAfter x.r (recFieldsQ x.r).length
  let bs := encodeRecord x.r
  have hmem : s.mem ⊨ deserLocalsQ L x.p bs
      (((recFieldsQ x.r).drop (recFieldsQ x.r).length).flatMap GenFieldQ.enc) v ∗
    memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R := hmem
  rw [List.drop_length, List.flatMap_nil] at hmem
  unfold deserLocalsQ at hmem
  rw [sliceCursorAfter_nil_dexitQP L x.p bs, memRegion_3f8_split_dexitQP L,
      deserSaved_eq_atL_dexitQP s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGQAt A0 (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗ memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
       memRegion (L + 0x6f0#64) 0x20 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQP L s0 ∗ R) := by
    dsimp only [c0]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, Hframe, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGQAt_move hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ Hframe ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
       memRegion (L + 0x6f0#64) 0x20 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQP L s0 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_dexitQP hmem3
  let F := (x.p ↦ₛ bs) ∗ Hframe ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ R
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
        ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗ memRegion (x.out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQP L s0) ∗ F := by
    dsimp only [F]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_placed_dexitQP hmc_ok (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc hrun hsp hal hx29 hx19 hx20 hw0 hrest hcrl.1 hvregs
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by rw [hspf]; dsimp [L, deserSpL]; bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗
          ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗
          ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_dexitQP L s0))) ∗ R := by
    dsimp only [F, L] at hmf ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hss_out : ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe ⊢
      prostSSGQAt A0 (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64)
    rwa [show x.out + 0x18#64 + 8#64 = x.out + 0x20#64 by bv_omega] at hr
  have hstk := dexit_frame_entails_stackAt_dexitQP s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawQ deserOutRecordQ
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [v, bs] at hmf2
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

/-- Relocatable `SessionRecord::deserialize` loop exit (`k = |recFieldsQ x.r|` → return) on
`lsProg_46 H`, discharged from `Stage2ContractsA0Placed H`. -/
theorem deserLoopExitQ_placed_ok_extW [LibsignalPlacement] (H : LibsignalHooks)
    (hC : Stage2ContractsA0Placed H)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (hs : DeserLoopQPlacedW x R s0 (recFieldsQ x.r).length s) :
    DeserStepQPlacedW H x R s0 s (DeserRetQAtW x R s0) :=
  deserLoopExitQ_placed_ok_of_memcpy H (memcpy_placed_ok_extW hC) x R s0 s hr hs

/-! ## Relocatable exact and general loop assembly -/

/-- Bundle of the 3 relocatable `SessionRecord::deserialize` leaf theorems on `lsProg_46 H` for
`DeserializeScopeP_Q NonEmptyV1Q`. -/
structure DeserLeavesQPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (blkPl_46).base → s0.status = .Running →
    (s0.mem ⊨ deserializeQPlacedSpecW.pre x s0 ∗ R) → s0.spAligned = true →
    DeserStepQPlacedW H x R s0 s0 (DeserLoopQPlacedW x R s0 0)
  iter : MergeFieldQPlacedOkW H (fun _ => True) →
    ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
      DeserializeScopeP_Q NonEmptyV1Q x.r → k < (recFieldsQ x.r).length →
      DeserLoopQPlacedW x R s0 k s →
      DeserStepQPlacedW H x R s0 s (DeserLoopQPlacedW x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State),
    DeserializeScopeP_Q NonEmptyV1Q x.r →
    DeserLoopQPlacedW x R s0 (recFieldsQ x.r).length s →
    DeserStepQPlacedW H x R s0 s (DeserRetQAtW x R s0)

/-- Construct `DeserLeavesQPlacedW H` from `DeserializeCalleesPlacedW H` and `memcpy` at `extHookStack`. -/
theorem deserLeavesQPlacedW_of_memcpy [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H)
    (hMemcpy : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    DeserLeavesQPlacedW H :=
  ⟨deserLoopEntryQ_placed_okW H hCallees,
   deserLoopIterQ_placed_okW H,
   deserLoopExitQ_placed_ok_of_memcpy H (memcpy_placed_ok_of_extHookStack hMemcpy)⟩

/-- Construct `DeserLeavesQPlacedW H` from `DeserializeCalleesPlacedW H` and `Stage2ContractsA0Placed H`. -/
theorem deserLeavesQPlacedW_of_contracts [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H)
    (hC : Stage2ContractsA0Placed H) : DeserLeavesQPlacedW H :=
  deserLeavesQPlacedW_of_memcpy H hCallees hC.memcpy

/-- Induction over remaining `m` fields of `recFieldsQ x.r` for `deserializeQExactPlacedSpecW`. -/
theorem deserLoopQPlacedW_run_exact [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesQPlacedW H) (hMF : MergeFieldQPlacedOkW H (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length →
      DeserLoopQPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeQExactPlacedSpecW x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    exact segStepG_then (hD.exit x R s0 s hr hs) fun sf ⟨hret, hcc, hmem⟩ =>
      reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs; have hlt : k < (recFieldsQ x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Relocatable exact `SessionRecord::deserialize` contract (`deserializeQExactPlacedSpecW`) on `lsProg_46 H`. -/
theorem deserializeExactQPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesQPlacedW H) (hMF : MergeFieldQPlacedOkW H (fun _ => True)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQExactPlacedSpecW := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := by
    have h := hpre
    dsimp only [deserializeQExactPlacedSpecW, deserializeQPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at h
    simp only [deserializeQExactRawSpecW, deserializeQRawSpecW,
      sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2
  have hpre_gen : s0.mem ⊨ deserializeQPlacedSpecW.pre x s0 ∗ R := hpre
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre_gen hal) fun s hs =>
    deserLoopQPlacedW_run_exact H hD hMF hr _ 0 s (Nat.zero_add _) hs

/-- Representation bridge from `deserOutRawQ` to `deserializeQRawSpecW.post`. -/
theorem deserOutQPlacedW_post (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (s0 sf : State) :
    deserOutRawQ x s0 sf ⊢ deserializeQRawSpecW.post x s0 sf := by
  dsimp only [deserOutRawQ, deserializeQRawSpecW]
  refine sepConj_mono_right (sepConj_mono_right (Entails.trans (sepConj_mono_left (deserReprQ_ok x.r hr x.out)) ?_))
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  rw [sepConj_assoc]; exact Entails.refl _

/-- Induction over `recFieldsQ x.r` for `deserializeQPlacedSpecW`. -/
theorem deserLoopQPlacedW_run [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesQPlacedW H) (hMF : MergeFieldQPlacedOkW H (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length →
      DeserLoopQPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeQPlacedSpecW x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_; rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (deserOutQPlacedW_post x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs; have hlt : k < (recFieldsQ x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' => ih (k + 1) s' (by omega) hs'

/-- Relocatable general `SessionRecord::deserialize` contract (`deserializeQPlacedSpecW`) on `lsProg_46 H`. -/
theorem deserializeBodyQPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesQPlacedW H) (hMF : MergeFieldQPlacedOkW H (fun _ => True)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQPlacedSpecW := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := by
    have h := hpre
    dsimp only [deserializeQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded] at h
    simp only [deserializeQRawSpecW, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopQPlacedW_run H hD hMF hr (recFieldsQ x.r).length 0 s (Nat.zero_add _) hs

/-- Relocatable transport (generic in `prog`, `entry`, and `pl`): the exact `Q`-scope
deserialize contract under `LibsignalCodeRoLoaded pl` implies
`withLsCodeRoLoaded pl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)`. -/
theorem recordDeserializeOpen_placed_of_exactQ {prog : Program} {entry : BitVec 64}
    (pl : Obj.MultiPlacement)
    (hdeser : subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded pl deserializeQExactRawSpecW)) :
    subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded pl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)) := by
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcrl, hpre'⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [recordDeserializeOpenSpec_Q] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 33 :=
    encodeRecord_length_ltQ hr
  have hx1 : s0.readReg64 .x1 =
      BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp := (A0.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - recDeserializeStack) ∗ R)
  have hpre_deserialize :
      s0.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl deserializeQExactRawSpecW).pre
        x_deserialize s0 ∗ R_deserialize := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeQExactRawSpecW,
      deserializeQRawSpecW, x_deserialize, R_deserialize]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hdeser.mono_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeQExactRawSpecW,
      deserOutRawQ, x_deserialize, R_deserialize] at hq
    have hrepr := deserOutRecordQ_entails_binCanonSession sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, recordDeserializeOpenSpec_Q]
    rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeQExactRawSpecW,
      allocPanic, recordDeserializeOpenSpec_Q, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ A0.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeQExactRawSpecW] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · exact (not_satisfies_false_sepConj hq).elim

end Placed

end Symbolic.Swarm.TRREF.B3DeserQ
