/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.CalleesBudget
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Canonical-or-Fallback `PreKeySignalMessage::try_from` Slot Bridge

Establishes `SubsetA4PksmTryFromPlaced`, `PksmSlotOkPlacedAt`, and
`CliPksmSlotExistsPlaced` at `CanonicalOrFallbackPksmEnv PksmTryFromEnv`. Canonical
`PreKeyMessageFields` byte slices (`∃ m, x.bytes = m.bytes`) use the tight `< 2 ^ 64`
characterization `pksmParse_bytes_lt64` and `PksmCanonSliceEnv`; non-canonical inputs
fall back to `PksmTryFromEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux

open Arm64 SepProp
open ProofLib hiding SepWPp
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSession
  (PublicKey SignalMessage SignalProtocolError currentVersion djbType preKyberVersion versionByte)
open CryptoGames.LibsignalSessionApi
  (PreKeySignalMessage ProtoPreKeySignalMessage)
open CryptoGames.LibsignalSessionApi.Prost (bytesField uint32Field)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_111 blkPl_111
   ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl)
open CryptoVerification.E2E (PreKeyMessageFields)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey_encodeKey encodeBytesField encodeKey encodeUint32Field encodeVarint
   encodeVarint_ne_nil mergeBytes mergeBytes_encode mergeUint32 mergeUint32_encode
   protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (PreKeyMsgGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded smallRootStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Prost (bytesMergeStack)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp entails_of_eq stackAt_sub_split)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag speAt)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (PreKeyTryFromArgs cur8 extract_withPreKeyInv keepsFrozenInv_codeRoLoaded
   ls_subroutine_ok_cro_of_block opkTag preKeyCalleeSavedAt
   preKeyPlacedProg preKeyResultAt preKeyTryFromStack preKeyTryFromSubStack
   stackAt_preKeyTryFrom_split subroutine_ok_withPreKeyInv_of_cl)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem pksmResAt)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm
  (decodeProto decodeProtoLoop emptyProto kyberOk mergeProtoField pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (subroutine_ok_withPreKeyInv_of_cro)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
  (PreKeyPostEnv PreKeyTryFromEnv preKeyTryFromPlacedRawEnvSpec preKeyTryFromPlacedRawSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget
  (preKeyLoopEvents preKey_entry_to_f90_cro_placed_wp)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
  (epilogue_034_placed_wp post_f90_to_034_placed_wp)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
  (int32Merge_ok_at_prekey_placed preKeyDropSpeOk_cro_of_hookSat preKeyIntoBoxOk_of_hooks
   preKeySigTryFromOk_cro_of_deps preKeyTryCloneOk_of_hooks)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
  (preKeyDeallocOk_of_hookSat preKeyNoPanicQp)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
  (SigTryFromConcreteEnv)
open LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.CalleesBudget (bytes_merge_placed_ok)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv fitsEnv_preKeyTryFromConcrete_of_pksmCanonSlice
   preKeyArgsOfFields preKeyArgsOfFields_bytes preKeyArgsOfFields_inner
   preKeyArgsOfFields_of_args preKeyFieldsOfArgs_of_fields
   preKeyTryFromConcrete_sub_pksmCanonSlice)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (hookSat_framelessMemcpyBudget_of_withVmPreserved hookSat_noAllocShimBudget_of_withVmPreserved
   hookSat_sessionShimBudget_of_withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (PksmSlotOkPlaced PksmSlotOkPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
  (tripleRatchetHooksWPlaced_of_codecHooks tryFromDepsPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmLoopEnv PksmTryFromEnv PksmTryFromEnvGen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
  (subsetA4PksmTryFromPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
  (CliPksmSlotExistsPlaced CliPksmSlotExistsPlacedAt codecHooksPlaced_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (SubsetA4PksmTryFromPlaced cliPksmTryFrom_placed_at_block pksmTryFromSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)

/-! ## `< 2 ^ 64` Bound for `pksmParse_bytes` -/

/-- Relaxes the length side condition of `Pksm.pksmParse_bytes` from `x.inner.length + 2048 < 2 ^ 32` to `x.inner.length < 2 ^ 64`. -/
private theorem pksmParse_bytes_lt64 (x : PreKeyTryFromArgs) (hx : x.inner.length < 2 ^ 64) :
    pksmParse x.bytes =
      match SignalMessage.tryFrom protoSignalCodec x.inner with
      | .ok i => some (x.toModel i)
      | .error _ => none := by
  have prost_key_eq : ∀ (t : Nat) (wt : WireType), t < 2 ^ 28 →
      CryptoGames.LibsignalSessionApi.Prost.key t wt.toNat = encodeKey t wt := by
    intro t wt ht
    have hw : wt.toNat < 8 := by cases wt <;> decide
    rw [CryptoGames.LibsignalSessionApi.Prost.key,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_varint_length_eq_encodeVarint
        _ (by omega),
      show 8 * t + wt.toNat = t * 8 + wt.toNat by omega, encodeKey]
  have prost_uint32Field_eq : ∀ (t : Nat) (o : Option (BitVec 32)), t < 2 ^ 28 →
      uint32Field t o = encodeUint32Field t o := by
    intro t o ht
    cases o with
    | none => rfl
    | some v =>
      rw [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_uint32Field_some,
        show (0 : Nat) = WireType.varint.toNat from rfl, prost_key_eq t .varint ht,
        encodeUint32Field]
  have prost_bytesField_eq : ∀ (t : Nat) (o : Option (List (BitVec 8))), t < 2 ^ 28 →
      (∀ v, o = some v → v.length < 2 ^ 64) →
      bytesField t o = encodeBytesField t o := by
    intro t o ht hl
    cases o with
    | none => rfl
    | some v =>
      rw [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_bytesField_some
          t v (hl v rfl),
        show (2 : Nat) = WireType.lengthDelimited.toNat from rfl,
        prost_key_eq t .lengthDelimited ht, encodeBytesField]
  let ProtoLoopsTo (m : ProtoPreKeySignalMessage) (bs : List (BitVec 8))
      (r : ProtoPreKeySignalMessage) : Prop :=
    ∀ n, bs.length ≤ n → decodeProtoLoop n m bs = some r
  have protoLoopsTo_nil : ∀ m : ProtoPreKeySignalMessage, ProtoLoopsTo m [] m := by
    intro m n _
    cases n <;> rfl
  have protoLoopsTo_field : ∀ (t : Nat) (wt : WireType), 1 ≤ t → t < 2 ^ 28 →
      ∀ (m m' r : ProtoPreKeySignalMessage) (body rest : List (BitVec 8)),
      mergeProtoField m t wt (body ++ rest) = some (m', rest) →
      ProtoLoopsTo m' rest r →
      ProtoLoopsTo m (encodeKey t wt ++ (body ++ rest)) r := by
    intro t wt h1 h2 m m' r body rest hmerge h n hn
    have hkey := decodeKey_encodeKey t wt (body ++ rest) h1 h2
    have hpos : 0 < (encodeKey t wt).length := List.length_pos_iff.mpr (encodeVarint_ne_nil _)
    simp only [List.length_append] at hn
    obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
      (List.length_pos_iff.mp (by simp only [List.length_append]; omega) :
        encodeKey t wt ++ (body ++ rest) ≠ [])
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hk] at hkey ⊢
    simp only [decodeProtoLoop, hkey, hmerge]
    exact h n' (by omega)
  have protoLoopsTo_uint32 : ∀ (t : Nat), 1 ≤ t → t < 2 ^ 28 →
      ∀ (o : Option (BitVec 32)) (upd : Option (BitVec 32) → ProtoPreKeySignalMessage)
        (rest : List (BitVec 8)) (r : ProtoPreKeySignalMessage),
      (∀ bs, mergeProtoField (upd none) t .varint bs =
        (mergeUint32 .varint bs).map fun (v, r) => (upd (some v), r)) →
      ProtoLoopsTo (upd o) rest r →
      ProtoLoopsTo (upd none) (uint32Field t o ++ rest) r := by
    intro t h1 h2 o upd rest r hm h
    rw [prost_uint32Field_eq t o h2]
    cases o with
    | none => simpa [encodeUint32Field] using h
    | some v =>
      rw [show encodeUint32Field t (some v) ++ rest =
        encodeKey t .varint ++ (encodeVarint (v.zeroExtend 64) ++ rest) by simp [encodeUint32Field]]
      refine protoLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h
      rw [hm, mergeUint32_encode v rest]
      rfl
  have protoLoopsTo_bytes : ∀ (t : Nat), 1 ≤ t → t < 2 ^ 28 →
      ∀ (o : Option (List (BitVec 8))) (upd : Option (List (BitVec 8)) → ProtoPreKeySignalMessage)
        (rest : List (BitVec 8)) (r : ProtoPreKeySignalMessage),
      (∀ v, o = some v → v.length < 2 ^ 64) →
      (∀ bs, mergeProtoField (upd none) t .lengthDelimited bs =
        (mergeBytes .lengthDelimited bs).map fun (v, r) => (upd (some v), r)) →
      ProtoLoopsTo (upd o) rest r →
      ProtoLoopsTo (upd none) (bytesField t o ++ rest) r := by
    intro t h1 h2 o upd rest r hl hm h
    rw [prost_bytesField_eq t o h2 hl]
    cases o with
    | none => simpa [encodeBytesField] using h
    | some v =>
      rw [show encodeBytesField t (some v) ++ rest =
        encodeKey t .lengthDelimited ++
          ((encodeVarint (BitVec.ofNat 64 v.length) ++ v) ++ rest) by simp [encodeBytesField]]
      refine protoLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h
      rw [hm, List.append_assoc, mergeBytes_encode v rest (hl v rfl)]
      rfl
  have hbk_fit : ∀ v, some x.bkBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hik_fit : ∀ v, some x.ikBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hin_fit : ∀ v, some x.inner = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; exact hx
  have hkyb_fit : ∀ v, some x.kyberBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hloop : ProtoLoopsTo emptyProto
      (uint32Field 1 x.opkId ++ (bytesField 2 (some x.bkBytes) ++
        (bytesField 3 (some x.ikBytes) ++ (bytesField 4 (some x.inner) ++
          (uint32Field 5 (some x.regId) ++ (uint32Field 6 (some x.spkId) ++
            (uint32Field 7 (some x.kpkId) ++
              (bytesField 8 (some x.kyberBytes) ++ []))))))))
      x.protoMsg :=
    protoLoopsTo_uint32 1 (by omega) (by omega) x.opkId
      (fun o => ⟨none, o, none, none, none, none, none, none⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_bytes 2 (by omega) (by omega) (some x.bkBytes)
      (fun o => ⟨none, x.opkId, none, none, none, o, none, none⟩) _ _ hbk_fit (fun _ => rfl) <|
    protoLoopsTo_bytes 3 (by omega) (by omega) (some x.ikBytes)
      (fun o => ⟨none, x.opkId, none, none, none, some x.bkBytes, o, none⟩) _ _ hik_fit
      (fun _ => rfl) <|
    protoLoopsTo_bytes 4 (by omega) (by omega) (some x.inner)
      (fun o => ⟨none, x.opkId, none, none, none, some x.bkBytes, some x.ikBytes, o⟩) _ _ hin_fit
      (fun _ => rfl) <|
    protoLoopsTo_uint32 5 (by omega) (by omega) (some x.regId)
      (fun o => ⟨o, x.opkId, none, none, none, some x.bkBytes, some x.ikBytes, some x.inner⟩) _ _
      (fun _ => rfl) <|
    protoLoopsTo_uint32 6 (by omega) (by omega) (some x.spkId)
      (fun o => ⟨some x.regId, x.opkId, o, none, none, some x.bkBytes, some x.ikBytes,
        some x.inner⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_uint32 7 (by omega) (by omega) (some x.kpkId)
      (fun o => ⟨some x.regId, x.opkId, some x.spkId, o, none, some x.bkBytes, some x.ikBytes,
        some x.inner⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_bytes 8 (by omega) (by omega) (some x.kyberBytes)
      (fun o => ⟨some x.regId, x.opkId, some x.spkId, some x.kpkId, o, some x.bkBytes,
        some x.ikBytes, some x.inner⟩) _ _ hkyb_fit (fun _ => rfl) <|
    protoLoopsTo_nil _
  have hdec : decodeProto x.protoBytes = some x.protoMsg := by
    have henc : x.protoBytes =
        uint32Field 1 x.opkId ++ (bytesField 2 (some x.bkBytes) ++
          (bytesField 3 (some x.ikBytes) ++ (bytesField 4 (some x.inner) ++
            (uint32Field 5 (some x.regId) ++ (uint32Field 6 (some x.spkId) ++
              (uint32Field 7 (some x.kpkId) ++
                (bytesField 8 (some x.kyberBytes) ++ []))))))) := by
      simp only [PreKeyTryFromArgs.protoBytes, PreKeyTryFromArgs.protoMsg,
        ProtoPreKeySignalMessage.encode, List.append_assoc, List.append_nil]
    rw [decodeProto, henc]
    exact hloop _ (Nat.le_refl _)
  have deserialize_djb_ok : ∀ v : List.Vector (BitVec 8) 32,
      PublicKey.deserialize (0x05#8 :: v.toList) = .ok ⟨v⟩ := by
    rintro ⟨l, hl⟩
    simp [PublicKey.deserialize, djbType, hl, List.take_of_length_le (Nat.le_of_eq hl)]
  have hvb : versionByte 4#8 >>> 4 = 4#8 := by decide
  have hver : ¬ (4#8 < preKyberVersion ∨ currentVersion < 4#8) := by decide
  have hkyb : kyberOk 4#8 x.protoMsg = true := rfl
  have hbk : PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩ := deserialize_djb_ok x.baseKey
  have hik : PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩ := deserialize_djb_ok x.idPub
  simp only [PreKeyTryFromArgs.bytes, pksmParse, hvb, hver, ↓reduceIte, hdec, hkyb]
  simp only [PreKeyTryFromArgs.protoMsg, hbk, hik]
  cases SignalMessage.tryFrom protoSignalCodec x.inner <;> rfl

/-! ## Canonical Block-111 Subroutine Contract from `CodecHooksPlaced` -/

private theorem fromRecord_lsLogOff_eq [LibsignalPlacement] :
    lsLogOff = CryptoVerification.LibsignalTripleRatchet.lsLogOff :=
  rfl

private theorem sepWPp_bind_frame_noPanic_pk {prog : Program} {mid ret : BitVec 64}
    {s : State} {P F : SepProp} {Qm Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm preKeyNoPanicQp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q preKeyNoPanicQp) :
    SepWPp prog ret s (P ∗ F) Q preKeyNoPanicQp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h1 (F ∗ R) hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hqm, hvm⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom⟩⟩
  · rw [← sepConj_assoc] at hmm
    rcases h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpan⟩
    · exact ⟨sf, hsteps1.trans hsteps2, Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hvm⟩⟩
    · exact ⟨sf, hsteps1.trans hsteps2, Or.inr hpan⟩
  · exact False.elim hp
  · rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-- Block-111 `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` subroutine contract on canonical `PreKeyTryFromArgs` under `withLsCodeRoLoaded`. -/
theorem preKeyTryFrom_cro_placed_ok_of_codecHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (withLsCodeRoLoaded lsmpl
        (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim)) := by
  have hcl_of_cro : ∀ m, LibsignalCodeRoLoaded lsmpl m → LibsignalCodeLoaded lsmpl m :=
    fun _ h => h.1
  have hshim_s := hookSat_sessionShimBudget_of_withVmPreserved hH.shim
  have hshim := hookSat_noAllocShimBudget_of_withVmPreserved hH.shim
  have hmc := hookSat_framelessMemcpyBudget_of_withVmPreserved hH.memcpy
  have hint32 := subroutine_ok_withPreKeyInv_of_cl hcl_of_cro
    (int32Merge_ok_at_prekey_placed hshim_s hH.alloc)
  have hbytes0 := subroutine_ok_withPreKeyInv_of_cro
    (ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H) (i := 111) (j := 7)
      (bytes_merge_placed_ok hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy))
  have hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (CryptoVerification.E2E.Pqxdh.ResponderWire.withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpec A lim)) := by
    simpa only [ls_blockPlacement_base] using hbytes0
  have hdealloc := preKeyDeallocOk_of_hookSat (Inv := LibsignalCodeRoLoaded lsmpl) hH.dealloc
  have hDropSpe := preKeyDropSpeOk_cro_of_hookSat hH.dealloc
  have hIntoBox := preKeyIntoBoxOk_of_hooks hcl_of_cro hH.dealloc hH.realloc
  have hSigTryFrom := preKeySigTryFromOk_cro_of_deps
    (tripleRatchetHooksWPlaced_of_codecHooks hH) (tryFromDepsPlaced_of_codecHooks hH)
  have hTryClone := preKeyTryCloneOk_of_hooks hcl_of_cro hshim hH.alloc hmc
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hinv0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hinv0.1
  have hL : (preKeyPlacedProg H).CodeLoaded s0.mem :=
    (IsLsBlockProg.eq_blockProgram (prog := preKeyPlacedProg H) (i := 111) (H := H)).symm ▸
      hcl0 111 (by decide) (by decide) H (fun _ => none) Syscall.standard
  dsimp only [preKeyTryFromPlacedRawSpec, preKeyTryFromPlacedRawEnvSpec] at hpre0
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1_nat, hlt, hx8, hfits⟩, hmem⟩
  have hfit_loop : FitsEvents M lim st (preKeyLoopEvents x) :=
    FitsEnv.seq_left hfits (preKeyLoopEvents x) rfl
  have hfits_post : FitsEnv M lim (M.stepEvents (preKeyLoopEvents x) st)
      (PreKeyPostEnv SigTryFromConcreteEnv x) :=
    FitsEnv.seq_right hfits rfl
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set sp' := s0.sp - 608#64
  have hstk_top := stackAt_preKeyTryFrom_split s0.sp
  have hstk_sub := stackAt_sub_split sp' bytesMergeStack smallRootStack (by decide) (by decide)
  have hmem' : s0.mem ⊨
      (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0)) ∗ R := by
    ac_nf at hmem ⊢
  have hfull : SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim).post (x, st) s0 sf))
      preKeyNoPanicQp := by
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗
          A.pool lim st s0 ∗ stackAt sp' bytesMergeStack) ∗
        (memRegion x.sret 248 ∗ lsLogOff ∗
          memRegion sp' 296 ∗ memRegion (sp' + 448#64) 64 ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - bytesMergeStack)))
      (by
        rw [hstk_top, show preKeyTryFromSubStack = smallRootStack from rfl]
        dsimp only [sp'] at hstk_sub ⊢
        rw [hstk_sub]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_noPanic_pk
      (preKey_entry_to_f90_cro_placed_wp hint32 hbytes
        hfit_loop rfl hlt hpc hrun hsp hinv0 hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hregs1, hsp1, hinv1, htr1, hx24_1,
      opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopk, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ memRegion sp' 296 ∗
          ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
          vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
          vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
          vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
          vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
          ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
          ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (preKeyLoopEvents x) st) s1 ∗
          stackAt sp' smallRootStack) ∗
        (memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0))
      (by
        rw [hstk_sub]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_noPanic_pk
      (post_f90_to_034_placed_wp (st := M.stepEvents (preKeyLoopEvents x) st)
        keepsFrozenInv_codeRoLoaded hcl_of_cro hdealloc hDropSpe hIntoBox hSigTryFrom hTryClone
        hlt hfits_post hopk hpc1 hrun1 hregs1 hsp1 hinv1 htr1 hx24_1) ?_
    intro s2 P2 hpc2 hrun2 ⟨evs_post, hevs_post, hst2, hent2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
    clear hent2
    refine SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents (preKeyLoopEvents x ++ evs_post) st) s2)
      (by
        rw [M.stepEvents_append (preKeyLoopEvents x) evs_post st, fromRecord_lsLogOff_eq]
        dsimp only [sp']
        apply entails_of_eq; sep_ac_rfl) ?_
    exact epilogue_034_placed_wp keepsFrozenInv_codeRoLoaded (SeqEnv.append rfl hevs_post)
      hsp hst2 hpc2 hrun2
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ |
    ⟨_, _, _, hp⟩ | ⟨_, hoom⟩
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
        Satisfies.mono (sepConj_mono_left hent_f) hmf⟩))
  · exact False.elim hp
  · rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-! ## Byte-Slice Congruence and `CanonicalOrFallbackPksmEnv` Slot Closure -/

/-- `PksmTryFromEnv x` depends only on `x.bytes`. -/
theorem pksmTryFromEnv_congr_bytes (x y : PksmGhost) (h : x.bytes = y.bytes) :
    PksmTryFromEnv x = PksmTryFromEnv y := by
  have aux : ∀ a b : PksmGhost, a.bytes = b.bytes → ∀ evs, PksmTryFromEnv a evs → PksmTryFromEnv b evs := by
    intro a b hab evs hevs
    rcases hevs with _ | ⟨ha, h1, h2, hl⟩ | ⟨ha, h1, h2, hl, hp⟩
    · exact PksmTryFromEnvGen.nil
    · exact PksmTryFromEnvGen.loopOnly (hab.symm.trans ha) h1 h2
        (by simpa only [PksmLoopEnv, hab] using hl)
    · exact PksmTryFromEnvGen.loopAfter (hab.symm.trans ha) h1 h2
        (by simpa only [PksmLoopEnv, hab] using hl) (by simpa only [hab] using hp)
  funext evs
  exact propext ⟨aux x y h evs, aux y x h.symm evs⟩

/-- `CanonicalOrFallbackPksmEnv PksmTryFromEnv x` depends only on `x.bytes`. -/
theorem canonicalOrFallbackPksmEnv_congr_bytes (x y : PksmGhost) (h : x.bytes = y.bytes) :
    CanonicalOrFallbackPksmEnv PksmTryFromEnv x = CanonicalOrFallbackPksmEnv PksmTryFromEnv y := by
  have hxy := pksmTryFromEnv_congr_bytes x y h
  funext evs
  simp only [CanonicalOrFallbackPksmEnv, h, hxy]

private theorem satisfies_pksmResAt_of_preKeyResultAt
    {A : RustAlloc} {x : PreKeyTryFromArgs} {F : SepProp} {m : Memory}
    (hx : x.inner.length < 2 ^ 64)
    (hm : m ⊨ preKeyResultAt A x.sret x ∗ F) :
    m ⊨ pksmResAt A x.sret (pksmParse x.bytes) ∗ F := by
  have hany : (emp : SepProp) ⊢ anyHeap := entails_anyHeap emp
  rw [pksmParse_bytes_lt64 x hx]
  unfold preKeyResultAt at hm
  cases hsig : SignalMessage.tryFrom protoSignalCodec x.inner with
  | ok innerMsg =>
    rw [hsig] at hm
    dsimp only [pksmResAt]
    have hm0 : m ⊨ emp ∗ ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g x.sret (x.toModel innerMsg)) ∗ F) := by
      rw [emp_sepConj]
      exact hm
    have hm1 := Satisfies.mono (sepConj_mono_left hany) hm0
    ac_nf at hm1 ⊢
  | error e =>
    rw [hsig] at hm
    dsimp only [pksmResAt]
    have hm0 : m ⊨ emp ∗ ((x.sret ↦₆₄ errTag) ∗ speAt A ([] : List (BitVec 8)) (x.sret + 8#64) e ∗
        memRegion (x.sret + 56#64) 192 ∗ F) := by
      rw [emp_sepConj]
      ac_nf at hm ⊢
    have hm1 := Satisfies.mono (sepConj_mono_left hany) hm0
    have hm2 : m ⊨ speAt A ([] : List (BitVec 8)) (x.sret + 8#64) e ∗
        ((x.sret ↦₆₄ errTag) ∗ memRegion (x.sret + 56#64) 192 ∗ anyHeap ∗ F) := by
      ac_nf at hm1 ⊢
    have hm3 : m ⊨ (∃∗ fn : List (BitVec 8), ∃∗ e' : SignalProtocolError, speAt A fn (x.sret + 8#64) e') ∗
        ((x.sret ↦₆₄ errTag) ∗ memRegion (x.sret + 56#64) 192 ∗ anyHeap ∗ F) := by
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      exact ⟨[], e, hm2⟩
    ac_nf at hm3 ⊢

/-- `SubsetA4PksmTryFromPlaced` at `CanonicalOrFallbackPksmEnv PksmTryFromEnv` from `CodecHooksPlaced`. -/
theorem subsetA4PksmTryFromPlaced_canonOrFallback [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hH : CodecHooksPlaced M A lim H) :
    SubsetA4PksmTryFromPlaced M A lim (CanonicalOrFallbackPksmEnv PksmTryFromEnv) H where
  pksmTryFrom_placed := by
    have hFallback := (subsetA4PksmTryFromPlaced_of_codecHooks hH).pksmTryFrom_placed
    have hCanon := preKeyTryFrom_cro_placed_ok_of_codecHooks hH
    apply subroutine_ok_outcome_intro
    rintro ⟨x, st⟩ R s0 hpc hrun hpre hal
    by_cases hcan : ∃ m : PreKeyMessageFields, x.bytes = m.bytes
    · obtain ⟨m, hm⟩ := hcan
      let x0 : PreKeyTryFromArgs := preKeyArgsOfFields 0#64 0#64 m
      let x' : PreKeyTryFromArgs := { x0 with ptr := x.ptr, sret := x.ret }
      have hx'_eq : x' = preKeyArgsOfFields x.ptr x.ret m := by
        have h1 := (preKeyArgsOfFields_of_args x.ptr x.ret x0).symm
        rw [show x0 = preKeyArgsOfFields 0#64 0#64 m from rfl,
          preKeyFieldsOfArgs_of_fields] at h1
        exact h1
      have hx'_bytes : x'.bytes = x.bytes := by
        rw [hx'_eq, preKeyArgsOfFields_bytes, hm]
      have hx'_in : x'.inner = m.inner := by
        rw [hx'_eq, preKeyArgsOfFields_inner]
      have ⟨hcro, hraw⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [pksmTryFromSpecPlaced] at hraw
      rw [sepConj_assoc, satisfies_pure_sepConj] at hraw
      rcases hraw with ⟨⟨hx0, hx1, hlt, hx8, _hstk, hfit⟩, hmem⟩
      have hfit_cs : FitsEnv M lim st (PksmCanonSliceEnv x'.bytes) := fun evs hevs =>
        hfit evs (Or.inl ⟨⟨m, hm⟩, hx'_bytes ▸ hevs⟩)
      have hfit' : FitsEnv M lim st (PreKeyTryFromEnv SigTryFromConcreteEnv x') :=
        fitsEnv_preKeyTryFromConcrete_of_pksmCanonSlice hfit_cs
      have hpre_raw : s0.mem ⊨
          (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim).pre (x', st) s0 ∗ R := by
        dsimp only [preKeyTryFromPlacedRawSpec, preKeyTryFromPlacedRawEnvSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, ?_, ?_, hx8, hfit'⟩, ?_⟩
        · simpa only [hx'_bytes] using hx1
        · simpa only [hx'_bytes] using hlt
        · simpa only [x', hx'_bytes, fromRecord_lsLogOff_eq] using hmem
      have hpre' : s0.mem ⊨
          (withLsCodeRoLoaded lsmpl
            (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim)).pre (x', st) s0 ∗ R := by
        dsimp only [withLsCodeRoLoaded]
        rw [sepConj_comm _ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝, sepConj_assoc,
          satisfies_pure_sepConj]
        exact ⟨hcro, hpre_raw⟩
      refine hCanon.mono_outcome (x', st) R s0 hpc hrun hpre' hal fun sf hout => ?_
      rcases hout with ⟨hret, hcc, hpost⟩ | hrest
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeRoLoaded, pksmTryFromSpecPlaced,
          preKeyTryFromPlacedRawSpec, preKeyTryFromPlacedRawEnvSpec] at hpost ⊢
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
        rcases hpost with ⟨evs, hevs⟩
        refine ⟨evs, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
        rcases hevs with ⟨⟨htr, hE⟩, hmem_f⟩
        have hcs : PksmCanonSliceEnv x.bytes evs :=
          preKeyTryFromConcrete_sub_pksmCanonSlice hx'_bytes.symm hE
        refine ⟨⟨htr, Or.inl ⟨⟨m, hm⟩, hcs⟩⟩, ?_⟩
        have hinner_le : m.inner.length ≤ m.bytes.length :=
          LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit.PreKeyMessageFields.inner_length_le_bytes m
        have hx'_inner_lt : x'.inner.length < 2 ^ 64 := by
          have hx'_in_len : x'.inner.length = m.inner.length := congrArg List.length hx'_in
          have hm_len : m.bytes.length = x.bytes.length := by rw [hm]
          have h32_64 : (2 ^ 32 : Nat) < 2 ^ 64 := by decide
          omega
        rw [sepConj_assoc] at hmem_f
        have hmem_res := satisfies_pksmResAt_of_preKeyResultAt hx'_inner_lt hmem_f
        rw [← sepConj_assoc] at hmem_res
        simpa only [x', hx'_bytes, fromRecord_lsLogOff_eq] using hmem_res
      · exact Or.inr hrest
    · have ⟨hcro, hraw⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [pksmTryFromSpecPlaced] at hraw
      rw [sepConj_assoc, satisfies_pure_sepConj] at hraw
      rcases hraw with ⟨⟨hx0, hx1, hlt, hx8, hstk, hfit⟩, hmem⟩
      have hfit' : FitsEnv M lim st (PksmTryFromEnv x) := fun evs hevs =>
        hfit evs (Or.inr ⟨hcan, hevs⟩)
      have hpre_raw : s0.mem ⊨
          (pksmTryFromSpecPlaced M A lim PksmTryFromEnv).pre (x, st) s0 ∗ R := by
        dsimp only [pksmTryFromSpecPlaced, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
        rw [sepConj_comm _ ⌜CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨hcro, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hlt, hx8, hstk, hfit'⟩, hmem⟩
      refine hFallback.mono_outcome (x, st) R s0 hpc hrun hpre_raw hal fun sf hout => ?_
      rcases hout with ⟨hret, hcc, hpost⟩ | hrest
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [pksmTryFromSpecPlaced,
          CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
        rcases hpost with ⟨evs, hevs⟩
        refine ⟨evs, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
        rcases hevs with ⟨⟨htr, hE⟩, hmem_f⟩
        exact ⟨⟨htr, Or.inr ⟨hcan, hE⟩⟩, hmem_f⟩
      · exact Or.inr hrest

theorem subsetA4PksmTryFromPlaced_canonOrFallback_cli [LibsignalPlacement]
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    SubsetA4PksmTryFromPlaced M A lim (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  subsetA4PksmTryFromPlaced_canonOrFallback (codecHooksPlaced_cli mmpl g W hG)

/-- `PksmSlotOkPlacedAt` at `CanonicalOrFallbackPksmEnv PksmTryFromEnv` from `CodecHooksPlaced`. -/
theorem pksmSlotOkPlacedAt_canonOrFallback [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hCodec : CodecHooksPlaced M A lim H) :
    PksmSlotOkPlacedAt H A lim (CanonicalOrFallbackPksmEnv PksmTryFromEnv) :=
  fun _ hS =>
    cliPksmTryFrom_placed_at_block
      (callerProg := CryptoVerification.SignalSession.Cli.Run.Placed.lsProg_579 H) (i := 579)
      (subsetA4PksmTryFromPlaced_canonOrFallback hCodec)
      (fun b => congrFun hS b)

/-- `CliPksmSlotExistsPlacedAt` at `CanonicalOrFallbackPksmEnv PksmTryFromEnv` from `CodecHooksPlaced`. -/
theorem cliPksmSlotExistsPlacedAt_canonOrFallback [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hCodec : CodecHooksPlaced M A lim H) :
    CliPksmSlotExistsPlacedAt H A lim (CanonicalOrFallbackPksmEnv PksmTryFromEnv) :=
  ⟨pksmParse, pksmSlotOkPlacedAt_canonOrFallback hCodec⟩

/-- `CliPksmSlotExistsPlaced` on `cliGhostExterns` under `CliGhostAllocHooks`. -/
theorem cliPksmSlotExistsPlaced_canonOrFallback [LibsignalPlacement]
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CliPksmSlotExistsPlaced mmpl g W A lim (CanonicalOrFallbackPksmEnv PksmTryFromEnv) :=
  cliPksmSlotExistsPlacedAt_canonOrFallback (codecHooksPlaced_cli mmpl g W hG)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux
