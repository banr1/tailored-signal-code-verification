/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma

/-!
# Off-Table `(15, 4)` Agreement and `compTag4` MAC Propagation

Under `evictedI0`, X25519 agreement between Bob's ratchet secret `15` and Alice's evicted ratchet
public key `4` evaluates to `compDefaultDh`. Because `padTail64 compDefaultDh` is absent from
`evictedSha256Rows`, the 4-byte fallback tag `compTag4` propagates through `createChain`, `kdfCk`,
`trMsgKeys`, and `computeMac`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTag

open ByteSpecs (sha256IV sha256Pad chunks64 sha256With hmacWith toBEBytes)
open DY.X25519 (isLowOrderKey)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (shaStateBytes)
open DY.Libsignal.TripleRatchet
  (hmac hkdfBlock2 kdfRk createChain kdfCk trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement (OpaqueSymbolSemantics Ghost gamma clamp)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compDefaultDh compTag4 compTag4Opad compDefaultSha256)
open Symbolic.BugInjection.Proofs.Common443.CompRTag
  (sha256With_length sha256Pad_append64 chunks64_append64
   chunks64_padTail64_32 padTail64 padTail64_take4)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (compDefaultSha256_take4 tagW toBEBytes_tagW kblk kblk_length)
open Symbolic.BugInjection.Proofs.Common443.CompRGamma (gamma_agree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows
  (evictedSha256Rows evictedSha256)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedPubOfIdx evictedSecretIdx evictedPointIdx evictedDhByIdx evictedLookupDh)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedI0_agreement evictedPubOfOpt_not_lowOrder evictedPointIdx_evictedPubOfOpt
   evictedI0_cryptoEquationsHold)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
  (FE OnTabE evictedSha256_row_of_untagged hT2_E onTabE_of_sha256With_untagged
   hmac_inner_untaggedE hmac_outer_first_onTabE normKeyE normKeyE_length_le
   hmacWith_eq_normKeyE gamma_hmacE gamma_computeMacE)

theorem evictedLookupDh_15_4 {sk pk : HwBytes}
    (hsk : evictedSecretIdx sk = some ⟨15, by decide⟩)
    (hpk : pk = evictedPubOfIdx ⟨4, by decide⟩) :
    evictedLookupDh sk pk = evictedDhByIdx ⟨15, by decide⟩ ⟨4, by decide⟩ := by
  subst hpk
  let i4 : Fin 16 := ⟨4, by decide⟩
  have hlo : isLowOrderKey ((evictedPubOfIdx i4).map BitVec.toNat) = false :=
    evictedPubOfOpt_not_lowOrder (some i4)
  have hpt : evictedPointIdx (evictedPubOfIdx i4) = some i4 :=
    evictedPointIdx_evictedPubOfOpt (some i4)
  unfold evictedLookupDh
  rw [hlo, hsk, hpt]
  rfl

theorem evicted_gamma_dh_norm_15_4 (S : OpaqueSymbolSemantics) (g : Ghost)
    {theirPk ourSk : DY.Bytes}
    (hpk : gamma evictedI0 S g theirPk = evictedPubOfIdx ⟨4, by decide⟩)
    (hsk : evictedSecretIdx (clamp (gamma evictedI0 S g ourSk)) = some ⟨15, by decide⟩) :
    gamma evictedI0 S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk) ourSk) =
      evictedDhByIdx ⟨15, by decide⟩ ⟨4, by decide⟩ := by
  have h := gamma_agree evictedI0 evictedI0_cryptoEquationsHold S g theirPk ourSk
  unfold DY.Libsignal.PQXDH.agree at h
  rw [h, evictedI0_agreement, Option.getD_some]
  exact evictedLookupDh_15_4 hsk hpk

def ffDhBlock : HwBytes := padTail64 compDefaultDh

theorem evictedSha256Rows_no_ffDh :
    evictedSha256Rows.all (fun r => r.2.1 != bytesToNat ffDhBlock) = true := by
  decide +kernel

def TaggedE (x : HwBytes) : Prop := x.length = 32 ∧ x.take 4 = compTag4

private theorem hmacWith_FE_length (k m : HwBytes) : (hmacWith FE k m).length = 32 := by
  unfold hmacWith
  split <;> exact sha256With_length FE _

theorem hmacWith_FE_of_tagged_key {k : HwBytes} (m : HwBytes) (hk : TaggedE k) :
    TaggedE (hmacWith FE k m) := by
  have hklen : k.length = 32 := hk.1
  refine ⟨hmacWith_FE_length k m, Classical.byContradiction fun h => ?_⟩
  have htab : OnTabE sha256IV (kblk k 0x5c) :=
    hmac_outer_first_onTabE k m (by omega) h
  have hk4 : (kblk k 0x5c).take 4 = compTag4Opad := by
    unfold kblk
    rw [← List.map_take, List.take_append_of_le_length (by omega), hk.2]
    decide
  apply htab
  unfold evictedSha256
  simp only [hk4, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem hmacWith_FE_of_tagged_msg (k : HwBytes) {m : HwBytes} (hm : TaggedE m) :
    TaggedE (hmacWith FE k m) := by
  refine ⟨hmacWith_FE_length k m, Classical.byContradiction fun h => ?_⟩
  rw [hmacWith_eq_normKeyE k m] at h
  set k' := normKeyE k
  have hk' : k'.length ≤ 64 := normKeyE_length_le k
  have hin : (sha256With FE (kblk k' 0x36 ++ m)).take 4 ≠ compTag4 :=
    hmac_inner_untaggedE k' m hk' h
  set x := kblk k' 0x36
  have hx : x.length = 64 := kblk_length k' 0x36 hk'
  have hsplit : chunks64 (ByteSpecs.sha256Pad (x ++ m)) = [x] ++ padTail64 m :: [] := by
    rw [sha256Pad_append64 x m hx, chunks64_append64 x _ hx, chunks64_padTail64_32 m hm.1]
    rfl
  have hon : OnTabE (FE sha256IV x) (padTail64 m) :=
    onTabE_of_sha256With_untagged _ hin [x] (padTail64 m) [] hsplit
  have hp4 : (padTail64 m).take 4 = ByteSpecs.toBEBytes 4 tagW := by
    rw [padTail64_take4 m hm.1, hm.2, toBEBytes_tagW]
  exact hT2_E (FE sha256IV x) (padTail64 m) hp4 hon

theorem hmacWith_FE_of_compDefaultDh (k : HwBytes) :
    TaggedE (hmacWith FE k compDefaultDh) := by
  refine ⟨hmacWith_FE_length k compDefaultDh, Classical.byContradiction fun h => ?_⟩
  rw [hmacWith_eq_normKeyE k compDefaultDh] at h
  set k' := normKeyE k
  have hk' : k'.length ≤ 64 := normKeyE_length_le k
  have hin : (sha256With FE (kblk k' 0x36 ++ compDefaultDh)).take 4 ≠ compTag4 :=
    hmac_inner_untaggedE k' compDefaultDh hk' h
  set x := kblk k' 0x36
  have hx : x.length = 64 := kblk_length k' 0x36 hk'
  have hdlen : compDefaultDh.length = 32 := by decide
  have hsplit : chunks64 (ByteSpecs.sha256Pad (x ++ compDefaultDh)) =
      [x] ++ ffDhBlock :: [] := by
    unfold ffDhBlock
    rw [sha256Pad_append64 x compDefaultDh hx, chunks64_append64 x _ hx,
        chunks64_padTail64_32 compDefaultDh hdlen]
    rfl
  have hon : OnTabE (FE sha256IV x) ffDhBlock :=
    onTabE_of_sha256With_untagged _ hin [x] ffDhBlock [] hsplit
  obtain ⟨_, _, _, row, hmem, _, hr2, _⟩ := evictedSha256_row_of_untagged hon
  have hall := List.all_eq_true.mp evictedSha256Rows_no_ffDh row hmem
  simp [hr2] at hall

def TT (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes) : Prop :=
  TaggedE (gamma evictedI0 S g t)

theorem tt_hmac_of_key {S : OpaqueSymbolSemantics} {g : Ghost} {k : DY.Bytes} (m : DY.Bytes)
    (hk : TT S g k) : TT S g (hmac k m) := by
  unfold TT
  rw [gamma_hmacE]
  exact hmacWith_FE_of_tagged_key _ hk

theorem tt_hmac_of_msg {S : OpaqueSymbolSemantics} {g : Ghost} (k : DY.Bytes) {m : DY.Bytes}
    (hm : TT S g m) : TT S g (hmac k m) := by
  unfold TT
  rw [gamma_hmacE]
  exact hmacWith_FE_of_tagged_msg _ hm

theorem tt_hkdfBlock2 {S : OpaqueSymbolSemantics} {g : Ghost} {prk : DY.Bytes} (info : DY.Bytes)
    (hprk : TT S g prk) : TT S g (hkdfBlock2 prk info) := by
  unfold hkdfBlock2
  exact tt_hmac_of_key _ hprk

theorem tt_createChain_15_4 (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk theirPk ourSk : DY.Bytes)
    (hpk : gamma evictedI0 S g theirPk = evictedPubOfIdx ⟨4, by decide⟩)
    (hsk : evictedSecretIdx (clamp (gamma evictedI0 S g ourSk)) = some ⟨15, by decide⟩) :
    TT S g (createChain rk theirPk ourSk).2 := by
  unfold createChain DY.X25519.agree kdfRk
  apply tt_hkdfBlock2
  unfold TT
  rw [gamma_hmacE, evicted_gamma_dh_norm_15_4 S g hpk hsk]
  exact hmacWith_FE_of_tagged_msg _ ⟨by decide, by decide⟩

theorem tt_kdfCk_snd {S : OpaqueSymbolSemantics} {g : Ghost} {ck : DY.Bytes}
    (hck : TT S g ck) : TT S g (kdfCk ck).2 := by
  unfold kdfCk
  exact tt_hmac_of_key _ hck

theorem tt_trMsgKeys_macKey {S : OpaqueSymbolSemantics} {g : Ghost}
    (pqSalt : DY.Bytes) {seed : DY.Bytes} (hseed : TT S g seed) :
    TT S g (trMsgKeys pqSalt seed).macKey := by
  unfold trMsgKeys
  exact tt_hkdfBlock2 _ (tt_hmac_of_msg pqSalt hseed)

theorem computeMac_take4_of_tt {S : OpaqueSymbolSemantics} {g : Ghost}
    {mk : DY.Bytes} (sIk rIk w : DY.Bytes) (hmk : TT S g mk) :
    (gamma evictedI0 S g (computeMac mk sIk rIk w)).take 4 = compTag4 := by
  rw [gamma_computeMacE, List.take_take]
  exact (hmacWith_FE_of_tagged_key _ hmk).2

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTag
