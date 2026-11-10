/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.ReductionDsl.Size
import Mathlib.Algebra.Order.Ring.Star

/-!
# E2E `ReductionDsl` tables: block-size honesty and codec roundtrips

Proves `SampSizeHonest (e2eSamplers ℓ)` and `OpsSizeHonest` (with `Costed*` counterparts) for
the E2E `ReductionDsl` operator tables, provides `Expr.op` smart constructors, and proves
roundtrip identities for the shared value encodings and game codecs.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.TablesHonest

open List Option Bool Prod Sum Fin OracleSpec OracleComp
open ReductionDsl (Ty Ops Samplers Var Expr Comp Iface GameCodec Env OpsSizeHonest SampSizeHonest
  bits lt_two_pow_bits one_le_bits bits_le_of_lt bits_mono bits_mul)
open CryptoVerification.LibsignalSession (CostedFits CostedOpsSizeHonest CostedSampSizeHonest)
open CryptoVerification.E2E (Bytes BinState EpochGhost wirePrekey wireWhisper binStateOfUnderExtras
  ofU8 toU8 vecU8)
open CryptoVerification.E2E.Costed (E2ESort E2EUnifBase E2EPureOp E2ECurveCheckOp E2ECryptoOp
  E2EAdapterTag e2eSig e2eSamplers e2ePureOps e2eCurveCheckOps e2eCryptoOps e2ePrimOps
  e2eAdapterOps e2eOps e2eAdapterIface e2eAdapterCodec
  PB PU32 B U8 U32 U64 BV128 BV256 BV512 FinT PK IdKey PlainT GhostStT BinStT
  ghostStBlocks binStBlocks drKeyT drKeyV drKeyOfV bundleT bundleV bundleOfV hdrT hdrV hdrOfV
  sidT sidV sidOfV dhSecretsT keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec
  spqrParamsT spqrVnT spqrPrevEntryT spqrDirT spqrEpochLinkT spqrChainT spqrStatePartsT
  drSenderChainT drRecvChainT ghostPartsT signalHdrT signalParsedT recvResultT recvResultEnc
  recvResultDec partyToBool boolToParty smQT smQenc smRT smRdec e2eReadU32BE e2eDecodePreKeyMsg
  e2eHdrOfPreKeyMsg e2eExpectedPreKeyMsg e2ePartneredInnerBytes e2eWireInnerBytes
  splitSpqrPrev joinSpqrPrev spqrParamsToV spqrParamsOfV spqrVnToV spqrVnOfV spqrDirToV
  spqrDirOfV spqrChainToV spqrChainOfV spqrSplitEval spqrJoinEval ghostSplitEval ghostJoinEval
  e2eRecordExtras e2eEncodeSessionRecord spqrMsgPayloadSuffix spqrBraidSendEval
  spqrBraidRecvEval spqrNegotiateInitEval spqrChainFromVnEval spqrChainAddEpochEval
  spqrChainNextKeyEval costedFits_iff_fits costedOpsSizeHonest_of_opsSizeHonest
  costedSampSizeHonest_of_sampSizeHonest)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey SignalMessage IdentityKey
  GhostState ReceiverChain MessageKeyGenerator aesCbcDecrypt)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

/-! ## Block-size characterizations and list helpers -/

theorem blocks_pbytes_le_iff (ℓ : ℕ) (w : ℕ+) (x : SignalPqxdh.Bytes) (M : ℕ) :
    E2ESort.blocks ℓ (.pbytes w) x ≤ M ↔ x.length ≤ M * w := by
  have hw : 0 < (w : ℕ) := w.pos
  have hmul : (M + 1) * (w : ℕ) = M * w + w := by ring
  rw [E2ESort.blocks, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw, hmul]
  omega

theorem fits_pbytes_iff (ℓ : ℕ) (w : ℕ+) (M : ℕ) (x : SignalPqxdh.Bytes) :
    (PB (ℓ := ℓ) w).Fits M x ↔ x.length ≤ M * w :=
  blocks_pbytes_le_iff ℓ w x M

theorem blocks_bytes_le_iff (ℓ : ℕ) (w : ℕ+) (x : Bytes) (M : ℕ) :
    E2ESort.blocks ℓ (.bytes w) x ≤ M ↔ x.length ≤ M * w := by
  have hw : 0 < (w : ℕ) := w.pos
  have hmul : (M + 1) * (w : ℕ) = M * w + w := by ring
  rw [E2ESort.blocks, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw, hmul]
  omega

theorem fits_bytes_iff (ℓ : ℕ) (w : ℕ+) (M : ℕ) (x : Bytes) :
    (B (ℓ := ℓ) w).Fits M x ↔ x.length ≤ M * w :=
  blocks_bytes_le_iff ℓ w x M

private theorem fits_pbytes_take (ℓ : ℕ) (w : ℕ+) {K M : ℕ} (hKM : K ≤ M)
    (x : SignalPqxdh.Bytes) : (PB (ℓ := ℓ) w).Fits M (x.take ((w : ℕ) * K)) := by
  rw [fits_pbytes_iff]
  have hlen : (x.take ((w : ℕ) * K)).length ≤ (w : ℕ) * K := List.length_take_le _ x
  calc (x.take ((w : ℕ) * K)).length
      ≤ (w : ℕ) * K := hlen
    _ = K * (w : ℕ) := Nat.mul_comm _ _
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hKM

private theorem fits_bytes_take (ℓ : ℕ) (w : ℕ+) {K M : ℕ} (hKM : K ≤ M)
    (x : Bytes) : (B (ℓ := ℓ) w).Fits M (x.take ((w : ℕ) * K)) := by
  rw [fits_bytes_iff]
  have hlen : (x.take ((w : ℕ) * K)).length ≤ (w : ℕ) * K := List.length_take_le _ x
  calc (x.take ((w : ℕ) * K)).length
      ≤ (w : ℕ) * K := hlen
    _ = K * (w : ℕ) := Nat.mul_comm _ _
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hKM

private theorem fits_pbytes_of_len (ℓ : ℕ) (w : ℕ+) {M : ℕ} (hM : 1 ≤ M)
    {x : SignalPqxdh.Bytes} (hx : x.length ≤ (w : ℕ)) : (PB (ℓ := ℓ) w).Fits M x := by
  rw [fits_pbytes_iff]
  calc x.length ≤ 1 * (w : ℕ) := by omega
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hM

private theorem fits_bytes_of_len (ℓ : ℕ) (w : ℕ+) {M : ℕ} (hM : 1 ≤ M)
    {x : Bytes} (hx : x.length ≤ (w : ℕ)) : (B (ℓ := ℓ) w).Fits M x := by
  rw [fits_bytes_iff]
  calc x.length ≤ 1 * (w : ℕ) := by omega
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hM

private theorem bits_le_self {M : ℕ} (hM : 1 ≤ M) : bits M ≤ M :=
  bits_le_of_lt Nat.lt_two_pow_self hM

private theorem foldr_max_ge_init {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z : ℕ), z ≤ l.foldr (fun x acc => max acc (f x)) z
  | [], _ => le_rfl
  | _ :: xs, z => le_trans (foldr_max_ge_init f xs z) (le_max_left _ _)

private theorem foldr_max_mem_le {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z : ℕ) {x : α}, x ∈ l → f x ≤ l.foldr (fun y acc => max acc (f y)) z
  | [], _, _, hx => nomatch hx
  | y :: ys, z, x, hx => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact le_max_right _ _
    · exact le_trans (foldr_max_mem_le f ys z hmem) (le_max_left _ _)

private theorem foldr_max_le {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z M : ℕ), z ≤ M → (∀ x ∈ l, f x ≤ M) →
      l.foldr (fun x acc => max acc (f x)) z ≤ M
  | [], z, M, hz, _ => hz
  | x :: xs, z, M, hz, hxs => by
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨foldr_max_le f xs z M hz (fun y hy => hxs y (List.mem_cons_of_mem x hy)),
      hxs x List.mem_cons_self⟩

theorem splitSpqrPrev_fst_length_le :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).1.length ≤ fuel
  | 0, bs => by simp [splitSpqrPrev]
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · simp
    · have ih := splitSpqrPrev_fst_length_le fuel (bs.drop 36)
      simp only [List.length_cons]
      omega

theorem splitSpqrPrev_snd_length_le :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).2.length ≤ 35
  | 0, bs => by simp [splitSpqrPrev]
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · dsimp only; omega
    · exact splitSpqrPrev_snd_length_le fuel (bs.drop 36)

theorem splitSpqrPrev_fst_length_le_div36 :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).1.length ≤ bs.length / 36
  | 0, _ => Nat.zero_le _
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · simp
    · next hlt =>
      have hge : 36 ≤ bs.length := Nat.le_of_not_lt hlt
      have ih := splitSpqrPrev_fst_length_le_div36 fuel (bs.drop 36)
      rw [List.length_drop] at ih
      have hdiv : bs.length / 36 = (bs.length - 36) / 36 + 1 :=
        Nat.div_eq_sub_div (by decide) hge
      simp only [List.length_cons]
      omega

private theorem flatMap_prev_length :
    ∀ (entries : List (BitVec 32 × BitVec 256)),
      (entries.flatMap fun (idx, key) =>
        CryptoGames.HMAC.toBEBytes 4 idx ++ CryptoGames.HMAC.keyToBytes32 key).length =
        36 * entries.length
  | [] => rfl
  | (idx, key) :: rest => by
    have hhead : (CryptoGames.HMAC.toBEBytes 4 idx ++ CryptoGames.HMAC.keyToBytes32 key).length = 36 := by
      simp [CryptoGames.HMAC.toBEBytes, CryptoGames.HMAC.keyToBytes32]
    rw [List.flatMap_cons, List.length_append, hhead, flatMap_prev_length rest]
    simp only [List.length_cons]
    ring

theorem joinSpqrPrev_length_le (entries : List (BitVec 32 × BitVec 256)) (tail : Bytes) :
    (joinSpqrPrev entries tail).length ≤ 36 * entries.length + 35 := by
  simp only [joinSpqrPrev, List.length_append, flatMap_prev_length]
  have ht := List.length_take_le 35 tail
  omega

/-! ## `SampSizeHonest` for `e2eSamplers` -/

@[simp] theorem e2eSamplers_sDom_eq_unit (ℓ : ℕ) (s : (e2eSamplers ℓ).Samp) :
    (e2eSamplers ℓ).sDom s = .unit := rfl

/-- Size honesty of the shared coin-only sampler table `e2eSamplers ℓ`. -/
theorem e2eSamplers_sizeHonest (ℓ : ℕ) : SampSizeHonest (e2eSamplers ℓ) :=
  SampSizeHonest.unifSamplers (S := e2eSig ℓ) E2EUnifBase.sort E2EUnifBase.cost
    (fun b _ => by cases b <;> rfl)

/-! ## Helper bounds for wire, SPQR, and session-state ops -/

private theorem fits_hdrV (ℓ : ℕ) {M : ℕ} (hM : 1 ≤ M) (m : CryptoVerification.E2E.PreKeyMessageFields) :
    (hdrT (ℓ := ℓ)).Fits M (hdrV (e2eHdrOfPreKeyMsg m)) := by
  have hik : (vecU8 m.idPub).length ≤ 32 := by simp [vecU8, toU8]
  have hek : (vecU8 m.baseKey).length ≤ 32 := by simp [vecU8, toU8]
  have hct : (vecU8 m.kyberCt).length ≤ 1568 := by simp [vecU8, toU8]
  dsimp only [hdrV, e2eHdrOfPreKeyMsg]
  refine ⟨fits_pbytes_of_len ℓ 32 hM hik, fits_pbytes_of_len ℓ 32 hM hek, hM, ?_, hM,
    fits_pbytes_of_len ℓ 1568 hM hct⟩
  rcases m.opkId with _ | _
  · trivial
  · exact hM

private theorem fits_bytes_take48000 (ℓ : ℕ) {M : ℕ} (hM : 1500 ≤ M) (x : Bytes) :
    (B (ℓ := ℓ) 32).Fits M (x.take 48000) := by
  rw [fits_bytes_iff]
  have hlen : (x.take 48000).length ≤ 48000 := List.length_take_le 48000 x
  simp only [PNat.val_ofNat]
  omega

private theorem fits_bytes_take64000 (ℓ : ℕ) {M : ℕ} (hM : 2000 ≤ M) (x : Bytes) :
    (B (ℓ := ℓ) 32).Fits M (x.take 64000) := by
  rw [fits_bytes_iff]
  have hlen : (x.take 64000).length ≤ 64000 := List.length_take_le 64000 x
  simp only [PNat.val_ofNat]
  omega

private theorem e2eWireInnerBytes_length_le (c : Bytes) {inner : Bytes}
    (h : e2eWireInnerBytes c = some inner) : inner.length ≤ c.length := by
  unfold e2eWireInnerBytes at h
  rcases hm : e2eDecodePreKeyMsg c with _ | m
  · rw [hm] at h
    rcases c with _ | ⟨t, body⟩
    · simp at h
    · dsimp only at h
      split at h
      · injection h with h'; subst h'; simp
      · simp at h
  · rw [hm] at h
    injection h with h'; subst h'
    exact List.length_take_le c.length m.inner

private theorem e2ePartneredInnerBytes_length_le (bobAcc : Bool) (regIdA : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes) {inner : Bytes}
    (h : e2ePartneredInnerBytes bobAcc regIdA hdr c = some inner) : inner.length ≤ c.length := by
  unfold e2ePartneredInnerBytes at h
  split at h
  · rcases hm : e2eDecodePreKeyMsg c with _ | m
    · rw [hm] at h; simp at h
    · rw [hm] at h; dsimp only at h
      split at h
      · injection h with h'; subst h'; exact List.length_take_le c.length m.inner
      · simp at h
  · rcases hm : e2eDecodePreKeyMsg c with _ | m
    · rw [hm] at h
      rcases c with _ | ⟨t, body⟩
      · simp at h
      · dsimp only at h
        split at h
        · injection h with h'; subst h'; simp
        · simp at h
    · rw [hm] at h; dsimp only at h
      split at h
      · injection h with h'; subst h'; exact List.length_take_le c.length m.inner
      · simp at h

private theorem fits_spqrParamsToV (ℓ : ℕ) {M : ℕ} (hM : 1 ≤ M)
    (p : CryptoVerification.LibsignalSpqrV1.ChainParamsPB) :
    (spqrParamsT (ℓ := ℓ)).Fits M (spqrParamsToV p) :=
  ⟨hM, hM⟩

private theorem fits_spqrVnToV (ℓ : ℕ) {M : ℕ} (hM : 2 ≤ M)
    (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB) :
    (spqrVnT (ℓ := ℓ)).Fits M (spqrVnToV vn) := by
  have h1 : 1 ≤ M := by omega
  dsimp only [spqrVnToV]
  refine ⟨fits_bytes_take ℓ 32 (K := 2) hM vn.authKey, h1, h1, ?_⟩
  rcases vn.chainParams with _ | p
  · trivial
  · exact fits_spqrParamsToV ℓ h1 p

private theorem fits_spqrDirToV_of_bound (ℓ : ℕ) {M : ℕ} (hM : 2 ≤ M)
    {d : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB}
    (hd : (splitSpqrPrev 2201 d.prev).1.length ≤ M) :
    (spqrDirT (ℓ := ℓ)).Fits M (spqrDirToV d) := by
  have h1 : 1 ≤ M := by omega
  dsimp only [spqrDirToV]
  refine ⟨h1, fits_bytes_take ℓ 32 (K := 2) hM d.next, ⟨hd, fun e _ => ⟨h1, h1⟩⟩, ?_⟩
  exact fits_bytes_of_len ℓ 35 h1 (splitSpqrPrev_snd_length_le 2201 d.prev)

private theorem fits_spqrChainToV_2201 (ℓ : ℕ) {M : ℕ} (hM : 2201 ≤ M)
    (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    (spqrChainT (ℓ := ℓ)).Fits M (spqrChainToV c) := by
  have h1 : 1 ≤ M := by omega
  have h2 : 2 ≤ M := by omega
  dsimp only [spqrChainToV]
  refine ⟨h1, h1, ⟨?_, ?_⟩, fits_bytes_take ℓ 32 (K := 2) h2 c.nextRoot, h1, ?_⟩
  · simp only [List.length_map]
    exact le_trans (List.length_take_le 4 c.links) (by omega)
  · intro lk hlk
    simp only [List.mem_map] at hlk
    obtain ⟨orig, -, rfl⟩ := hlk
    constructor
    · rcases orig.send with _ | s
      · trivial
      · exact fits_spqrDirToV_of_bound ℓ h2
          (le_trans (splitSpqrPrev_fst_length_le 2201 s.prev) hM)
    · rcases orig.recv with _ | r
      · trivial
      · exact fits_spqrDirToV_of_bound ℓ h2
          (le_trans (splitSpqrPrev_fst_length_le 2201 r.prev) hM)
  · rcases c.params with _ | p
    · trivial
    · exact fits_spqrParamsToV ℓ h1 p

private theorem fits_ghostSplitEval (ℓ : ℕ) (M : ℕ) (g : GhostState Bytes)
    (hg : ghostStBlocks g ≤ M) :
    (ghostPartsT (ℓ := ℓ)).Fits (M + 16) (ghostSplitEval g) := by
  dsimp only [ghostStBlocks] at hg
  simp only [Nat.max_le] at hg
  obtain ⟨-, hpq, hrc, hce, hep⟩ := hg
  have h1 : 1 ≤ M + 16 := by omega
  have h2 : 2 ≤ M + 16 := by omega
  dsimp only [ghostSplitEval]
  refine ⟨trivial, h1, h2, ?_, h1, h1, trivial, by simp [Ty.Fits]; omega, ?_, ?_, ?_, ?_⟩
  · rcases g.session.remoteIdentity with _ | _
    · trivial
    · exact h2
  · refine ⟨le_trans (foldr_max_ge_init bits g.chainEpochs g.chainEpochs.length) (by omega), ?_⟩
    intro e he
    have := le_trans (foldr_max_mem_le bits g.chainEpochs g.chainEpochs.length he) hce
    simp only [Ty.Fits]; omega
  · rcases g.session.senderChain with _ | _
    · trivial
    · exact ⟨⟨h2, h1⟩, ⟨h1, h1⟩⟩
  · refine ⟨?_, ?_⟩
    · simp only [List.length_map]
      exact le_trans (List.length_take_le 5 g.session.receiverChains) (by omega)
    · intro rcV hrcV
      simp only [List.mem_map] at hrcV
      obtain ⟨rc, hrcTake, rfl⟩ := hrcV
      have hrcMem := List.mem_of_mem_take hrcTake
      refine ⟨h2, ?_, ?_⟩
      · rcases rc.chainKey with _ | _
        · trivial
        · exact ⟨h1, h1⟩
      · refine ⟨?_, fun mkV hmkV => ?_⟩
        · simp only [List.length_map]
          have hrcLe := le_trans (foldr_max_mem_le
            (fun rc : ReceiverChain => rc.messageKeys.foldr
              (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length)
            g.session.receiverChains g.session.receiverChains.length hrcMem) hrc
          have hmkInit := foldr_max_ge_init (fun mk : MessageKeyGenerator =>
            (mk.seed.length + 31) / 32) rc.messageKeys rc.messageKeys.length
          omega
        · simp only [List.mem_map] at hmkV
          obtain ⟨_, -, rfl⟩ := hmkV
          exact ⟨h1, h1⟩
  · change (g.session.pqRatchetState.length + 32 - 1) / 32 ≤ M + 16
    omega

private theorem fits_ghostJoinEval (ℓ : ℕ) (M : ℕ) (p : (ghostPartsT (ℓ := ℓ)).denote)
    (hp : (ghostPartsT (ℓ := ℓ)).Fits M p) :
    (GhostStT (ℓ := ℓ)).Fits (M + 16) (ghostJoinEval p) := by
  rcases p with ⟨isB, ver, locId, remId?, rk, prevCtr, pend, ep, cEps, sc?, rcs, pqSt⟩
  rcases hp with ⟨-, _, _, _, _, _, -, hep, hcEps, _, hrcs, hpqSt⟩
  dsimp only at hep hcEps hrcs hpqSt
  change ghostStBlocks (ghostJoinEval (isB, (ver, (locId, (remId?, (rk, (prevCtr,
    (pend, (ep, (cEps, (sc?, (rcs, pqSt)))))))))))) ≤ M + 16
  dsimp only [ghostStBlocks, ghostJoinEval]
  have hpq : (pqSt.length + 31) / 32 ≤ M + 16 := by
    change (pqSt.length + 32 - 1) / 32 ≤ M at hpqSt
    omega
  have hce : cEps.foldr (fun e acc => max acc (bits e)) cEps.length ≤ M + 16 := by
    apply foldr_max_le bits cEps cEps.length (M + 16) (by have := hcEps.1; omega)
    intro e he
    have := hcEps.2 e he
    simp only [Ty.Fits] at this
    omega
  simp only [Ty.Fits] at hep
  simp only [Nat.max_le]
  refine ⟨by omega, hpq, ?_, hce, by omega⟩
  apply foldr_max_le
    (fun rc : ReceiverChain => rc.messageKeys.foldr
      (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length)
    _ _ (M + 16)
    (by simp only [List.length_map]; exact le_trans (List.length_take_le 5 rcs) (by omega))
  intro rc hrcMem
  simp only [List.mem_map] at hrcMem
  obtain ⟨⟨srk, ck?, mks⟩, hTake, rfl⟩ := hrcMem
  have hMem := List.mem_of_mem_take hTake
  have hEntry := hrcs.2 (srk, (ck?, mks)) hMem
  have hlenMks : mks.length ≤ M := hEntry.2.2.1
  apply foldr_max_le (fun mk : MessageKeyGenerator => (mk.seed.length + 31) / 32)
    _ _ (M + 16) (by simp only [List.length_map]; omega)
  intro mk hmkMem
  simp only [List.mem_map] at hmkMem
  obtain ⟨⟨sd, ctr⟩, -, rfl⟩ := hmkMem
  have hlen : (CryptoGames.HMAC.keyToBytes32 sd).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  rw [hlen]
  omega

private theorem mem_snd_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | [], _, _, hp => by simp at hp
  | _, [], _, hp => by simp at hp
  | _ :: xs, y :: ys, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem y (mem_snd_of_mem_zip hmem)

private theorem fits_e2eEncodeSessionRecord (ℓ : ℕ) (M : ℕ)
    (inp : ((U32 (ℓ := ℓ)).denote × (U32 (ℓ := ℓ)).denote ×
      (U32 (ℓ := ℓ)).denote × (hdrT (ℓ := ℓ)).denote) × GhostState Bytes)
    (hinp : (Ty.prod (.prod U32 (.prod U32 (.prod U32 hdrT))) GhostStT).Fits M inp) :
    (BinStT (ℓ := ℓ)).Fits (M + 24576) (e2eEncodeSessionRecord inp) := by
  rcases inp with ⟨meta0, g⟩
  have hg : ghostStBlocks g ≤ M := hinp.2
  dsimp only [ghostStBlocks] at hg
  simp only [Nat.max_le] at hg
  obtain ⟨-, -, -, hce, hep⟩ := hg
  change binStBlocks (e2eEncodeSessionRecord (meta0, g)) ≤ M + 24576
  dsimp only [binStBlocks, e2eEncodeSessionRecord, binStateOfUnderExtras, EpochGhost.ofGhost]
  have hbBlk : (((CryptoVerification.E2E.encodeRecordUnderExtras
      (e2eRecordExtras meta0.1 meta0.2.1 meta0.2.2.1 (hdrOfV meta0.2.2.2)) g).take
      (32 * 24000)).length + 31) / 32 ≤ M + 24576 := by
    have ht := List.length_take_le (32 * 24000)
      (CryptoVerification.E2E.encodeRecordUnderExtras
        (e2eRecordExtras meta0.1 meta0.2.1 meta0.2.2.1 (hdrOfV meta0.2.2.2)) g)
    omega
  have hchBlk : ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).foldr
      (fun p acc => max acc (bits p.2))
      ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).length ≤ M + 24576 := by
    apply foldr_max_le (fun p : PublicKey × ℕ => bits p.2) _ _ (M + 24576)
    · rw [List.length_zip]
      have hinit := foldr_max_ge_init bits g.chainEpochs g.chainEpochs.length
      omega
    · intro p hp
      have hm := mem_snd_of_mem_zip hp
      have hle := le_trans (foldr_max_mem_le bits g.chainEpochs g.chainEpochs.length hm) hce
      omega
  simp only [Nat.max_le]
  exact ⟨by omega, hbBlk, hchBlk, by omega⟩

/-! ## `OpsSizeHonest` for `e2ePureOps` and `e2eCurveCheckOps` -/

theorem e2ePureOps_sizeHonest (ℓ : ℕ) : OpsSizeHonest (e2ePureOps ℓ) := by
  intro o x M hx
  cases o with
  | pbytesLit w v =>
    change (PB (ℓ := ℓ) w).Fits (M + (w + v.length)) v
    rw [fits_pbytes_iff]
    have hw : 1 ≤ (w : ℕ) := w.pos
    have h1 : v.length ≤ (M + ((w : ℕ) + v.length)) * 1 := by omega
    exact le_trans h1 (Nat.mul_le_mul_left _ hw)
  | pbytesCat m n =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * m := (fits_pbytes_iff ℓ m M x₁).1 hx.1
    have hx₂ : x₂.length ≤ M * n := (fits_pbytes_iff ℓ n M x₂).1 hx.2
    change (PB (ℓ := ℓ) (m + n)).Fits (M + (m + n)) (x₁ ++ x₂)
    rw [fits_pbytes_iff, List.length_append]
    simp only [PNat.add_coe]
    calc x₁.length + x₂.length
        ≤ M * (m : ℕ) + M * (n : ℕ) := by omega
      _ = M * ((m : ℕ) + n) := by ring
      _ ≤ (M + ((m : ℕ) + n)) * ((m : ℕ) + n) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | pbytesCons b w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ w M x).1 hx
    change (PB (ℓ := ℓ) (w + 1)).Fits (M + (w + 1)) (b :: x)
    rw [fits_pbytes_iff]
    simp only [List.length_cons, PNat.add_coe, PNat.val_ofNat]
    have : M * (w : ℕ) + 1 ≤ (M + ((w : ℕ) + 1)) * ((w : ℕ) + 1) := by nlinarith
    omega
  | pbytesWiden w d =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ w M x).1 hx
    change (PB (ℓ := ℓ) (w + d)).Fits (M + (w + d)) x
    rw [fits_pbytes_iff]
    simp only [PNat.add_coe]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + d)) * ((w : ℕ) + d) := by nlinarith
    omega
  | pbytesTakeK w k =>
    change (PB (ℓ := ℓ) k).Fits (M + (w + k)) (x.take k)
    rw [fits_pbytes_iff]
    have hlen : (x.take k).length ≤ (k : ℕ) := List.length_take_le k x
    have hk : 1 ≤ M + ((w : ℕ) + k) := by have := w.pos; omega
    calc (x.take k).length ≤ 1 * (k : ℕ) := by omega
      _ ≤ (M + ((w : ℕ) + k)) * k := Nat.mul_le_mul_right _ hk
  | pbytesTake w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_pbytes_iff ℓ w M s).1 hx.2
    change (PB (ℓ := ℓ) w).Fits (M + (w + 1)) (s.take n)
    rw [fits_pbytes_iff]
    have hlen : (s.take n).length ≤ s.length := List.length_take_le' n s
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pbytesDrop w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_pbytes_iff ℓ w M s).1 hx.2
    change (PB (ℓ := ℓ) w).Fits (M + (w + 1)) (s.drop n)
    rw [fits_pbytes_iff, List.length_drop]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pbytesLen w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ w M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have hx0 : x.length = 0 := by omega
      have h1 : bits 0 = 1 := rfl
      have hbw := one_le_bits w
      rw [hx0, h1]; omega
    · have h1 : bits x.length ≤ bits ((w : ℕ) * M) :=
        bits_mono (by rw [Nat.mul_comm]; exact hxw)
      have h2 := bits_mul w M
      have h3 := bits_le_self hM
      omega
  | bytesLit w v =>
    change (B (ℓ := ℓ) w).Fits (M + (w + v.length)) v
    rw [fits_bytes_iff]
    have hw : 1 ≤ (w : ℕ) := w.pos
    have h1 : v.length ≤ (M + ((w : ℕ) + v.length)) * 1 := by omega
    exact le_trans h1 (Nat.mul_le_mul_left _ hw)
  | bytesCat m n =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * m := (fits_bytes_iff ℓ m M x₁).1 hx.1
    have hx₂ : x₂.length ≤ M * n := (fits_bytes_iff ℓ n M x₂).1 hx.2
    change (B (ℓ := ℓ) (m + n)).Fits (M + (m + n)) (x₁ ++ x₂)
    rw [fits_bytes_iff, List.length_append]
    simp only [PNat.add_coe]
    calc x₁.length + x₂.length
        ≤ M * (m : ℕ) + M * (n : ℕ) := by omega
      _ = M * ((m : ℕ) + n) := by ring
      _ ≤ (M + ((m : ℕ) + n)) * ((m : ℕ) + n) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | bytesCons b w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ w M x).1 hx
    change (B (ℓ := ℓ) (w + 1)).Fits (M + (w + 1)) (b :: x)
    rw [fits_bytes_iff]
    simp only [List.length_cons, PNat.add_coe, PNat.val_ofNat]
    have : M * (w : ℕ) + 1 ≤ (M + ((w : ℕ) + 1)) * ((w : ℕ) + 1) := by nlinarith
    omega
  | bytesWiden w d =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ w M x).1 hx
    change (B (ℓ := ℓ) (w + d)).Fits (M + (w + d)) x
    rw [fits_bytes_iff]
    simp only [PNat.add_coe]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + d)) * ((w : ℕ) + d) := by nlinarith
    omega
  | bytesTakeK w k =>
    change (B (ℓ := ℓ) k).Fits (M + (w + k)) (x.take k)
    rw [fits_bytes_iff]
    have hlen : (x.take k).length ≤ (k : ℕ) := List.length_take_le k x
    have hk : 1 ≤ M + ((w : ℕ) + k) := by have := w.pos; omega
    calc (x.take k).length ≤ 1 * (k : ℕ) := by omega
      _ ≤ (M + ((w : ℕ) + k)) * k := Nat.mul_le_mul_right _ hk
  | bytesTake w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff ℓ w M s).1 hx.2
    change (B (ℓ := ℓ) w).Fits (M + (w + 1)) (s.take n)
    rw [fits_bytes_iff]
    have hlen : (s.take n).length ≤ s.length := List.length_take_le' n s
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesDrop w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff ℓ w M s).1 hx.2
    change (B (ℓ := ℓ) w).Fits (M + (w + 1)) (s.drop n)
    rw [fits_bytes_iff, List.length_drop]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesLen w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ w M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have hx0 : x.length = 0 := by omega
      have h1 : bits 0 = 1 := rfl
      have hbw := one_le_bits w
      rw [hx0, h1]; omega
    · have h1 : bits x.length ≤ bits ((w : ℕ) * M) :=
        bits_mono (by rw [Nat.mul_comm]; exact hxw)
      have h2 := bits_mul w M
      have h3 := bits_le_self hM
      omega
  | pbytesToBytes w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ w M x).1 hx
    change (B (ℓ := ℓ) w).Fits (M + w) (ofU8 x)
    rw [fits_bytes_iff]
    have hlen : (ofU8 x).length = x.length := by simp [ofU8]
    have : M * (w : ℕ) ≤ (M + (w : ℕ)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesToPbytes w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ w M x).1 hx
    change (PB (ℓ := ℓ) w).Fits (M + w) (toU8 x)
    rw [fits_pbytes_iff]
    have hlen : (toU8 x).length = x.length := by simp [toU8]
    have : M * (w : ℕ) ≤ (M + (w : ℕ)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pu32Lit _ | pu32OfNat | pu32ToU32 | u32ToPu32 | u8Lit _ | u8OfNat | u64Trunc8
  | u32Lit _ | u32OfNat | u32Add | u32Sub | u64Lit _ | u64OfNat | u64Add | u64Sub
  | bv256Lit _ | pbytesToBv256 | bytesToBv256 | bv512Lit _ | idKeyOfPbytes | pkOfPbytes
  | plainDefault =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits, E2ESort.blocks]
    omega
  | pu32ToNat =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 32 := bits_le_of_lt x.toBitVec.isLt (by omega)
    omega
  | u8ToNat =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 8 := bits_le_of_lt x.isLt (by omega)
    omega
  | u32ToNat =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 32 := bits_le_of_lt x.isLt (by omega)
    omega
  | u64ToNat =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 64 := bits_le_of_lt x.isLt (by omega)
    omega
  | finVal n =>
    dsimp only [e2ePureOps, E2EPureOp.dom, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost,
      Ty.Fits, E2ESort.blocks] at hx ⊢
    omega
  | u32BeBytes =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_bytes_of_len ℓ 4 (by omega)
    simp [CryptoGames.HMAC.toBEBytes]
  | bv256ToPbytes32 =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_pbytes_of_len ℓ 32 (by omega)
    simp [SignalPqxdh.word256ToBytes]
  | bv256ToBytes32 =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_bytes_of_len ℓ 32 (by omega)
    simp [CryptoGames.HMAC.keyToBytes32]
  | bv512ToBytes64 =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_bytes_of_len ℓ 64 (by omega)
    simp [CryptoVerification.LibsignalSpqrV1.coinBytes_length]
  | idKeySerialize =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_bytes_of_len ℓ 33 (by omega)
    simp [IdentityKey.serialize, PublicKey.serialize]
  | pkSerialize =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    apply fits_bytes_of_len ℓ 33 (by omega)
    simp [PublicKey.serialize]
  | pkDeserialize =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases (PublicKey.deserialize x).toOption with _ | _
    · trivial
    · dsimp only [Ty.Fits, E2ESort.blocks]; omega
  | plainToBytes =>
    change (B (ℓ := ℓ) 32).Fits (M + (ℓ / 32 + 2)) x.toList
    rw [fits_bytes_iff]
    simp only [List.Vector.toList_length, PNat.val_ofNat]
    omega
  | bytesToPlain =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    split
    · dsimp only [Ty.Fits, E2ESort.blocks]; omega
    · trivial
  | parsePreKeyWire =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases e2eDecodePreKeyMsg x with _ | m
    · trivial
    · dsimp only [Option.map]
      have h1 : 1 ≤ M + 96 := by omega
      refine ⟨h1, fits_hdrV ℓ h1 m, ?_⟩
      rw [fits_bytes_iff]
      have ht := List.length_take_le x.length m.inner
      simp only [PNat.val_ofNat] at hxc ⊢
      omega
  | partneredInnerBytes =>
    rcases x with ⟨bobAcc, regIdA, hdr, c⟩
    have hcc : c.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M c).1 hx.2.2.2
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases h : e2ePartneredInnerBytes bobAcc regIdA (hdrOfV hdr) c with _ | inner
    · trivial
    · change (B (ℓ := ℓ) 32).Fits (M + 128) inner
      rw [fits_bytes_iff]
      have hlen := e2ePartneredInnerBytes_length_le bobAcc regIdA (hdrOfV hdr) c h
      simp only [PNat.val_ofNat] at hcc ⊢
      omega
  | wireInnerBytes =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases h : e2eWireInnerBytes x with _ | inner
    · trivial
    · change (B (ℓ := ℓ) 32).Fits (M + 96) inner
      rw [fits_bytes_iff]
      have hlen := e2eWireInnerBytes_length_le x h
      simp only [PNat.val_ofNat] at hxc ⊢
      omega
  | splitWhisperWire =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases x with _ | ⟨t, body⟩
    · trivial
    · dsimp only
      split
      · change (B (ℓ := ℓ) 32).Fits (M + 2) body
        rw [fits_bytes_iff]
        simp only [List.length_cons, PNat.val_ofNat] at hxc ⊢
        omega
      · trivial
  | signalMsgParse =>
    have hxb : x.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases SignalMessage.tryFrom protoSignalCodec x with _ | m
    · trivial
    · have h1 : 1 ≤ M + (ℓ / 32 + 18) := by omega
      have h2 : 2 ≤ M + (ℓ / 32 + 18) := by omega
      have hslice : ∀ s : Bytes, (B (ℓ := ℓ) 32).Fits (M + (ℓ / 32 + 18)) (s.take x.length) := by
        intro s
        rw [fits_bytes_iff]
        have ht := List.length_take_le x.length s
        simp only [PNat.val_ofNat] at hxb ⊢
        omega
      refine ⟨⟨h1, h2, h1, h1⟩, hslice m.ciphertext, hslice m.pqRatchet, ?_⟩
      rcases m.addresses with _ | addr
      · trivial
      · exact hslice addr
  | wrapWhisperWire =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    split
    · rw [fits_bytes_iff]; simp
    · exact fits_bytes_take ℓ 32 (K := 2 * (ℓ / 32) + 26) (by omega) _
  | wrapPreKeyWire =>
    rcases x with ⟨regIdA, hdr, inner⟩
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    split
    · rw [fits_bytes_iff]; simp
    · exact fits_bytes_take ℓ 32 (K := 2 * (ℓ / 32) + 84) (by omega) _
  | spqrParsePreamble =>
    have hxm : x.length ≤ M * 32 := (fits_bytes_iff ℓ 32 M x).1 hx
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    rcases CryptoVerification.LibsignalSpqrV1.msgPreamble x with _ | p
    · trivial
    · have h1 : 1 ≤ M + 4 := by omega
      dsimp only [Option.map]
      refine ⟨h1, h1, h1, ?_⟩
      rw [fits_bytes_iff]
      have ht := List.length_take_le x.length p.remaining
      simp only [PNat.val_ofNat] at hxm ⊢
      omega
  | spqrAssembleMsg =>
    rcases x with ⟨ep, idx, sfx⟩
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    exact fits_bytes_take ℓ 32 (K := 3) (by omega)
      (CryptoVerification.LibsignalSpqrV1.encode_varint (idx.zeroExtend 64)
        (CryptoVerification.LibsignalSpqrV1.encode_varint ep [1#8]) ++ sfx.take 64)
  | spqrStateSplit =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost, spqrSplitEval]
    rcases CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState x with _ | st
    · trivial
    · dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rcases st.inner with _ | ⟨⟨v⟩⟩
        · trivial
        · dsimp only [Option.map]
          exact fits_bytes_take64000 ℓ (by omega) (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v)
      · rcases st.versionNegotiation with _ | vn
        · trivial
        · dsimp only [Option.map]
          exact fits_spqrVnToV ℓ (by omega) vn
      · rcases st.chain with _ | c
        · trivial
        · dsimp only [Option.map]
          exact fits_spqrChainToV_2201 ℓ (by omega) c
  | spqrStateJoin =>
    dsimp only [e2ePureOps, E2EPureOp.cod, E2EPureOp.eval, E2EPureOp.cost]
    exact fits_bytes_take ℓ 32 (K := 11000) (by omega) _
  | ghostStateSplit =>
    exact fits_ghostSplitEval ℓ M x hx
  | ghostStateJoin =>
    exact fits_ghostJoinEval ℓ M x hx
  | encodeSessionRecord =>
    exact fits_e2eEncodeSessionRecord ℓ M x hx
  | pbytesEq _ _ | bytesEq _ _ | bytesLtOp _ _ | pu32Eq | u8Eq | u8Lt | u32Eq | u32Lt
  | u64Eq | u64Lt | finEq _ | bv128Eq | bv256Eq | idKeyEq | pkEq | plainEq
  | checkShortCiphertext | isValidSignalWire =>
    trivial

theorem e2eCurveCheckOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2eCurveCheckOps ℓ decT encT) := by
  intro o _ _ _
  cases o <;> trivial

/-! ## `OpsSizeHonest` for `e2eCryptoOps` and combined tables -/

private theorem linksFromPb_prev_bound {ℓ : ℕ} {M : ℕ} :
    ∀ {pbs : List ((spqrEpochLinkT (ℓ := ℓ)).denote)}
      {links : List CryptoVerification.LibsignalSpqrV1.ChainEpoch},
      (∀ p ∈ pbs, (spqrEpochLinkT (ℓ := ℓ)).Fits M p) →
      CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb
        (pbs.map fun (s?, r?) =>
          ({ send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV } :
            CryptoVerification.LibsignalSpqrV1.ChainEpochPB)) = .ok links →
      ∀ lk ∈ links,
        lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35
  | [], _, _, hok, lk, hlk => by
    simp [CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb] at hok
    subst hok; simp at hlk
  | (s?, r?) :: rest, _, hpbs, hok, lk, hlk => by
    simp only [List.map_cons, CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb] at hok
    rcases s? with _ | sv
    · simp [Bind.bind, Except.bind] at hok
    · rcases r? with _ | rv
      · rcases heq : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.fromPb
            (spqrDirOfV sv) with _ | _ <;>
          simp [heq, Bind.bind, Except.bind] at hok
      · simp only [Option.map_some, Bind.bind, Except.bind, Pure.pure, Except.pure] at hok
        rcases hs : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.fromPb
            (spqrDirOfV sv) with _ | sendCed
        · rw [hs] at hok; simp at hok
        · rw [hs] at hok; dsimp only at hok
          rcases hr : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.fromPb
              (spqrDirOfV rv) with _ | recvCed
          · rw [hr] at hok; simp at hok
          · rw [hr] at hok; dsimp only at hok
            rcases ht : CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb
                (rest.map fun (s?, r?) =>
                  { send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV }) with _ | tail
            · rw [ht] at hok; simp at hok
            · rw [ht] at hok; dsimp only at hok
              injection hok with hEq; subst hEq
              rcases List.mem_cons.1 hlk with rfl | hmem
              · have hhead := hpbs (some sv, some rv) List.mem_cons_self
                have hsEq : sendCed.prev.data = (spqrDirOfV sv).prev := by
                  unfold CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.fromPb at hs
                  split at hs
                  · simp at hs
                  · injection hs with hs'; rw [← hs']
                have hrEq : recvCed.prev.data = (spqrDirOfV rv).prev := by
                  unfold CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.fromPb at hr
                  split at hr
                  · simp at hr
                  · injection hr with hr'; rw [← hr']
                have hsvLen : sv.2.2.1.length ≤ M := hhead.1.2.2.1.1
                have hrvLen : rv.2.2.1.length ≤ M := hhead.2.2.2.1.1
                have hsJ := joinSpqrPrev_length_le sv.2.2.1 sv.2.2.2
                have hrJ := joinSpqrPrev_length_le rv.2.2.1 rv.2.2.2
                simp only [spqrDirOfV] at hsEq hrEq
                rw [hsEq, hrEq]
                exact ⟨by omega, by omega⟩
              · exact linksFromPb_prev_bound
                  (fun p hp => hpbs p (List.mem_cons_of_mem _ hp)) ht lk hmem

private theorem fits_spqrChainFromVnEval (ℓ : ℕ) (M : ℕ) (F : ShaCompress)
    (vn : (spqrVnT (ℓ := ℓ)).denote) :
    (Ty.opt (spqrChainT (ℓ := ℓ))).Fits (M + 16) (spqrChainFromVnEval F vn) := by
  unfold spqrChainFromVnEval CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
  rcases CryptoVerification.LibsignalSpqrV1.Direction.fromI32? (spqrVnOfV vn).direction with _ | dir
  · trivial
  · simp only [Bind.bind, Except.bind]
    rcases (spqrVnOfV vn).chainParams with _ | params
    · trivial
    · simp only [CryptoVerification.LibsignalSpqrV1.Chain.new,
        CryptoVerification.LibsignalSpqrV1.Chain.intoPb,
        CryptoVerification.LibsignalSpqrV1.Chain.cedForDirection,
        CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.new,
        CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.intoPb,
        CryptoVerification.LibsignalSpqrV1.KeyHistory.new]
      have h1 : 1 ≤ M + 16 := by omega
      have h2 : 2 ≤ M + 16 := by omega
      dsimp only [spqrChainToV]
      refine ⟨h1, h1, ⟨by simp, ?_⟩, fits_bytes_take ℓ 32 (K := 2) h2 _, h1, ⟨h1, h1⟩⟩
      intro lk hlk
      dsimp only [List.take, List.map] at hlk
      simp only [List.mem_singleton] at hlk
      subst hlk
      have hdir : ∀ nextBytes : Bytes,
          (spqrDirT (ℓ := ℓ)).Fits (M + 16)
            (spqrDirToV { ctr := 0#32, next := nextBytes, prev := [] }) :=
        fun nextBytes => fits_spqrDirToV_of_bound ℓ h2 (by simp [splitSpqrPrev])
      exact ⟨hdir _, hdir _⟩

private theorem fits_spqrChainAddEpochEval (ℓ : ℕ) (M : ℕ) (F : ShaCompress)
    (ch : (spqrChainT (ℓ := ℓ)).denote) (ep : BitVec 64) (sec : BitVec 256)
    (hch : (spqrChainT (ℓ := ℓ)).Fits M ch) :
    (Ty.prod .bool (.opt (spqrChainT (ℓ := ℓ)))).Fits (M + 24)
      (spqrChainAddEpochEval F ch ep sec) := by
  refine ⟨trivial, ?_⟩
  unfold spqrChainAddEpochEval
  rcases hfrom : CryptoVerification.LibsignalSpqrV1.Chain.fromPb (spqrChainOfV ch) with _ | c0
  · trivial
  · dsimp only
    rcases hadd : c0.addEpoch (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F)
        ⟨ep, CryptoGames.HMAC.keyToBytes32 sec⟩ with _ | c1
    · trivial
    · dsimp only
      have hc0Links : ∀ lk ∈ c0.links,
          lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35 := by
        unfold CryptoVerification.LibsignalSpqrV1.Chain.fromPb at hfrom
        rcases hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32? (spqrChainOfV ch).direction
          with _ | d
        · rw [hd] at hfrom; simp [Bind.bind, Except.bind] at hfrom
        · rw [hd] at hfrom
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hfrom
          rcases hlinks : CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb
              (spqrChainOfV ch).links with _ | ls
          · rw [hlinks] at hfrom; simp at hfrom
          · rw [hlinks] at hfrom; dsimp only at hfrom
            rcases hp : (spqrChainOfV ch).params with _ | p
            · rw [hp] at hfrom; simp at hfrom
            · rw [hp] at hfrom; dsimp only at hfrom
              injection hfrom with hc0Eq; subst hc0Eq
              exact linksFromPb_prev_bound hch.2.2.1.2 hlinks
      have hc1Links : ∀ lk ∈ c1.links,
          lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35 := by
        unfold CryptoVerification.LibsignalSpqrV1.Chain.addEpoch at hadd
        split at hadd
        · simp at hadd
        · split at hadd
          · simp at hadd
          · injection hadd with hc1Eq; subst hc1Eq
            intro lk hlk
            rcases List.mem_append.1 hlk with hmem | hnew
            · exact hc0Links lk hmem
            · simp only [List.mem_singleton] at hnew
              subst hnew
              simp [CryptoVerification.LibsignalSpqrV1.Chain.cedForDirection,
                CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.new,
                CryptoVerification.LibsignalSpqrV1.KeyHistory.new]
      have h1 : 1 ≤ M + 24 := by omega
      have h2 : 2 ≤ M + 24 := by omega
      dsimp only [spqrChainToV]
      refine ⟨h1, h1, ⟨?_, ?_⟩, fits_bytes_take ℓ 32 (K := 2) h2 _, h1, ?_⟩
      · simp only [List.length_map]
        exact le_trans (List.length_take_le 4 c1.intoPb.links) (by omega)
      · intro lkV hlkV
        simp only [List.mem_map] at hlkV
        obtain ⟨lkPb, hlkTake, rfl⟩ := hlkV
        have hlkIn := List.mem_of_mem_take hlkTake
        simp only [CryptoVerification.LibsignalSpqrV1.Chain.intoPb, List.mem_map] at hlkIn
        obtain ⟨lk, hlkMem, rfl⟩ := hlkIn
        obtain ⟨hsLen, hrLen⟩ := hc1Links lk hlkMem
        have hsDiv : (splitSpqrPrev 2201 lk.send.intoPb.prev).1.length ≤ M + 24 := by
          have h1 := splitSpqrPrev_fst_length_le_div36 2201 lk.send.intoPb.prev
          simp only [CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.intoPb] at h1 ⊢
          omega
        have hrDiv : (splitSpqrPrev 2201 lk.recv.intoPb.prev).1.length ≤ M + 24 := by
          have h1 := splitSpqrPrev_fst_length_le_div36 2201 lk.recv.intoPb.prev
          simp only [CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.intoPb] at h1 ⊢
          omega
        exact ⟨fits_spqrDirToV_of_bound ℓ h2 hsDiv, fits_spqrDirToV_of_bound ℓ h2 hrDiv⟩
      · rcases c1.intoPb.params with _ | p
        · trivial
        · exact fits_spqrParamsToV ℓ h1 p

theorem e2eCryptoOps_sizeHonest (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) :
    OpsSizeHonest (e2eCryptoOps ℓ P C K) := by
  intro o x M hx
  cases o with
  | x25519 =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_pbytes_take ℓ 32 (K := 1) (by omega) _
  | x25519Base =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_pbytes_take ℓ 32 (K := 1) (by omega) _
  | pow8 =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_pbytes_take ℓ 32 (K := 1) (by omega) _
  | sigSign =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_pbytes_take ℓ 64 (K := 1) (by omega) _
  | kemKeyGen =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    have h1 : 1 ≤ M + 160 := by omega
    exact ⟨fits_pbytes_take ℓ 1568 (K := 1) h1 _, fits_pbytes_take ℓ 3168 (K := 1) h1 _⟩
  | kemEncaps =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    rcases P.kemEncaps x.1 x.2 with _ | ⟨ss, ct⟩
    · trivial
    · have h1 : 1 ≤ M + 160 := by omega
      exact ⟨fits_pbytes_take ℓ 32 (K := 1) h1 ss, fits_pbytes_take ℓ 1568 (K := 1) h1 ct⟩
  | kemDecaps =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    rcases P.kemDecaps x.1 x.2 with _ | ss
    · trivial
    · exact fits_pbytes_take ℓ 32 (K := 1) (by omega) ss
  | hkdfDerive96 =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    have h1 : 1 ≤ M + 16 := by omega
    exact ⟨fits_pbytes_take ℓ 32 (K := 1) h1 _,
      fits_pbytes_take ℓ 32 (K := 1) h1 _,
      fits_pbytes_take ℓ 32 (K := 1) h1 _⟩
  | sessionKeyPairGen =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost,
      Ty.Fits, E2ESort.blocks]
    omega
  | sessionRootCreateChain =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    rcases CryptoGames.LibsignalSession.rootCreateChain C x.1 x.2.1
        ⟨CryptoGames.Ratchet.keyToBytesVec32 x.2.2⟩ with _ | ⟨_, _⟩
    · trivial
    · dsimp only [Ty.Fits, E2ESort.blocks]; omega
  | chainStep =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    rcases CryptoGames.LibsignalSession.ChainKey.nextChainKey C.F
        { key := x.1, index := x.2 } with _ | _
    · trivial
    · dsimp only [Ty.Fits, E2ESort.blocks]; omega
  | deriveMsgKeys =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost,
      Ty.Fits, E2ESort.blocks]
    omega
  | aes256CbcEnc =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_bytes_take ℓ 32 (K := ℓ / 32 + 2) (by omega) _
  | aes256CbcDec =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    rcases aesCbcDecrypt C.D x.1 x.2.1 x.2.2 with _ | ptBytes
    · trivial
    · dsimp only [Option.map, Ty.Fits, E2ESort.blocks]; omega
  | signalMsgEncode =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_bytes_take ℓ 32 (K := 2 * (ℓ / 32) + 24) (by omega) _
  | spqrV1InitOp =>
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    exact fits_bytes_take ℓ 32 (K := 16) (by omega) _
  | spqrNegotiateInit =>
    rcases x with ⟨verByte, dirI32, authKey⟩
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    unfold spqrNegotiateInitEval
    rcases CryptoVerification.LibsignalSpqrV1.Version.fromU8? verByte with _ | v
    · exact ⟨trivial, trivial⟩
    · dsimp only
      rcases CryptoVerification.LibsignalSpqrV1.Direction.fromI32? dirI32 with _ | dir
      · exact ⟨trivial, trivial⟩
      · dsimp only
        rcases CryptoVerification.LibsignalSpqrV1.initInner
            (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) v dir authKey with _ | pb?
        · exact ⟨trivial, trivial⟩
        · dsimp only
          rcases pb? with _ | pb
          · exact ⟨trivial, trivial⟩
          · dsimp only [Option.map]
            exact ⟨trivial, fits_bytes_take48000 ℓ (by omega) pb.encodeRaw⟩
  | spqrBraidSend =>
    rcases x with ⟨v1Raw, coins⟩
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    unfold spqrBraidSendEval
    rcases CryptoVerification.LibsignalSpqrV1.V1State.decode v1Raw with _ | pb
    · exact ⟨trivial, trivial⟩
    · dsimp only
      rcases CryptoVerification.LibsignalSpqrV1.States.from_pb
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          (CryptoVerification.LibsignalSpqrV1.spqrAuthApi C.F) pb with ⟨_ | _⟩ | st0
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, trivial⟩
      · dsimp only
        rcases st0.send K (CryptoVerification.LibsignalSpqrV1.coinBytes coins)
            with ⟨_ | _⟩ | ⟨sOut, _⟩
        · exact ⟨trivial, trivial⟩
        · exact ⟨trivial, trivial⟩
        · dsimp only
          have h1 : 1 ≤ M + 3072 := by omega
          refine ⟨trivial, fits_bytes_take64000 ℓ (by omega) _, h1, ?_, ?_⟩
          · rcases sOut.key with _ | _
            · trivial
            · exact ⟨h1, h1⟩
          · apply fits_bytes_of_len ℓ 64 h1
            unfold spqrMsgPayloadSuffix
            exact List.length_take_le 64 _
  | spqrBraidRecv =>
    rcases x with ⟨v1Raw, msgEpoch, rem⟩
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    unfold spqrBraidRecvEval
    rcases CryptoVerification.LibsignalSpqrV1.Message.deserialize
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi msgEpoch rem with _ | sckaMsg
    · exact ⟨trivial, trivial, trivial⟩
    · dsimp only
      rcases CryptoVerification.LibsignalSpqrV1.V1State.decode v1Raw with _ | pb
      · exact ⟨trivial, trivial, trivial⟩
      · dsimp only
        rcases CryptoVerification.LibsignalSpqrV1.States.from_pb
            CryptoVerification.LibsignalSpqrV1.spqrPolyApi
            (CryptoVerification.LibsignalSpqrV1.spqrAuthApi C.F) pb with ⟨_ | _⟩ | st0
        · exact ⟨trivial, trivial, trivial⟩
        · exact ⟨trivial, trivial, trivial⟩
        · dsimp only
          rcases st0.recv K sckaMsg with ⟨_ | _⟩ | rOut
          · exact ⟨trivial, trivial, trivial⟩
          · exact ⟨trivial, trivial, trivial⟩
          · dsimp only
            have h1 : 1 ≤ M + 3072 := by omega
            refine ⟨trivial, trivial, ?_, fits_bytes_take64000 ℓ (by omega) _⟩
            rcases rOut.key with _ | _
            · trivial
            · exact ⟨h1, h1⟩
  | spqrChainFromVn =>
    exact fits_spqrChainFromVnEval ℓ M C.F x
  | spqrChainAddEpoch =>
    rcases x with ⟨ch, ep, sec⟩
    exact fits_spqrChainAddEpochEval ℓ M C.F ch ep sec hx.1
  | spqrChainNextKey =>
    rcases x with ⟨next, ctr⟩
    dsimp only [e2eCryptoOps, E2ECryptoOp.cod, E2ECryptoOp.eval, E2ECryptoOp.cost]
    refine ⟨trivial, ?_⟩
    unfold spqrChainNextKeyEval
    rcases CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal
        (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F) next ctr with _ | ⟨next', _, idx, mkB⟩
    · trivial
    · have h1 : 1 ≤ M + 12 := by omega
      exact ⟨fits_bytes_take ℓ 32 (K := 1) h1 next', h1, h1⟩
  | isCanonical | sigVerify | signalMsgVerifyMac =>
    trivial

theorem e2ePrimOps_sizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2ePrimOps ℓ P C K decT encT) :=
  OpsSizeHonest.sum (e2eCurveCheckOps_sizeHonest ℓ decT encT) (e2eCryptoOps_sizeHonest ℓ P C K)

theorem e2eAdapterOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2eAdapterOps ℓ decT encT) :=
  OpsSizeHonest.sum (e2ePureOps_sizeHonest ℓ) (e2eCurveCheckOps_sizeHonest ℓ decT encT)

/-- Size honesty of the full E2E composition op table `e2eOps ℓ P C K decT encT`. -/
theorem e2eOps_sizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2eOps ℓ P C K decT encT) :=
  OpsSizeHonest.sum (e2ePureOps_sizeHonest ℓ) (e2ePrimOps_sizeHonest ℓ P C K decT encT)

/-! ## Codec and value-encoding roundtrip identities -/

@[simp] theorem drKeyOfV_drKeyV {ℓ : ℕ} (k : SignalPqxdh.DRKey) :
    drKeyOfV (drKeyV (ℓ := ℓ) k) = k := by
  cases k; rfl

@[simp] theorem drKeyV_drKeyOfV {ℓ : ℕ} (v : (drKeyT (ℓ := ℓ)).denote) :
    drKeyV (ℓ := ℓ) (drKeyOfV (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _⟩; rfl

@[simp] theorem bundleOfV_bundleV {ℓ : ℕ} (b : SignalPqxdh.PreKeyBundleInput) :
    bundleOfV (bundleV (ℓ := ℓ) b) = b := by
  cases b; rfl

@[simp] theorem bundleV_bundleOfV {ℓ : ℕ} (v : (bundleT (ℓ := ℓ)).denote) :
    bundleV (ℓ := ℓ) (bundleOfV (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _, _, _, _, _, _⟩; rfl

@[simp] theorem hdrOfV_hdrV {ℓ : ℕ} (h : SignalPqxdh.HandshakeHdr) :
    hdrOfV (hdrV (ℓ := ℓ) h) = h := by
  cases h; rfl

@[simp] theorem hdrV_hdrOfV {ℓ : ℕ} (v : (hdrT (ℓ := ℓ)).denote) :
    hdrV (ℓ := ℓ) (hdrOfV (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _, _, _, _⟩; rfl

@[simp] theorem sidOfV_sidV {ℓ : ℕ} {S : SignalPqxdh.Setup} (sid : SignalPqxdh.SessionId S) :
    sidOfV (sidV (ℓ := ℓ) sid) = sid := by
  cases sid <;> rfl

@[simp] theorem sidV_sidOfV {ℓ : ℕ} {S : SignalPqxdh.Setup} (v : (sidT (ℓ := ℓ) S).denote) :
    sidV (ℓ := ℓ) (sidOfV (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> rfl

@[simp] theorem keyIndQdec_keyIndQenc {ℓ : ℕ} {S : SignalPqxdh.Setup}
    (q : SignalPqxdh.KeyIndQuery S) :
    keyIndQdec (keyIndQenc (ℓ := ℓ) q) = q := by
  cases q <;> simp [keyIndQenc, keyIndQdec]

@[simp] theorem keyIndQenc_keyIndQdec {ℓ : ℕ} {S : SignalPqxdh.Setup}
    (v : (keyIndQT (ℓ := ℓ) S).denote) :
    keyIndQenc (ℓ := ℓ) (keyIndQdec (ℓ := ℓ) v) = v := by
  rcases v with u | u | ⟨u, j⟩ | ⟨u, j, o⟩ | ⟨u, i, b⟩ | ⟨u, i, b⟩ | ⟨k, j, o, h⟩ |
    ⟨k, j, l, h⟩ | sid | sec | ⟨⟩ | sid | sk | ⟨u, j⟩ <;>
    simp [keyIndQenc, keyIndQdec]

@[simp] theorem keyIndRdec_keyIndRenc {ℓ : ℕ} (r : SignalPqxdh.KeyIndResponse) :
    keyIndRdec (keyIndRenc (ℓ := ℓ) r) = r := by
  cases r <;> simp [keyIndRenc, keyIndRdec]

@[simp] theorem keyIndRenc_keyIndRdec {ℓ : ℕ} (v : (keyIndRT (ℓ := ℓ)).denote) :
    keyIndRenc (ℓ := ℓ) (keyIndRdec (ℓ := ℓ) v) = v := by
  rcases v with ⟨⟩ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _ | _ | ⟨_, _⟩ | ⟨⟩ | _ | ⟨_, _, _, _⟩ | _ <;>
    simp [keyIndRenc, keyIndRdec]

@[simp] theorem recvResultDec_recvResultEnc {ℓ : ℕ} (r : CryptoGames.SM.RecvResult (Plain ℓ)) :
    recvResultDec (recvResultEnc r) = r := by
  cases r <;> rfl

@[simp] theorem recvResultEnc_recvResultDec {ℓ : ℕ} (v : (recvResultT (ℓ := ℓ)).denote) :
    recvResultEnc (recvResultDec (ℓ := ℓ) v) = v := by
  rcases v with ⟨⟩ | ⟨_, _, _⟩ <;> rfl

@[simp] theorem boolToParty_partyToBool (p : Party) : boolToParty (partyToBool p) = p := by
  cases p <;> rfl

@[simp] theorem partyToBool_boolToParty (b : Bool) : partyToBool (boolToParty b) = b := by
  cases b <;> rfl

/-! ## `CostedFits`, `CostedOpsSizeHonest`, and `CostedSampSizeHonest` bridges -/

theorem e2eCostedFits_iff (ℓ B : ℕ) (t : Ty (e2eSig ℓ)) (x : t.denote) :
    CostedFits B t x ↔ t.Fits B x :=
  costedFits_iff_fits B t x

theorem e2eSamplers_costedSizeHonest (ℓ : ℕ) : CostedSampSizeHonest (e2eSamplers ℓ) :=
  costedSampSizeHonest_of_sampSizeHonest (e2eSamplers_sizeHonest ℓ)

theorem e2ePureOps_costedSizeHonest (ℓ : ℕ) : CostedOpsSizeHonest (e2ePureOps ℓ) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2ePureOps_sizeHonest ℓ)

theorem e2eCurveCheckOps_costedSizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2eCurveCheckOps ℓ decT encT) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2eCurveCheckOps_sizeHonest ℓ decT encT)

theorem e2eCryptoOps_costedSizeHonest (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) :
    CostedOpsSizeHonest (e2eCryptoOps ℓ P C K) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2eCryptoOps_sizeHonest ℓ P C K)

theorem e2ePrimOps_costedSizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2ePrimOps ℓ P C K decT encT) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2ePrimOps_sizeHonest ℓ P C K decT encT)

theorem e2eAdapterOps_costedSizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2eAdapterOps ℓ decT encT) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2eAdapterOps_sizeHonest ℓ decT encT)

theorem e2eOps_costedSizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2eOps ℓ P C K decT encT) :=
  costedOpsSizeHonest_of_opsSizeHonest (e2eOps_sizeHonest ℓ P C K decT encT)

/-! ## `Expr.op` smart constructors -/

def adapterPureOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ (o.dom ℓ)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (o.cod ℓ) :=
  Expr.op (O := e2eAdapterOps ℓ decT encT) (Sum.inl o) a

@[simp] theorem eval_adapterPureOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ (o.dom ℓ)) (env : Env Γ) :
    (adapterPureOp o a).eval env = o.eval ℓ (a.eval env) := rfl

@[simp] theorem cost_adapterPureOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ (o.dom ℓ)) :
    (adapterPureOp o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem e2ePureOps_opSize (ℓ : ℕ) (o : E2EPureOp) :
    (e2ePureOps ℓ).opSize o = o.opSize := rfl

@[simp] theorem e2eAdapterOps_opSize_inl (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (o : E2EPureOp) :
    (e2eAdapterOps ℓ decT encT).opSize (.inl o) = o.opSize := rfl

@[simp] theorem e2eAdapterOps_opSize_inr (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (o : E2ECurveCheckOp) :
    (e2eAdapterOps ℓ decT encT).opSize (.inr o) = 0 := rfl

@[simp] theorem e2eOps_opSize_inl (ℓ : ℕ) {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (o : E2EPureOp) :
    (e2eOps ℓ P C K decT encT).opSize (.inl o) = o.opSize := rfl

@[simp] theorem e2eOps_opSize_inr (ℓ : ℕ) {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (o : (e2ePrimOps ℓ P C K decT encT).Op) :
    (e2eOps ℓ P C K decT encT).opSize (.inr o) = 0 := by
  cases o <;> rfl

@[simp] theorem size_adapterPureOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ (o.dom ℓ)) :
    (adapterPureOp o a).size = a.size + o.opSize + 1 := rfl

def adapterCurveOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).cod o) :=
  Expr.op (O := e2eAdapterOps ℓ decT encT) (Sum.inr o) a

@[simp] theorem eval_adapterCurveOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) (env : Env Γ) :
    (adapterCurveOp o a).eval env = (e2eCurveCheckOps ℓ decT encT).eval o (a.eval env) := rfl

@[simp] theorem cost_adapterCurveOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    (adapterCurveOp o a).cost = a.cost + (e2eCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem size_adapterCurveOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    (adapterCurveOp o a).size = a.size + 1 := rfl

def e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    Expr (e2eOps ℓ P C K decT encT) Γ (o.cod ℓ) :=
  Expr.op (O := e2eOps ℓ P C K decT encT) (Sum.inl o) a

@[simp] theorem eval_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) (env : Env Γ) :
    (e2ePureOp o a).eval env = o.eval ℓ (a.eval env) := rfl

@[simp] theorem cost_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2ePureOp o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem size_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2ePureOp o a).size = a.size + o.opSize + 1 := rfl

def e2eCurveOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).cod o) :=
  Expr.op (O := e2eOps ℓ P C K decT encT) (Sum.inr (Sum.inl o)) a

@[simp] theorem eval_e2eCurveOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) (env : Env Γ) :
    (e2eCurveOp o a).eval env = (e2eCurveCheckOps ℓ decT encT).eval o (a.eval env) := rfl

@[simp] theorem cost_e2eCurveOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    (e2eCurveOp o a).cost = a.cost + (e2eCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem size_e2eCurveOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECurveCheckOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCurveCheckOps ℓ decT encT).dom o)) :
    (e2eCurveOp o a).size = a.size + 1 := rfl

def e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    Expr (e2eOps ℓ P C K decT encT) Γ (o.cod ℓ) :=
  Expr.op (O := e2eOps ℓ P C K decT encT) (Sum.inr (Sum.inr o)) a

@[simp] theorem eval_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) (env : Env Γ) :
    (e2eCryptoOp o a).eval env = o.eval ℓ P C K (a.eval env) := rfl

@[simp] theorem cost_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2eCryptoOp o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem size_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2eCryptoOp o a).size = a.size + 1 := rfl

/-! ## `L_bh` `.cr` handler arm and cost -/

/-- Per-instance metadata stored by `L_bh` in `σ.1`:
`((regIdA, (regIdB, (bobRemoteRegId, hdr))), bobAccepted)`. -/
@[reducible] def adapterInstMetaT {ℓ : ℕ} : Ty (e2eSig ℓ) :=
  .prod (.prod U32 (.prod U32 (.prod U32 hdrT))) .bool

/-- State layout of `L_bh` over a driver-mirror state type `drvMirrorT`:
`(instMetaTbl, (aliceAckedTbl, drvMirror))`. -/
@[reducible] def adapterStateTy {ℓ : ℕ} (drvMirrorT : Ty (e2eSig ℓ)) : Ty (e2eSig ℓ) :=
  .prod (.tbl (.opt adapterInstMetaT)) (.prod (.tbl .bool) drvMirrorT)

@[reducible] def adapterNoneSmRespExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Ctl Pt : Type}
    {unStart : Ctl → SignalPqxdh.SessionId S}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} :
    Expr (e2eAdapterOps ℓ decT encT) Γ (e2eAdapterCodec S ℓ unStart).R :=
  .inr (.pair .none (.pair .none .none))

@[reducible] def adapterCrCtx (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl : Type}
    (unStart : Ctl → SignalPqxdh.SessionId S) (drvMirrorT : Ty (e2eSig ℓ)) :
    List (Ty (e2eSig ℓ)) :=
  [.bool,
   .sum (.prod .bool (B 32)) .bool,
   .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
   .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
     (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
   .prod .nat smQT,
   adapterStateTy drvMirrorT,
   (e2eAdapterCodec S ℓ unStart).Q]

/-- `Comp` AST of `L_bh`'s `.cr` (`corrupt`) handler arm over `e2eAdapterOps` and
`e2eAdapterIface`. -/
def adapterCrArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl Pt : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl)
    (unStart : Ctl → SignalPqxdh.SessionId S)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drvMirrorT : Ty (e2eSig ℓ)) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eAdapterIface S ℓ mkStart)
      (adapterCrCtx S ℓ unStart drvMirrorT)
      (.prod (e2eAdapterCodec S ℓ unStart).R (adapterStateTy drvMirrorT)) :=
  .caseOpt (.tget (.fst .v5) (.fst .v4))
    (.ret (.pair adapterNoneSmRespExpr .v5))
    (.bind (.query E2EAdapterTag.cr (.pair (.fst .v5) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr
          (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
        (.ret (.pair
          (.inr (.pair .none (.pair .none
            (.some (adapterPureOp .encodeSessionRecord (.pair (.fst .v2) .v0))))))
          (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))

/-- Right-spine wrapper placing `adapterCrArm` under the 5 `caseSum` dispatches from
`[σ, (e2eAdapterCodec S ℓ unStart).Q]` to `.cr`. -/
def adapterCrSpine (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl Pt : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl)
    (unStart : Ctl → SignalPqxdh.SessionId S)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drvMirrorT : Ty (e2eSig ℓ)) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eAdapterIface S ℓ mkStart)
      [adapterStateTy drvMirrorT, (e2eAdapterCodec S ℓ unStart).Q]
      (.prod (e2eAdapterCodec S ℓ unStart).R (adapterStateTy drvMirrorT)) :=
  .caseSum (.var (.succ .zero))
    (.ret (.pair adapterNoneSmRespExpr .v1))
    (.caseSum (.snd .v0)
      (.ret (.pair adapterNoneSmRespExpr .v2))
      (.caseSum .v0
        (.ret (.pair adapterNoneSmRespExpr .v3))
        (.caseSum .v0
          (.ret (.pair adapterNoneSmRespExpr .v4))
          (.caseSum .v0
            (.ret (.pair adapterNoneSmRespExpr .v5))
            (adapterCrArm S ℓ mkStart unStart decT encT drvMirrorT)))))

@[simp] theorem e2ePureOp_cost_encodeSessionRecord (ℓ : ℕ) :
    E2EPureOp.encodeSessionRecord.cost ℓ = 24576 := rfl

theorem adapterCrArm_cost (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl Pt : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl)
    (unStart : Ctl → SignalPqxdh.SessionId S)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drvMirrorT : Ty (e2eSig ℓ)) :
    (adapterCrArm S ℓ mkStart unStart decT encT drvMirrorT).cost = 56665 := by
  simp only [adapterCrArm, adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp,
    e2ePureOp_cost_encodeSessionRecord, Expr.v0, Expr.v1, Expr.v2, Expr.v4, Expr.v5]
  omega

theorem adapterCrSpine_total_cost (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl Pt : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl)
    (unStart : Ctl → SignalPqxdh.SessionId S)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drvMirrorT : Ty (e2eSig ℓ)) :
    (adapterCrSpine S ℓ mkStart unStart decT encT drvMirrorT).cost +
      (e2eAdapterCodec S ℓ unStart).codecCost ≤ 56740 := by
  have hcc : (e2eAdapterCodec S ℓ unStart).codecCost ≤ 64 := by dsimp [e2eAdapterCodec]; omega
  simp only [adapterCrSpine, adapterCrArm_cost, adapterNoneSmRespExpr, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

@[simp] theorem adapterCrArm_size (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl Pt : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl)
    (unStart : Ctl → SignalPqxdh.SessionId S)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drvMirrorT : Ty (e2eSig ℓ)) :
    (adapterCrArm S ℓ mkStart unStart decT encT drvMirrorT).size = 46 := by
  simp only [adapterCrArm, adapterNoneSmRespExpr, size_adapterPureOp, E2EPureOp.opSize,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4, Expr.v5]

end Computational.Proofs.E2E.Dsl.TablesHonest
