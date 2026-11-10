/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewSpqr
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf

/-!
# Pure SPQR V1 Chain-Key Salt Extraction

Proves receive-side salt extraction on Bob's initial `spqrInitB` state in direction `b2a`
(`spqr_hkdfExtract_eq_hmacWith_spqrSaltBytes_sem`) and lifts `.ok` receive steps from
`spqrV1WithMac` to SPQR models that map empty raw keys to `none`
(`spqrV1WithMacEmptyAsNone_recv_of_spqrV1WithMac_recv_ok`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed.Refinement (PreKeyFields OpaqueSymbolSemantics)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.SHARED.SpqrBytes (spqrInitB spqrChainKeyOf)
open Symbolic.Swarm.SHARED.HookAuth (HmacFn hmacFnOf mlkemOf spqrV1WithMac spqrV1RecvWithMac)

/-! ## Initial Chain Key Extraction -/

private theorem spqrIdxOfBytes?_spqrLeBytes4_eq (idx : BitVec 32) :
    Symbolic.Swarm.SHARED.SpqrBytes.spqrIdxOfBytes?
      (Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4 idx) = some idx := by
  simp only [Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4,
    Symbolic.Swarm.SHARED.SpqrBytes.spqrIdxOfBytes?, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 4294967296 := idx.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (idx.toNat % 256 + idx.toNat / 256 % 256 * 256 +
    idx.toNat / 65536 % 256 * 65536 + idx.toNat / 16777216 % 256 * 16777216) % 4294967296 = idx.toNat
  have hd1 : idx.toNat / 65536 = idx.toNat / 256 / 256 := by rw [Nat.div_div_eq_div_mul]
  have hd2 : idx.toNat / 16777216 = idx.toNat / 65536 / 256 := by rw [Nat.div_div_eq_div_mul]
  have hm0 := Nat.mod_add_div idx.toNat 256
  have hm1 := Nat.mod_add_div (idx.toNat / 256) 256
  have hm2 := Nat.mod_add_div (idx.toNat / 65536) 256
  rw [← hd1] at hm1; rw [← hd2] at hm2
  have hm3 : idx.toNat / 16777216 % 256 = idx.toNat / 16777216 := Nat.mod_eq_of_lt (by omega)
  rw [hm3]
  have hsum : idx.toNat % 256 + idx.toNat / 256 % 256 * 256 +
      idx.toNat / 65536 % 256 * 65536 + idx.toNat / 16777216 * 16777216 = idx.toNat := by omega
  rw [hsum, Nat.mod_eq_of_lt hlt]

private def b2aChain0 (F : ShaCompress) (k : HwBytes) : CryptoVerification.LibsignalSpqrV1.Chain :=
  let genr8r := CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F (List.replicate 32 0#8) k
    CryptoVerification.LibsignalSpqrV1.chainStartInfo 96
  { dir := .b2a
    currentEpoch := 0#64
    sendEpoch := 0#64
    links := [{ send := CryptoVerification.LibsignalSpqrV1.Chain.cedForDirection genr8r .b2a
                recv := CryptoVerification.LibsignalSpqrV1.Chain.cedForDirection genr8r .a2b }]
    nextRoot := genr8r.take 32
    params := CryptoVerification.LibsignalSpqrV1.DEFAULT_CHAIN_PARAMS.intoPb }

private theorem spqrChainKeyB_b2a_eq (F : ShaCompress) (k : HwBytes) (idx : BitVec 32) :
    Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyB F k [0#8]
      (Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4 idx) =
      match (b2aChain0 F k).recvKey (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) 0#64 idx with
      | .ok (_, key) => key
      | .error _ => [] := by
  unfold Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyB
  rw [show Symbolic.Swarm.SHARED.SpqrBytes.spqrDirOfParams? [0#8] = some .a2b from rfl,
    spqrIdxOfBytes?_spqrLeBytes4_eq]
  rfl

private theorem msgDeserialize_epoch_eq (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (mac : HmacFn)
    (ep : CryptoVerification.LibsignalSpqrV1.Epoch) (rem : HwBytes)
    (m : CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi)
    (h : (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac).msgDeserialize ep rem = .ok m) :
    m.epoch = ep := by
  dsimp only [Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize] at h
  cases rem with
  | nil => nomatch h
  | cons b0 rest =>
    dsimp only at h
    cases htry : CryptoVerification.LibsignalSpqrV1.MessageType.tryFromU8 b0 <;>
      rw [htry] at h <;> dsimp only at h
    · nomatch h
    · rename_i msgType
      cases msgType <;> dsimp only [Bind.bind, Except.bind] at h
      · injection h with h; subst h; rfl
      · cases hd : CryptoVerification.LibsignalSpqrV1.decode_chunk
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi rest <;> rw [hd] at h <;> dsimp only at h
        · nomatch h
        · injection h with h; subst h; rfl
      · cases hd : CryptoVerification.LibsignalSpqrV1.decode_chunk
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi rest <;> rw [hd] at h <;> dsimp only at h
        · nomatch h
        · injection h with h; subst h; rfl
      · cases hd : CryptoVerification.LibsignalSpqrV1.decode_chunk
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi rest <;> rw [hd] at h <;> dsimp only at h
        · nomatch h
        · injection h with h; subst h; rfl
      · injection h with h; subst h; rfl
      · cases hd : CryptoVerification.LibsignalSpqrV1.decode_chunk
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi rest <;> rw [hd] at h <;> dsimp only at h
        · nomatch h
        · injection h with h; subst h; rfl
      · cases hd : CryptoVerification.LibsignalSpqrV1.decode_chunk
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi rest <;> rw [hd] at h <;> dsimp only at h
        · nomatch h
        · injection h with h; subst h; rfl

private theorem statesRecv_noHeaderReceived_key (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (mac : HmacFn)
    (state : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi
      (Symbolic.Swarm.SHARED.HookAuth.spqrAuthApiWithMac F mac))
    (m : CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi)
    (key : Option CryptoVerification.LibsignalSpqrV1.EpochSecret)
    (st1 : CryptoVerification.LibsignalSpqrV1.States
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi
      (Symbolic.Swarm.SHARED.HookAuth.spqrAuthApiWithMac F mac))
    (h : (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac).statesRecv
      (.noHeaderReceived state) m = .ok (key, st1)) :
    m.epoch ≤ state.epoch ∧ key = none := by
  dsimp only [Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac,
    CryptoVerification.LibsignalSpqrV1.States.recv] at h
  by_cases hgt : m.epoch > state.epoch
  · simp [hgt] at h
  · refine ⟨BitVec.not_lt.mp hgt, ?_⟩
    simp only [hgt, ↓reduceIte] at h
    by_cases hlt : m.epoch < state.epoch
    · simp only [hlt, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1.symm
    · simp only [hlt, ↓reduceIte] at h
      cases hpay : m.payload <;> rw [hpay] at h <;> dsimp only [Bind.bind, Except.bind] at h
      case hdr chunk =>
        cases hchunk : state.recv_hdr_chunk m.epoch chunk <;> rw [hchunk] at h <;> dsimp only at h
        · rename_i se; cases se <;> nomatch h
        · rename_i res; cases res <;> dsimp only at h <;>
          (injection h with h; exact (Prod.mk.inj h).1.symm)
      all_goals injection h with h; exact (Prod.mk.inj h).1.symm

private theorem b2a_recv_ok_rawKey
    (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (mac : HmacFn)
    (pqr msg : HwBytes) (r : CryptoVerification.LibsignalSpqrV1.Recv)
    (pre : CryptoVerification.LibsignalSpqrV1.MsgPreamble)
    (hpqr_len : pqr.length = 32)
    (hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble msg = .ok pre)
    (htop : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac)
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F)
      (spqrInitB F K mac pqr [1#8]) msg = .ok r) :
    ∃ (c' : CryptoVerification.LibsignalSpqrV1.Chain) (rawKey : HwBytes),
      (b2aChain0 F pqr).recvKey (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) 0#64 pre.index =
        .ok (c', rawKey) ∧
      (r.key = some rawKey ∨ (rawKey.isEmpty = true ∧ r.key = none)) := by
  unfold CryptoVerification.LibsignalSpqrV1.recv at htop
  rw [hpre, decodeState_spqrInitB_b2a_eq F K mac hpqr_len] at htop
  dsimp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind,
    CryptoVerification.LibsignalSpqrV1.stateVersion,
    CryptoVerification.LibsignalSpqrV1.Version.toU8] at htop
  have hminv : (b0VnPb pqr).minVersion.truncate 8 = 1#8 := rfl
  simp only [hminv] at htop
  by_cases hlt : pre.version < 1#8
  · simp [hlt] at htop
  · simp only [hlt, ↓reduceIte] at htop
    have hmis : (pre.version != 1#8 && !true) = false := by simp
    have hcv0 : (1#8 == 0#8) = false := rfl
    rw [hmis, hcv0] at htop; simp only [Bool.false_eq_true, ↓reduceIte] at htop
    by_cases hgt : pre.version > 1#8
    · simp only [hgt, ↓reduceIte] at htop
      have hcf : CryptoVerification.LibsignalSpqrV1.chainFrom
          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) none (some (b0VnPb pqr)) =
          .ok (b2aChain0 F pqr) := rfl
      rw [hcf] at htop
      dsimp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind] at htop
      cases hrec : (b2aChain0 F pqr).recvKey
          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) 0#64 pre.index with
      | error ce =>
        rw [hrec] at htop
        cases ce <;> nomatch htop
      | ok cp =>
        rcases cp with ⟨chain1, rawKey⟩
        rw [hrec] at htop; injection htop with htop; subst htop
        exact ⟨chain1, rawKey, rfl, Or.inl rfl⟩
    · simp only [hgt, ↓reduceIte] at htop
      have heq : (pre.version == 1#8) = true := by
        simp only [beq_iff_eq]
        exact BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      rw [heq] at htop
      dsimp only [↓reduceIte, Pure.pure, Except.pure, Bind.bind, Except.bind] at htop
      cases hdeser : (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac).msgDeserialize
          pre.epoch pre.remaining with
      | error _ => rw [hdeser] at htop; nomatch htop
      | ok sckaMsg =>
        rw [hdeser] at htop; dsimp only at htop
        have hfrom : (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac).statesFromPb
            (b0V1StatePb F pqr) =
          .ok (.noHeaderReceived
            { uc := { epoch := 1#64, auth := CryptoVerification.LibsignalSpqrV1.Authenticator.new F pqr 1#64 }
              receiving_hdr := { ptsNeeded := 48, pts := (List.replicate 16 (CryptoVerification.LibsignalSpqrV1.SortedSetPt.withCapacity 0)), isComplete := false } }) := rfl
        rw [hfrom] at htop; dsimp only at htop
        cases hstRecv : (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac).statesRecv
            (.noHeaderReceived
              { uc := { epoch := 1#64, auth := CryptoVerification.LibsignalSpqrV1.Authenticator.new F pqr 1#64 }
                receiving_hdr := { ptsNeeded := 48, pts := (List.replicate 16 (CryptoVerification.LibsignalSpqrV1.SortedSetPt.withCapacity 0)), isComplete := false } })
            sckaMsg with
        | error _ => rw [hstRecv] at htop; nomatch htop
        | ok ks =>
          rcases ks with ⟨key, st1⟩
          rw [hstRecv] at htop; dsimp only at htop
          have hmsgEp := msgDeserialize_epoch_eq F K mac pre.epoch pre.remaining sckaMsg hdeser
          have ⟨hle1, hkeyNone⟩ := statesRecv_noHeaderReceived_key F K mac _ sckaMsg key st1 hstRecv
          subst hkeyNone
          by_cases hep0 : (pre.epoch == 0#64) = true
          · simp [hep0] at htop
          · simp only [hep0, Bool.false_eq_true, ↓reduceIte] at htop
            have hep1 : pre.epoch = 1#64 := by
              have hne0 : pre.epoch ≠ 0#64 := by simpa using hep0
              have hle : pre.epoch ≤ 1#64 := hmsgEp ▸ hle1
              apply BitVec.eq_of_toNat_eq
              have hne0' : pre.epoch.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
              have hle' : pre.epoch.toNat ≤ 1 := BitVec.le_def.mp hle
              change pre.epoch.toNat ≤ 1 at hle'; change pre.epoch.toNat = 1; omega
            have hcf : CryptoVerification.LibsignalSpqrV1.chainFrom
                (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) none (some (b0VnPb pqr)) =
                .ok (b2aChain0 F pqr) := rfl
            rw [hcf, hep1] at htop
            dsimp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError] at htop
            have hsub : (1#64 - 1#64 : BitVec 64) = 0#64 := rfl
            rw [hsub] at htop
            cases hrec : (b2aChain0 F pqr).recvKey
                (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) 0#64 pre.index with
            | error ce =>
              rw [hrec] at htop
              cases ce <;> nomatch htop
            | ok cp =>
              rcases cp with ⟨chain2, msgKey⟩
              rw [hrec] at htop; injection htop with htop; subst htop
              by_cases hemp : msgKey.isEmpty = true
              · exact ⟨chain2, msgKey, rfl, Or.inr ⟨hemp, by simp [hemp]⟩⟩
              · have hempF : msgKey.isEmpty = false := Bool.eq_false_iff.mpr hemp
                exact ⟨chain2, msgKey, rfl, Or.inl (by simp [hempF])⟩

/-! ## Preamble Index and Salt Equivalence -/

private theorem decodeVarintLoop_eq_refinement_spqrVarintAux (i : Nat) (out : BitVec 64) (bs : HwBytes) :
    CryptoVerification.LibsignalSpqrV1.decodeVarintLoop i out bs =
      DY.Libsignal.PQXDH.Refinement.spqrVarintAux i out bs := by
  induction bs generalizing i out with
  | nil => rfl
  | cons b rest ih =>
    simp only [CryptoVerification.LibsignalSpqrV1.decodeVarintLoop,
      DY.Libsignal.PQXDH.Refinement.spqrVarintAux,
      CryptoVerification.LibsignalSpqrV1.MAX_VARINT_BYTES_LEN,
      DY.Libsignal.PQXDH.Refinement.spqrMaxVarintBytes]
    split
    · rfl
    · by_cases h10 : i + 1 = 10 <;> simp [h10, ih]

private theorem spqrIdx_of_msgPreamble_ok (p : PreKeyFields)
    (pre : CryptoVerification.LibsignalSpqrV1.MsgPreamble)
    (hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble p.inner.pqRatchet = .ok pre) :
    DY.Libsignal.Composed.Refinement.preKeySpqrIndex p = UInt32.ofNat pre.index.toNat := by
  unfold DY.Libsignal.Composed.Refinement.preKeySpqrIndex
  revert hpre
  cases h : p.inner.pqRatchet with
  | nil =>
    intro hpre
    simp [CryptoVerification.LibsignalSpqrV1.msgPreamble,
      CryptoVerification.LibsignalSpqrV1.msg_preamble,
      DY.Libsignal.PQXDH.Refinement.msgPreamble?] at hpre ⊢
    cases hpre; rfl
  | cons version rest =>
    simp only [CryptoVerification.LibsignalSpqrV1.msgPreamble,
      CryptoVerification.LibsignalSpqrV1.msg_preamble,
      CryptoVerification.LibsignalSpqrV1.decode_varint,
      DY.Libsignal.PQXDH.Refinement.msgPreamble?,
      DY.Libsignal.PQXDH.Refinement.spqrDecodeVarint,
      decodeVarintLoop_eq_refinement_spqrVarintAux]
    cases DY.Libsignal.PQXDH.Refinement.spqrVarintAux 0 0#64 rest with
    | none => intro hpre; cases hpre
    | some epRest =>
      rcases epRest with ⟨epoch, rest1⟩
      by_cases hEp : epoch = 0#64
      · simp [hEp, Bind.bind, Except.bind]
      · simp only [hEp, ↓reduceIte, Bind.bind, Except.bind]
        cases DY.Libsignal.PQXDH.Refinement.spqrVarintAux 0 0#64 rest1 with
        | none => intro hpre; cases hpre
        | some idxRest =>
          rcases idxRest with ⟨index64, rest2⟩
          by_cases hIdx : index64.toNat < 2 ^ 32
          · simp only [hIdx, ↓reduceIte]
            intro hpre; cases hpre; rfl
          · simp only [hIdx, ↓reduceIte]
            intro hpre; cases hpre

private theorem bitvec32_shiftRight_setWidth8_eq (idx : BitVec 32) (n : Nat) (hn : n < 4294967296) :
    (idx >>> BitVec.ofNat 32 n).setWidth 8 = BitVec.ofNat 8 (idx.toNat >>> n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hn]

private theorem spqrIdxBytes_ofNat_eq_spqrLeBytes4 (idx : BitVec 32) :
    TR.spqrIdxBytes (UInt32.ofNat idx.toNat) =
      Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4 idx := by
  have hidx : UInt32.ofNat idx.toNat = ⟨idx⟩ := by
    ext; simp
  rw [hidx]
  change [idx.setWidth 8, (idx >>> 8#32).setWidth 8, (idx >>> 16#32).setWidth 8, (idx >>> 24#32).setWidth 8] =
    [idx.truncate 8, BitVec.ofNat 8 (idx.toNat >>> 8), BitVec.ofNat 8 (idx.toNat >>> 16), BitVec.ofNat 8 (idx.toNat >>> 24)]
  rw [bitvec32_shiftRight_setWidth8_eq idx 8 (by decide),
    bitvec32_shiftRight_setWidth8_eq idx 16 (by decide),
    bitvec32_shiftRight_setWidth8_eq idx 24 (by decide)]

private theorem salt_bytes_eq_spqrKeyBytes
    {rKey : Option HwBytes} {rawKey : HwBytes} {saltVal : CryptoGames.HKDF.Salt}
    (hsalt : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? rKey = some saltVal)
    (hkey_cases : rKey = some rawKey ∨ (rawKey.isEmpty = true ∧ rKey = none)) :
    (saltVal.map List.Vector.toList).getD (List.replicate 32 0) = spqrKeyBytes rawKey := by
  rcases hkey_cases with hsome | ⟨hemp, hnone⟩
  · rw [hsome] at hsalt
    unfold CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? at hsalt
    split at hsalt
    · rename_i hnil_some
      injection hnil_some with hnil
      subst hnil
      injection hsalt with hsalt; subst hsalt
      rfl
    · dsimp only [CryptoVerification.LibsignalSpqrV1.messageKeyToSalt?] at hsalt
      split at hsalt
      · rename_i hlen32
        injection hsalt with hsalt; subst hsalt
        exact (Symbolic.Swarm.TRREF.SpqrSemOf.spqrKeyBytes_of_length_32 hlen32).symm
      · nomatch hsalt
  · rw [hnone] at hsalt
    injection hsalt with hsalt; subst hsalt
    have hnil : rawKey = [] := List.isEmpty_iff.mp hemp
    subst hnil
    rfl

theorem spqr_hkdfExtract_eq_hmacWith_spqrSaltBytes_sem
    (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (hS_ck : S.chainKey = spqrChainKeyOf interpretation)
    (p : PreKeyFields) (pqr newPqrState : HwBytes) (pqrKey : CryptoGames.HKDF.Salt) (seed : HwBytes)
    (hpqr_len : pqr.length = 32)
    (hspqr : (spqrV1WithMac (sha256CompressFunction interpretation)
      (mlkemOf interpretation) (hmacFnOf interpretation)).recv
      (spqrInitB (sha256CompressFunction interpretation)
        (mlkemOf interpretation) (hmacFnOf interpretation) pqr [1#8])
      p.inner.pqRatchet = .ok (newPqrState, pqrKey)) :
    CryptoGames.HKDF.hkdfExtract (sha256CompressFunction interpretation) pqrKey seed =
      CryptoGames.HMAC.hmacWith (sha256CompressFunction interpretation)
        (TR.spqrSaltBytes S pqr (DY.Libsignal.Composed.Refinement.preKeySpqrIndex p)) seed := by
  set F := sha256CompressFunction interpretation
  set K := mlkemOf interpretation
  set mac := hmacFnOf interpretation
  have hspqr' := hspqr
  clear hspqr
  unfold spqrV1WithMac CryptoVerification.LibsignalSpqrV1.toSpqrModel at hspqr'
  dsimp only at hspqr'
  cases htop : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac)
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F)
      (spqrInitB F K mac pqr [1#8]) p.inner.pqRatchet with
  | error e =>
    rw [htop] at hspqr'; cases e <;> nomatch hspqr'
  | ok r =>
    rw [htop] at hspqr'; dsimp only at hspqr'
    cases hsalt : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? r.key with
    | none => rw [hsalt] at hspqr'; nomatch hspqr'
    | some saltVal =>
      rw [hsalt] at hspqr'; injection hspqr' with hpair
      have hsalt_eq : saltVal = pqrKey := (Prod.mk.inj hpair).2
      subst hsalt_eq
      clear hpair
      cases hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble p.inner.pqRatchet with
      | error _ =>
        unfold CryptoVerification.LibsignalSpqrV1.recv at htop
        simp [hpre, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind] at htop
      | ok pre =>
        obtain ⟨c', rawKey, hrec, hkey_cases⟩ :=
          b2a_recv_ok_rawKey F K mac pqr p.inner.pqRatchet r pre hpqr_len hpre htop
        clear htop
        have hck_eq : Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyB F pqr [0#8]
            (Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4 pre.index) = rawKey := by
          rw [spqrChainKeyB_b2a_eq, hrec]
        have hs_eq : TR.spqrSaltBytes S pqr (DY.Libsignal.Composed.Refinement.preKeySpqrIndex p) =
            spqrKeyBytes rawKey := by
          rw [spqrIdx_of_msgPreamble_ok p pre hpre]
          unfold TR.spqrSaltBytes
          by_cases hidx0 : UInt32.ofNat pre.index.toNat = 0
          · simp only [hidx0, ↓reduceIte]
            have hpre0 : pre.index = 0#32 := by
              have h0 : BitVec.ofNat 32 pre.index.toNat = 0#32 := congrArg UInt32.toBitVec hidx0
              simpa using h0
            have hck0 : Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyB F pqr [0#8]
                (Symbolic.Swarm.SHARED.SpqrBytes.spqrLeBytes4 0#32) = [] := rfl
            rw [hpre0, hck0] at hck_eq
            subst hck_eq; rfl
          · simp only [hidx0, ↓reduceIte, hS_ck, spqrChainKeyOf, spqrIdxBytes_ofNat_eq_spqrLeBytes4]
            exact congrArg spqrKeyBytes hck_eq
        rw [hs_eq, ← CryptoVerification.LibsignalSpqrV1.hkdfExtractBytes_of_salt]
        unfold CryptoVerification.LibsignalSpqrV1.hkdfExtractBytes
        rw [salt_bytes_eq_spqrKeyBytes hsalt hkey_cases]

/-! ## Empty-Key Salt Lift -/

theorem emptyAsNoneSalt_of_recvKeyToSalt?_some {key? : Option HwBytes}
    {salt : CryptoGames.HKDF.Salt} :
    CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? key? = some salt →
    (match key? with
     | some k => if hk : k.length = 32 then some ⟨k, hk⟩ else none
     | none => none) = salt := by
  intro h
  rcases key? with _ | (_ | ⟨b, bs⟩)
  · simp [CryptoVerification.LibsignalSpqrV1.recvKeyToSalt?,
      CryptoVerification.LibsignalSpqrV1.messageKeyToSalt?] at h
    simp [← h]
  · simp [CryptoVerification.LibsignalSpqrV1.recvKeyToSalt?] at h
    simp [← h]
  · have hne : (some (b :: bs) = (some ([] : HwBytes))) = False := by simp
    unfold CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? at h
    simp only [hne, ↓reduceIte, CryptoVerification.LibsignalSpqrV1.messageKeyToSalt?] at h
    by_cases hlen : (b :: bs).length = 32
    · simp only [hlen, ↓reduceDIte, Option.some.injEq] at h ⊢
      exact h
    · simp only [hlen, ↓reduceDIte] at h
      nomatch h

theorem spqrV1WithMacEmptyAsNone_recv_of_spqrV1WithMac_recv_ok
    {F : ShaCompress} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {mac : HmacFn}
    {S' : CryptoGames.LibsignalSession.Spqr HwBytes HwBytes}
    {s m st' : HwBytes} {salt : CryptoGames.HKDF.Salt}
    (h : (spqrV1WithMac F K mac).recv s m = .ok (st', salt))
    (hrecv : S'.recv = (fun s m =>
      match (spqrV1RecvWithMac F K mac).recv s m with
      | .ok (st', key?) =>
        .ok (st', match key? with
                  | some k => if hk : k.length = 32 then some ⟨k, hk⟩ else none
                  | none => none)
      | .error b => .error b) := by rfl) :
    S'.recv s m = .ok (st', salt) := by
  unfold spqrV1WithMac CryptoVerification.LibsignalSpqrV1.toSpqrModel at h
  rw [hrecv]
  unfold spqrV1RecvWithMac CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel
  dsimp only at h ⊢
  cases htop : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac)
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) s m with
  | error e =>
    rw [htop] at h; cases e <;> nomatch h
  | ok r =>
    rw [htop] at h; dsimp only at h ⊢
    cases hsalt : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? r.key with
    | none => rw [hsalt] at h; nomatch h
    | some saltVal =>
      rw [hsalt] at h
      injection h with hpair
      obtain ⟨hst, hsalt_eq⟩ := Prod.mk.inj hpair
      subst hst hsalt_eq
      exact congrArg (fun x => Except.ok (r.state, x)) (emptyAsNoneSalt_of_recvKeyToSalt?_some hsalt)

end Symbolic.Swarm.CREF.Cli.Slots
