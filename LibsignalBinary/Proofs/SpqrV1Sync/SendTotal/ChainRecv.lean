/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.VarintPure
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Encaps1Total
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import ProofLib

set_option autoImplicit false

/-!
# Chain Receive Preservation

Proves that any successful `Chain.recvKey` call preserves `ChainOk` (with updated receive sets)
and `RecvSmall` (`st_chainRecv`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress)

theorem crcv_epochIdx_eq {ch : Chain} {e : Epoch} {i : ℕ}
    (hsend_le : ch.sendEpoch.toNat ≤ ch.currentEpoch.toNat)
    (hlen : ch.links.length = ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1)
    (hep : ch.epochIdx e = .ok i) :
    ch.sendEpoch.toNat - 1 ≤ e.toNat ∧ e.toNat ≤ ch.currentEpoch.toNat ∧
      i = e.toNat - (ch.sendEpoch.toNat - 1) := by
  unfold Chain.epochIdx at hep
  dsimp only at hep
  by_cases hgt : e > ch.currentEpoch
  · simp only [hgt, ↓reduceIte] at hep
    nomatch hep
  · simp only [hgt, ↓reduceIte] at hep
    have hhi : e.toNat ≤ ch.currentEpoch.toNat := by
      simp only [gt_iff_lt, BitVec.lt_def] at hgt
      omega
    have hsub : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat := by
      have := ch.currentEpoch.isLt
      have := e.isLt
      rw [BitVec.toNat_sub]
      omega
    by_cases hge : (ch.currentEpoch - e).toNat ≥ ch.links.length
    · simp only [hge, ↓reduceIte] at hep
      nomatch hep
    · simp only [hge, ↓reduceIte, Except.ok.injEq] at hep
      rw [hsub, hlen] at hge hep
      exact ⟨by omega, hhi, by omega⟩

/-- Any successful `Chain.recvKey` preserves `ChainOk` and `RecvSmall`. -/
theorem st_chainRecv (F : ShaCompress) (hRD : RecvDirStmt F) (hRP : RecvPrevStmt F) :
    ChainRecvStmt F := by
  intro authKey dir secret sendCtr recvSet ch ch' e idx out h hsmall hrecv
  unfold Chain.recvKey at hrecv
  by_cases hzero : (e == 0#64 && idx == 0#32) = true
  · simp only [hzero, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrecv
    rcases hrecv with ⟨rfl, _⟩
    exact ⟨recvSet, h, hsmall, rfl, rfl⟩
  · simp only [Bool.not_eq_true] at hzero
    simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hrecv
    cases hep : ch.epochIdx e with
    | error _ => rw [hep] at hrecv; nomatch hrecv
    | ok epochIndex =>
      obtain ⟨hlo, hhi, heq_idx⟩ := crcv_epochIdx_eq h.hsend_le h.hlen hep
      obtain ⟨link, hlink_get, hlink_ok⟩ := h.hrecvDir e.toNat hlo hhi
      rw [← heq_idx] at hlink_get
      rw [hep] at hrecv
      dsimp only [ChainResult.ofError, Bind.bind, Except.bind] at hrecv
      rw [hlink_get] at hrecv
      dsimp only at hrecv
      cases hkey : link.recv.key (spqrHkdfWith F) idx ch.params with
      | error _ => rw [hkey] at hrecv; nomatch hrecv
      | ok p =>
        rcases p with ⟨recv', out'⟩
        rw [hkey] at hrecv
        dsimp only [Pure.pure, Except.pure] at hrecv
        injection hrecv with hrecv_eq
        rcases Prod.mk.inj hrecv_eq with ⟨hch', _⟩
        subst hch'
        rw [h.hparams] at hkey
        have hseed : (seedAt F authKey secret dir.switch e.toNat).length = 32 :=
          length_seedAt F authKey secret dir.switch e.toNat
        obtain ⟨_, _, _, hrecv'⟩ :=
          hRD (seedAt F authKey secret dir.switch e.toNat) (recvSet e.toNat)
            link.recv recv' idx out' hseed hlink_ok hkey
        have hlink_mem : link ∈ ch.links := List.mem_of_getElem? hlink_get
        have hprev_small : recv'.prev.data.length < 2 ^ 20 :=
          hRP (seedAt F authKey secret dir.switch e.toNat) (recvSet e.toNat)
            link.recv recv' idx out' hseed hlink_ok (hsmall link hlink_mem) hkey
        have hidx_lt : epochIndex < ch.links.length :=
          (List.getElem?_eq_some_iff.mp hlink_get).1
        refine ⟨Function.update recvSet e.toNat (insert idx.toNat (recvSet e.toNat)),
          ?_, ?_, rfl, rfl⟩
        · refine
            { hdir := h.hdir
              hparams := h.hparams
              hsend_le := h.hsend_le
              hroot := h.hroot
              hlen := by dsimp only; rw [List.length_set, h.hlen]
              hsendDir := ?_
              hsendOld := ?_
              hrecvDir := ?_
              hfreshSend := h.hfreshSend
              hfreshRecv := ?_ }
          · intro e' hlo' hhi'
            dsimp only at hlo' hhi' ⊢
            by_cases heq' : epochIndex = e' - (ch.sendEpoch.toNat - 1)
            · rw [← heq', List.getElem?_set_self hidx_lt]
              obtain ⟨l0, hl0, hsok⟩ := h.hsendDir e' hlo' hhi'
              rw [← heq', hlink_get] at hl0
              injection hl0 with hl0_eq
              subst hl0_eq
              exact ⟨_, rfl, hsok⟩
            · rw [List.getElem?_set_ne heq']
              exact h.hsendDir e' hlo' hhi'
          · intro l hpos hl0
            dsimp only at hpos hl0
            by_cases heq0 : epochIndex = 0
            · rw [← heq0, List.getElem?_set_self hidx_lt, Option.some.injEq] at hl0
              subst hl0
              exact h.hsendOld link hpos (heq0 ▸ hlink_get)
            · rw [List.getElem?_set_ne heq0] at hl0
              exact h.hsendOld l hpos hl0
          · intro e' hlo' hhi'
            dsimp only at hlo' hhi' ⊢
            by_cases he' : e' = e.toNat
            · subst he'
              rw [← heq_idx, List.getElem?_set_self hidx_lt, Function.update_self]
              exact ⟨_, rfl, hrecv'⟩
            · have hne_idx : epochIndex ≠ e' - (ch.sendEpoch.toNat - 1) := by omega
              rw [List.getElem?_set_ne hne_idx, Function.update_of_ne he']
              exact h.hrecvDir e' hlo' hhi'
          · intro e' hgt
            dsimp only at hgt
            have hne' : e' ≠ e.toNat := by omega
            rw [Function.update_of_ne hne']
            exact h.hfreshRecv e' hgt
        · intro l hl
          rcases List.mem_or_eq_of_mem_set hl with hl_old | rfl
          · exact hsmall l hl_old
          · exact hprev_small

end CryptoVerification.SpqrV1Sync.SendTotal
