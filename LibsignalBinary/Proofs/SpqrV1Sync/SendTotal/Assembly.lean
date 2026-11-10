/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Erasure
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecAdd
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecMsg
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSendClosed
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvEk
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvCt
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSize
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainDir
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainPrev
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainRecv
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainSmall
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopBytesSize
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
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
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
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
# SPQR V1 Send Totality Assembly

Assembles the top-level SPQR V1 send-totality invariant obligations (`TopStmts`) from the braid,
chain, erasure-code, and serialized-size components.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)

private theorem asm_authOk_new (F : ShaCompress) (rootKey : Bytes) (ep : Epoch) :
    AuthOk (Authenticator.new F rootKey ep) := by
  unfold AuthOk Authenticator.new Authenticator.update hkdfToVecUnchecked hkdfToSliceUnchecked
  simp [length_hkdfExpand]

private theorem asm_bInit (F : ShaCompress) : BInitStmt F := by
  intro authKey dir _hauth
  cases dir with
  | a2b =>
    refine ⟨.keysUnsampled { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 } },
      ?_, asm_authOk_new F authKey 1#64, ?_⟩
    · simp [initStates, St, States.init_a, Chunked.SendEk.KeysUnsampled.new,
        Unchunked.SendEk.KeysUnsampled.new, spqrAuthApi, Bind.bind, Except.bind,
        liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    · simp [phiB, freshB, States.epoch, Chunked.SendEk.KeysUnsampled.epoch]
  | b2a =>
    obtain ⟨d, hdec, hwf⟩ := st_decFresh (HEADER_SIZE + AUTHENTICATOR_MACSIZE) (by decide)
    have hwf48 : DecWF 48 d := by
      simpa [HEADER_SIZE, AUTHENTICATOR_MACSIZE] using hwf
    refine ⟨.noHeaderReceived
        { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 }, receiving_hdr := d },
      ?_, ⟨asm_authOk_new F authKey 1#64, hwf48⟩, ?_⟩
    · simp [initStates, St, States.init_b, Chunked.SendCt.NoHeaderReceived.new,
        Unchunked.SendCt.NoHeaderReceived.new, spqrPolyApi, spqrAuthApi, hdec, Except.mapError,
        Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    · simp [phiB, freshB, States.epoch, Chunked.SendCt.NoHeaderReceived.epoch]

private theorem asm_topInit (F : ShaCompress) (K : MlKem) : TopInitStmt F K := by
  intro spqrdir k
  let authKey := CryptoGames.HMAC.keyToBytes32 k
  have hauth : authKey.length = 32 := by
    simp [authKey, CryptoGames.HMAC.keyToBytes32]
  let dir := Direction.ofSpqrDirection spqrdir
  obtain ⟨st, hst, hbok, hphi⟩ := asm_bInit F authKey dir hauth
  obtain ⟨vn?, ch?, chE, htop⟩ := top_init F K spqrdir k (fun _ => []) st hst
  have hcur0 : chE.currentEpoch.toNat = 0 := by
    have hle := chainCur_le_phiB st
    have hcur := htop.hcur
    omega
  have hse0 : chE.sendEpoch.toNat = 0 := by
    have hle := htop.hok.hsend_le
    omega
  have hlen1 : chE.links.length = 1 := by
    have hlen := htop.hok.hlen
    omega
  have hsmall : RecvSmall chE := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨l0, hl0, hrd⟩ := htop.hok.hrecvDir 0 (by omega) (by omega)
    have hidx0 : 0 - (chE.sendEpoch.toNat - 1) = 0 := by omega
    rw [hidx0] at hl0
    rw [List.getElem?_eq_getElem hi] at hl0
    injection hl0 with hl_eq
    subst hl_eq
    have hctr0 : chE.links[0].recv.ctr.toNat = 0 := by
      simpa using hrd.hctr
    obtain ⟨S, ⟨L, _, hLF, hdata⟩, hSlt, _⟩ := hrd.hprev
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons j tl =>
        exfalso
        have hjS : j ∈ S := by
          rw [← hLF]
          exact List.mem_toFinset.mpr List.mem_cons_self
        have hj := hSlt j hjS
        omega
    subst hLnil
    simp [hdata]
  exact ⟨authKey, dir, fun _ => [], st, 0, fun _ => 0, fun _ => ∅, vn?, ch?, chE,
    { htop := htop
      hauth := hauth
      hbok := hbok
      hphi := by omega
      hctr := fun _ => Nat.le_refl 0
      hsmall := hsmall }⟩

private theorem asm_nextChunk_ok {len : ℕ} {e : PolyEncoder} (hwf : EncWF len e)
    (hle : len ≤ 2 ^ 20) :
    ∃ e' c, spqrPolyApi.next_chunk e = .ok (e', c) := by
  obtain ⟨e', c, hnc, _⟩ := st_encNext len e hwf hle
  exact ⟨e', c, by simp [spqrPolyApi, hnc, Except.mapError]⟩

private theorem asm_expectEncode_ok (site : String) {msg : Bytes}
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 2 ^ 20) :
    ∃ e, expectEncodeBytes spqrPolyApi site msg = .ok e ∧ EncWF msg.length e := by
  obtain ⟨e, henc, hwf⟩ := st_encNew msg heven hle
  refine ⟨e, ?_, hwf⟩
  simp [expectEncodeBytes, spqrPolyApi, henc, Except.mapError, Bind.bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

private theorem asm_bSendOk (F : ShaCompress) (K : MlKem) : BSendOkStmt F K := by
  intro st tape hbok hK htape
  cases st with
  | ekSentCt1Received s => exact ⟨_, _, rfl⟩
  | noHeaderReceived s => exact ⟨_, _, rfl⟩
  | ct1Acknowledged s => exact ⟨_, _, rfl⟩
  | keysSampled s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2.2 (by decide)
    dsimp only [States.send, Chunked.SendEk.KeysSampled.send_hdr_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | headerSent s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2.2.1 (by decide)
    dsimp only [States.send, Chunked.SendEk.HeaderSent.send_ek_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | ct1Received s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2.2 (by decide)
    dsimp only [States.send, Chunked.SendEk.Ct1Received.send_ek_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | ct1Sampled s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2.2.1 (by decide)
    dsimp only [States.send, Chunked.SendCt.Ct1Sampled.send_ct1_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | ekReceivedCt1Sampled s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2.2 (by decide)
    dsimp only [States.send, Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | ct2Sampled s =>
    obtain ⟨e', c, hnc⟩ := asm_nextChunk_ok hbok.2 (by decide)
    dsimp only [States.send, Chunked.SendCt.Ct2Sampled.send_ct2_chunk]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | keysUnsampled s =>
    have htake64 : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE := by
      simp [KEY_GENERATION_SEED_SIZE]
      omega
    let seed : List.Vector (BitVec 8) KEY_GENERATION_SEED_SIZE :=
      ⟨tape.take KEY_GENERATION_SEED_SIZE, htake64⟩
    have hbv64 : bytesToVector? KEY_GENERATION_SEED_SIZE (tape.take KEY_GENERATION_SEED_SIZE) =
        some seed := by
      simp [bytesToVector?, htake64, seed]
    let ktr := K.fromSeed seed
    have hgen : generate K tape =
        .ok ({ ek := ktr.2.1.toList, dk := ktr.2.2.toList, hdr := ktr.1.toList },
          tape.drop KEY_GENERATION_SEED_SIZE) := by
      simp [generate, hbv64, ktr]
    have hhdr64 : ktr.1.toList.length = 64 := ktr.1.2
    have hmac : (spqrAuthApi F).mac_hdr s.uc.auth s.uc.epoch ktr.1.toList =
        .ok (Authenticator.macHdrUnchecked F s.uc.auth s.uc.epoch ktr.1.toList) := by
      have hmk : s.uc.auth.macKey.length < 2 ^ 32 := by
        have hlen := hbok.2
        omega
      have hhd : (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 s.uc.epoch ++
          ktr.1.toList).length < 2 ^ 32 := by
        have hlbl : Authenticator.hdrLabel.length = 33 := by decide
        have hbe : (CryptoGames.HMAC.toBEBytes 8 s.uc.epoch).length = 8 := by
          simp [CryptoGames.HMAC.toBEBytes]
        rw [List.length_append, List.length_append, hlbl, hbe, hhdr64]
        decide
      exact Authenticator.macHdr_of_lt F s.uc.auth s.uc.epoch ktr.1.toList hmk hhd
    have hmac_len : (Authenticator.macHdrUnchecked F s.uc.auth s.uc.epoch ktr.1.toList).length =
        32 :=
      Authenticator.length_macHdrUnchecked F s.uc.auth s.uc.epoch ktr.1.toList
    have hfull_len :
        (ktr.1.toList ++ Authenticator.macHdrUnchecked F s.uc.auth s.uc.epoch ktr.1.toList).length =
          96 := by
      rw [List.length_append, hhdr64, hmac_len]
    obtain ⟨e0, henc, hwf0⟩ := asm_expectEncode_ok "v1/chunked/send_ek.rs:63"
      (msg := ktr.1.toList ++ Authenticator.macHdrUnchecked F s.uc.auth s.uc.epoch ktr.1.toList)
      (by rw [hfull_len]) (by rw [hfull_len]; decide)
    obtain ⟨e1, c1, hnc⟩ := asm_nextChunk_ok hwf0 (by rw [hfull_len]; decide)
    dsimp only [States.send, Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
      Unchunked.SendEk.KeysUnsampled.send_header]
    rw [hgen]
    dsimp only [Bind.bind, Except.bind]
    rw [hmac]
    dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    rw [henc]
    dsimp only [Bind.bind, Except.bind]
    rw [hnc]
    exact ⟨_, _, rfl⟩
  | headerReceived s =>
    have htake32 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := by
      simp [SHARED_SECRET_SIZE]
      omega
    let rand : List.Vector (BitVec 8) SHARED_SECRET_SIZE :=
      ⟨tape.take SHARED_SECRET_SIZE, htake32⟩
    have hbv32 : bytesToVector? SHARED_SECRET_SIZE (tape.take SHARED_SECRET_SIZE) = some rand := by
      simp [bytesToVector?, htake32, rand]
    have hhdr64 : s.uc.hdr.length = 64 := hbok.2.1
    have hisSome : (K.encaps1 s.uc.hdr rand).isSome := hK s.uc.hdr rand hhdr64
    obtain ⟨⟨ct1V, esV, ssV⟩, henc1⟩ := Option.isSome_iff_exists.mp hisSome
    have hencaps : encaps1 K s.uc.hdr tape =
        .ok ((ct1V.toList, esV.toList, ssV.toList), tape.drop SHARED_SECRET_SIZE) := by
      simp [encaps1, hbv32, henc1]
    have hhkdf : (spqrAuthApi F).hkdf_to_vec (List.replicate 32 0#8) ssV.toList
        (sckaKeyInfoPrefix ++ u64ToBeBytes s.uc.epoch) 32 =
        .ok (hkdfToVecUnchecked F (List.replicate 32 0#8) ssV.toList
          (sckaKeyInfoPrefix ++ u64ToBeBytes s.uc.epoch) 32) :=
      hkdfToVec_of_le F (List.replicate 32 0#8) ssV.toList
        (sckaKeyInfoPrefix ++ u64ToBeBytes s.uc.epoch) (okmLen := 32) (by decide)
    have hct1_len : ct1V.toList.length = 960 := ct1V.2
    obtain ⟨e0, henc, hwf0⟩ := asm_expectEncode_ok "v1/chunked/send_ct.rs:131"
      (msg := ct1V.toList) (by rw [hct1_len]) (by rw [hct1_len]; decide)
    obtain ⟨e1, c1, hnc⟩ := asm_nextChunk_ok hwf0 (by rw [hct1_len]; decide)
    dsimp only [States.send, Chunked.SendCt.HeaderReceived.send_ct1_chunk,
      Unchunked.SendCt.HeaderReceived.send_ct1]
    rw [hencaps]
    dsimp only [Bind.bind, Except.bind]
    rw [hhkdf]
    dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
      spqrAuthApi]
    rw [henc]
    dsimp only [Bind.bind, Except.bind]
    rw [hnc]
    exact ⟨_, _, rfl⟩

private theorem asm_topTotal (F : ShaCompress) (K : MlKem) (hTS : TopSizeStmt F K)
    (hBC : BCodecStmt F) : TopTotalStmt F K := by
  intro n bytes tape hAdv hn hK htape
  have hsize : bytes.length < 2 ^ 64 := hTS n bytes hAdv (by omega)
  rcases hAdv with ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩
  have hpt : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes :=
    ⟨vn?, ch?, chE, hw.htop⟩
  have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos hpt
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st := hBC st hw.hbok
  obtain ⟨⟨m, key, st'⟩, tape', hsendB⟩ := asm_bSendOk F K st tape hw.hbok hK htape
  let secret' : ℕ → Bytes :=
    match key with
    | none => secret
    | some es => Function.update secret es.epoch.toNat es.secret
  have hok' : ChainOk F authKey dir secret' sendCtr recvSet chE := by
    refine chainOk_congr F authKey dir secret secret' sendCtr recvSet chE hw.htop.hok ?_
    intro e _ he_hi
    cases key with
    | none => rfl
    | some es =>
      rcases chainCur_send_key F K st st' tape tape' m es hep_pos hsendB with ⟨hes_ep, _⟩
      have hcur := hw.htop.hcur
      have hne : e ≠ es.epoch.toNat := by omega
      exact Function.update_of_ne hne es.secret secret
  have hpt' : PartyTop F K authKey dir secret' st sendEp sendCtr recvSet bytes :=
    ⟨vn?, ch?, chE, { hw.htop with hok := hok' }⟩
  have hsec' : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
    intro es hkeq
    subst hkeq
    simp [secret']
  have hctr_lt : sendCtr (st.epoch.toNat - 1) + 1 < 2 ^ 32 := by
    have hle := hw.hctr (st.epoch.toNat - 1)
    omega
  obtain ⟨bytes', hsendTop, _⟩ :=
    top_send F K authKey dir secret' st st' sendEp sendCtr recvSet bytes hpt' hsize hcodec
      tape tape' m key hsendB hsec' hctr_lt
  rw [hsendTop]
  rfl

/-- Assembles the four top-level SPQR V1 send-totality obligations (`TopStmts`). -/
theorem topStmts (F : ShaCompress) (K : MlKem) : TopStmts F K := by
  have hTS : TopSizeStmt F K := st_topSize F K (st_bSize F)
  have hBC : BCodecStmt F := st_bCodec F
  have hSC : BSendClosedStmt F K := st_bSendClosed F K st_encNew st_encNext
  have hPhi : BPhiStmt F K := st_bPhi F K
  have hEk : BRecvEkStmt F K := st_bRecvEk F K st_decFresh st_decAdd st_decMsg st_encNew
  have hCt : BRecvCtStmt F K := st_bRecvCt F K st_decFresh st_decAdd st_decMsg st_encNew
  have hCR : ChainRecvStmt F := st_chainRecv F (st_recvDir F) (st_recvPrev F)
  have hRE : TopRecvEqualStmt F K :=
    st_topRecvEqual F K hBC hEk hCt hPhi hCR st_recvSmallAdd
  exact
    { init := asm_topInit F K
      total := asm_topTotal F K hTS hBC
      sendClosed := st_topSend F K hTS hBC hSC hPhi st_recvSmallAdd st_recvSmallSend
      recvClosed := st_topRecv F K hTS hRE hCR }

end CryptoVerification.SpqrV1Sync.SendTotal
