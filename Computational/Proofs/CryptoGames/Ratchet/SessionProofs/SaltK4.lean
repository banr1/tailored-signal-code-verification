/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK3
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK1
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK2
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.SM.Theorem7Proof

/-!
# Two-step sender seed extraction (`k4Seed`) and corruption-window exclusion

**Checked by Lean.** Defines `k4Seed` for branch K4 of `LibsignalSimC.snapshotMessageKeySeed` (DEV-LS37), proves trace-level completeness of K1–K4, and establishes `knownSeedR_none_no_corr_window`: when `snapshotMessageKeySeed` returns `none` on an accepted non-evicted honest delivery, no snapshot falls inside the active corruption window.
-/

@[expose] public section

open CryptoGames.Ratchet CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.CKA CryptoGames.SM
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed decryptWithKnownSeed)

namespace CryptoGames.LibsignalSM.Proofs.SaltMismatch

open CryptoGames.LibsignalSM.Proofs.Correctness CryptoGames.SM.Construction

/-- Seed extracted by branch K4 of `snapshotMessageKeySeed` via a two-step root-KDF chain from snapshots at epochs `t - 2` and `t`. -/
def k4Seed (C : Crypto) (sc_cur? : Option SenderChain) (rc_last? : Option ReceiverChain)
    (rk_prev : LibsignalSession.RootKey) (sc_prev? : Option SenderChain)
    (Y : PublicKey) (n : BitVec 32) : Option (List (BitVec 8)) :=
  sc_cur?.bind fun sc_cur =>
    if sc_cur.ratchetKey.publicKey = Y then
      rc_last?.bind fun rc_last =>
        sc_prev?.bind fun sc_prev =>
          match rootCreateChain C rk_prev rc_last.senderRatchetKey
              sc_prev.ratchetKey.privateKey with
          | .ok (rk1, _) =>
            match rootCreateChain C rk1 rc_last.senderRatchetKey
                sc_cur.ratchetKey.privateKey with
            | .ok (_, ck0) => chainSeedAt C.F ck0 n
            | .error _ => none
          | .error _ => none
    else none

section TraceLemmas

variable {Pt : Type} [Zero Pt] [DecidableEq Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}

theorem k4Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace C.F Dh encPt) {t : ℕ} (ht2 : 2 ≤ t) (ht : t ≤ tr.tFront)
    {sc_cur sc_prev : SenderChain} {rc_last : ReceiverChain}
    (hsc_cur : sc_cur.ratchetKey = KeyPair.generate C (tr.x t))
    (hrc_last : rc_last.senderRatchetKey = encT (tr.T (t - 1)))
    (hsc_prev : sc_prev.ratchetKey = KeyPair.generate C (tr.x (t - 2)))
    (n : BitVec 32) :
    k4Seed C (some sc_cur) (some rc_last) (tr.rk (t - 2)) (some sc_prev)
      (encT (tr.T t)) n = some (msgSeedAt C.F (tr.ck t) n.toNat) := by
  have hpk_cur : sc_cur.ratchetKey.publicKey = encT (tr.T t) := by
    rw [hsc_cur, KeyPair_generate_publicKey hX, EpochTrace.T]
  have hsk_cur : sc_cur.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x t))⟩ := by
    rw [hsc_cur, KeyPair_generate_privateKey]
  have hsk_prev : sc_prev.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x (t - 2)))⟩ := by
    rw [hsc_prev, KeyPair_generate_privateKey]
  have hT_ne : tr.T (t - 1) ≠ 0 := tr.T_ne_zero hX (t - 1)
  have hstep1 : Ratchet.rootKdf C.F (tr.rk (t - 2))
      (encPt (Dh.dh (tr.x (t - 2)) (tr.T (t - 1)))) = (tr.rk (t - 1), tr.ck (t - 1)) := by
    have h := tr.rootKdf_step_symm hDh (e := t - 2) (by omega)
    rwa [show t - 2 + 1 = t - 1 by omega] at h
  have hstep2 : Ratchet.rootKdf C.F (tr.rk (t - 1))
      (encPt (Dh.dh (tr.x t) (tr.T (t - 1)))) = (tr.rk t, tr.ck t) := by
    have h := tr.hStep (t - 1) (by omega)
    rwa [show t - 1 + 1 = t by omega] at h
  unfold k4Seed
  simp only [Option.bind_some, hpk_cur, ↓reduceIte, hrc_last, hsk_prev, hsk_cur,
    rootCreateChain_encT hX hT_ne, hstep1, hstep2]
  exact chainSeedAt_chainKeyValAt C.F (tr.ck t) (Nat.two_pow_pos 32) n (Nat.zero_le _)

theorem k2Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace C.F Dh encPt) {e : ℕ} (he : e < tr.tFront)
    {sc : SenderChain} (hsc : sc.ratchetKey = KeyPair.generate C (tr.x e))
    (n : BitVec 32) :
    k2Seed C (tr.rk e) (some sc) (encT (tr.T (e + 1))) n =
      some (msgSeedAt C.F (tr.ck (e + 1)) n.toNat) := by
  have hsk : sc.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x e))⟩ := by
    rw [hsc, KeyPair_generate_privateKey]
  have hT_ne : tr.T (e + 1) ≠ 0 := tr.T_ne_zero hX (e + 1)
  have hstep := tr.rootKdf_step_symm hDh he
  unfold k2Seed
  simp only [Option.bind_some, hsk, rootCreateChain_encT hX hT_ne, hstep]
  exact chainSeedAt_chainKeyValAt C.F (tr.ck (e + 1)) (Nat.two_pow_pos 32) n (Nat.zero_le _)

theorem k3Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT)
    (tr : EpochTrace C.F Dh encPt) {t j : ℕ} (hj : j < 2 ^ 32)
    {sc : SenderChain} (hrk : sc.ratchetKey = KeyPair.generate C (tr.x t))
    (hck : sc.chainKey = ⟨chainKeyValAt C.F (tr.ck t) j, BitVec.ofNat 32 j⟩)
    {n : BitVec 32} (hle : j ≤ n.toNat) :
    k3Seed C.F sc (encT (tr.T t)) n = some (msgSeedAt C.F (tr.ck t) n.toNat) := by
  have hpk : sc.ratchetKey.publicKey = encT (tr.T t) := by
    rw [hrk, KeyPair_generate_publicKey hX, EpochTrace.T]
  unfold k3Seed
  simp only [hpk, ↓reduceIte, hck, chainSeedAt_chainKeyValAt C.F (tr.ck t) hj n hle]

theorem k1Seed_eq_some_of_consume {F : ShaCompress} {ck0 : BitVec 256} {maxSnap maxAcc : ℕ}
    {rcSnap : ReceiverChain} (hsnap : RcvChainInv F ck0 maxSnap rcSnap)
    (hle : maxSnap ≤ maxAcc)
    {s s' : RatchetState} {their : PublicKey} {idx : ℕ} {c : ReceiverChain}
    {counter : BitVec 32} {msgType : MessageType} {key : MessageKeyGenerator}
    (hsub : ∀ mk ∈ c.messageKeys, mk.counter.toNat < maxSnap → mk ∈ rcSnap.messageKeys)
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c)
    (hinv : RcvChainInv F ck0 maxAcc c)
    (hexec : Mut.exec
      (RatchetState.consumeMessageKey F their
        ⟨chainKeyValAt F ck0 maxAcc, BitVec.ofNat 32 maxAcc⟩ counter msgType) s =
      (Except.ok key, s')) :
    k1Seed F rcSnap counter = some key.seed := by
  obtain ⟨_, _, _, _, hkey, _⟩ := consumeMessageKey_ok hfind hget hinv hexec
  unfold k1Seed
  cases hmk : rcSnap.messageKeys.find? (·.counter == counter) with
  | some mk =>
    simp only [Option.some.injEq]
    have hc : mk.counter = counter := by simpa using List.find?_some hmk
    have hwf := hsnap.keys_wf mk (List.mem_of_find?_eq_some hmk)
    rw [hwf.2, hkey]
    simp [hc]
  | none =>
    rw [hsnap.ck_eq]
    simp only [Option.bind_some]
    have hge : maxSnap ≤ counter.toNat := by
      by_contra hlt_cnt
      rw [Nat.not_le] at hlt_cnt
      have hlt_bv : counter < BitVec.ofNat 32 maxAcc := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hinv.maxAcc_lt]
        omega
      unfold RatchetState.consumeMessageKey at hexec
      simp only [hlt_bv, ↓reduceIte, Mut.exec_bind] at hexec
      cases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none =>
        rw [takeSkippedKey_exec_none hfind hget hpos] at hexec
        simp [Mut.exec_throw] at hexec
      | some pos =>
        rcases findIdx?_eq_some_getElem? hpos with ⟨k0, hk0_get, hk0_eq⟩
        have hk0_mem : k0 ∈ c.messageKeys := List.mem_of_getElem? hk0_get
        have hk0_cnt : k0.counter = counter := by simpa using hk0_eq
        have hk0_snap : k0 ∈ rcSnap.messageKeys :=
          hsub k0 hk0_mem (by rw [hk0_cnt]; exact hlt_cnt)
        have hnone := List.find?_eq_none.mp hmk k0 hk0_snap
        simp [hk0_cnt] at hnone
    rw [chainSeedAt_chainKeyValAt F ck0 hsnap.maxAcc_lt counter hge, hkey]

/-- Invariant relating a corruption snapshot in `snaps` to the epoch trace `tr` and current receiver state `s_Q`. -/
structure SnapInv {PQ : Type} (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (tr : EpochTrace C.F Dh encPt)
    (Q : Party) (s_Q : RatchetState) (maxAcc_Q : ℕ → ℕ)
    (snap : Party × ℕ × GhostState PQ) : Prop where
  sendsIn_eq : snap.1.sendsIn snap.2.1 = true
  le_tFront : snap.2.1 ≤ tr.tFront
  rk_eq : snap.2.2.session.rootKey = tr.rk snap.2.1
  sc_inv : ∃ j < 2 ^ 32,
    snap.2.2.session.senderChain =
      some ⟨KeyPair.generate C (tr.x snap.2.1),
            ⟨chainKeyValAt C.F (tr.ck snap.2.1) j, BitVec.ofNat 32 j⟩⟩
  chains_len : snap.2.2.session.receiverChains.length = (storedEpochs snap.1 snap.2.1).length
  chains_inv : ∀ k (hk : k < (storedEpochs snap.1 snap.2.1).length),
    let ep := (storedEpochs snap.1 snap.2.1)[k]
    ∃ rc maxSnap,
      snap.2.2.session.receiverChains[k]? = some rc ∧
      rc.senderRatchetKey = encT (tr.T ep) ∧
      RcvChainInv C.F (tr.ck ep) maxSnap rc ∧
      (snap.1 = Q →
        maxSnap ≤ maxAcc_Q ep ∧
        ∀ idx c, s_Q.findReceiverChainIndex (encT (tr.T ep)) = some idx →
          s_Q.receiverChains[idx]? = some c →
          ∀ mk ∈ c.messageKeys, mk.counter.toNat < maxSnap → mk ∈ rc.messageKeys)

omit [Zero Pt] [DecidableEq Pt] in
theorem SnapInv.getLast?_senderRatchetKey {PQ : Type}
    {tr : EpochTrace C.F Dh encPt} {Q : Party} {s_Q : RatchetState} {maxAcc_Q : ℕ → ℕ}
    {snap : Party × ℕ × GhostState PQ}
    (hsnap : SnapInv C Dh encPt encT tr Q s_Q maxAcc_Q snap)
    {t : ℕ} (hP : snap.1 = Q.other) (ht_eq : snap.2.1 = t) (ht2 : 2 ≤ t) :
    ∃ rc_last, snap.2.2.session.receiverChains.getLast? = some rc_last ∧
      rc_last.senderRatchetKey = encT (tr.T (t - 1)) := by
  have hsends : Q.other.sendsIn t = true := hP ▸ ht_eq ▸ hsnap.sendsIn_eq
  have hns : Q.other.sendsIn (t - 1) = false := by
    have h1 : (t - 1) + 1 = t := by omega
    rw [← h1, Party.sendsIn_succ] at hsends
    simpa using hsends
  have hdiv : (t - (t - 1)) / 2 < maxReceiverChains := by
    rw [show t - (t - 1) = 1 by omega]; decide
  rcases storedEpochs_getElem?_from_end Q.other t (t - 1) (by omega) hns hdiv with
    ⟨hlen_pos, hget_ep⟩
  rw [show (t - (t - 1)) / 2 = 0 by omega, Nat.sub_zero] at hget_ep
  have hk_lt :
      (storedEpochs snap.1 snap.2.1).length - 1 < (storedEpochs snap.1 snap.2.1).length := by
    rw [hP, ht_eq]; omega
  rcases hsnap.chains_inv ((storedEpochs snap.1 snap.2.1).length - 1) hk_lt with
    ⟨rc_last, _, hget_rc, hrk, _, _⟩
  have hep_eq :
      (storedEpochs snap.1 snap.2.1)[(storedEpochs snap.1 snap.2.1).length - 1] = t - 1 := by
    have hget_ep' : (storedEpochs snap.1 snap.2.1)[(storedEpochs snap.1 snap.2.1).length - 1]? =
        some (t - 1) := by simpa [hP, ht_eq] using hget_ep
    rw [List.getElem?_eq_getElem hk_lt, Option.some.injEq] at hget_ep'
    exact hget_ep'
  have hlast : snap.2.2.session.receiverChains.getLast? =
      snap.2.2.session.receiverChains[snap.2.2.session.receiverChains.length - 1]? := by
    cases hrc : snap.2.2.session.receiverChains with
    | nil =>
      have h0 : (storedEpochs snap.1 snap.2.1).length = 0 := by
        rw [← hsnap.chains_len, hrc]; rfl
      omega
    | cons hd tl =>
      simp [List.getLast?_eq_getElem?]
  rw [hlast, hsnap.chains_len]
  exact ⟨rc_last, hget_rc, hep_eq ▸ hrk⟩

theorem mem_of_findSome?_eq_some {α β : Type} {f : α → Option β} {l : List α} {b : β}
    (h : l.findSome? f = some b) : ∃ x ∈ l, f x = some b := by
  rcases List.findSome?_eq_some_iff.mp h with ⟨l₁, x, l₂, rfl, hx, _⟩
  exact ⟨x, by simp, hx⟩

/-- When `snapshotMessageKeySeed` returns `none` on an accepted non-evicted delivery of epoch `t`, all snapshots in `snaps` satisfying `SnapInv` lie outside the epoch-`t` corruption window. -/
theorem knownSeedR_none_no_corr_window {PQ PQC : Type} (P : Params PQ PQC)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace P.C.F Dh encPt)
    {Q : Party} {s_Q s_Q' : RatchetState} {maxAcc_Q : ℕ → ℕ}
    {snaps : List (Party × ℕ × GhostState PQ)}
    (hsnaps : ∀ snap ∈ snaps, SnapInv P.C Dh encPt encT tr Q s_Q maxAcc_Q snap)
    {t idx : ℕ} (ht : t ≤ tr.tFront) (hsends : Q.other.sendsIn t = true)
    {c : ReceiverChain} {msg : SignalMessage} {msgType : MessageType} {key : MessageKeyGenerator}
    {w : List (BitVec 8)}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T t))
    (hfind : s_Q.findReceiverChainIndex (encT (tr.T t)) = some idx)
    (hget : s_Q.receiverChains[idx]? = some c)
    (hinv : RcvChainInv P.C.F (tr.ck t) (maxAcc_Q t) c)
    (hexec : Mut.exec
      (RatchetState.consumeMessageKey P.C.F (encT (tr.T t))
        ⟨chainKeyValAt P.C.F (tr.ck t) (maxAcc_Q t), BitVec.ofNat 32 (maxAcc_Q t)⟩
        msg.counter msgType) s_Q = (Except.ok key, s_Q'))
    (hstored : ∀ e g, (Q, e, g) ∈ snaps → t < e → t ∈ storedEpochs Q e)
    (hnone : snapshotMessageKeySeed P snaps Q t w = none) :
    (∀ e g, (Q, e, g) ∈ snaps → e + 3 ≤ t) ∧
    (∀ e g, (Q.other, e, g) ∈ snaps → t ≠ e + 1) ∧
    (∀ g sc, (Q.other, t, g) ∈ snaps → g.session.senderChain = some sc →
      msg.counter.toNat < sc.chainKey.index.toNat) ∧
    ¬ ((∃ e₁ g₁, (Q.other, e₁, g₁) ∈ snaps ∧ t = e₁ + 2) ∧
       (∃ g₂, (Q.other, t, g₂) ∈ snaps)) := by
  unfold snapshotMessageKeySeed at hnone
  rw [hw] at hnone
  dsimp only at hnone
  have hor_none {a b : Option (List (BitVec 8))} (h : (a <|> b) = none) :
      a = none ∧ b = none := by
    cases a <;> cases b <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  rcases hor_none hnone with ⟨hk1_none, hk324_none⟩
  rcases hor_none hk324_none with ⟨hk3_none, hk24_none⟩
  rcases hor_none hk24_none with ⟨hk2_none, hk4_none⟩
  have hQ_ns_t : Q.sendsIn t = false := by
    have h := sendsIn_other_eq_not Q t
    rw [hsends] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e g hmem
    have hsnap := hsnaps (Q, e, g) hmem
    have hQe : Q.sendsIn e = true := hsnap.sendsIn_eq
    by_cases hgt : t < e
    · have ht_mem := hstored e g hmem hgt
      rcases List.getElem_of_mem ht_mem with ⟨k, hk_lt, hk_eq⟩
      rcases hsnap.chains_inv k hk_lt with ⟨rcSnap, maxSnap, hget_rc, hrk, hrc_inv, hQ_sub⟩
      rw [hk_eq] at hrk hrc_inv hQ_sub
      rcases hQ_sub rfl with ⟨hle_max, hsub⟩
      have hrc_mem : rcSnap ∈ g.session.receiverChains := List.mem_of_getElem? hget_rc
      have hfind_some : ∃ rc', g.session.receiverChains.find?
          (·.senderRatchetKey == msg.senderRatchetKey) = some rc' := by
        cases hfind_rc : g.session.receiverChains.find?
            (·.senderRatchetKey == msg.senderRatchetKey) with
        | some rc' => exact ⟨rc', rfl⟩
        | none =>
          have hall := List.find?_eq_none.mp hfind_rc rcSnap hrc_mem
          simp [hY, hrk] at hall
      rcases hfind_some with ⟨rc', hfind_rc'⟩
      have hmem' := List.mem_of_find?_eq_some hfind_rc'
      have hkey' : rc'.senderRatchetKey = encT (tr.T t) := by
        rw [hY] at hfind_rc'; simpa using List.find?_some hfind_rc'
      rcases List.getElem_of_mem hmem' with ⟨k', hk'_lt, hk'_eq⟩
      have hk'_lt' : k' < (storedEpochs Q e).length := by rwa [← hsnap.chains_len]
      rcases hsnap.chains_inv k' hk'_lt' with ⟨rc'', maxSnap', hget'', hrk'', hinv'', hQ_sub'⟩
      rw [List.getElem?_eq_getElem hk'_lt, Option.some.injEq] at hget''
      have hrc'_eq : rc'' = rc' := hget''.symm.trans hk'_eq
      subst hrc'_eq
      have hep'_le : (storedEpochs Q e)[k'] ≤ tr.tFront :=
        Nat.le_trans (mem_storedEpochs_imp Q e _ (List.getElem_mem hk'_lt')).1 hsnap.le_tFront
      have hep'_eq : (storedEpochs Q e)[k'] = t :=
        tr.hDistinct _ hep'_le _ ht (encT_injective hX (hrk''.symm.trans hkey'))
      rw [hep'_eq] at hinv'' hQ_sub'
      rcases hQ_sub' rfl with ⟨hle_max', hsub'⟩
      have hk1_eq := k1Seed_eq_some_of_consume hinv'' hle_max'
        (hsub' idx c hfind hget) hfind hget hinv hexec
      have hnone_e := List.findSome?_eq_none_iff.mp hk1_none (Q, e, g) hmem
      simp only [↓reduceIte, hfind_rc', Option.bind_some] at hnone_e
      change k1Seed P.C.F _ msg.counter = none at hnone_e
      rw [hk1_eq] at hnone_e
      cases hnone_e
    · have hle : e ≤ t := by omega
      have hne_t : e ≠ t := by
        rintro rfl; rw [hQ_ns_t] at hQe; cases hQe
      have hne_t1 : t ≠ e + 1 := by
        intro ht1
        have hnone_e := List.findSome?_eq_none_iff.mp hk2_none (Q, e, g) hmem
        rcases hsnap.sc_inv with ⟨j, _, hsc_eq⟩
        have hk2_eq := k2Seed_eq_some_of_trace hX hDh tr (e := e) (by omega)
          (sc := ⟨KeyPair.generate P.C (tr.x e),
            ⟨chainKeyValAt P.C.F (tr.ck e) j, BitVec.ofNat 32 j⟩⟩) rfl msg.counter
        unfold k2Seed at hk2_eq
        have hrk_e : g.session.rootKey = tr.rk e := hsnap.rk_eq
        have hsc_e : g.session.senderChain =
            some ⟨KeyPair.generate P.C (tr.x e),
              ⟨chainKeyValAt P.C.F (tr.ck e) j, BitVec.ofNat 32 j⟩⟩ := hsc_eq
        simp only [hQe, hY, ht1, and_self, ↓reduceIte, hrk_e, hsc_e,
          Option.bind_some] at hnone_e hk2_eq
        exact nomatch hnone_e.symm.trans hk2_eq
      have hne_t2 : t ≠ e + 2 := by
        intro ht2
        rw [ht2, Party.sendsIn_succ, Party.sendsIn_succ, Bool.not_not] at hQ_ns_t
        rw [hQ_ns_t] at hQe
        cases hQe
      omega
  · intro e g hmem ht1
    have hsnap := hsnaps (Q.other, e, g) hmem
    have h1 : Q.other.sendsIn e = true := hsnap.sendsIn_eq
    rw [ht1, Party.sendsIn_succ, h1] at hsends
    cases hsends
  · intro g sc hmem hsc
    have hsnap := hsnaps (Q.other, t, g) hmem
    rcases hsnap.sc_inv with ⟨j, hj, hsc_eq⟩
    have hsc' : sc = ⟨KeyPair.generate P.C (tr.x t),
        ⟨chainKeyValAt P.C.F (tr.ck t) j, BitVec.ofNat 32 j⟩⟩ :=
      Option.some.inj (hsc.symm.trans hsc_eq)
    have hidx : sc.chainKey.index.toNat = j := by
      rw [hsc']
      exact Nat.mod_eq_of_lt hj
    rw [hidx]
    by_contra hge
    rw [Nat.not_lt] at hge
    have hk3_eq := k3Seed_eq_some_of_trace hX tr hj (sc := sc)
      (by rw [hsc']) (by rw [hsc']) hge
    unfold k3Seed at hk3_eq
    have hnone_t := List.findSome?_eq_none_iff.mp hk3_none (Q.other, t, g) hmem
    simp only [↓reduceIte, hsc, Option.bind_some, hY] at hnone_t
    rw [hnone_t] at hk3_eq
    cases hk3_eq
  · rintro ⟨⟨e₁, g₁, hmem₁, ht_e1⟩, ⟨g₂, hmem₂⟩⟩
    have hsnap₁ := hsnaps (Q.other, e₁, g₁) hmem₁
    have hsnap₂ := hsnaps (Q.other, t, g₂) hmem₂
    rcases hsnap₁.sc_inv with ⟨j₁, _, hsc₁_eq⟩
    rcases hsnap₂.sc_inv with ⟨j₂, _, hsc₂_eq⟩
    have ht2 : 2 ≤ t := by omega
    rcases hsnap₂.getLast?_senderRatchetKey rfl rfl ht2 with
      ⟨rc_last, hlast, hrc_last_rk⟩
    have he₁_eq : e₁ = t - 2 := by omega
    have hpk_cur : (KeyPair.generate P.C (tr.x t)).publicKey = encT (tr.T t) := by
      rw [KeyPair_generate_publicKey hX, EpochTrace.T]
    have hsc₂_eq' : g₂.session.senderChain =
        some ⟨KeyPair.generate P.C (tr.x t),
          ⟨chainKeyValAt P.C.F (tr.ck t) j₂, BitVec.ofNat 32 j₂⟩⟩ := hsc₂_eq
    have hlast' : g₂.session.receiverChains.getLast? = some rc_last := hlast
    rcases hcur_opt : (snaps.findSome? fun e_cur =>
        if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
          e_cur.2.2.session.senderChain.bind fun sc_cur =>
            if sc_cur.ratchetKey.publicKey = msg.senderRatchetKey then
              e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
                (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
            else none
        else none) with _ | p
    · have hnone_cur := List.findSome?_eq_none_iff.mp hcur_opt (Q.other, t, g₂) hmem₂
      simp only [and_self, ↓reduceIte, hsc₂_eq', Option.bind_some, hY, hpk_cur, hlast',
        Option.map_some, reduceCtorEq] at hnone_cur
    · rw [hcur_opt, Option.bind_some] at hk4_none
      rcases mem_of_findSome?_eq_some hcur_opt with ⟨e_cur, hmem_cur, hbody_cur⟩
      split at hbody_cur
      · rename_i hcur_cond
        rcases hcur_cond with ⟨hP_cur, ht_cur⟩
        have hsnap_cur := hsnaps e_cur hmem_cur
        rcases hsnap_cur.sc_inv with ⟨j_cur, _, hsc_cur_eq⟩
        rw [ht_cur] at hsc_cur_eq
        rw [hsc_cur_eq, Option.bind_some] at hbody_cur
        split at hbody_cur
        · rw [Option.map_eq_some_iff] at hbody_cur
          rcases hbody_cur with ⟨rc_last_cur, hlast_cur_opt, hp_eq⟩
          rcases hsnap_cur.getLast?_senderRatchetKey hP_cur ht_cur ht2 with
            ⟨rc_last_cur', hlast_cur', hrc_last_cur_rk⟩
          rw [hlast_cur_opt] at hlast_cur'
          injection hlast_cur' with hrc_cur_eq
          subst hrc_cur_eq
          subst hp_eq
          have hk4_eq := k4Seed_eq_some_of_trace hX hDh tr (t := t) ht2 ht
            (sc_cur := ⟨KeyPair.generate P.C (tr.x t),
              ⟨chainKeyValAt P.C.F (tr.ck t) j_cur, BitVec.ofNat 32 j_cur⟩⟩)
            (sc_prev := ⟨KeyPair.generate P.C (tr.x e₁),
              ⟨chainKeyValAt P.C.F (tr.ck e₁) j₁, BitVec.ofNat 32 j₁⟩⟩)
            (rc_last := rc_last_cur)
            rfl hrc_last_cur_rk (by simp [he₁_eq]) msg.counter
          unfold k4Seed at hk4_eq
          simp only [Option.bind_some, hpk_cur, ↓reduceIte, ← he₁_eq] at hk4_eq
          have hnone_prev := List.findSome?_eq_none_iff.mp hk4_none (Q.other, e₁, g₁) hmem₁
          have hsends₁ : Q.other.sendsIn e₁ = true := hsnap₁.sendsIn_eq
          have hrk₁_eq : g₁.session.rootKey = tr.rk e₁ := hsnap₁.rk_eq
          have hsc₁_eq' : g₁.session.senderChain =
              some ⟨KeyPair.generate P.C (tr.x e₁),
                ⟨chainKeyValAt P.C.F (tr.ck e₁) j₁, BitVec.ofNat 32 j₁⟩⟩ := hsc₁_eq
          simp only [hsends₁, ← ht_e1, and_self, ↓reduceIte] at hnone_prev
          rw [hrk₁_eq, hsc₁_eq', Option.bind_some] at hnone_prev
          exact nomatch hnone_prev.symm.trans hk4_eq
        · cases hbody_cur
      · cases hbody_cur

end TraceLemmas

end CryptoGames.LibsignalSM.Proofs.SaltMismatch
