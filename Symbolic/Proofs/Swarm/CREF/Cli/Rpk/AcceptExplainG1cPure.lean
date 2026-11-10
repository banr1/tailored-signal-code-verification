/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineShapeModKemInv
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptExplainG1cPureA
import DY.Trace.Basic
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Own-Key MAC Branch Exclusion for Pre-Key Session Start

Proves `rpk_not_bsG1cOwnKeyCase`, ruling out `BsG1cOwnKeyCase` during Bob's pre-key receive
when the derived message-key seed `seed'` is not attacker-known.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.TripleRatchet (RecvChain createChain chainKeyAt consumeMessageKey hmac hkdfBlock1
  lit litByte zeroSalt)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhLabel agree errToOption serializedIk)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine

/-- Seed separation against `Q` for attacker-known honest KDF outputs and logged skipped seeds. -/
def SeedSepAKBob (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace)
    (Q : DY.Bytes → Prop) : Prop :=
  ∀ (u' v' : DY.Bytes), u'.AttackerKnows T → (HonestKdfOut T u' ∨ SkippedSeedLogged T u') → Q v' →
    (gamma' i S g u').shape = (gamma' i S g v').shape →
    u' = v' ∨ v'.AttackerKnows T ∨
      ∃ (s i₀ : DY.Bytes), u' = KdfExtract.kdfExtract s i₀ ∧ s.AttackerKnows T ∧ i₀.AttackerKnows T

private theorem seedSepAK_bobQ_of_recvChainSpine
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (hne : r.alice ≠ r.bob)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (p : PreKeyFields) (x' : PreKeyRep)
    (keys' : HandshakeKeys) (msg' : TRSignalMsg) {seed' : DY.Bytes} {c' : RecvChain}
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hct_ak : x'.ct.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : AliceKemLen32 interpretation S g (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    {c : RecvChain} (hc : RecvChainSpine (runTraceMoves r ms) c) (b_u : Bool)
    {v' : DY.Bytes} (hv : BobQ r keys' msg' v')
    (hsh : (gamma' interpretation S g (ckOut b_u c.chainKey)).shape =
      (gamma' interpretation S g v').shape) :
    ckOut b_u c.chainKey = v' ∨ v'.AttackerKnows (runTraceMoves r ms) ∨
      ∃ (s i₀ : DY.Bytes), ckOut b_u c.chainKey = KdfExtract.kdfExtract s i₀ ∧
        s.AttackerKnows (runTraceMoves r ms) ∧ i₀.AttackerKnows (runTraceMoves r ms) := by
  obtain ⟨ikm, _, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  rcases hc with ⟨rk', t, j_u, -, -, hcj, hH | hprk⟩ |
      ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j_u, hcj, _⟩
  · have hroot_sp : SpineRk (LoggedOrBobIkmRk r ms p x') true (ckOut b_u c.chainKey) := by
      rw [hcj]
      exact spineRk_ckOut b_u (spineRk_chainKeyAt
        (spineRk_mono (fun _ _ h => Or.inl h) (spineRk_of_honestSendRoot hH)) j_u)
    rcases hv with ⟨j_v, b_v, rfl⟩ | rfl
    · have hv_sp := spineRk_bobChain_ckOut hne ms hkeys hcmk j_v b_v
      exact .inl (oppParity_of_spineRk_bob interpretation r hne S g ms p x' hreach hct_ak
        (fun t hs => by
          obtain ⟨_, _, _, a₀, b₀, ikA₀, ikB₀, spk₀, pqpk₀, opk₀, ek₀, ct₀, keys₀, _, _, hevA⟩ := hs
          exact halice_len32 t a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀ hevA)
        (fun _ _ => kemEncap_fst_attackerKnows_inv hreach)
        (fun b₀ a₀ ikB ikA spk pqpk opk ek ct keys idx hev =>
          (bobDone_ct_pqpk_attackerKnows_of_reachable hreach hev).1)
        hroot_sp hv_sp hsh rfl)
    · rw [hcj, createChain_snd_eq, hkeys_eq, pqxdhKdf_rk_eq] at hsh
      exact absurd hsh (ckOut_ne_hkdfBlock1 b_u _ _ _ _ j_u)
  · rw [hcj, createChain_snd_eq]
    exact .inr (.inr (ckOut_hkdfBlock2_split_of_ak hprk b_u j_u))
  · rcases hv with ⟨j_v, b_v, rfl⟩ | rfl
    · rw [hcj, pqxdhKdf_ck_eq, createChain_snd_eq] at hsh
      have hroot := (ckOut_align hsh).2.2
      have hlbl := (hkdfBlock2_inj hroot).2
      exact absurd hlbl.symm (shape_lit_wr_ne_pq interpretation S g)
    · rw [hcj, pqxdhKdf_ck_eq, hkeys_eq, pqxdhKdf_rk_eq] at hsh
      exact absurd hsh (ckOut_ne_hkdfBlock1 b_u _ _ _ _ j_u)

theorem seedSepAK_bobQ
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (hne : r.alice ≠ r.bob)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (p : PreKeyFields) (x' : PreKeyRep)
    (keys' : HandshakeKeys) (msg' : TRSignalMsg) {seed' : DY.Bytes} {c' : RecvChain}
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hct_ak : x'.ct.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : AliceKemLen32 interpretation S g (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c')) :
    SeedSepAKBob interpretation S g (runTraceMoves r ms) (BobQ r keys' msg') := by
  intro u' v' _ hu hv hsh
  obtain ⟨ikm, _, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  rcases hu with ⟨me, st, idx, hst, rfl | rfl | ⟨c, hc, rfl⟩⟩ | ⟨k, ses, pk, n, rIdx, src, hev⟩
  · obtain ⟨prk, hrk⟩ := stored_rk_form hreach hst
    rcases hv with ⟨j_v, b_v, rfl⟩ | rfl
    · rw [hrk, createChain_snd_eq] at hsh
      exact absurd hsh.symm (ckOut_ne_hkdfBlock1 b_v _ _ _ _ j_v)
    · rw [hrk, hkeys_eq, pqxdhKdf_rk_eq] at hsh
      exact absurd (hkdfBlock1_inj hsh).2 (shape_lit_wr_ne_pq interpretation S g)
  · rcases hv with ⟨j_v, b_v, rfl⟩ | rfl
    · have hu_sp : SpineRk (LoggedOrBobIkmRk r ms p x') true st.cks :=
        spineRk_mono (fun _ _ h => Or.inl h)
          (spStateRk_of_trStoredAt (traceOkR_runTrace r ms) hst).cks
      have hv_sp := spineRk_bobChain_ckOut hne ms hkeys hcmk j_v b_v
      exact .inl (oppParity_of_spineRk_bob interpretation r hne S g ms p x' hreach hct_ak
        (fun t hs => by
          obtain ⟨_, _, _, a₀, b₀, ikA₀, ikB₀, spk₀, pqpk₀, opk₀, ek₀, ct₀, keys₀, _, _, hevA⟩ := hs
          exact halice_len32 t a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀ hevA)
        (fun _ _ => kemEncap_fst_attackerKnows_inv hreach)
        (fun b₀ a₀ ikB ikA spk pqpk opk ek ct keys idx hev =>
          (bobDone_ct_pqpk_attackerKnows_of_reachable hreach hev).1)
        hu_sp hv_sp hsh rfl)
    · obtain ⟨rk1, k, j_u, hcks, _⟩ := stCksIsCreateChain_of_stored hreach hst
      have hsh' : (gamma' interpretation S g
          (ckOut false (chainKeyAt (createChain rk1 k st.dhs).2 j_u))).shape =
          (gamma' interpretation S g keys'.rk).shape := by
        simpa [ckOut, ← hcks] using hsh
      rw [createChain_snd_eq, hkeys_eq, pqxdhKdf_rk_eq] at hsh'
      exact absurd hsh' (ckOut_ne_hkdfBlock1 false _ _ _ _ j_u)
  · exact seedSepAK_bobQ_of_recvChainSpine interpretation r hne S g ms p x' keys' msg'
      hreach hct_ak halice_len32 hkeys hcmk ((stRkSpine_of_stored hreach hst).2 c hc) false hv hsh
  · obtain ⟨c, hc, rfl⟩ :=
      (jRkSpine_reachable hreach (DY.Trace.le_refl (runTraceMoves r ms))).2 k ses pk n u' rIdx src hev
    exact seedSepAK_bobQ_of_recvChainSpine interpretation r hne S g ms p x' keys' msg'
      hreach hct_ak halice_len32 hkeys hcmk (activeRecvChainSpine_imp_recvChainSpine hc) true hv hsh

private theorem peel_stepAK_bob {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {T : ExecTrace} (hT : ReachableTrace T) {Q : DY.Bytes → Prop}
    (hSP : SeedSepAKBob i S g T Q)
    {s₁ i₁ u : DY.Bytes} (hQv : Q (KdfExtract.kdfExtract s₁ i₁))
    (h7 : ∀ b1, (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g i₁).shape)
    (hu : u.AttackerKnows T)
    (hsh : (gamma' i S g u).shape = (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).shape) :
    (KdfExtract.kdfExtract s₁ i₁).AttackerKnows T ∨
      ∃ s' i', u = KdfExtract.kdfExtract s' i' ∧
        (gamma' i S g s').shape = (gamma' i S g s₁).shape ∧
        (gamma' i S g i').shape = (gamma' i S g i₁).shape ∧
        s'.AttackerKnows T ∧ i'.AttackerKnows T := by
  obtain ⟨s', i', hu_eq, hs, hi, hprov⟩ := peel_outer i S g hT hu hsh
  rcases hprov with hH | ⟨b1, rfl⟩ | ⟨hs', hi'⟩
  · rcases hSP u _ hu hH hQv hsh with h | h | ⟨s'', i'', hu'', hs'', hi''⟩
    · exact .inl (by rw [← h]; exact hu)
    · exact .inl h
    · obtain ⟨h1, h2⟩ := kdfExtract_injective (hu_eq.symm.trans hu'')
      exact .inr ⟨s', i', hu_eq, hs, hi, h1 ▸ hs'', h2 ▸ hi''⟩
  · exact absurd hi (h7 b1)
  · exact .inr ⟨s', i', hu_eq, hs, hi, hs', hi'⟩

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace}
    (hle : t ≤ T) {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) :
    (T.at? j : Option E) = some x := by
  by_cases hj : j < t.length
  · rw [← h, at?_of_le hle hj]
  · simp [DY.Trace.at?, hj] at h

local macro "peel_setup_at" : tactic => `(tactic|
  (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
   repeat (first
     | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [DY.Trace.append, DY.Trace.length])
     | exact TR.at?_append_eq _ _ rfl)))

private theorem agree_eq_dh_x25519Key_local (pk : DY.Bytes) {sk : DY.Bytes} {t : Nat}
    (h : sk = randTerm t 32) :
    DY.Libsignal.PQXDH.agree pk sk =
      dh (DY.X25519.normalizeX25519Key pk) (randTerm t 32) := by
  rw [h]; rfl

private theorem runTrace_at?_20 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 20 = some (TR.NetE (DY.PQKem.kemPk (setupSecret r 4))) := by
  have h6 : setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) := by
    rw [(TR.setupPublic_eq r hne).2.2, (TR.setupSecret_eq r hne).2.2.2.1]
  rw [← (TR.setupPublic_eq r hne).2.2, h6]
  refine at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
     repeat (first
       | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
       | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

private theorem ikmHolesKemK_bobPreKeyIkm
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (hne : r.alice ≠ r.bob)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (p : PreKeyFields) (x' : PreKeyRep)
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hek_ak : x'.ek.AttackerKnows (runTraceMoves r ms))
    (hct_ak : x'.ct.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : AliceKemLen32 interpretation S g (runTraceMoves r ms))
    {ikm : DY.Bytes} (hBob : BobPreKeyIkm r p x' ikm) :
    IkmHolesKemK interpretation S g (runTraceMoves r ms) ikm := by
  have hsetup_sec := TR.setupSecret_eq r hne
  obtain ⟨opk, hsel, rfl⟩ := hBob
  refine ⟨agree (setupPublic r 0) (setupSecret r 2), agree x'.ek (setupSecret r 1),
    agree x'.ek (setupSecret r 2),
    opk.map (fun k => agree x'.ek k),
    bobKemShare r x', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨DY.X25519.normalizeX25519Key (setupPublic r 0), 10,
      agree_eq_dh_x25519Key_local _ hsetup_sec.2.2.1,
      attackerKnows_x25519Key (setupPublic_0_attackerKnows r hne ms)⟩
  · exact ⟨DY.X25519.normalizeX25519Key x'.ek, 5,
      agree_eq_dh_x25519Key_local _ hsetup_sec.2.1,
      attackerKnows_x25519Key hek_ak⟩
  · exact ⟨DY.X25519.normalizeX25519Key x'.ek, 10,
      agree_eq_dh_x25519Key_local _ hsetup_sec.2.2.1,
      attackerKnows_x25519Key hek_ak⟩
  · intro d hd
    rcases hsel with ⟨_, rfl⟩ | ⟨hw, _, rfl⟩
    · cases hd
    · simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      exact ⟨DY.X25519.normalizeX25519Key x'.ek, 22,
        agree_eq_dh_x25519Key_local _ (hsetup_sec.2.2.2.2 hw),
        attackerKnows_x25519Key hek_ak⟩
  · have hpqpk_ak : (DY.PQKem.kemPk (setupSecret r 4)).AttackerKnows (runTraceMoves r ms) :=
      Symbolic.Swarm.CREF.TR.attackerKnows_of_at?_network (runTrace_at?_20 r hne ms)
    exact Symbolic.Swarm.CREF.TR.G1.Spine.kemKnownFromTwin_bobKemShare
      interpretation S g hreach halice_len32 hsetup_sec.2.2.2.1 hct_ak hpqpk_ak

private theorem peel_bobChain_chainKeyAt
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {r : ProtocolSetup} {ms : List Move}
    {keys' : HandshakeKeys} {msg' : TRSignalMsg}
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hSP : SeedSepAKBob i S g (runTraceMoves r ms) (BobQ r keys' msg')) :
    ∀ (j : Nat) {u : DY.Bytes}, u.AttackerKnows (runTraceMoves r ms) →
      (gamma' i S g u).shape =
        (gamma' i S g (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)).shape →
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j).AttackerKnows (runTraceMoves r ms) ∨
        ∃ u₀ : DY.Bytes, u₀.AttackerKnows (runTraceMoves r ms) ∧
          (gamma' i S g u₀).shape =
            (gamma' i S g (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2).shape
  | 0, u, hu, hsh => .inr ⟨u, hu, hsh⟩
  | j + 1, u, hu, hsh => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hsh ⊢
    have hQv : BobQ r keys' msg'
        (KdfExtract.kdfExtract
          (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j) (litByte 2)) :=
      .inl ⟨j + 1, false,
        (chainKeyAt_succ_eq_kdfCk_fst (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j).symm⟩
    rcases peel_stepAK_bob hreach hSP hQv (no7_lit i S g _) hu hsh with h |
        ⟨s', _, _, hs, -, hs', -⟩
    · exact .inl h
    · rcases peel_bobChain_chainKeyAt hreach hSP j hs' hs with h | h
      · exact .inl (ak_hmac h (ak_lit _))
      · exact .inr h

/-- Rules out `BsG1cOwnKeyCase` for Bob's pre-key receive when `seed'` is not attacker-known. -/
theorem rpk_not_bsG1cOwnKeyCase
    {interpretation : ExternInterpretation} {r : ProtocolSetup} (hne : r.alice ≠ r.bob)
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {keys' : PQXDH.HandshakeKeys} {seed' salt' : DY.Bytes} {c' : TripleRatchet.RecvChain}
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hek_ak : x'.ek.AttackerKnows (runTraceMoves r ms))
    (hct_ak : x'.ct.AttackerKnows (runTraceMoves r ms))
    (hmsg_ak : x'.msg.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : AliceKemLen32 interpretation S g (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hparse : parseTrSignalMsg x'.msg = some msg')
    (hcmk : TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hseed_ak : ¬ seed'.AttackerKnows (runTraceMoves r ms))
    (hCase : MacInv.BsG1cOwnKeyCase interpretation r S g ms msg' seed' salt') :
    False := by
  let T := runTraceMoves r ms
  have hrk_ak : msg'.ratchetKey.AttackerKnows T :=
    (TR.attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg hmsg_ak hparse).1
  obtain ⟨salt₁, inp₀, _hsalt₁, _hgam, hmac₀, hinp_ak, hsh⟩ := hCase
  obtain ⟨ck₁, hseed'_kdf, _⟩ := consumeMessageKey_eq_some_kdfExtract _ _ _ _ hcmk
  obtain ⟨_salt₀, seed₀, _hsalt₀_ak, hseed₀_ak, _hsalt₀_sh, hseed₀_sh, _hprk_memo, _hmemo₀⟩ :=
    hmac_wire_attackerKnows_inv_memo_of_kdf interpretation r S g ms hreach x'.msg msg' hparse
      ck₁ salt₁ seed' (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2)) inp₀
      hseed'_kdf hmac₀ hinp_ak hsh
  have hSP := seedSepAK_bobQ interpretation r hne S g ms p x' keys' msg'
    hreach hct_ak halice_len32 hkeys hcmk
  let j₀ := msg'.counter.toNat - (bobChain r keys' msg').index.toNat
  have hseed_eq : seed' = KdfExtract.kdfExtract
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j₀) (litByte 1) :=
    (consumeMessageKey_eq_spine hcmk).1
  have hseed₀_sh' : (gamma' interpretation S g seed₀).shape =
      (gamma' interpretation S g (KdfExtract.kdfExtract
        (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j₀) (litByte 1))).shape := by
    rw [← hseed_eq]; exact hseed₀_sh
  have hQ_seed : BobQ r keys' msg' (KdfExtract.kdfExtract
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j₀) (litByte 1)) :=
    .inl ⟨j₀, true, rfl⟩
  rcases peel_stepAK_bob hreach hSP hQ_seed (no7_lit interpretation S g _) hseed₀_ak hseed₀_sh' with
      h | ⟨s₁, _, _, hs₁_sh, -, hs₁_ak, -⟩
  · exact hseed_ak (hseed_eq ▸ h)
  rcases peel_bobChain_chainKeyAt hreach hSP j₀ hs₁_ak hs₁_sh with hck_ak | ⟨u₀, hu₀_ak, hu₀_sh⟩
  · exact hseed_ak (hseed_eq ▸ ak_hmac hck_ak (ak_lit _))
  have hQ_cc : BobQ r keys' msg' (KdfExtract.kdfExtract
      (hmac keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2)))
      (Concat.concat (hkdfBlock1 (hmac keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2))) (lit "WhisperRatchet"))
        (Concat.concat (lit "WhisperRatchet") (litByte 2)))) :=
    .inl ⟨0, false, rfl⟩
  rcases peel_stepAK_bob hreach hSP hQ_cc (no7_wr2 interpretation S g _) hu₀_ak hu₀_sh with
      hcc_ak | ⟨s₂, _, _, hs₂_sh, -, hs₂_ak, -⟩
  · exact hseed_ak (hseed_eq ▸ ak_hmac (attackerKnows_chainKeyAt_srk j₀ hcc_ak) (ak_lit _))
  have hd_hole : DhHoleK (·.AttackerKnows T)
      (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2)) := by
    refine ⟨DY.X25519.normalizeX25519Key msg'.ratchetKey, 10, ?_, attackerKnows_x25519Key hrk_ak⟩
    rw [(TR.setupSecret_eq r hne).2.2.1]
  obtain ⟨rk', _, _, hrk'_sh, hrk'_ak, hd_ak⟩ :=
    peel_rk interpretation S g hreach hd_hole hs₂_ak hs₂_sh
  obtain ⟨ikm, hBob, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  have hrk_eq : keys'.rk = KdfExtract.kdfExtract (hmac zeroSalt ikm)
      (Concat.concat pqxdhLabel (litByte 1)) := by
    rw [hkeys_eq]; rfl
  have hrk'_sh' : (gamma' interpretation S g rk').shape =
      (gamma' interpretation S g (KdfExtract.kdfExtract (hmac zeroSalt ikm)
        (Concat.concat pqxdhLabel (litByte 1)))).shape := by
    rw [← hrk_eq]; exact hrk'_sh
  have hQ_rk : BobQ r keys' msg' (KdfExtract.kdfExtract (hmac zeroSalt ikm)
      (Concat.concat pqxdhLabel (litByte 1))) :=
    .inr hrk_eq.symm
  rcases peel_stepAK_bob hreach hSP hQ_rk (no7_x1 interpretation S g _) hrk'_ak hrk'_sh' with
      hrk_ak' | ⟨s₃, _, _, hs₃_sh, -, hs₃_ak, -⟩
  · have hcc_ak : (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2.AttackerKnows T :=
      ak_hkdfBlock2 (ak_hmac (hrk_eq ▸ hrk_ak') hd_ak) (ak_lit _)
    exact hseed_ak (hseed_eq ▸ ak_hmac (attackerKnows_chainKeyAt_srk j₀ hcc_ak) (ak_lit _))
  have hikm_ak : ikm.AttackerKnows T :=
    peel_ikm interpretation S g hreach
      (ikmHolesKemK_bobPreKeyIkm interpretation r hne S g ms p x'
        hreach hek_ak hct_ak halice_len32 hBob)
      hs₃_ak hs₃_sh
  have hrk_ak' : keys'.rk.AttackerKnows T :=
    hrk_eq ▸ ak_hkdfBlock1 (ak_hmac (ak_lit _) hikm_ak) (ak_lit _)
  have hcc_ak : (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2.AttackerKnows T :=
    ak_hkdfBlock2 (ak_hmac hrk_ak' hd_ak) (ak_lit _)
  exact hseed_ak (hseed_eq ▸ ak_hmac (attackerKnows_chainKeyAt_srk j₀ hcc_ak) (ak_lit _))

end Symbolic.Swarm.CREF.CliPure
