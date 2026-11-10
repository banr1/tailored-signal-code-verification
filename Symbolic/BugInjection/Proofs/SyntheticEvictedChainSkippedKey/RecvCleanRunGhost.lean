/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Clean Ghost Construction and Ratchet Key Injectivity

Defines the canonical clean ghost `gClean r cls` aligned with the compact trace timestamps of
`ssClean cls cleanSpqrIdxs`, transfers `GhostAndSemMatchSetup` from any outer ghost to `gClean`,
and proves that all 13 honest DH ratchet public keys in `ratchetKeyTimestamps` concretize to
pairwise distinct `evictedPubOfIdx` values (`gamma_ratchetKeyTimestamps_inj`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost

open scoped DY.Libsignal.Composed
open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.TripleRatchet (TRState trHonestWireMsg messageVersion)
open DY.Libsignal.Refinement (x25519PublicKeySymbol canonicalVariation)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost
   gamma gamma' concretizeAll concretizeKemPk concretizeSign clamp slice randTerm
   setupRandomsAt setupPublic secretBytes GhostAndSemMatchSetup)
open DY.Libsignal.Composed.Refinement.Cli (serializeAddresses aliceUuid bobUuid)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (stA0)
open Symbolic.Swarm.CREF.TR (gamma_rand gamma_litByte gamma_concat gamma_dhPk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedSecretIdx evictedPubOfIdx
   evictedLookupPub evictedPubOfOpt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws (evictedI0_publicKey)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev ev3_coins_idx ev7_coins_idx ev11_coins_idx ev15_coins_idx ev19_coins_idx ev23_coins_idx
   evictedPubOfIdx_inj)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace (r_names_of_fit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev0KyberEnt ev0_coins_facts ev5_coins_idx ev9_coins_idx ev13_coins_idx ev17_coins_idx ev21_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (ratchetKeyTimestamps pt1Clean coins1Clean key1Clean pt2Clean coins2Clean key2Clean stA1Clean)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- Serialized `(alice, bob)` protocol address pair on `PreKeySignalMessage` sends. -/
abbrev pqAddrBytes : HwBytes :=
  serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩

/-- Canonical clean `Ghost` aligned with the compact timestamps of `ssClean cls cleanSpqrIdxs`. -/
def gClean (r : ProtocolSetup) (cls : Nat → Nat) : Ghost where
  σ ts n :=
    if ts < 22 then r.fresh ts n
    else if ts = 22 then slice (ev 0).coins 0 32
    else if ts = 23 then ev0KyberEnt
    else if ts = 24 then slice (ev 0).coins 160 32
    else if ts = 31 then (ev 1).input
    else if ts = 32 then (ev 1).coins.take n
    else if ts = 38 then (ev 2).input
    else if ts = 39 then (ev 2).coins.take n
    else if ts = 45 then (ev 3).coins.take 32
    else if 55 ≤ ts ∧ (ts - 55) / 14 < 10 then
      let h := (ts - 55) / 14
      let rem := (ts - 55) % 14
      if rem = 0 then (ev (4 + 2 * h)).input
      else if rem = 1 then (ev (4 + 2 * h)).coins.take n
      else if rem = 7 then (ev (5 + 2 * h)).coins.take 32
      else r.fresh ts n
    else r.fresh ts n
  addr t :=
    if t == (encSig stA0 (coins1Clean cls) (key1Clean cls) pt1Clean).wire ||
       t == (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean).wire then
      pqAddrBytes
    else []

theorem gClean_sigma_lt22 (r : ProtocolSetup) (cls : Nat → Nat) {ts n : Nat} (h : ts < 22) :
    (gClean r cls).σ ts n = r.fresh ts n := by
  simp [gClean, h]

theorem gClean_sigma_22 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 22 n = slice (ev 0).coins 0 32 := rfl

theorem gClean_sigma_23 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 23 n = ev0KyberEnt := rfl

theorem gClean_sigma_24 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 24 n = slice (ev 0).coins 160 32 := rfl

theorem gClean_sigma_31 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 31 n = (ev 1).input := rfl

theorem gClean_sigma_32 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 32 n = (ev 1).coins.take n := rfl

theorem gClean_sigma_38 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 38 n = (ev 2).input := rfl

theorem gClean_sigma_39 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 39 n = (ev 2).coins.take n := rfl

theorem gClean_sigma_45 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 45 n = (ev 3).coins.take 32 := rfl

theorem gClean_sigma_whisper_pt (r : ProtocolSetup) (cls : Nat → Nat) {h n : Nat} (hh : h < 10) :
    (gClean r cls).σ (55 + 14 * h) n = (ev (4 + 2 * h)).input := by
  have h1 : ¬ (55 + 14 * h < 22) := by omega
  have hdiv : (55 + 14 * h - 55) / 14 = h := by omega
  have hrem : (55 + 14 * h - 55) % 14 = 0 := by omega
  unfold gClean
  simp only [h1, show 55 + 14 * h ≠ 22 by omega, show 55 + 14 * h ≠ 23 by omega,
    show 55 + 14 * h ≠ 24 by omega, show 55 + 14 * h ≠ 31 by omega,
    show 55 + 14 * h ≠ 32 by omega, show 55 + 14 * h ≠ 38 by omega,
    show 55 + 14 * h ≠ 39 by omega, show 55 + 14 * h ≠ 45 by omega,
    show 55 ≤ 55 + 14 * h by omega, hdiv, hh, and_self, hrem, ↓reduceIte]

theorem gClean_sigma_whisper_coins (r : ProtocolSetup) (cls : Nat → Nat) {h n : Nat} (hh : h < 10) :
    (gClean r cls).σ (55 + 14 * h + 1) n = (ev (4 + 2 * h)).coins.take n := by
  have h1 : ¬ (55 + 14 * h + 1 < 22) := by omega
  have hdiv : (55 + 14 * h + 1 - 55) / 14 = h := by omega
  have hrem : (55 + 14 * h + 1 - 55) % 14 = 1 := by omega
  unfold gClean
  simp only [h1, show 55 + 14 * h + 1 ≠ 22 by omega, show 55 + 14 * h + 1 ≠ 23 by omega,
    show 55 + 14 * h + 1 ≠ 24 by omega, show 55 + 14 * h + 1 ≠ 31 by omega,
    show 55 + 14 * h + 1 ≠ 32 by omega, show 55 + 14 * h + 1 ≠ 38 by omega,
    show 55 + 14 * h + 1 ≠ 39 by omega, show 55 + 14 * h + 1 ≠ 45 by omega,
    show 55 ≤ 55 + 14 * h + 1 by omega, hdiv, hh, and_self, hrem,
    show (1 : Nat) ≠ 0 by decide, ↓reduceIte]

theorem gClean_sigma_whisper_dhs (r : ProtocolSetup) (cls : Nat → Nat) {h n : Nat} (hh : h < 10) :
    (gClean r cls).σ (55 + 14 * h + 7) n = (ev (5 + 2 * h)).coins.take 32 := by
  have h1 : ¬ (55 + 14 * h + 7 < 22) := by omega
  have hdiv : (55 + 14 * h + 7 - 55) / 14 = h := by omega
  have hrem : (55 + 14 * h + 7 - 55) % 14 = 7 := by omega
  unfold gClean
  simp only [h1, show 55 + 14 * h + 7 ≠ 22 by omega, show 55 + 14 * h + 7 ≠ 23 by omega,
    show 55 + 14 * h + 7 ≠ 24 by omega, show 55 + 14 * h + 7 ≠ 31 by omega,
    show 55 + 14 * h + 7 ≠ 32 by omega, show 55 + 14 * h + 7 ≠ 38 by omega,
    show 55 + 14 * h + 7 ≠ 39 by omega, show 55 + 14 * h + 7 ≠ 45 by omega,
    show 55 ≤ 55 + 14 * h + 7 by omega, hdiv, hh, and_self, hrem,
    show (7 : Nat) ≠ 0 by decide, show (7 : Nat) ≠ 1 by decide, ↓reduceIte]

theorem trHonestWireMsg_rk_inj {rk1 rk2 ct1 ct2 pq1 pq2 : Bytes} {ns1 pn1 ns2 pn2 : UInt32}
    (h : trHonestWireMsg rk1 ns1 pn1 ct1 pq1 = trHonestWireMsg rk2 ns2 pn2 ct2 pq2) :
    rk1 = rk2 := by
  have hpack :
      (({ version := messageVersion, senderRatchetKey := rk1, counter := ns1,
          previousCounter := pn1, ciphertext := ct1, pqRatchet := pq1,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) =
      (({ version := messageVersion, senderRatchetKey := rk2, counter := ns2,
          previousCounter := pn2, ciphertext := ct2, pqRatchet := pq2,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := h
  have hsub := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack
  exact congrArg DY.TrWire.TrWireMsg.SubF.senderRatchetKey hsub

theorem dhPk_rnd_inj {ts1 ts2 n1 n2 : Nat}
    (h : dhPk (rnd ts1 n1) = dhPk (rnd ts2 n2)) : ts1 = ts2 := by
  have hpack1 :
      (({ sk := rnd ts1 n1 } : DY.DiffieHellman.DhPk.SubF Bytes).pack) =
      (({ sk := rnd ts2 n2 } : DY.DiffieHellman.DhPk.SubF Bytes).pack) := h
  have hsk := congrArg DY.DiffieHellman.DhPk.SubF.sk
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack1)
  have hpack2 :
      (({ timestamp := ts1, size := n1 } : DY.Random.Random Bytes).pack) =
      (({ timestamp := ts2, size := n2 } : DY.Random.Random Bytes).pack) := hsk
  exact congrArg DY.Random.Random.timestamp
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack2)

theorem gClean_addr_m1 (r : ProtocolSetup) (cls : Nat → Nat) :
    (gClean r cls).addr (encSig stA0 (coins1Clean cls) (key1Clean cls) pt1Clean).wire =
      pqAddrBytes := by
  unfold gClean
  simp

theorem gClean_addr_m2 (r : ProtocolSetup) (cls : Nat → Nat) :
    (gClean r cls).addr (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean).wire =
      pqAddrBytes := by
  unfold gClean
  simp

theorem gClean_addr_whisper (r : ProtocolSetup) (cls : Nat → Nat)
    {stSend : TRState} {coins pqKey pt : Bytes} {tsSend : Nat}
    (hdhs : stSend.dhs = rnd tsSend 32) (hne : tsSend ≠ 24) :
    (gClean r cls).addr (encSig stSend coins pqKey pt).wire = [] := by
  have hne1 : (encSig stSend coins pqKey pt).wire ≠
      (encSig stA0 (coins1Clean cls) (key1Clean cls) pt1Clean).wire := by
    intro heq
    have hrk := trHonestWireMsg_rk_inj heq
    rw [hdhs] at hrk
    exact hne (dhPk_rnd_inj hrk)
  have hne2 : (encSig stSend coins pqKey pt).wire ≠
      (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean).wire := by
    intro heq
    have hrk := trHonestWireMsg_rk_inj heq
    rw [hdhs] at hrk
    exact hne (dhPk_rnd_inj hrk)
  unfold gClean
  simp [hne1, hne2]

theorem gamma_KemPk (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk : Bytes) :
    gamma i S g (DY.PQKem.kemPk sk) = S.kemPk (gamma i S g sk) := by
  unfold gamma gamma'
  show ((({ sk } : DY.PQKem.Pk.SubF Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]; rfl

theorem gamma_Sign (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk n m : Bytes) :
    gamma i S g (DY.Signature.sign sk n m) =
      S.sign (gamma i S g sk) (gamma i S g n) (gamma i S g m) := by
  unfold gamma gamma'
  show ((({ sk, nonce := n, msg := m } : DY.Signature.Sign.SubF Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]; rfl

theorem setupRandomsAt_of_fit {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  have ho : r.withOpk = false := hfit.1.1.2.1
  have h := Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe
  rw [ho] at h
  simpa using h

theorem ghostAndSemMatchSetup_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (cls : Nat → Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hCompat : GhostAndSemMatchSetup evictedI0 r S g) :
    GhostAndSemMatchSetup evictedI0 r S (gClean r cls) := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  have hrandAt := setupRandomsAt_of_fit hfit
  have hc1 : ∀ p ∈ setupRandomsAt r, (gClean r cls).σ p.1 p.2 = r.fresh p.1 p.2 := by
    rw [hrandAt]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact gClean_sigma_lt22 r cls (by decide)
  have hsig_eq : ∀ ts n, (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] →
      n ≠ 0 → gamma evictedI0 S (gClean r cls) (randTerm ts n) =
        gamma evictedI0 S g (randTerm ts n) := by
    intro ts n hmem hn
    have hmem' : (ts, n) ∈ setupRandomsAt r := hrandAt ▸ hmem
    unfold randTerm
    rw [gamma_rand, gamma_rand]
    simp only [hn, ↓reduceIte]
    exact (hc1 (ts, n) hmem').trans (hCompat.1 (ts, n) hmem').symm
  refine ⟨hc1, ?_, hCompat.2.2⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [← hCompat.2.1 r.spkSigTerm (by simp), show r.spkSigTerm = setupPublic r 5 from rfl,
      Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]
    unfold DY.Libsignal.PQXDH.encodeEC
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_dhPk, gamma_dhPk,
        hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 11 64 (by decide) (by decide),
        hsig_eq 10 32 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkPubTerm (by simp), show r.pqpkPubTerm = setupPublic r 6 from rfl,
      Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe]
    rw [gamma_KemPk, gamma_KemPk, hsig_eq 16 64 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkSigTerm (by simp), show r.pqpkSigTerm = setupPublic r 7 from rfl,
      Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]
    unfold DY.Libsignal.PQXDH.encodeKEM
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_KemPk, gamma_KemPk,
        hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 17 64 (by decide) (by decide),
        hsig_eq 16 64 (by decide) (by decide)]

/-- Secret-table index in `Fin 16` for each timestamp in `ratchetKeyTimestamps` under `gClean`. -/
def ratchetTsSecretIdx : Nat → Fin 16
  | 10 => ⟨2, by decide⟩
  | 24 => ⟨4, by decide⟩
  | 45 => ⟨5, by decide⟩
  | 62 => ⟨6, by decide⟩
  | 76 => ⟨7, by decide⟩
  | 90 => ⟨8, by decide⟩
  | 104 => ⟨9, by decide⟩
  | 118 => ⟨10, by decide⟩
  | 132 => ⟨11, by decide⟩
  | 146 => ⟨12, by decide⟩
  | 160 => ⟨13, by decide⟩
  | 174 => ⟨14, by decide⟩
  | _ => ⟨15, by decide⟩

private theorem spkSec_idx : evictedSecretIdx (clamp w0.spk) = some ⟨2, by decide⟩ := by
  decide +kernel

theorem gamma_dhPk_ratchetTs {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {ts : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hts : ts ∈ ratchetKeyTimestamps) :
    gamma evictedI0 S (gClean r cls) (dhPk (rnd ts 32)) =
      evictedPubOfIdx (ratchetTsSecretIdx ts) := by
  have hsecIdx : evictedSecretIdx (clamp ((gClean r cls).σ ts 32)) =
      some (ratchetTsSecretIdx ts) := by
    simp only [ratchetKeyTimestamps, List.mem_cons, List.not_mem_nil, or_false] at hts
    rcases hts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gClean_sigma_lt22 r cls (by decide)]
      have hsec2 : secretBytes r 2 = r.fresh 10 32 := by
        unfold secretBytes
        rw [setupRandomsAt_of_fit hfit]; rfl
      have hspk : secretBytes r 2 = w0.spk := hfit.1.1.2.2.2.2.2.2.2.2.1
      rw [← hsec2, hspk]
      exact spkSec_idx
    · rw [gClean_sigma_24]; exact ev0_coins_facts.2.2.1
    · rw [gClean_sigma_45]; exact ev3_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 0) (n := 32) (by decide))).trans ev5_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 1) (n := 32) (by decide))).trans ev7_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 2) (n := 32) (by decide))).trans ev9_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 3) (n := 32) (by decide))).trans ev11_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 4) (n := 32) (by decide))).trans ev13_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 5) (n := 32) (by decide))).trans ev15_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 6) (n := 32) (by decide))).trans ev17_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 7) (n := 32) (by decide))).trans ev19_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 8) (n := 32) (by decide))).trans ev21_coins_idx
    · exact (congrArg (fun b => evictedSecretIdx (clamp b))
        (gClean_sigma_whisper_dhs r cls (h := 9) (n := 32) (by decide))).trans ev23_coins_idx
  unfold rnd
  rw [gamma_dhPk, gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, evictedI0_publicKey]
  unfold evictedLookupPub evictedPubOfOpt
  rw [hsecIdx]; rfl

theorem gamma_ratchetKeyTimestamps_inj {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {ts₁ ts₂ : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (h1 : ts₁ ∈ ratchetKeyTimestamps) (h2 : ts₂ ∈ ratchetKeyTimestamps)
    (heq : gamma evictedI0 S (gClean r cls) (dhPk (rnd ts₁ 32)) =
           gamma evictedI0 S (gClean r cls) (dhPk (rnd ts₂ 32))) :
    ts₁ = ts₂ := by
  rw [gamma_dhPk_ratchetTs hfit h1, gamma_dhPk_ratchetTs hfit h2] at heq
  have hidx := evictedPubOfIdx_inj heq
  simp only [ratchetKeyTimestamps, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (simp [ratchetTsSecretIdx] at hidx)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
