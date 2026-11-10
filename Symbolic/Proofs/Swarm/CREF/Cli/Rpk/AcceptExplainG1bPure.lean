/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.MacInv
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainG1bAux
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# Honest-Send MAC Branch for Pre-Key Session Start

Proves `rpk_bsG1bHonestSendCase`: when Bob's pre-key receive matches an honest sender's MAC input
(`BsG1bHonestSendCase`), the wire bytes admit a canonical `PreKeyRep` whose MAC and ciphertext
decrypt under the same `(salt', seed')`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg trMsgKeys trHonestWireMsg)
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey computeMac messageVersion)
open DY.Libsignal.PQXDH (HandshakeKeys agree errToOption serializedIk)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

private theorem g1b_eq_of_uOf_eq_canonical {A B : HwBytes} (hA : A.length = 32)
    (hB : B.length = 32)
    (hAc : DY.X25519.leValue (A.map BitVec.toNat) < DY.X25519.p25519)
    (hBc : DY.X25519.leValue (B.map BitVec.toNat) < DY.X25519.p25519)
    (hu : x25519UCoord A = x25519UCoord B) : A = B := by
  have hp := TR.p25519_lt
  have hAB : DY.X25519.leValue (A.map BitVec.toNat) = DY.X25519.leValue (B.map BitVec.toNat) := by
    unfold x25519UCoord DY.X25519.uCoord at hu
    rwa [Nat.mod_eq_of_lt (by omega : DY.X25519.leValue (A.map BitVec.toNat) < 2 ^ 255),
      Nat.mod_eq_of_lt (by omega : DY.X25519.leValue (B.map BitVec.toNat) < 2 ^ 255),
      Nat.mod_eq_of_lt hAc, Nat.mod_eq_of_lt hBc] at hu
  rw [← TR.RecvRep.leBytes_leValue A, ← TR.RecvRep.leBytes_leValue B, hA, hB, hAB]

private theorem g1b_gamma_variant_pack (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : DY.X25519.Variant.SubF DY.Bytes) :
    gamma i S g v.pack =
      variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g v.key) v.torsion)
        v.variation := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

private theorem g1b_torsionShift_length (i : ExternInterpretation) (point : HwBytes) (t : Fin 8) :
    (DY.Libsignal.Refinement.torsionShift i point t).length = point.length := by
  unfold DY.Libsignal.Refinement.torsionShift
  split
  · rfl
  · rename_i h
    have hlen : point.length = 32 := by revert h; simp
    split
    · split
      · rename_i q _ hq; omega
      · rfl
    · rfl

private theorem g1b_gamma_x25519Key_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold i)
    (hPubCanon : X25519PubCanonical i)
    (hRej : DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected i)
    (ek sk : DY.Bytes)
    (hkey : DY.X25519.normalizeX25519Key ek = DY.DiffieHellman.dhPk sk)
    (hek_canon : DY.X25519.leValue ((gamma i S g ek).map BitVec.toNat) < DY.X25519.p25519)
    (hek_tf : DY.Libsignal.PQXDH.Refinement.X25519TorsionFree i (gamma i S g ek)) :
    gamma i S g (DY.X25519.normalizeX25519Key ek) = gamma i S g ek := by
  unfold DY.X25519.normalizeX25519Key at hkey ⊢
  cases hview : ek.view? DY.X25519.Variant.SubF with
  | none => rfl
  | some x =>
    simp only [hview] at hkey ⊢
    have hpack : x.pack = ek := by
      have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF ek
      simpa [hview] using hp
    have hgamma_ek : gamma i S g ek =
        variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion)
          x.variation := by
      rw [← hpack, g1b_gamma_variant_pack]
    have hl_key : (gamma i S g x.key).length = 32 := by
      rw [hkey, TR.gamma_dhPk]
      exact hEq.x25519_public_key_length (clamp (gamma i S g sk))
    have hk_canon : DY.X25519.leValue ((gamma i S g x.key).map BitVec.toNat) < DY.X25519.p25519 := by
      rw [hkey, TR.gamma_dhPk]
      exact hPubCanon (clamp (gamma i S g sk))
    have hl_ts :
        (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion).length = 32 := by
      rw [g1b_torsionShift_length, hl_key]
    have hs := TR.variantBytes_spec _ hl_ts x.variation
    have hl_ek : (gamma i S g ek).length = 32 := by
      rw [hgamma_ek]; exact hs.1
    have hu_ek_ts : x25519UCoord (gamma i S g ek) =
        x25519UCoord (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion) := by
      rw [hgamma_ek]; exact hs.2
    have hu_eq : x25519UCoord (gamma i S g ek) = x25519UCoord (gamma i S g x.key) := by
      by_contra hne
      have hvk : gamma i S g x.key =
          (i DY.Libsignal.Refinement.x25519PublicKeySymbol [clamp (gamma i S g sk)]).getD [] := by
        rw [hkey, TR.gamma_dhPk]
      unfold x25519UCoord at hu_ek_ts hne
      rw [hvk] at hu_ek_ts hne
      exact hRej (clamp (gamma i S g sk)) x.torsion (gamma i S g ek)
        hl_ek hu_ek_ts hne hek_tf
    exact (g1b_eq_of_uOf_eq_canonical hl_ek hl_key hek_canon hk_canon hu_eq).symm

private theorem g1b_spqrRecv_init_salt {a q m m' st salt : DY.Bytes} {idx : UInt32}
    (hm' : DY.Spqr.spqrEmptyMsg m' = false)
    (h : DY.Spqr.spqrRecv (DY.Spqr.spqrInit a q) m idx = some (st, salt)) :
    ∃ st', DY.Spqr.spqrRecv (DY.Spqr.spqrInit a q) m' idx = some (st', salt) := by
  unfold DY.Spqr.spqrRecv at h ⊢
  rw [hm']
  split at h
  · cases h
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split at h <;> rename_i hview
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨_, by rw [← h.2]⟩
      · cases h
    · exfalso; unfold DY.Spqr.spqrInit at hview; rw [DY.BytesView.view_pack] at hview
      cases hview

private theorem g1b_spineRk_mono {B B' : Bool → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → B' c m) {b : Bool} {u : DY.Bytes}
    (hu : SpineRk B b u) : SpineRk B' b u := by
  induction hu with
  | hsRk h => exact .hsRk (hB _ _ h)
  | hsCk h => exact .hsCk (hB _ _ h)
  | rkStep1 hrk hh ih => exact .rkStep1 ih hh
  | rkStep2 hrk hh ih => exact .rkStep2 ih hh
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

set_option linter.unusedVariables false in
theorem rpk_bsG1bHonestSendCase
    {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b pt : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {keys' : PQXDH.HandshakeKeys} {seed' salt' st'' : DY.Bytes} {c' : TripleRatchet.RecvChain}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (hpubcanon : X25519PubCanonical interpretation ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected interpretation)
    (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hp : parsePreKeyWire b = some p)
    (hx' : x' ∈ preKeyRepresentations interpretation r S g ms b)
    (hnbsc : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g ms p x')
    (hkeys : bobKeys r p x' = some keys')
    (hparse : parseTrSignalMsg x'.msg = some msg')
    (hcmk : TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hspqr : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys'.pqr TripleRatchet.spqrB2A)
      msg'.pqRatchet (preKeySpqrIndex p) = some (st'', salt'))
    (hbss : TR.bobSaltSeed r p x' = some (salt', seed'))
    (hek_len : (gamma interpretation S g x'.ek).length = 32)
    (hek_canon : DY.X25519.leValue ((gamma interpretation S g x'.ek).map BitVec.toNat) < DY.X25519.p25519)
    (hek_notlow : DY.X25519.isLowOrderKey ((gamma interpretation S g x'.ek).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation (gamma interpretation S g x'.ek))
    (hlow' : TripleRatchet.x25519LowOrder msg'.ratchetKey = false)
    (hdec_wire : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [gamma interpretation S g msg'.ciphertext,
       gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').cipherKey,
       (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt)
    (hpq_ne : gamma interpretation S g msg'.pqRatchet ≠ [])
    (hseed_ak : ¬ seed'.AttackerKnows (runTraceMoves r ms))
    (hCase : MacInv.BsG1bHonestSendCase interpretation r S g ms msg' seed' salt') :
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g ms b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt', seed') ∧
      pqSalt.AttackerKnows (runTraceMoves r ms) ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed').macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed').cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed').iv msg.ciphertext) = some m ∧
      gamma interpretation S g m = pt := by
  have hne : r.alice ≠ r.bob := hwf.1
  have hreach : (runTraceMoves r ms).Reachable reachability := hmp.2.1.2.2.1.1
  obtain ⟨salt₁, hsalt₁, ⟨hck_eq, _hmk_eq, hiv_eq⟩, pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s,
    pqMsg_s, ns_s, pn_s, t_s, st_s, hmac_eq, htrunc_ak, hpq_ak, ht'_ak, ha_eq, hst_s, hmyIk_s,
    hpeerIk_s, hseed_s, hsh_inp⟩ := hCase
  obtain ⟨hpq_sh, hseed_sh, hmyIk_sh, hpeerIk_sh, hwire_sh⟩ :=
    shape_inp_honest_inj interpretation S g hsh_inp
  obtain ⟨hek_ak, hct_ak, _, hmatch, p₀, hp₀, hfaith⟩ := hx'
  have hseed_eq : seed_s = seed' := by
    have hu : SpineRk (LoggedOrBobIkmRk r ms p x') false seed' := spineRk_bobSeed hne ms hkeys hcmk
    have hv : SpineRk (LoggedOrBobIkmRk r ms p x') true seed_s := by
      rw [← hseed_s]
      exact g1b_spineRk_mono (fun _ _ h => Or.inl h) (spineRk_send_runTrace hst_s)
    exact oppParity_of_spineRk_bob interpretation r hne S g ms p x' hreach hct_ak
      (fun t hs => by
        obtain ⟨_, _, _, a₀, b₀, ikA₀, ikB₀, spk₀, pqpk₀, opk₀, ek₀, ct₀, keys₀, _, _, hevA⟩ := hs
        exact aliceKemLen32_of_matchedPrefix hmp t a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀ hevA)
      (fun _ _ => kemEncap_fst_attackerKnows_inv hreach)
      (fun b₀ a₀ ikB ikA spk pqpk opk ek ct keys idx hev =>
        (bobDone_ct_pqpk_attackerKnows_of_reachable hreach hev).1)
      hv hu hseed_sh rfl
  have hIk := TR.G1.Ik.availableIkShapeId_all r ms st_s hst_s
  have hmyIk_eq : myIk_s = serializedIk (setupPublic r 0) := by
    rw [← hmyIk_s] at hmyIk_sh ⊢
    refine eq_of_shape_eq_of_shapeId hIk.1 (TR.G1.Ik.shapeId_serializedIk ?_) hmyIk_sh
    rw [(TR.setupPublic_eq r hne).1, (TR.setupSecret_eq r hne).1]
    exact TR.G1.termShapeId_dhPk (TR.G1.termShapeId_randTerm32 0)
  have hpeerIk_eq : peerIk_s = serializedIk (setupPublic r 2) := by
    rw [← hpeerIk_s] at hpeerIk_sh ⊢
    refine eq_of_shape_eq_of_shapeId hIk.2 (TR.G1.Ik.shapeId_serializedIk ?_) hpeerIk_sh
    rw [(TR.setupPublic_eq r hne).2.1, (TR.setupSecret_eq r hne).2.1]
    exact TR.G1.termShapeId_dhPk (TR.G1.termShapeId_randTerm32 5)
  obtain ⟨t_e, hek_key⟩ := rpk_g1b_ek_honest interpretation S g hne hkeys hcmk hst_s
    (hseed_s.trans hseed_eq)
  have hek_gamma : gamma interpretation S g (DY.X25519.normalizeX25519Key x'.ek) =
      gamma interpretation S g x'.ek :=
    g1b_gamma_x25519Key_eq interpretation S g hEq hpubcanon.1 hpubcanon.2
      x'.ek (randTerm t_e 32) hek_key hek_canon hek_notlow.2
  let ct_s := SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s
  let wire_s := trHonestWireMsg (dhPk a_s) ns_s pn_s ct_s pqMsg_s
  let t' := Concat.concat wire_s msg'.mac
  let msg₁ : TRSignalMsg :=
    { wire := wire_s, mac := msg'.mac, version := messageVersion, ratchetKey := dhPk a_s,
      counter := ns_s, ciphertext := ct_s, pqRatchet := pqMsg_s }
  have hmac' : msg'.mac = computeMac (trMsgKeys pqSalt_s seed_s).macKey myIk_s peerIk_s wire_s := by
    unfold computeMac; exact hmac_eq
  obtain ⟨hver_eq, hsh_rk, hctr_eq, hsh_ct, hsh_pq⟩ :
      messageVersion = msg'.version ∧
      (gamma' interpretation S g (dhPk a_s)).shape =
        (gamma' interpretation S g msg'.ratchetKey).shape ∧
      ns_s = msg'.counter ∧
      (gamma' interpretation S g ct_s).shape =
        (gamma' interpretation S g msg'.ciphertext).shape ∧
      (gamma' interpretation S g pqMsg_s).shape =
        (gamma' interpretation S g msg'.pqRatchet).shape := by
    unfold parseTrSignalMsg at hparse
    cases hsp : Concat.split x'.msg (x'.msg.length - Trunc.trunc8Length) with
    | none => rw [hsp] at hparse; cases hparse
    | some wm =>
      rcases wm with ⟨w₀, mac₀⟩
      rw [hsp] at hparse
      dsimp only [Bind.bind, Option.bind] at hparse
      have hvp := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF w₀
      cases hwf : DY.TrWire.trWireMsgFields? w₀ with
      | none => rw [hwf] at hparse; cases hparse
      | some x₀ =>
        rw [hwf] at hparse
        dsimp only [Pure.pure] at hparse
        have hview : w₀.view? DY.TrWire.TrWireMsg.SubF = some x₀ := hwf
        rw [hview] at hvp; dsimp only at hvp
        injection hparse with hmsg; subst hmsg
        rw [← hvp] at hwire_sh
        obtain ⟨_, hv_eq, hsh_rk, hctr_eq, _, hsh_ct, hsh_pq, _⟩ :=
          TR.G1.trWireMsg_shape_eq_imp_addr_eq interpretation interpretation S S g g
            messageVersion (dhPk a_s) ns_s pn_s ct_s pqMsg_s DY.TrWire.canonicalVariation
            x₀.version x₀.senderRatchetKey x₀.counter x₀.previousCounter
            x₀.ciphertext x₀.pqRatchet x₀.encodingVariation hwire_sh
        exact ⟨by dsimp only; rw [← hv_eq]; decide, hsh_rk, hctr_eq, hsh_ct, hsh_pq⟩
  have hrk_eq : dhPk a_s = msg'.ratchetKey := by
    rw [ha_eq] at hsh_rk ⊢
    exact eq_dhPk_randTerm32_of_shape_eq interpretation S g t_s hsh_rk
  have hct_gamma : gamma interpretation S g ct_s = gamma interpretation S g msg'.ciphertext :=
    gamma_eq_of_shape_eq interpretation S g ct_s msg'.ciphertext hsh_ct
  have hpq_gamma : gamma interpretation S g pqMsg_s = gamma interpretation S g msg'.pqRatchet :=
    gamma_eq_of_shape_eq interpretation S g pqMsg_s msg'.pqRatchet hsh_pq
  have hwire_gamma : gamma interpretation S g wire_s = gamma interpretation S g msg'.wire :=
    gamma_eq_of_shape_eq interpretation S g wire_s msg'.wire hwire_sh
  have hparse₁ : parseTrSignalMsg t' = some msg₁ := by
    dsimp only [t', msg₁]
    rw [hmac']
    exact parseTrSignalMsg_trHonestWireMsg_computeMac (dhPk a_s) ns_s pn_s ct_s pqMsg_s
      (trMsgKeys pqSalt_s seed_s).macKey myIk_s peerIk_s
  have ht'_gamma : gamma interpretation S g t' = gamma interpretation S g x'.msg := by
    rw [parseTrSignalMsg_eq_concat hparse]
    dsimp only [t']
    rw [TR.gamma_concat, TR.gamma_concat, hwire_gamma]
  have hv_var : (dhPk (randTerm t_e 32)).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  have hv_lit : (dhPk (randTerm t_e 32)).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  have hkk : DY.X25519.normalizeX25519Key (DY.X25519.normalizeX25519Key x'.ek) = DY.X25519.normalizeX25519Key x'.ek := by
    rw [hek_key]
    simp only [DY.X25519.normalizeX25519Key, hv_var]
  have hkeys₁ : bobKeys r p { ek := DY.X25519.normalizeX25519Key x'.ek, ct := x'.ct, msg := t' } =
      some keys' := by
    rw [← hkeys]
    unfold bobKeys bobKeysOf PQXDH.agree
    simp only [hkk]
  have hchain : bobChain r keys' msg₁ = bobChain r keys' msg' := by
    unfold bobChain Symbolic.Swarm.Stage1Trials.bobInitChain
    dsimp only [msg₁]; rw [hrk_eq]
  have hcmk₁ : consumeMessageKey (bobChain r keys' msg₁) msg₁.counter = some (seed', c') := by
    rw [hchain]; dsimp only [msg₁]; rw [hctr_eq]; exact hcmk
  obtain ⟨st₁, hspqr₁⟩ := g1b_spqrRecv_init_salt (m' := msg₁.pqRatchet)
    (TR.spqrEmptyMsg_false_of_gamma_ne_nil interpretation S g _ (by
      dsimp only [msg₁]; rw [hpq_gamma]; exact hpq_ne)) hspqr
  have hbss₁ : TR.bobSaltSeed r p { ek := DY.X25519.normalizeX25519Key x'.ek, ct := x'.ct, msg := t' } =
      some (salt', seed') := by
    have hk_eq : ∀ q : PreKeyRep, TR.bobKeys r p q = bobKeys r p q := by
      intro q
      unfold TR.bobKeys bobKeys Symbolic.Swarm.Stage1Trials.bobOpk? bobKeysOf
      cases p.preKeyId with
      | none => rfl
      | some id =>
        by_cases h1 : r.withOpk = true <;> by_cases h2 : id = r.opkId <;>
          simp [h1, h2, Bind.bind, Option.bind, Pure.pure, Option.map]
    have hk_tr : TR.bobKeys r p { ek := DY.X25519.normalizeX25519Key x'.ek, ct := x'.ct, msg := t' } = some keys' := by
      rw [hk_eq]; exact hkeys₁
    have hc_tr : TR.bobChain r keys' msg₁ = bobChain r keys' msg₁ := rfl
    unfold TR.bobSaltSeed
    simp only [hk_tr, hparse₁, hc_tr, hcmk₁, hspqr₁, Bind.bind, Option.bind, Pure.pure]
  refine ⟨{ ek := DY.X25519.normalizeX25519Key x'.ek, ct := x'.ct, msg := t' }, msg₁, pqSalt_s, m_s,
    ⟨attackerKnows_x25519Key hek_ak, hct_ak, ?_, ?_, p₀, hp₀, ?_⟩, ?_, hparse₁, ?_, hbss₁,
    hpq_ak, ?_, ?_, ?_⟩
  · dsimp only [t']; rw [hmac_eq]; exact ht'_ak
  · obtain ⟨p₁, hp₁, hbase, hkyb, hmsgb⟩ := hmatch
    exact ⟨p₁, hp₁, by rw [hek_gamma]; exact hbase, hkyb, by rw [ht'_gamma]; exact hmsgb⟩
  · obtain ⟨msg₀, hparse₀, hw₀, hm₀, hspqr₀, hct₀, hrk₀, hpq₀, hcnt₀, hv₀'⟩ := hfaith
    rw [hparse] at hparse₀
    cases hparse₀
    refine ⟨msg₁, hparse₁, hwire_gamma.trans hw₀, hm₀, hspqr₀, hct_gamma.trans hct₀,
      by dsimp only [msg₁]; rw [hrk_eq]; exact hrk₀, hpq_gamma.trans hpq₀,
      by dsimp only [msg₁]; rw [hctr_eq]; exact hcnt₀,
      by dsimp only [msg₁]; rw [hver_eq]; exact hv₀'⟩
  · show PQXDH.isCanonicalKey (DY.X25519.normalizeX25519Key x'.ek) = true
    rw [hek_key]
    simp only [PQXDH.isCanonicalKey, PQXDH.x25519LowOrder, DY.X25519.normalizeX25519Key, hv_var,
      DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
    rfl
  · dsimp only [msg₁]; rw [hrk_eq]; exact hlow'
  · dsimp only [msg₁]
    rw [hmac', ← hseed_eq, ← hmyIk_eq, ← hpeerIk_eq]
  · dsimp only [msg₁, ct_s]
    rw [← hseed_eq]
    exact DY.SymEnc.symDec_symEnc _ _ _
  · have hpqs_gamma : gamma interpretation S g pqSalt_s = gamma interpretation S g salt₁ :=
      gamma_eq_of_shape_eq interpretation S g pqSalt_s salt₁ hpq_sh
    have hseed_gamma : gamma interpretation S g seed_s = gamma interpretation S g seed' := by
      rw [hseed_eq]
    rw [← hck_eq, ← hiv_eq] at hdec_wire
    exact gamma_m_eq_ptext_of_decOk interpretation hEq S g hpqs_gamma hseed_gamma hct_gamma hdec_wire

end Symbolic.Swarm.CREF.CliPure
