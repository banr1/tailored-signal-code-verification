/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep

/-!
# Wire-Term Rebuild for Byte-Chain Reselection

Constructs a reselected wire representation `t₁` naming a stored receive chain's
`c.ratchetKey` with identical wire and MAC bytes, `recvSeed`, `ownKeys`, and
`recvRepresentations` membership (`reselect_exists_of_macFn_unbundled` and
`reselect_exists_mac_eq_unbundled`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey computeMac messageVersion recvChainFor)
open DY.Libsignal.Refinement (EncodingVariation canonicalVariation)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

open DY.Libsignal.Refinement (WireFields FieldItem)
open DY.Libsignal.TripleRatchet.Refinement (withSentinel withSentinel_ne_canonical
  encode_withFields)

unseal DY.Bytes in
private instance bcrWireRebuild_subKdf0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance bcrWireRebuild_subTrunc0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem bcrWireRebuild_gamma_kdfExtract (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (s ikm : DY.Bytes) :
    gamma i S g (KdfExtract.kdfExtract s ikm) =
      CryptoGames.HMAC.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g s) (gamma i S g ikm) := by
  unfold gamma gamma'
  show ((({ salt := s, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]; rfl

private theorem bcrWireRebuild_gamma_trunc8 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

theorem bcrWireRebuild_gamma_computeMac_congr_wire
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk peerIk myIk w₁ w₂ : DY.Bytes)
    (hw : gamma interpretation S g w₁ = gamma interpretation S g w₂) :
    gamma interpretation S g (computeMac mk peerIk myIk w₁) =
      gamma interpretation S g (computeMac mk peerIk myIk w₂) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [bcrWireRebuild_gamma_trunc8, bcrWireRebuild_gamma_trunc8,
      bcrWireRebuild_gamma_kdfExtract, bcrWireRebuild_gamma_kdfExtract,
      RecvRep.gamma_concat, RecvRep.gamma_concat, RecvRep.gamma_concat, RecvRep.gamma_concat, hw]

theorem bcrWireRebuild_findRecvChain_eq_some_of_mem_hist
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c : RecvChain} (hc_mem : c ∈ st₀.recv) :
    DY.Libsignal.TripleRatchet.findRecvChain st₀.recv c.ratchetKey = some c := by
  cases hf : DY.Libsignal.TripleRatchet.findRecvChain st₀.recv c.ratchetKey with
  | none => exact absurd (beq_self_eq_true c.ratchetKey) (List.find?_eq_none.mp hf c hc_mem)
  | some c₂ =>
    unfold DY.Libsignal.TripleRatchet.findRecvChain at hf
    have hc₂_mem : c₂ ∈ st₀.recv := List.mem_of_find?_eq_some hf
    have hbeq := List.find?_some hf
    have hc₂_rk : c₂.ratchetKey = c.ratchetKey := beq_iff_eq.mp hbeq
    exact congrArg some (List.inj_on_of_nodup_map (hHist st₀ hst₀) hc_mem hc₂_mem (by rw [hc₂_rk])).symm

theorem bcrWireRebuild_recvSeed_eq_some_of_mem_hist
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv) {msg : TRSignalMsg} {seed : DY.Bytes}
    (hver : msg.version = messageVersion) (hrk : msg.ratchetKey = c.ratchetKey)
    (hcons : consumeMessageKey c msg.counter = some (seed, c')) :
    recvSeed st₀ msg = some seed := by
  have hfind := bcrWireRebuild_findRecvChain_eq_some_of_mem_hist hHist hst₀ hc_mem
  unfold recvSeed; simp only [hver, ↓reduceIte, recvChainFor, hrk, hfind]
  change Option.map Prod.fst (consumeMessageKey c msg.counter) = some seed; rw [hcons]; rfl

private def bcrWireRebuild_freezeAddrItem (addr₀ : HwBytes) : FieldItem → FieldItem
  | .known 6 kp vp => .extra 6 (.bytes addr₀) kp vp
  | it => it

private def bcrWireRebuild_freezeAddrVar (addr₀ pq : HwBytes) (v₀ : EncodingVariation) :
    EncodingVariation :=
  withSentinel { v₀ with fields := (trFields addr₀ v₀ pq).map (bcrWireRebuild_freezeAddrItem addr₀) }

private theorem bcrWireRebuild_trItemEncode_freezeAddrItem
    (addr₀ addr₁ pq : HwBytes) (v₀ : EncodingVariation) (fs : List FieldItem)
    (f : WireFields) (it : FieldItem) :
    trItemEncode addr₁ { v₀ with fields := fs } f pq (bcrWireRebuild_freezeAddrItem addr₀ it) =
      trItemEncode addr₀ v₀ f pq it := by
  cases it with
  | known t kp vp =>
    by_cases h6 : t = 6
    · subst h6
      rfl
    · by_cases h5 : t = 5
      · subst h5
        rfl
      · have hfr : bcrWireRebuild_freezeAddrItem addr₀ (.known t kp vp) = .known t kp vp := by
          cases t with
          | zero => rfl
          | succ n =>
            rcases n with _ | _ | _ | _ | _ | n
            · rfl
            · rfl
            · rfl
            · rfl
            · exact absurd rfl h5
            · cases n with
              | zero => exact absurd rfl h6
              | succ _ => rfl
        rw [hfr]
        simp only [trItemEncode, h5, h6, ↓reduceIte]
        exact encode_withFields v₀ fs f (.known t kp vp)
  | extra t x kp vp =>
    exact encode_withFields v₀ fs f (.extra t x kp vp)

private theorem bcrWireRebuild_flatMap_freezeAddrItem
    (addr₀ addr₁ pq : HwBytes) (v₀ : EncodingVariation) (fs : List FieldItem) (f : WireFields) :
    ∀ l : List FieldItem,
      (l.map (bcrWireRebuild_freezeAddrItem addr₀)).flatMap
        (trItemEncode addr₁ { v₀ with fields := fs } f pq) =
      l.flatMap (trItemEncode addr₀ v₀ f pq)
  | [] => rfl
  | it :: l => by
    simp only [List.map_cons, List.flatMap_cons,
      bcrWireRebuild_trItemEncode_freezeAddrItem addr₀ addr₁ pq v₀ fs f it,
      bcrWireRebuild_flatMap_freezeAddrItem addr₀ addr₁ pq v₀ fs f l]

private theorem bcrWireRebuild_trWireBytes_freezeAddrVar
    (addr₀ addr₁ pq : HwBytes) (v₀ : EncodingVariation) (f : WireFields) :
    trWireBytes addr₁ (bcrWireRebuild_freezeAddrVar addr₀ pq v₀) f pq =
      trWireBytes addr₀ v₀ f pq := by
  have hne : bcrWireRebuild_freezeAddrVar addr₀ pq v₀ ≠ canonicalVariation :=
    withSentinel_ne_canonical _
  unfold trWireBytes
  have htf : trFields addr₁ (bcrWireRebuild_freezeAddrVar addr₀ pq v₀) pq =
      .known 0 0 0 :: (trFields addr₀ v₀ pq).map (bcrWireRebuild_freezeAddrItem addr₀) := by
    simp only [trFields, hne, ↓reduceIte]
    rfl
  rw [htf]
  have hvl : (bcrWireRebuild_freezeAddrVar addr₀ pq v₀).versionLowNibble = v₀.versionLowNibble := rfl
  rw [hvl, List.flatMap_cons]
  have h0 : trItemEncode addr₁ (bcrWireRebuild_freezeAddrVar addr₀ pq v₀) f pq (.known 0 0 0) = [] := rfl
  rw [h0, List.nil_append]
  unfold bcrWireRebuild_freezeAddrVar withSentinel
  rw [bcrWireRebuild_flatMap_freezeAddrItem addr₀ addr₁ pq v₀ _ f (trFields addr₀ v₀ pq)]

private theorem bcrWireRebuild_length_trWireMsg (v : UInt8) (rk : DY.Bytes) (c pc : UInt32)
    (ct pq : DY.Bytes) (ev : EncodingVariation) :
    (DY.TrWire.trWireMsg v rk c pc ct pq ev).length =
      1 + rk.length + 4 + 4 + ct.length + pq.length := by
  simp only [DY.TrWire.trWireMsg]
  grind [DY.TrWire.TrWireMsg.SubF.length]

private theorem bcrWireRebuild_parseTrSignalMsg_inv {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    ∃ (v₀ : UInt8) (pc₀ : UInt32) (ev₀ : EncodingVariation),
      t₀ = DY.Concat.concat msg₀.wire msg₀.mac ∧
      msg₀.mac.length = Trunc.trunc8Length ∧
      msg₀.wire = DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀ ∧
      msg₀.version = v₀ % 16 := by
  obtain ⟨v₀, pc₀, ev₀, hwire₀, hver⟩ :=
    G1.parseTrSignalMsg_eq_some_inv hparse₀
  unfold parseTrSignalMsg at hparse₀
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse₀
  obtain ⟨⟨wire, mac⟩, hsp, f, _hwf, hmsg⟩ := hparse₀
  subst hmsg
  dsimp only at hwire₀ ⊢
  obtain ⟨hcat, hlen⟩ := G1.split_eq_some_concat_and_length_tr32 hsp
  have hcat_len : t₀.length = wire.length + mac.length := by
    rw [hcat, Concat.length_concat]
  have hw_pos : wire.length > 0 := by
    rw [hwire₀, bcrWireRebuild_length_trWireMsg]
    omega
  have htr8 : Trunc.trunc8Length = 8 := rfl
  have hmac_len : mac.length = Trunc.trunc8Length := by
    rw [htr8] at hlen ⊢
    omega
  exact ⟨v₀, pc₀, ev₀, hcat, hmac_len, hwire₀, hver⟩

/-- Rebuilds a received wire representation `t₁` naming `c.ratchetKey` with MAC `macFn wire₁`
and identical concretized wire and MAC bytes, `recvSeed`, and `ownKeys`. -/
theorem reselect_exists_of_macFn_unbundled
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {body : HwBytes} {m : SignalMessage}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv)
    (hγ_pk : gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList)
    (hrkK : c.ratchetKey.AttackerKnows (runTraceMoves r₀ ms))
    {seed k_own : DY.Bytes}
    (hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (macFn : DY.Bytes → DY.Bytes)
    (hK : ∀ w, w.AttackerKnows (runTraceMoves r₀ ms) → (macFn w).AttackerKnows (runTraceMoves r₀ ms))
    (hγ : ∀ w, gamma interpretation S g w = gamma interpretation S g msg₀.wire →
      gamma interpretation S g (macFn w) = gamma interpretation S g msg₀.mac)
    (hlen : ∀ w, (macFn w).length = Trunc.trunc8Length)
    (hns : ∀ w, spqrHeaded (macFn w) = false) :
    ∃ t₁ msg₁, msg₁.mac = macFn msg₁.wire ∧
      (∃ (v₀ : UInt8) (c₀ pc₀ : UInt32) (ev₀ ev₁ : EncodingVariation),
        msg₀.wire = DY.TrWire.trWireMsg v₀ msg₀.ratchetKey c₀ pc₀ msg₀.ciphertext
          msg₀.pqRatchet ev₀ ∧
        t₀ = DY.Concat.concat msg₀.wire msg₀.mac ∧
        (ev₁ = ev₀ ∨ ∃ v : EncodingVariation, v ≠ canonicalVariation ∧ ev₁ = v) ∧
        msg₁.wire = DY.TrWire.trWireMsg v₀ c.ratchetKey c₀ pc₀ msg₀.ciphertext
          msg₀.pqRatchet ev₁ ∧
        gamma interpretation S g msg₁.mac = gamma interpretation S g msg₀.mac ∧
        msg₁.version = msg₀.version ∧
        msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
        msg₁.ciphertext = msg₀.ciphertext ∧ msg₁.pqRatchet = msg₀.pqRatchet ∧
        t₁ = DY.Concat.concat msg₁.wire msg₁.mac ∧
        t₁ ∈ recvRepresentations interpretation r₀ S g ms body ∧
        parseTrSignalMsg t₁ = some msg₁) ∧
      recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g
          (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) := by
  let tr := runTraceMoves r₀ ms
  obtain ⟨v₀, pc₀, ev₀, ht₀_cat, hmac₀_len, hwire₀_eq, hver_raw⟩ :=
    bcrWireRebuild_parseTrSignalMsg_inv hparse₀
  have hsplit_kn : msg₀.wire.AttackerKnows tr ∧ msg₀.mac.AttackerKnows tr := by
    have hsp := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) tr ht₀.1
    have hlen₀ : t₀.length - Trunc.trunc8Length = msg₀.wire.length := by
      rw [ht₀_cat, Concat.length_concat, hmac₀_len]; omega
    rw [hlen₀, ht₀_cat, Concat.split_concat] at hsp
    exact hsp
  have hargs₀ := DY.TrWire.attacker_knows_trWireMsg_args v₀ msg₀.ratchetKey msg₀.counter pc₀
    msg₀.ciphertext msg₀.pqRatchet ev₀ tr (hwire₀_eq ▸ hsplit_kn.1)
  obtain ⟨hwire₀_take, hmac₀_drop, _hmac₀_ns, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  obtain ⟨hct₀_gam, hrk₀_gam, hpq₀_gam, hctr₀_nat, hver₀_nat⟩ := htry₀ m htry
  let addr₀ := g.addr (DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀
    msg₀.ciphertext msg₀.pqRatchet ev₀)
  let pqBytes := gamma interpretation S g msg₀.pqRatchet
  let v := bcrWireRebuild_freezeAddrVar addr₀ pqBytes ev₀
  have hv_ne : v ≠ canonicalVariation :=
    withSentinel_ne_canonical
      { ev₀ with fields := (trFields addr₀ ev₀ pqBytes).map (bcrWireRebuild_freezeAddrItem addr₀) }
  let ev₁ := v
  let wire₁ := DY.TrWire.trWireMsg v₀ c.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₁
  let mac₁ := macFn wire₁
  let t₁ := DY.Concat.concat wire₁ mac₁
  let msg₁ : TRSignalMsg :=
    { wire := wire₁
      mac := mac₁
      version := msg₀.version
      ratchetKey := c.ratchetKey
      counter := msg₀.counter
      ciphertext := msg₀.ciphertext
      pqRatchet := msg₀.pqRatchet }
  have hwire₁_kn : wire₁.AttackerKnows tr :=
    DY.TrWire.attacker_knows_trWireMsg v₀ c.ratchetKey msg₀.counter pc₀
      msg₀.ciphertext msg₀.pqRatchet ev₁ tr
      hrkK hargs₀.2.1 hargs₀.2.2
  have hmac₁_kn : mac₁.AttackerKnows tr := hK wire₁ hwire₁_kn
  have ht₁_kn : t₁.AttackerKnows tr :=
    Concat.attacker_knows_concat wire₁ mac₁ tr hwire₁_kn hmac₁_kn
  have hmac₁_len : mac₁.length = Trunc.trunc8Length := hlen wire₁
  have hparse₁ : parseTrSignalMsg t₁ = some msg₁ := by
    unfold parseTrSignalMsg
    have hlen₁ : t₁.length - Trunc.trunc8Length = wire₁.length := by
      dsimp only [t₁]
      rw [Concat.length_concat, hmac₁_len]; omega
    rw [hlen₁]
    dsimp only [t₁]
    rw [Concat.split_concat]
    dsimp only [wire₁, msg₁]
    simp only [Bind.bind, Pure.pure, Option.bind_some, DY.TrWire.trWireMsgFields?_trWireMsg,
      ← hver_raw]
  have hwire₁_gamma_eq : gamma interpretation S g wire₁ = gamma interpretation S g msg₀.wire := by
    dsimp only [wire₁, ev₁, v]
    rw [hwire₀_eq, RecvRep.gamma_trWireMsg, RecvRep.gamma_trWireMsg,
        hγ_pk, hrk₀_gam]
    exact bcrWireRebuild_trWireBytes_freezeAddrVar addr₀ (g.addr wire₁) pqBytes ev₀ _
  have hmac₁_gamma_eq : gamma interpretation S g mac₁ = gamma interpretation S g msg₀.mac :=
    hγ wire₁ hwire₁_gamma_eq
  have hwire₁_take : gamma interpretation S g wire₁ = body.take (body.length - 8) :=
    hwire₁_gamma_eq.trans hwire₀_take
  have hmac₁_drop : gamma interpretation S g mac₁ = body.drop (body.length - 8) :=
    hmac₁_gamma_eq.trans hmac₀_drop
  have ht₁_gamma : gamma interpretation S g t₁ = body := by
    dsimp only [t₁]
    rw [RecvRep.gamma_concat, hwire₁_gamma_eq, hmac₁_gamma_eq, ← RecvRep.gamma_concat, ← ht₀_cat]
    exact ht₀.2.1
  have ht₁_rep : t₁ ∈ recvRepresentations interpretation r₀ S g ms body := by
    refine ⟨ht₁_kn, ht₁_gamma, by rw [hparse₁]; rfl, fun msg' hmsg' => ?_⟩
    rw [hparse₁] at hmsg'
    injection hmsg' with hmsg_eq
    subst hmsg_eq
    refine ⟨hwire₁_take, hmac₁_drop, hns wire₁, fun m' hm'_try => ?_⟩
    have hm'_eq : m' = m := by rw [htry] at hm'_try; exact (Except.ok.inj hm'_try).symm
    subst hm'_eq
    exact ⟨hct₀_gam, hγ_pk, hpq₀_gam, hctr₀_nat, hver₀_nat⟩
  have hseed₁ : recvSeed st₀ msg₁ = some seed :=
    bcrWireRebuild_recvSeed_eq_some_of_mem_hist hHist hst₀ hc_mem hver₀ rfl hcons₀
  have hk_own₁ : k_own ∈ ownKeys r₀ tr st₀ msg₁ := hk_own
  have hMacBytes₁ : body.drop (body.length - 8) =
      gamma interpretation S g
        (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) := by
    rw [bcrWireRebuild_gamma_computeMac_congr_wire interpretation S g _ _ _ msg₁.wire msg₀.wire
      hwire₁_gamma_eq]
    exact hMacBytes
  exact ⟨t₁, msg₁, rfl,
    ⟨v₀, msg₀.counter, pc₀, ev₀, ev₁, hwire₀_eq, ht₀_cat, Or.inr ⟨v, hv_ne, rfl⟩,
      rfl, hmac₁_gamma_eq, rfl, rfl, rfl, rfl, rfl, rfl, ht₁_rep, hparse₁⟩,
    hseed₁, hk_own₁, hMacBytes₁⟩

/-- Rebuilds a received wire representation `t₁` naming `c.ratchetKey` with `msg₁.mac = msg₀.mac`
and identical concretized wire and MAC bytes, `recvSeed`, and `ownKeys`. -/
theorem reselect_exists_mac_eq_unbundled
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {body : HwBytes} {m : SignalMessage}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv)
    (hγ_pk : gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList)
    (hrkK : c.ratchetKey.AttackerKnows (runTraceMoves r₀ ms))
    {seed k_own : DY.Bytes}
    (hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire)) :
    ∃ t₁ msg₁, msg₁.mac = msg₀.mac ∧
      (∃ (v₀ : UInt8) (c₀ pc₀ : UInt32) (ev₀ ev₁ : EncodingVariation),
        msg₀.wire = DY.TrWire.trWireMsg v₀ msg₀.ratchetKey c₀ pc₀ msg₀.ciphertext
          msg₀.pqRatchet ev₀ ∧
        t₀ = DY.Concat.concat msg₀.wire msg₀.mac ∧
        (ev₁ = ev₀ ∨ ∃ v : EncodingVariation, v ≠ canonicalVariation ∧ ev₁ = v) ∧
        msg₁.wire = DY.TrWire.trWireMsg v₀ c.ratchetKey c₀ pc₀ msg₀.ciphertext
          msg₀.pqRatchet ev₁ ∧
        gamma interpretation S g msg₁.mac = gamma interpretation S g msg₀.mac ∧
        msg₁.version = msg₀.version ∧
        msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
        msg₁.ciphertext = msg₀.ciphertext ∧ msg₁.pqRatchet = msg₀.pqRatchet ∧
        t₁ = DY.Concat.concat msg₁.wire msg₁.mac ∧
        t₁ ∈ recvRepresentations interpretation r₀ S g ms body ∧
        parseTrSignalMsg t₁ = some msg₁) ∧
      recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g
          (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) := by
  let tr := runTraceMoves r₀ ms
  obtain ⟨_v₀, _pc₀, _ev₀, ht₀_cat, hmac₀_len, _hwire₀_eq, _hver_raw⟩ :=
    bcrWireRebuild_parseTrSignalMsg_inv hparse₀
  have hmac₀_kn : msg₀.mac.AttackerKnows tr := by
    have hsp := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) tr ht₀.1
    have hlen₀ : t₀.length - Trunc.trunc8Length = msg₀.wire.length := by
      rw [ht₀_cat, Concat.length_concat, hmac₀_len]; omega
    rw [hlen₀, ht₀_cat, Concat.split_concat] at hsp
    exact hsp.2
  obtain ⟨_, _, hmac₀_ns, _⟩ := ht₀.2.2.2 msg₀ hparse₀
  exact reselect_exists_of_macFn_unbundled hHist htry ht₀ hparse₀ hver₀ hst₀ hc_mem
    hγ_pk hrkK hcons₀ hk_own hMacBytes (fun _ => msg₀.mac)
    (fun _ _ => hmac₀_kn) (fun _ _ => rfl) (fun _ => hmac₀_len) (fun _ => hmac₀_ns)

end Symbolic.Swarm.CREF.TR
