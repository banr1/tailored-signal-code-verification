/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.BugInjection.Proofs.Common443.CompRI0Census
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
open ByteSpecs CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.HwEvents
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes sha256CompressSymbol)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys computeMac)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompRGamma Symbolic.BugInjection.Proofs.Common443.CompRI0Census Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
theorem bobTrials_length_le_one (r : Records) (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep) (msg : TRSignalMsg) : (bobTrials r tr p x msg).length ≤ 1 := by unfold bobTrials; split <;> [simp; (dsimp only; split <;> [simp; (split <;> simp)])]
private theorem mem_eq_of_length_le_one {α : Type} {l : List α} (hl : l.length ≤ 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  rcases l with _ | ⟨x, _ | ⟨y, xs⟩⟩
  · cases ha
  · simp only [List.mem_singleton] at ha hb; exact ha.trans hb.symm
  · simp at hl
theorem not_ownSaltMacCollision_of_subsingleton {i : ExternInterpretation} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} (hlen : ctxs.length ≤ 1) (hi : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed → ∀ k ∈ ctx.ownSalts, gamma i S g (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) = gamma i S g msg.mac → ∃ salt ∈ honest, (gamma i S g (trMsgKeys salt seed).cipherKey, gamma i S g (trMsgKeys salt seed).macKey, gamma i S g (trMsgKeys salt seed).iv) = (gamma i S g (trMsgKeys k seed).cipherKey, gamma i S g (trMsgKeys k seed).macKey, gamma i S g (trMsgKeys k seed).iv)) : ¬ OwnSaltMacCollision i S g known honest msg ctxs := by
  rintro (⟨ctx, hctx, seed, hseed, k, hk, hmac, _, hno⟩ | ⟨ctx, hctx, seed, hseed, k, hk, hmac, ctx₀, hctx₀, seed₀, hseed₀, hne, _⟩)
  · obtain ⟨salt, hsalt, heq⟩ := hi ctx hctx seed hseed k hk hmac; exact hno salt hsalt heq
  · cases mem_eq_of_length_le_one hlen hctx hctx₀
    cases hseed.symm.trans hseed₀; exact hne rfl
theorem gamma_lit0 {i : ExternInterpretation} {S : Sem} {g : Ghost} (b : ByteArray) : gamma i S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma; show (gamma' i S g (({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_lit]; rfl
theorem gamma_concat0 {i : ExternInterpretation} {S : Sem} {g : Ghost} (a b : DY.Bytes) : gamma i S g (DY.Concat.concat a b) = gamma i S g a ++ gamma i S g b := by
  unfold gamma; show (gamma' i S g (({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_concat]; rfl
theorem gamma_hmac_gen {i : ExternInterpretation} {S : Sem} {g : Ghost} (k m : DY.Bytes) : gamma i S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith (sha256CompressFunction i) (gamma i S g k) (gamma i S g m) := by
  unfold gamma DY.Libsignal.TripleRatchet.hmac
  show (gamma' i S g (({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_kdf]; rfl
theorem gamma_trunc80 {i : ExternInterpretation} {S : Sem} {g : Ghost} (a : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 a) = (gamma i S g a).take 8 := by
  unfold gamma; show (gamma' i S g (({input := a} : DY.Trunc.Trunc8.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_trunc]; rfl
theorem trMsgKeys_gamma_congr_salt {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt₁ salt₂ : DY.Bytes} (seed : DY.Bytes) (hs : gamma i S g salt₁ = gamma i S g salt₂) : (gamma i S g (trMsgKeys salt₁ seed).cipherKey, gamma i S g (trMsgKeys salt₁ seed).macKey, gamma i S g (trMsgKeys salt₁ seed).iv) = (gamma i S g (trMsgKeys salt₂ seed).cipherKey, gamma i S g (trMsgKeys salt₂ seed).macKey, gamma i S g (trMsgKeys salt₂ seed).iv) := by unfold trMsgKeys DY.Libsignal.TripleRatchet.hkdfBlock3 DY.Libsignal.TripleRatchet.hkdfBlock2 DY.Libsignal.TripleRatchet.hkdfBlock1; dsimp only; simp only [gamma_hmac_gen, gamma_concat0, hs]
theorem gamma_spqrChainKey_length {i : ExternInterpretation} {S : Sem} {g : Ghost} (a p idx : DY.Bytes) : (gamma i S g (DY.Spqr.spqrChainKey a p idx)).length = 32 := by
  unfold gamma gamma' DY.Spqr.spqrChainKey
  rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll i S g)]; show (spqrKeyBytes _).length = 32; simp [spqrKeyBytes]
theorem gamma_spqrSendKey_length {i : ExternInterpretation} {S : Sem} {g : Ghost} (st c : DY.Bytes) : (gamma i S g (DY.Spqr.spqrSend st c).2.1).length = 32 := by
  unfold DY.Spqr.spqrSend; dsimp only
  cases st.view? DY.Spqr.InitState.SubF with
  | some x => exact gamma_spqrChainKey_length x.authKey x.params _
  | none =>
    unfold gamma gamma'; rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll i S g)]
    show (spqrKeyBytes _).length = 32; simp [spqrKeyBytes]
theorem gamma_ownSalt_bobTrials_length {i : ExternInterpretation} {S : Sem} {g : Ghost} {r : Records} {tr : ExecTrace} {p : PreKeyFields} {x : PreKeyRep} {msg : TRSignalMsg} {ctx : TrialCtx} (hctx : ctx ∈ bobTrials r tr p x msg) {k : DY.Bytes} (hk : k ∈ ctx.ownSalts) : (gamma i S g k).length = 32 := by
  unfold bobTrials at hctx; split at hctx; · simp at hctx
  dsimp only at hctx; split at hctx; · simp at hctx
  split at hctx <;> simp only [List.mem_singleton] at hctx <;> subst hctx
  · simp at hk
  · unfold DY.Spqr.spqrRecv at hk
    split at hk; · simp at hk
    split at hk
    · split at hk
      · simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hk; subst hk
        split
        · unfold DY.Spqr.zeroKey; rw [gamma_lit0]; decide +kernel
        · exact gamma_spqrChainKey_length _ _ _
      · simp at hk
    · simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hk; subst hk
      unfold gamma gamma'; rw [DY.Bytes.rec_eq (gSpqrRecvKey S) (gAll i S g)]
      show (spqrKeyBytes _).length = 32; simp [spqrKeyBytes]
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
export Symbolic.BugInjection.Proofs.Common443.CompRNbscTable ( F0 OnTab tagW compI0_sha256Compress sha256CompressFunction_compI0_head compDefaultSha256_take4 compSha256_row_of_untagged leBytes_bytesToNat toBEBytes_tagW shaStateOfBytes_compTag4_head hstep0 shaStateBytes_take4_of_head hT1_0 onTab_of_sha256With_untagged kblk kblk_length hmacWith_eq hmac_outer_first_onTab ivNat map_xor_xor digestOfOut rowOfTake8 rowByOut keyOfRow1 keyOfTake8 rows_out_nodup rows_take8_nodup rows_out_roundtrip find?_eq_some_of_nodup F0_eq row_step keyOfTake8_hmacWith)
theorem gamma_hmac_length (S : Sem) (g : Ghost) (k m : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by rw [gamma_hmac_gen]; exact sha256With_length F0 _
def ws2MacKey : HwBytes := [114, 127, 169, 60, 91, 52, 199, 80, 101, 192, 3, 134, 56, 105, 7, 52, 114, 241, 239, 250, 80, 195, 8, 61, 18, 159, 46, 1, 166, 229, 124, 3]
def ws2Prk : HwBytes := [218, 60, 112, 85, 168, 5, 198, 88, 0, 67, 68, 248, 250, 106, 86, 99, 10, 117, 19, 237, 185, 102, 31, 145, 90, 242, 107, 126, 210, 166, 108, 15]
def wsSalt2 : HwBytes := [3, 135, 79, 214, 65, 239, 215, 73, 23, 43, 93, 228, 9, 241, 97, 76, 22, 238, 115, 16, 46, 97, 110, 254, 183, 166, 247, 35, 87, 20, 76, 122]
def msgMac8 (p : PreKeyFields) : HwBytes := p.message.drop (p.message.length - 8)
def macChainOk (k P : HwBytes) (p : PreKeyFields) : Bool := ((msgMac8 p).take 4 != compTag4) && (keyOfTake8 (msgMac8 p) == some k) && (k.take 4 != compTag4) && (keyOfTake8 (k.take 8) == some P)
def wireMacChainOk (k P w : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | some p => macChainOk k P p
  | none => false
theorem macChainOk_spec {k P : HwBytes} {p : PreKeyFields} (h : macChainOk k P p = true) : (msgMac8 p).take 4 ≠ compTag4 ∧ keyOfTake8 (msgMac8 p) = some k ∧ k.take 4 ≠ compTag4 ∧ keyOfTake8 (k.take 8) = some P := by simp only [macChainOk, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
theorem macChainOk_of_wire {k P w : HwBytes} (h : wireMacChainOk k P w = true) {p : PreKeyFields} (hp : parsePreKeyWire w = some p) : macChainOk k P p = true := by unfold wireMacChainOk at h; rw [hp] at h; exact h
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
section FastWire40
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex_def" id:ident : term => do
  let eWhnf ← Lean.Meta.whnf (Lean.mkConst (← Lean.resolveGlobalConstNoOverload id))
  let sLit ← Lean.Meta.whnf eWhnf.getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "str_of_hex_def" id:ident : term => do
  let eWhnf ← Lean.Meta.whnf (Lean.mkConst (← Lean.resolveGlobalConstNoOverload id))
  Lean.Meta.whnf eWhnf.getAppArgs[0]!
def wire3Idx1Chars : List Char := chars_of_hex_def wire3Idx1Bytes
theorem wire3Idx1_getElem?_eq : (Witnesses.Cheval26WeakStateIdx1.trace)[40]? = some (.recv (hexBytes (str_of_hex_def wire3Idx1Bytes))) := rfl
set_option maxRecDepth 200000 in theorem wire3Idx1Str_eq : (str_of_hex_def wire3Idx1Bytes) = String.ofList wire3Idx1Chars := rfl
theorem wire3Idx1Bytes_eq_fast : wire3Idx1Bytes = hexBytes.go hexDigit wire3Idx1Chars := by
  have h : wire3Idx1Bytes = hexBytes (str_of_hex_def wire3Idx1Bytes) := by
    unfold wire3Idx1Bytes recvAt; rw [wire3Idx1_getElem?_eq]
  rw [h, wire3Idx1Str_eq, hexBytes_ofList]
def wire3Idx1Fast : HwBytes := hexBytes.go hexDigit wire3Idx1Chars
end FastWire40
set_option maxRecDepth 200000 in theorem wireMacChainOk_wire3Idx1Fast : wireMacChainOk ws2MacKey ws2Prk wire3Idx1Fast = true := by decide +kernel
theorem wireMacChainOk_wire3Idx1 : wireMacChainOk ws2MacKey ws2Prk wire3Idx1Bytes = true := by rw [wire3Idx1Bytes_eq_fast]; exact wireMacChainOk_wire3Idx1Fast
set_option maxRecDepth 200000 in theorem ws2Prk_pin : ws2Prk.take 4 ≠ compTag4 ∧ keyOfTake8 (ws2Prk.take 8) = some wsSalt2 := by decide +kernel
theorem take4_take8 (l : HwBytes) : (l.take 8).take 4 = l.take 4 := by rw [List.take_take]; rfl
private theorem hmac_key_eq {S : Sem} {g : Ghost} {k m : DY.Bytes} {K : HwBytes} (hk : (gamma compI0 S g k).length = 32) (htag : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).take 4 ≠ compTag4) (hrec : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).take 8) = some K) : gamma compI0 S g k = K := by rw [gamma_hmac_gen] at htag hrec; exact Option.some.inj ((keyOfTake8_hmacWith _ _ hk htag).symm.trans hrec)
theorem gamma_salt_eq_wsSalt2_of_computeMac {S : Sem} {g : Ghost} {salt seed peerIk myIk wire : DY.Bytes} {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hsalt : (gamma compI0 S g salt).length = 32) (hmac : gamma compI0 S g (computeMac (trMsgKeys salt seed).macKey peerIk myIk wire) = p.message.drop (p.message.length - 8)) : gamma compI0 S g salt = wsSalt2 := by
  obtain ⟨h1, h2, h3, h4⟩ := macChainOk_spec (macChainOk_of_wire wireMacChainOk_wire3Idx1 hp)
  have hmac8 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (trMsgKeys salt seed).macKey (DY.Concat.concat peerIk (DY.Concat.concat myIk wire)))).take 8 = msgMac8 p := by rw [← gamma_trunc80]; exact hmac
  have hmk_eq : gamma compI0 S g (trMsgKeys salt seed).macKey = ws2MacKey :=
    hmac_key_eq (gamma_hmac_length S g _ _) (by rw [← take4_take8, hmac8]; exact h1) (hmac8 ▸ h2)
  have hprk_eq : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac salt seed) = ws2Prk := hmac_key_eq (gamma_hmac_length S g _ _) (hmk_eq ▸ h3) (hmk_eq ▸ h4); exact hmac_key_eq hsalt (hprk_eq ▸ ws2Prk_pin.1) (hprk_eq ▸ ws2Prk_pin.2)
theorem parseTrSignalMsg_encOut_mac {tr₂ : ExecTrace} {stA : TRState} {cl pq : Nat} {msg : TRSignalMsg} (h : parseTrSignalMsg (encOut tr₂ stA cl pq) = some msg) : msg.mac = encMac tr₂ stA cl pq := by rw [CompRFaithfulInner.parseTrSignalMsg_encOut] at h; injection h with h; rw [← h]; rfl
@[simp] theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq tr x
theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
private theorem at?_append_of_lt {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i < tr.length) : ((tr.append x).at? i : Option T) = (tr.at? i : Option T) :=
  Symbolic.Swarm.CREF.at?_append_lt tr x hi
theorem encPreSaltTr_getMessageSentAt_self (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : (encPreSaltTr tr₂ stA cl).getMessageSentAt (tr₂.length + 2) = some (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?]
  unfold encPreSaltTr; dsimp only
  rw [at?_append_eq_of_eq (T := DY.Network.ExecEntryT) _ (NetE _) (i := tr₂.length + 2) (by simp)]; rfl
@[simp] theorem encSalt_self (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : encSalt tr₂ stA cl (tr₂.length + 2) = (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by unfold encSalt; rw [encPreSaltTr_getMessageSentAt_self]; rfl
theorem encNextTr_getMessageSentAt_salt (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : TRState) (cl pq : Nat) : (encNextTr tr₂ me sIdx stA cl pq).getMessageSentAt (tr₂.length + 2) = some (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?]
  unfold encNextTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp [encPreSaltTr]), at?_append_of_lt _ _ (by simp [encPreSaltTr]),
      at?_append_of_lt _ _ (by simp [encPreSaltTr]), at?_append_of_lt _ _ (by simp [encPreSaltTr]),
      ← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?]
  exact encPreSaltTr_getMessageSentAt_self tr₂ stA cl
theorem honestKeysFrom_append :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), honestKeysFrom tr (ms₁ ++ ms₂) = honestKeysFrom tr ms₁ ++ honestKeysFrom (runMoves ms₁ tr).1 ms₂
  | [], ms₂, tr => by simp [honestKeysFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, honestKeysFrom, runMoves, honestKeysFrom_append ms₁ ms₂ (m.next tr), List.append_assoc]
theorem spqrSend_mem_honestSalts_of_getElem? {r : Records} {ms' : List Move} {k : Nat} {tr : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wr : Option (Nat × Nat)} {stA : TRState} (htr : runTraceMoves r (ms'.take k) = tr) (hget : ms'[k]? = some (.encrypt me sIdx cl pq wr)) (henc : (Move.encrypt me sIdx cl pq wr).next tr = encNextTr tr me sIdx stA cl pq) : (DY.Spqr.spqrSend stA.spqr (randTerm (tr.length + 1) cl)).2.1 ∈ honestSalts r ms' := by
  obtain ⟨hk, hmk⟩ := List.getElem?_eq_some_iff.mp hget
  have hsplit : ms' = ms'.take k ++ Move.encrypt me sIdx cl pq wr :: ms'.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k ms', List.drop_eq_getElem_cons hk, hmk]
  unfold honestSalts; rw [List.mem_cons]; right; rw [hsplit, honestKeysFrom_append]; change _ ∈ honestKeysFrom (setupTrace r) (ms'.take k) ++ honestKeysFrom (runTraceMoves r (ms'.take k)) (Move.encrypt me sIdx cl pq wr :: ms'.drop (k + 1)); rw [htr, List.mem_append]; right; simp [honestKeysFrom, henc, encNextTr_getMessageSentAt_salt]
def Split40OwnSaltMac : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (msg : TRSignalMsg), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → parseTrSignalMsg (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg = some msg → ¬ OwnSaltMacCollision compI0 S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (honestSalts r ms') msg (bobTrials r (runTraceMoves r ms') p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂) msg)
theorem split40OwnSaltMac : Split40OwnSaltMac := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ msg _hfits hp hinv hparse; apply not_ownSaltMacCollision_of_subsingleton (bobTrials_length_le_one r (runTraceMoves r ms') p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂) msg); intro ctx hctx seed _hseed k hk hmac_eq
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
  let salt₂ := (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.1
  obtain ⟨k₁, k₂, k₃, hb₁, sh₁, s₁, s₂, pq₁, pq₂, w₁, w₂, _, _, _, _, _, _, htr₃, hget₃, _, _, hpq₂, _, henc₂⟩ := hinv.links
  have hsalt₂_mem : salt₂ ∈ honestSalts r ms' :=
    spqrSend_mem_honestSalts_of_getElem? htr₃ hget₃ (by rw [henc₂, hpq₂])
  have hmac_enc := (hinv.hwire₂ p hp).2.1
  have hk_eq : gamma compI0 S g k = wsSalt2 := gamma_salt_eq_wsSalt2_of_computeMac hp (gamma_ownSalt_bobTrials_length hctx hk)
      (by rw [hmac_eq, parseTrSignalMsg_encOut_mac hparse, hmac_enc])
  have hsalt₂_eq : gamma compI0 S g salt₂ = wsSalt2 := gamma_salt_eq_wsSalt2_of_computeMac hp (gamma_spqrSendKey_length _ _)
      (by
        have heq : encMac tr₃ stA₁' cl₂ (tr₃.length + 2) = computeMac (trMsgKeys salt₂ (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2).macKey stA₁'.myIk stA₁'.peerIk (encWire tr₃ stA₁' cl₂ (tr₃.length + 2)) := by unfold encMac; dsimp only; rw [encSalt_self]
        rw [← heq]; exact hmac_enc)
  exact ⟨salt₂, hsalt₂_mem, trMsgKeys_gamma_congr_salt seed (hsalt₂_eq.trans hk_eq.symm)⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
