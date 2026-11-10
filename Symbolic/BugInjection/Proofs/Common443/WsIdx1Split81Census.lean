/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse2
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.BugInjection.Proofs.Common443.CompRI0Census
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public meta import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public meta import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public meta import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public meta import Symbolic.Specifications.Concrete.ByteSpecs
public meta import Symbolic.Specifications.Concrete.ExternInterpretation
public meta import Symbolic.Specifications.Refinement.TraceExplanation

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompRGamma Symbolic.BugInjection.Proofs.Common443.CompRI0Census Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys computeMac)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable ( F0 OnTab tagW toBEBytes_tagW shaStateOfBytes_compTag4_head compI0_sha256Compress sha256CompressFunction_compI0_head compDefaultSha256_take4 hstep0 shaStateBytes_take4_of_head hT1_0 hT2_0 onTab_of_sha256With_untagged compSha256_row_of_untagged)
export Symbolic.BugInjection.Proofs.Common443.CompRNbscTable ( F0 OnTab tagW toBEBytes_tagW shaStateOfBytes_compTag4_head compI0_sha256Compress sha256CompressFunction_compI0_head compDefaultSha256_take4 hstep0 shaStateBytes_take4_of_head hT1_0 hT2_0 onTab_of_sha256With_untagged compSha256_row_of_untagged)
elab "eval_hwbytes " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t (some (Lean.mkConst ``HwBytes))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let v ← unsafe Lean.Meta.evalExpr (List (BitVec 8)) (Lean.mkConst ``HwBytes) e
  return Lean.toExpr v
def wsSeed6 : HwBytes := eval_hwbytes ((shaStateOfBytes (leBytes 32 0xcbd75b4faf2ec43d66b76e505c95c64adc2109f26aecccac5a68a74b89f1fa25)).toList.flatMap (toBEBytes 4))
theorem wsSeed6_length : wsSeed6.length = 32 := by decide +kernel
set_option maxRecDepth 200000 in
theorem compSha256Rows_wsSeed6_none :
    (compSha256Rows.all fun r => r.2.1 != bytesToNat (padTail64 wsSeed6)) = true := by decide +kernel
theorem sha256With_append64_wsSeed6_take4 (x : HwBytes) (hx : x.length = 64) : (sha256With F0 (x ++ wsSeed6)).take 4 = compTag4 := by
  by_contra hne
  have hchunks : chunks64 (sha256Pad (x ++ wsSeed6)) = [x] ++ padTail64 wsSeed6 :: [] := by rw [sha256Pad_append64 x wsSeed6 hx, chunks64_append64 x _ hx, chunks64_padTail64_32 wsSeed6 wsSeed6_length]; rfl
  obtain ⟨_, _, _, row, hrow, _, hblk, _⟩ := compSha256_row_of_untagged (onTab_of_sha256With_untagged _ hne [x] (padTail64 wsSeed6) [] hchunks); have hall := List.all_eq_true.mp compSha256Rows_wsSeed6_none row hrow; simp [hblk] at hall
theorem hmacWith_F0_wsSeed6_tagged (k : HwBytes) : (hmacWith F0 k wsSeed6).take 4 = compTag4 ∧ (hmacWith F0 k wsSeed6).length = 32 := by
  set k' := if 64 < k.length then sha256With F0 k else k
  have hk' : k'.length ≤ 64 := by dsimp only [k']; split <;> [ (rw [sha256With_length F0 k]; omega); omega ]
  have heq : hmacWith F0 k wsSeed6 = hmacWith F0 k' wsSeed6 := by
    unfold hmacWith; simp only [k', show ¬ 64 < k'.length by omega, ↓reduceIte]
  rw [heq]
  refine ⟨?_, by unfold hmacWith; simp only [show ¬ 64 < k'.length by omega, ↓reduceIte]; exact sha256With_length F0 _⟩
  rw [hmacWith_take4_of_inner OnTab tagW F0 hstep0 hT1_0 hT2_0 k' wsSeed6 hk', toBEBytes_tagW]
  rw [toBEBytes_tagW]; exact sha256With_append64_wsSeed6_take4 _ (by simp only [List.length_map, List.length_append, List.length_replicate]; omega)
theorem hmacWith_F0_tagged_of_key_tagged (k m : HwBytes) (hk : k.take 4 = compTag4 ∧ k.length = 32) : (hmacWith F0 k m).take 4 = compTag4 ∧ (hmacWith F0 k m).length = 32 := by
  have hk_le : ¬ 64 < k.length := by omega
  refine ⟨?_, by unfold hmacWith; simp only [hk_le, ↓reduceIte]; exact sha256With_length F0 _⟩
  by_contra hne; unfold hmacWith at hne; simp only [hk_le, ↓reduceIte] at hne
  set x := (k ++ List.replicate (64 - k.length) 0).map (· ^^^ (0x5c : BitVec 8))
  set inner := sha256With F0 ((k ++ List.replicate (64 - k.length) 0).map (· ^^^ (0x36 : BitVec 8)) ++ m)
  have hx_len : x.length = 64 := by dsimp only [x]; simp only [List.length_map, List.length_append, List.length_replicate, hk.2]
  have hchunks : chunks64 (sha256Pad (x ++ inner)) = [] ++ x :: chunks64 (padTail64 inner) := by rw [sha256Pad_append64 x inner hx_len, chunks64_append64 x _ hx_len]; rfl
  have hx_take4 : x.take 4 = compTag4Opad := by
    dsimp only [x]; rw [← List.map_take, List.take_append_of_le_length (by omega), hk.1]; decide
  apply onTab_of_sha256With_untagged (x ++ inner) hne [] x (chunks64 (padTail64 inner)) hchunks; unfold compSha256; simp only [hx_take4, beq_self_eq_true, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _
theorem gamma_lit0 {i : ExternInterpretation} {S : Sem} {g : Ghost} (b : ByteArray) : gamma i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) = ofByteArray b := by unfold gamma; rw [ms_pack_lit]; rfl
theorem gamma_concat0 {i : ExternInterpretation} {S : Sem} {g : Ghost} (a b : DY.Bytes) : gamma i S g (DY.Concat.concat a b) = gamma i S g a ++ gamma i S g b := by
  unfold gamma; show (gamma' i S g (({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_concat i S g ⟨a, b⟩]; rfl
theorem gamma_hmac0 {S : Sem} {g : Ghost} (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith F0 (gamma compI0 S g k) (gamma compI0 S g m) := by
  unfold gamma; show (gamma' compI0 S g (({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_kdf compI0 S g ⟨k, m⟩]; rfl
theorem gamma_trunc80 {i : ExternInterpretation} {S : Sem} {g : Ghost} (a : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 a) = (gamma i S g a).take 8 := by
  unfold gamma; show (gamma' i S g (({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_trunc i S g ⟨a⟩]; rfl
theorem gamma_hkdfBlock10 {S : Sem} {g : Ghost} (prk info : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g (DY.Concat.concat info (DY.Libsignal.TripleRatchet.litByte 1))) := by unfold DY.Libsignal.TripleRatchet.hkdfBlock1; exact gamma_hmac0 _ _
theorem gamma_hkdfBlock20 {S : Sem} {g : Ghost} (prk info : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) (DY.Concat.concat info (DY.Libsignal.TripleRatchet.litByte 2)))) := by unfold DY.Libsignal.TripleRatchet.hkdfBlock2; exact gamma_hmac0 _ _
theorem trMsgKeys_macKey_tagged_of_seed_wsSeed6 {S : Sem} {g : Ghost} (k seed : DY.Bytes) (hseed : gamma compI0 S g seed = wsSeed6) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys k seed).macKey).take 4 = compTag4 ∧ (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys k seed).macKey).length = 32 := by unfold DY.Libsignal.TripleRatchet.trMsgKeys; dsimp only; rw [gamma_hkdfBlock20]; apply hmacWith_F0_tagged_of_key_tagged; rw [gamma_hmac0, hseed]; exact hmacWith_F0_wsSeed6_tagged (gamma compI0 S g k)
theorem computeMac_take4_of_seed_wsSeed6 {S : Sem} {g : Ghost} (k seed peerIk myIk wire : DY.Bytes) (hseed : gamma compI0 S g seed = wsSeed6) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys k seed).macKey peerIk myIk wire)).take 4 = compTag4 := by unfold DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc80, gamma_hmac0, List.take_take]; exact (hmacWith_F0_tagged_of_key_tagged _ _ (trMsgKeys_macKey_tagged_of_seed_wsSeed6 k seed hseed)).1
theorem not_ownSaltMacCollision_of_seed_wsSeed6 {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {ctxs : List TrialCtx} (hseeds : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed → gamma compI0 S g seed = wsSeed6) (hmac_untagged : (gamma compI0 S g msg.mac).take 4 ≠ compTag4) : ¬ OwnSaltMacCollision compI0 S g known honest msg ctxs := by
  rintro (⟨ctx, hctx, seed, hseed?, k, _hk, hmac_eq, _⟩ | ⟨ctx, hctx, seed, hseed?, k, _hk, hmac_eq, _⟩) <;>
  { have htag := computeMac_take4_of_seed_wsSeed6 k seed ctx.peerIk ctx.myIk msg.wire (hseeds ctx hctx seed hseed?); rw [hmac_eq] at htag; exact hmac_untagged htag }
section FastWire81
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "tf_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let eWhnf ← Lean.Meta.whnf e
  let sLit ← Lean.Meta.whnf eWhnf.getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "tf_str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let eWhnf ← Lean.Meta.whnf e
  Lean.Meta.whnf eWhnf.getAppArgs[0]!
private theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
def wire6Idx1Chars : List Char := tf_chars_of_hex wire6Idx1Bytes
theorem wire6Idx1_eq_hex : wire6Idx1Bytes = hexBytes (tf_str_of_hex wire6Idx1Bytes) := rfl
set_option maxRecDepth 200000 in theorem wire6Idx1Str_eq : (tf_str_of_hex wire6Idx1Bytes) = String.ofList wire6Idx1Chars := rfl
def wire6Idx1Fast : HwBytes := hexBytes.go hexDigit wire6Idx1Chars
theorem wire6Idx1Bytes_eq : wire6Idx1Bytes = wire6Idx1Fast := by change wire6Idx1Bytes = hexBytes.go hexDigit wire6Idx1Chars; rw [wire6Idx1_eq_hex, wire6Idx1Str_eq, hexBytes_ofList]
end FastWire81
set_option maxRecDepth 200000 in theorem wire6Idx1Fast_preKeyId : (parsePreKeyWire wire6Idx1Fast).map (·.preKeyId) = some none := by decide +kernel
theorem wire6Idx1Bytes_preKeyId {p : PreKeyFields} (hp : parsePreKeyWire wire6Idx1Bytes = some p) : p.preKeyId = none := by
  have h := wire6Idx1Fast_preKeyId; rw [← wire6Idx1Bytes_eq, hp] at h; exact Option.some.inj h
set_option maxRecDepth 200000 in
theorem wire6Idx1Fast_mac_take4_ne_compTag4 :
    ((parsePreKeyWire wire6Idx1Fast).map (fun p => (p.message.drop (p.message.length - 8)).take 4 != compTag4)) = some true := by decide +kernel
theorem wire6Idx1Bytes_mac_take4_ne_compTag4 {p : PreKeyFields} (hp : parsePreKeyWire wire6Idx1Bytes = some p) : (p.message.drop (p.message.length - 8)).take 4 ≠ compTag4 := by
  have h := wire6Idx1Fast_mac_take4_ne_compTag4; rw [← wire6Idx1Bytes_eq, hp, Option.map_some, Option.some.injEq, bne_iff_ne] at h; exact h
def ws_dhs1_pub : HwBytes :=
  eval_hwbytes (match parsePreKeyWire wire6Idx1Fast with | some p => p.inner.senderRatchetKey.bytes.toList | none => [])
set_option maxRecDepth 200000 in
theorem wire6Idx1Fast_senderRatchetKey :
    (parsePreKeyWire wire6Idx1Fast).map (fun p => p.inner.senderRatchetKey.bytes.toList) = some ws_dhs1_pub := by decide +kernel
theorem wire6Idx1Bytes_senderRatchetKey {p : PreKeyFields} (hp : parsePreKeyWire wire6Idx1Bytes = some p) : p.inner.senderRatchetKey.bytes.toList = ws_dhs1_pub := by
  have h := wire6Idx1Fast_senderRatchetKey; rw [← wire6Idx1Bytes_eq, hp] at h; exact Option.some.inj h
def ws5_rk : HwBytes := eval_hwbytes (hmacWith F0 (hmacWith F0 (List.replicate 32 0#8) (List.replicate 32 0xFF#8 ++ (compLookupDh (clamp setup.aliceId) (compLookupPub (clamp setup.spk)) ++ (compLookupDh (clamp setup.bobId) ek2PubKey ++ (compLookupDh (clamp setup.spk) ek2PubKey ++ compKyberSs2))))) (ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 ++ [0x01#8]))
def ws6_bob_ck0 : HwBytes := eval_hwbytes (hmacWith F0 (hmacWith F0 ws5_rk (compLookupDh (clamp setup.spk) ws_dhs1_pub)) (hmacWith F0 (hmacWith F0 ws5_rk (compLookupDh (clamp setup.spk) ws_dhs1_pub)) (ofByteArray "WhisperRatchet".toUTF8 ++ [0x01#8]) ++ (ofByteArray "WhisperRatchet".toUTF8 ++ [0x02#8])))
def ws6_bob_ck1 : HwBytes := eval_hwbytes (hmacWith F0 ws6_bob_ck0 [0x02#8])
set_option maxRecDepth 200000 in
theorem kdfCk_ws6_bob_ck0 :
    hmacWith F0 ws6_bob_ck0 [0x02#8] = ws6_bob_ck1 ∧ hmacWith F0 ws6_bob_ck0 [0x01#8] = wsSeed6 := by decide +kernel
set_option maxRecDepth 200000 in theorem kemDecap_kemEncap_fst (sk e : DY.Bytes) : DY.PQKem.kemDecap sk (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).1 = some (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).2 := by simp only [DY.PQKem.kemDecap, DY.PQKem.CanPQKem.kemDecap, DY.PQKem.kemEncap, DY.PQKem.CanPQKem.kemEncap, DY.PQKem.kemPk, DY.PQKem.CanPQKem.kemPk, DY.BytesView.view_pack, ↓reduceIte]
theorem aliceAgreement_fst (ikA ek ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) (e : DY.Bytes) : (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1 = (DY.PQKem.kemEncap pqPk e).1 := rfl
open Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner (encParsedMsg parseTrSignalMsg_encOut)
export Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner (encParsedMsg parseTrSignalMsg_encOut)
theorem parseTrSignalMsg_x81Idx1 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    parseTrSignalMsg (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg = some (encParsedMsg tr₂ stA₁ cl₁ (tr₂.length + 2)) :=
  parseTrSignalMsg_encOut tr₂ _ cl₁ (tr₂.length + 2)
def Split81SetupPins (r : Records) : Prop := setupSecret r 0 = randTerm 0 32 ∧ setupSecret r 1 = randTerm 5 32 ∧ setupSecret r 2 = randTerm 10 32 ∧ setupSecret r 4 = randTerm 16 64 ∧ setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) ∧ setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) ∧ setupPublic r 4 = DY.DiffieHellman.dhPk (randTerm 10 32) ∧ setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) ∧ r.alice ≠ r.bob
theorem setupPublic_6_eq_kemPk_4 {r : Records} (hpins : Split81SetupPins r) :
    setupPublic r 6 = DY.PQKem.kemPk (setupSecret r 4) := by rw [hpins.2.2.2.2.2.2.2.1, hpins.2.2.2.1]
theorem gamma_randTerm_32 {i : ExternInterpretation} {S : Sem} {g : Ghost} (idx : Nat) :
    gamma i S g (randTerm idx 32) = g.σ idx 32 := by unfold gamma randTerm; rw [ms_pack_random i S g ⟨idx, 32⟩]; rfl
theorem gamma_setupSecret_0 {r : Records} {S : Sem} {g : Ghost} (hpins : Split81SetupPins r) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 0) = secretBytes r 0 := by
  rw [hpins.1, gamma_randTerm_32, hc.1 (0, 32) (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> simp)]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> rfl
theorem gamma_setupSecret_1 {r : Records} {S : Sem} {g : Ghost} (hpins : Split81SetupPins r) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 1) = secretBytes r 1 := by
  rw [hpins.2.1, gamma_randTerm_32, hc.1 (5, 32) (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> simp)]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> rfl
theorem gamma_setupSecret_2 {r : Records} {S : Sem} {g : Ghost} (hpins : Split81SetupPins r) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 2) = secretBytes r 2 := by
  rw [hpins.2.2.1, gamma_randTerm_32, hc.1 (10, 32) (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> simp)]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hpins.2.2.2.2.2.2.2.2]; cases r.withOpk <;> rfl
theorem gamma_setupPublic_0 {r : Records} {S : Sem} {g : Ghost} (hpins : Split81SetupPins r) (hc : Compat compI0 r S g) : gamma compI0 S g (setupPublic r 0) = compLookupPub (clamp (secretBytes r 0)) := by rw [hpins.2.2.2.2.1, gamma_dhPk, ← hpins.1, gamma_setupSecret_0 hpins hc]; rfl
theorem gamma_setupPublic_2 {r : Records} {S : Sem} {g : Ghost} (hpins : Split81SetupPins r) (hc : Compat compI0 r S g) : gamma compI0 S g (setupPublic r 2) = compLookupPub (clamp (secretBytes r 1)) := by rw [hpins.2.2.2.2.2.1, gamma_dhPk, ← hpins.2.1, gamma_setupSecret_1 hpins hc]; rfl
theorem gamma_kemEncap_snd_compI0 (S : Sem) (g : Ghost) (pk e : DY.Bytes) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = if (gamma compI0 S g e).length = 32 then ((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e]).getD []).drop 1568 else S.kemDecap (gamma compI0 S g pk) (gamma compI0 S g e) := by
  unfold gamma; show (gamma' compI0 S g (({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack)).bytes = _
  rw [ms_pack_kemSS compI0 S g ⟨pk, e⟩]; unfold gKemSS concretizeKemSS; dsimp only; split <;> rfl
theorem compKyberE2_length : compKyberE2.length = 32 := by decide +kernel
set_option maxRecDepth 200000 in
theorem gamma_ss2_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hpub6 : r.opaqueBytes (setupPublic r 6) = setup.kyberPk) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).2 = compKyberSs2 := by
  rw [gamma_kemEncap_snd_compI0, hinv.hent₂]
  have h6 : gamma compI0 S g (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) :=
    hinv.compat.2.1 r.pqpkPubTerm (by simp)
  simp only [compKyberE2_length, ↓reduceIte, h6, hpub6]; decide +kernel
theorem gamma_lit_bytes {S : Sem} {g : Ghost} (b : ByteArray) : gamma compI0 S g (DY.Literal.literalToBytes b) = ofByteArray b := gamma_lit0 b
theorem gamma_litByte0 {S : Sem} {g : Ghost} (b : UInt8) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b) = [b.toBitVec] := by unfold DY.Libsignal.TripleRatchet.litByte; rw [gamma_lit_bytes]; rfl
theorem gamma_zeroSalt0 {S : Sem} {g : Ghost} : gamma compI0 S g DY.Libsignal.TripleRatchet.zeroSalt = List.replicate 32 0#8 := by unfold DY.Libsignal.TripleRatchet.zeroSalt; rw [gamma_lit_bytes]; decide +kernel
theorem gamma_discontinuity0 {S : Sem} {g : Ghost} : gamma compI0 S g DY.Libsignal.PQXDH.discontinuity = List.replicate 32 0xFF#8 := by unfold DY.Libsignal.PQXDH.discontinuity; rw [gamma_lit_bytes]; decide +kernel
theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
theorem gamma_pqxdhLabel0 {S : Sem} {g : Ghost} : gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel = ofByteArray ("WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toList.utf8Encode) := by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [gamma_lit_bytes, toUTF8_eq_ofList]
theorem gamma_whisperRatchet0 {S : Sem} {g : Ghost} : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") = ofByteArray ("WhisperRatchet".toList.utf8Encode) := by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_lit_bytes, toUTF8_eq_ofList]
def bobStartKeys (r : Records) (x : PreKeyRep) : DY.Libsignal.PQXDH.HandshakeKeys :=
  let ikA := setupPublic r 0; let spk := setupSecret r 2; let pqsk := setupSecret r 4
  let ss := (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk x.ct)).getD (DY.PQKem.kemRejKey pqsk x.ct)
  DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree ikA spk) (DY.Libsignal.PQXDH.agree x.ek (setupSecret r 1)) (DY.Libsignal.PQXDH.agree x.ek spk)
    (Option.map (DY.Libsignal.PQXDH.agree x.ek ·) none) ss)
set_option maxRecDepth 200000 in
theorem gamma_bobStartKeys_rk_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hpins : Split81SetupPins r) (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0) (hs0 : secretBytes r 0 = setup.aliceId) (hs1 : secretBytes r 1 = setup.bobId) (hs2 : secretBytes r 2 = setup.spk) (hpub6 : r.opaqueBytes (setupPublic r 6) = setup.kyberPk) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (bobStartKeys r (x81Idx1 r tr₁ tr₂ tr₄ cl₁)).rk = ws5_rk := by
  let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
  have hss_eq : (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD (DY.PQKem.kemRejKey (setupSecret r 4) x.ct) = (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).2 := by dsimp only [x, x81Idx1, iniAliceOut]; rw [aliceAgreement_fst, setupPublic_6_eq_kemPk_4 hpins, kemDecap_kemEncap_fst]; rfl
  have hdh1 : gamma compI0 S g (DY.Libsignal.PQXDH.agree (setupPublic r 0) (setupSecret r 2)) = compLookupDh (clamp setup.spk) (compLookupPub (clamp setup.aliceId)) := by rw [gamma_agree compI0 hEq, gamma_setupSecret_2 hpins hinv.compat, gamma_setupPublic_0 hpins hinv.compat, hs0, hs2]; rfl
  have hdh2 : gamma compI0 S g (DY.Libsignal.PQXDH.agree x.ek (setupSecret r 1)) = compLookupDh (clamp setup.bobId) ek2PubKey := by change gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) (setupSecret r 1)) = _; rw [gamma_agree compI0 hEq, gamma_setupSecret_1 hpins hinv.compat, hinv.hek₂, hs1]; rfl
  have hdh3 : gamma compI0 S g (DY.Libsignal.PQXDH.agree x.ek (setupSecret r 2)) = compLookupDh (clamp setup.spk) ek2PubKey := by change gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) (setupSecret r 2)) = _; rw [gamma_agree compI0 hEq, gamma_setupSecret_2 hpins hinv.compat, hinv.hek₂, hs2]; rfl
  have hss2 := gamma_ss2_ws81Idx1 hpub6 hinv; unfold bobStartKeys; dsimp only [Option.map]; rw [hss_eq]; unfold DY.Libsignal.PQXDH.pqxdhKdf DY.Libsignal.PQXDH.pqxdhIkm; dsimp only; rw [gamma_hkdfBlock10, gamma_hmac0, gamma_zeroSalt0, gamma_concat0, gamma_discontinuity0, gamma_concat0, gamma_concat0, gamma_concat0, hdh1, hdh2, hdh3, hss2, gamma_concat0, gamma_pqxdhLabel0, gamma_litByte0]; decide +kernel
def bobChainCk0 (r : Records) (rk ratchetKey : DY.Bytes) : DY.Bytes := (DY.Libsignal.TripleRatchet.createChain rk ratchetKey (setupSecret r 2)).2
set_option maxRecDepth 200000 in
theorem gamma_bobChainCk0_ws81Idx1 {r : Records} {S : Sem} {g : Ghost}
    {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p : PreKeyFields}
    (hpins : Split81SetupPins r) (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0)
    (hs0 : secretBytes r 0 = setup.aliceId) (hs1 : secretBytes r 1 = setup.bobId)
    (hs2 : secretBytes r 2 = setup.spk) (hpub6 : r.opaqueBytes (setupPublic r 6) = setup.kyberPk)
    (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁; let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
    let msg := encParsedMsg tr₂ stA₁ cl₁ (tr₂.length + 2)
    gamma compI0 S g (bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey) = ws6_bob_ck0 := by
  intro o₁ stA₁ x msg; have hrk := gamma_bobStartKeys_rk_ws81Idx1 hpins hEq hs0 hs1 hs2 hpub6 hinv
  have hdhs : gamma compI0 S g msg.ratchetKey = ws_dhs1_pub := by change gamma compI0 S g (DY.DiffieHellman.dhPk stA₁.dhs) = ws_dhs1_pub; rw [(hinv.hwire₁ p hp).2.2, wire6Idx1Bytes_senderRatchetKey hp]
  have hdh_bob : gamma compI0 S g (DY.Libsignal.PQXDH.agree msg.ratchetKey (setupSecret r 2)) = compLookupDh (clamp setup.spk) ws_dhs1_pub := by rw [gamma_agree compI0 hEq, gamma_setupSecret_2 hpins hinv.compat, hdhs, hs2]; rfl
  change gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 (DY.Libsignal.TripleRatchet.hmac (bobStartKeys r x).rk (DY.Libsignal.PQXDH.agree msg.ratchetKey (setupSecret r 2))) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")) = ws6_bob_ck0; rw [gamma_hkdfBlock20, gamma_concat0, gamma_hkdfBlock10, gamma_concat0, gamma_concat0, gamma_hmac0, gamma_whisperRatchet0, gamma_litByte0, gamma_litByte0, hrk, hdh_bob]; decide +kernel
set_option maxRecDepth 200000 in
theorem gamma_bobSeed0_ws81Idx1 {r : Records} {S : Sem} {g : Ghost}
    {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p : PreKeyFields}
    (hpins : Split81SetupPins r) (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0)
    (hs0 : secretBytes r 0 = setup.aliceId) (hs1 : secretBytes r 1 = setup.bobId)
    (hs2 : secretBytes r 2 = setup.spk) (hpub6 : r.opaqueBytes (setupPublic r 6) = setup.kyberPk)
    (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁; let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
    let msg := encParsedMsg tr₂ stA₁ cl₁ (tr₂.length + 2)
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey)).2 = wsSeed6 := by
  intro o₁ stA₁ x msg; have hck := gamma_bobChainCk0_ws81Idx1 hpins hEq hs0 hs1 hs2 hpub6 hp hinv; unfold DY.Libsignal.TripleRatchet.kdfCk; dsimp only; rw [gamma_hmac0, gamma_litByte0, hck]; exact kdfCk_ws6_bob_ck0.2
theorem bobTrials_x81Idx1_seed_eq {r : Records} {tr : ExecTrace} {p : PreKeyFields} (hopk : p.preKeyId = none)
    (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁; let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
    let msg := encParsedMsg tr₂ stA₁ cl₁ (tr₂.length + 2)
    ∀ ctx ∈ bobTrials r tr p x msg, ∀ seed, ctx.seed? = some seed →
      seed = (DY.Libsignal.TripleRatchet.kdfCk (bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey)).2 := by
  intro o₁ stA₁ x msg ctx hctx seed hseed?
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm ProtocolSetup.spkSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.pqskSecTerm at hctx
  rw [hopk] at hctx
  dsimp only at hctx; split at hctx; · simp at hctx
  change ctx ∈ [{ peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 0), myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 2), extra := [(bobStartKeys r x).rk, (bobStartKeys r x).ck, (bobStartKeys r x).pqr, bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey, (DY.Libsignal.TripleRatchet.kdfCk (bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey)).1], ownSalts := _, seed? := some (DY.Libsignal.TripleRatchet.kdfCk (bobChainCk0 r (bobStartKeys r x).rk msg.ratchetKey)).2 }] at hctx
  simp only [List.mem_singleton] at hctx; subst hctx; exact Option.some.inj hseed?.symm
theorem fits_secrets {r : Records} (hfits : compFitsPinned setup compI0 r) : secretBytes r 0 = setup.aliceId ∧ secretBytes r 1 = setup.bobId ∧ secretBytes r 2 = setup.spk ∧ r.opaqueBytes (setupPublic r 6) = setup.kyberPk ∧ DY.Libsignal.Refinement.CryptoEquationsHold compI0 := by rcases hfits.1 with ⟨_, _, _, _, _, _, hs0, hs1, hs2, _, hpub6, _, _, hEq, _⟩; exact ⟨hs0, hs1, hs2, hpub6, hEq⟩
theorem not_ownSaltMacCollision_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {msg : TRSignalMsg} (hpins : Split81SetupPins r) (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hmsg : parseTrSignalMsg (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg = some msg) : ¬ OwnSaltMacCollision compI0 S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (honestSalts r ms') msg (bobTrials r (runTraceMoves r ms') p (x81Idx1 r tr₁ tr₂ tr₄ cl₁) msg) := by
  rw [parseTrSignalMsg_x81Idx1 r tr₁ tr₂ tr₄ cl₁] at hmsg; cases Option.some.inj hmsg.symm; obtain ⟨hs0, hs1, hs2, hpub6, hEq⟩ := fits_secrets hfits
  refine not_ownSaltMacCollision_of_seed_wsSeed6 (fun ctx hctx seed hseed? => ?_) ?_
  · rw [bobTrials_x81Idx1_seed_eq (wire6Idx1Bytes_preKeyId hp) tr₁ tr₂ tr₄ cl₁ ctx hctx seed hseed?]
    exact gamma_bobSeed0_ws81Idx1 hpins hEq hs0 hs1 hs2 hpub6 hp hinv
  · change (gamma compI0 S g (encMac tr₂ _ cl₁ (tr₂.length + 2))).take 4 ≠ compTag4
    rw [(hinv.hwire₁ p hp).2.1]; exact wire6Idx1Bytes_mac_take4_ne_compTag4 hp
def Split81PkPin : Prop := ∀ r : Records, compFitsPinned setup compI0 r → setupPublic r 6 = DY.PQKem.kemPk (setupSecret r 4)
def Split81PinObl : Prop := ∀ r : Records, compFitsPinned setup compI0 r → Split81SetupPins r
theorem split81PkPin_of_pinObl (hpin : Split81PinObl) : Split81PkPin := fun r hfits => setupPublic_6_eq_kemPk_4 (hpin r hfits)
def split81NewTerms (r : Records) (ms' : List Move) (p : PreKeyFields) (x : PreKeyRep) : List DY.Bytes :=
  match parseTrSignalMsg x.msg with
  | none => [x.ek, x.ct, x.msg]
  | some _ => [x.ek, x.ct, x.msg] ++ bobTerms r (honestSalts r ms') p x
def Split81OwnSaltMac : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (msg : TRSignalMsg), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → parseTrSignalMsg (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg = some msg → ¬ OwnSaltMacCollision compI0 S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (honestSalts r ms') msg (bobTrials r (runTraceMoves r ms') p (x81Idx1 r tr₁ tr₂ tr₄ cl₁) msg)
theorem split81OwnSaltMac_of_pin (hpin : Split81PinObl) : Split81OwnSaltMac := fun r _S _g _p _ms' _tr₁ _tr₂ _tr₃ _tr₄ _tr₅ _cl₁ _cl₂ _cl₅ _msg hfits hp hinv hP => not_ownSaltMacCollision_ws81Idx1 (hpin r hfits) hfits hp hinv hP
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census
