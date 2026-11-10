/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public meta import Symbolic.BugInjection.Proofs.Common443.CompRTag
public meta import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public meta import Symbolic.Specifications.Concrete.ByteSpecs

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompRTag
theorem gamma_hmac_compI0 (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith (sha256CompressFunction compI0) (gamma compI0 S g k) (gamma compI0 S g m) := by
  unfold gamma gamma'
  show ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gKdf0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_trunc8_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 b) = (gamma i S g b).take 8 := by
  unfold gamma gamma'
  show ((({ input := b } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt ( length_append_entry at?_append_eq_of_eq F0 OnTab tagW compI0_sha256Compress sha256CompressFunction_compI0_head compDefaultSha256_take4 compSha256_row_of_untagged leBytes_bytesToNat toBEBytes_tagW shaStateOfBytes_compTag4_head hstep0 shaStateBytes_take4_of_head hT1_0 onTab_of_sha256With_untagged kblk kblk_length hmacWith_eq hmac_outer_first_onTab ivNat map_xor_xor digestOfOut rowOfTake8 rowByOut keyOfRow1 keyOfTake8 rows_out_nodup rows_take8_nodup rows_out_roundtrip find?_eq_some_of_nodup F0_eq row_step keyOfTake8_hmacWith take4_take8 msgMac8 macChainOk wireMacChainOk macChainOk_spec macChainOk_of_wire hexBytes_ofList)
export Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs (hexDigit)
private theorem encPreSaltTr_getMessageSentAt_self (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : (encPreSaltTr tr₂ stA cl).getMessageSentAt (tr₂.length + 2) = some (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  unfold encPreSaltTr
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?]; dsimp only
  rw [at?_append_eq_of_eq (T := DY.Network.ExecEntryT) _ (NetE _) (i := tr₂.length + 2) (by simp)]; rfl
theorem encSalt_self (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : encSalt tr₂ stA cl (tr₂.length + 2) = (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by unfold encSalt; rw [encPreSaltTr_getMessageSentAt_self]; rfl
theorem gamma_spqrSendKey_length {S : Sem} {g : Ghost} (st c : DY.Bytes) : (gamma compI0 S g (DY.Spqr.spqrSend st c).2.1).length = 32 := by
  unfold DY.Spqr.spqrSend; dsimp only
  cases st.view? DY.Spqr.InitState.SubF with
  | some s =>
    unfold gamma gamma' DY.Spqr.spqrChainKey; rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll compI0 S g)]
    show (spqrKeyBytes _).length = 32; unfold spqrKeyBytes; simp
  | none =>
    unfold gamma gamma'; rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll compI0 S g)]
    show (spqrKeyBytes _).length = 32; unfold spqrKeyBytes; simp
theorem padTail64_take32 (h : List (BitVec 8)) (hh : h.length = 32) : (padTail64 h).take 32 = h := by unfold padTail64; rw [List.append_assoc, List.append_assoc, List.take_left' hh]
theorem padTail64_length_32 (h : List (BitVec 8)) (hh : h.length = 32) : (padTail64 h).length = 64 := by simp only [padTail64, List.length_append, List.length_cons, List.length_nil, List.length_replicate, toBEBytes_length, hh]
theorem hT2_0 : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTab s b := by intro s b hb h; rw [toBEBytes_tagW] at hb; apply h; unfold compSha256; simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _
theorem hmac_inner_untagged (k m : HwBytes) (hk : k.length ≤ 64) (h : (hmacWith F0 k m).take 4 ≠ compTag4) :
    (sha256With F0 (kblk k 0x36 ++ m)).take 4 ≠ compTag4 :=
  fun hin => h (by rw [hmacWith_take4_of_inner OnTab tagW F0 hstep0 hT1_0 hT2_0 k m hk (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW])
def msg32OfTake8 (v : HwBytes) : Option HwBytes :=
  match rowOfTake8 v with
  | none => none
  | some r2 =>
    match rowOfTake8 (((leBytes 64 r2.2.1).take 32).take 8) with
    | none => none
    | some r_in2 => some ((leBytes 64 r_in2.2.1).take 32)
theorem msg32OfTake8_hmacWith (k m : HwBytes) (hk : k.length = 32) (hm : m.length = 32) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : msg32OfTake8 ((hmacWith F0 k m).take 8) = some m := by
  have hk64 : k.length ≤ 64 := by omega
  have hx5c := kblk_length k 0x5c hk64; have hx36 := kblk_length k 0x36 hk64; have h_in_untagged := hmac_inner_untagged k m hk64 h
  set inner := sha256With F0 (kblk k 0x36 ++ m) with hinner_def
  have hil : inner.length = 32 := sha256With_length F0 _; have h_out := h; rw [hmacWith_eq k m hk64, ← hinner_def] at h_out
  have hch_out : chunks64 (sha256Pad (kblk k 0x5c ++ inner)) = [kblk k 0x5c] ++ padTail64 inner :: [] := by rw [sha256Pad_append64 _ _ hx5c, chunks64_append64 _ _ hx5c, chunks64_padTail64_32 inner hil]; rfl
  have h2_out : OnTab ([kblk k 0x5c].foldl F0 sha256IV) (padTail64 inner) := onTab_of_sha256With_untagged _ h_out [kblk k 0x5c] (padTail64 inner) [] hch_out; rw [List.foldl_cons, List.foldl_nil] at h2_out; obtain ⟨r2, hr2, _, hr2b, hF2_out⟩ := row_step h2_out
  have hsha_out : hmacWith F0 k m = digestOfOut r2.2.2 := by rw [hmacWith_eq k m hk64, ← hinner_def]; unfold sha256With digestOfOut; rw [hch_out, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2_out]
  have hblk_out : (leBytes 64 r2.2.1).take 32 = inner := by have hrt := leBytes_bytesToNat (padTail64 inner); rw [padTail64_length_32 inner hil] at hrt; rw [hr2b, hrt, padTail64_take32 inner hil]
  have hch_in : chunks64 (sha256Pad (kblk k 0x36 ++ m)) = [kblk k 0x36] ++ padTail64 m :: [] := by rw [sha256Pad_append64 _ _ hx36, chunks64_append64 _ _ hx36, chunks64_padTail64_32 m hm]; rfl
  have h2_in : OnTab ([kblk k 0x36].foldl F0 sha256IV) (padTail64 m) := onTab_of_sha256With_untagged _ h_in_untagged [kblk k 0x36] (padTail64 m) [] hch_in; rw [List.foldl_cons, List.foldl_nil] at h2_in; obtain ⟨r_in2, hr_in2, _, hr_in2b, hF2_in⟩ := row_step h2_in
  have hsha_in : inner = digestOfOut r_in2.2.2 := by rw [hinner_def]; unfold sha256With digestOfOut; rw [hch_in, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2_in]
  have hblk_in : (leBytes 64 r_in2.2.1).take 32 = m := by have hrt := leBytes_bytesToNat (padTail64 m); rw [padTail64_length_32 m hm] at hrt; rw [hr_in2b, hrt, padTail64_take32 m hm]
  have hfind_out : rowOfTake8 ((digestOfOut r2.2.2).take 8) = some r2 :=
    find?_eq_some_of_nodup compSha256Rows (fun r => (digestOfOut r.2.2).take 8) ((digestOfOut r2.2.2).take 8) rows_take8_nodup r2 hr2 rfl
  have hfind_in : rowOfTake8 (inner.take 8) = some r_in2 := by
    rw [hsha_in]; exact find?_eq_some_of_nodup compSha256Rows (fun r => (digestOfOut r.2.2).take 8) ((digestOfOut r_in2.2.2).take 8) rows_take8_nodup r_in2 hr_in2 rfl
  rw [hsha_out]; unfold msg32OfTake8; simp only [hfind_out, hblk_out, hfind_in, hblk_in]
theorem gamma_hmac_length (S : Sem) (g : Ghost) (k m : DY.Bytes) :
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by rw [gamma_hmac_compI0]; exact sha256With_length F0 _
abbrev encSeed (stA : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
theorem gamma_encSeed_length (S : Sem) (g : Ghost) (stA : DY.Libsignal.TripleRatchet.TRState) : (gamma compI0 S g (encSeed stA)).length = 32 := gamma_hmac_length S g stA.cks (DY.Libsignal.TripleRatchet.litByte 0x01)
abbrev msgPrk (salt seed : DY.Bytes) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac salt seed
abbrev encKeys (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.MessageKeys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (encSeed stA)
abbrev encPrk (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes := msgPrk (encSalt tr₂ stA cl pq) (encSeed stA)
theorem gamma_msgPrk_length (S : Sem) (g : Ghost) (salt seed : DY.Bytes) : (gamma compI0 S g (msgPrk salt seed)).length = 32 := gamma_hmac_length S g salt seed
theorem gamma_macKey_length (S : Sem) (g : Ghost) (salt seed : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).length = 32 := gamma_hmac_length S g _ _
theorem gamma_computeMac (S : Sem) (g : Ghost) (mk a b w : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w) = (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac mk (Concat.concat a (Concat.concat b w)))).take 8 := by unfold DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc8_eq]
theorem keyOfTake8_encMac (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (h : (gamma compI0 S g (encMac tr₂ stA cl pq)).take 4 ≠ compTag4) : keyOfTake8 (gamma compI0 S g (encMac tr₂ stA cl pq)) = some (gamma compI0 S g (encKeys tr₂ stA cl pq).macKey) := by
  change (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq))).take 4 ≠ compTag4 at h; change keyOfTake8 (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq))) = _; rw [gamma_computeMac, take4_take8, gamma_hmac_compI0] at h; rw [gamma_computeMac, gamma_hmac_compI0]
  exact keyOfTake8_hmacWith _ _ (gamma_macKey_length S g _ _) h
theorem keyOfTake8_encMacKey (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (h : (gamma compI0 S g (encKeys tr₂ stA cl pq).macKey).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (encKeys tr₂ stA cl pq).macKey).take 8) = some (gamma compI0 S g (encPrk tr₂ stA cl pq)) := by change (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encPrk tr₂ stA cl pq) _)).take 4 ≠ compTag4 at h; change keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encPrk tr₂ stA cl pq) _)).take 8) = _; rw [gamma_hmac_compI0] at h ⊢; exact keyOfTake8_hmacWith _ _ (gamma_msgPrk_length S g _ _) h
theorem encSalt_and_seed_of_prk (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) {P saltBytes seedBytes : HwBytes} (hs : (gamma compI0 S g (encSalt tr stA cl pq)).length = 32) (hP : gamma compI0 S g (encPrk tr stA cl pq) = P) (hPin : P.take 4 ≠ compTag4 ∧ keyOfTake8 (P.take 8) = some saltBytes ∧ msg32OfTake8 (P.take 8) = some seedBytes) : gamma compI0 S g (encSalt tr stA cl pq) = saltBytes ∧ gamma compI0 S g (encSeed stA) = seedBytes := by
  have htag : (hmacWith F0 (gamma compI0 S g (encSalt tr stA cl pq)) (gamma compI0 S g (encSeed stA))).take 4 ≠ compTag4 := by rw [← gamma_hmac_compI0]; change (gamma compI0 S g (encPrk tr stA cl pq)).take 4 ≠ compTag4; rw [hP]; exact hPin.1
  have hkey := keyOfTake8_hmacWith _ _ hs htag; have hmsg := msg32OfTake8_hmacWith _ _ hs (gamma_encSeed_length S g stA) htag; rw [← gamma_hmac_compI0] at hkey hmsg; change keyOfTake8 ((gamma compI0 S g (encPrk tr stA cl pq)).take 8) = _ at hkey; change msg32OfTake8 ((gamma compI0 S g (encPrk tr stA cl pq)).take 8) = _ at hmsg; rw [hP, hPin.2.1] at hkey; rw [hP, hPin.2.2] at hmsg; exact ⟨(Option.some.inj hkey).symm, (Option.some.inj hmsg).symm⟩
theorem encMac_chain_of_macChainOk (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) {k P : HwBytes} {p : PreKeyFields} (hmac : gamma compI0 S g (encMac tr stA cl pq) = msgMac8 p) (hok : macChainOk k P p = true) : gamma compI0 S g (encKeys tr stA cl pq).macKey = k ∧ gamma compI0 S g (encPrk tr stA cl pq) = P := by
  obtain ⟨h1, h2, h3, h4⟩ := macChainOk_spec hok
  have hk : gamma compI0 S g (encKeys tr stA cl pq).macKey = k := by
    have hrec := keyOfTake8_encMac S g tr stA cl pq (by rw [hmac]; exact h1); rw [hmac, h2] at hrec; exact (Option.some.inj hrec).symm
  have hP : gamma compI0 S g (encPrk tr stA cl pq) = P := by
    have hrec := keyOfTake8_encMacKey S g tr stA cl pq (by rw [hk]; exact h3); rw [hk, h4] at hrec; exact (Option.some.inj hrec).symm
  exact ⟨hk, hP⟩
theorem saltAndSeedPin_of_macChainOk (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) {k P saltBytes seedBytes : HwBytes} {p : PreKeyFields} (hmac : gamma compI0 S g (encMac tr stA cl (tr.length + 2)) = msgMac8 p) (hok : macChainOk k P p = true) (hPin : P.take 4 ≠ compTag4 ∧ keyOfTake8 (P.take 8) = some saltBytes ∧ msg32OfTake8 (P.take 8) = some seedBytes) : gamma compI0 S g (encKeys tr stA cl (tr.length + 2)).macKey = k ∧ gamma compI0 S g (encPrk tr stA cl (tr.length + 2)) = P ∧ gamma compI0 S g (encSalt tr stA cl (tr.length + 2)) = saltBytes ∧ gamma compI0 S g (encSeed stA) = seedBytes := by
  obtain ⟨hk, hP⟩ := encMac_chain_of_macChainOk S g tr stA cl (tr.length + 2) hmac hok
  have hs : (gamma compI0 S g (encSalt tr stA cl (tr.length + 2))).length = 32 := by rw [encSalt_self]; exact gamma_spqrSendKey_length _ _
  obtain ⟨hSalt, hSeed⟩ := encSalt_and_seed_of_prk S g tr stA cl (tr.length + 2) hs hP hPin; exact ⟨hk, hP, hSalt, hSeed⟩
elab "eval_hwbytes " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t (some (Lean.mkConst ``HwBytes))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let v ← unsafe Lean.Meta.evalExpr (List (BitVec 8)) (Lean.mkConst ``HwBytes) e
  return Lean.toExpr v
def wsSaltA : HwBytes := [117,101,207,237,172,88,7,20,94,126,243,182,84,254,20,66,172,96,97,156,179,198,46,30,247,246,247,198,68,58,11,138]
def wsSaltB : HwBytes := [3,135,79,214,65,239,215,73,23,43,93,228,9,241,97,76,22,238,115,16,46,97,110,254,183,166,247,35,87,20,76,122]
def wsSaltC : HwBytes := [32,235,61,216,224,48,56,38,58,71,234,77,62,147,122,119,64,243,207,133,153,241,175,174,72,83,193,34,71,164,22,175]
def wsMacKey : HwBytes := [57,0,208,163,69,193,232,212,124,95,127,218,65,194,127,66,236,188,184,18,216,32,180,137,222,237,167,51,15,37,86,17]
def wsPrk : HwBytes := [187,54,226,4,174,10,19,17,48,253,69,170,58,219,155,75,22,174,233,236,92,150,239,156,118,0,90,186,220,57,25,240]
def ws3MacKey : HwBytes := [114,127,169,60,91,52,199,80,101,192,3,134,56,105,7,52,114,241,239,250,80,195,8,61,18,159,46,1,166,229,124,3]
def ws3Prk : HwBytes := [218,60,112,85,168,5,198,88,0,67,68,248,250,106,86,99,10,117,19,237,185,102,31,145,90,242,107,126,210,166,108,15]
def ws5MacKey : HwBytes := [60,238,34,191,113,216,201,115,190,55,54,114,242,214,84,235,177,49,156,101,134,22,207,107,247,59,36,25,251,233,78,66]
def ws5Prk : HwBytes := [170,186,92,242,242,140,67,185,79,184,102,212,124,54,127,168,80,191,161,221,87,172,137,141,221,253,22,10,141,69,123,15]
def wsSeed1Bytes : HwBytes := eval_hwbytes ((msg32OfTake8 (wsPrk.take 8)).getD [])
def wsSeed2Bytes : HwBytes := eval_hwbytes ((msg32OfTake8 (ws3Prk.take 8)).getD [])
def wsSeed5Bytes : HwBytes := eval_hwbytes ((msg32OfTake8 (ws5Prk.take 8)).getD [])
theorem wsPrk_pin : wsPrk.take 4 ≠ compTag4 ∧ keyOfTake8 (wsPrk.take 8) = some wsSaltA ∧ msg32OfTake8 (wsPrk.take 8) = some wsSeed1Bytes := by decide +kernel
theorem ws3Prk_pin : ws3Prk.take 4 ≠ compTag4 ∧ keyOfTake8 (ws3Prk.take 8) = some wsSaltB ∧ msg32OfTake8 (ws3Prk.take 8) = some wsSeed2Bytes := by decide +kernel
theorem ws5Prk_pin : ws5Prk.take 4 ≠ compTag4 ∧ keyOfTake8 (ws5Prk.take 8) = some wsSaltC ∧ msg32OfTake8 (ws5Prk.take 8) = some wsSeed5Bytes := by decide +kernel
theorem eventBytes_recv (b : HwBytes) : Refinement.eventBytes (.recv b) = b := rfl
theorem eventBytes_send (b : HwBytes) : Refinement.eventBytes (.send b) = b := rfl
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def schedBCall1SendBytes : HwBytes := Refinement.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 37).headD (.send []))
def schedBCall2SendBytes : HwBytes := Refinement.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 39).headD (.send []))
def schedBCall5SendBytes : HwBytes := Refinement.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 80).headD (.send []))
def schedBCall6RecvBytes : HwBytes := Refinement.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 81).headD (.recv []))
def schedBCall1SendChars : List Char := chars_of_hex_def schedBCall1SendBytes
theorem schedBCall1Send_head_eq : (Witnesses.Cheval26WeakStateIdx1.trace.drop 37).headD (.send []) = .send (hexBytes (str_of_hex_def schedBCall1SendBytes)) := rfl
theorem schedBCall1SendStr_eq : (str_of_hex_def schedBCall1SendBytes) = String.ofList schedBCall1SendChars := rfl
theorem schedBCall1SendBytes_eq : schedBCall1SendBytes = hexBytes.go hexDigit schedBCall1SendChars := by rw [schedBCall1SendBytes, schedBCall1Send_head_eq, eventBytes_send, schedBCall1SendStr_eq, hexBytes_ofList]
def schedBCall1SendFast : HwBytes := hexBytes.go hexDigit schedBCall1SendChars
def schedBCall2SendChars : List Char := chars_of_hex_def schedBCall2SendBytes
theorem schedBCall2Send_head_eq : (Witnesses.Cheval26WeakStateIdx1.trace.drop 39).headD (.send []) = .send (hexBytes (str_of_hex_def schedBCall2SendBytes)) := rfl
theorem schedBCall2SendStr_eq : (str_of_hex_def schedBCall2SendBytes) = String.ofList schedBCall2SendChars := rfl
theorem schedBCall2SendBytes_eq : schedBCall2SendBytes = hexBytes.go hexDigit schedBCall2SendChars := by rw [schedBCall2SendBytes, schedBCall2Send_head_eq, eventBytes_send, schedBCall2SendStr_eq, hexBytes_ofList]
def schedBCall2SendFast : HwBytes := hexBytes.go hexDigit schedBCall2SendChars
def schedBCall5SendChars : List Char := chars_of_hex_def schedBCall5SendBytes
theorem schedBCall5Send_head_eq : (Witnesses.Cheval26WeakStateIdx1.trace.drop 80).headD (.send []) = .send (hexBytes (str_of_hex_def schedBCall5SendBytes)) := rfl
theorem schedBCall5SendStr_eq : (str_of_hex_def schedBCall5SendBytes) = String.ofList schedBCall5SendChars := rfl
theorem schedBCall5SendBytes_eq : schedBCall5SendBytes = hexBytes.go hexDigit schedBCall5SendChars := by rw [schedBCall5SendBytes, schedBCall5Send_head_eq, eventBytes_send, schedBCall5SendStr_eq, hexBytes_ofList]
def schedBCall5SendFast : HwBytes := hexBytes.go hexDigit schedBCall5SendChars
def schedBCall6RecvChars : List Char := chars_of_hex_def schedBCall6RecvBytes
theorem schedBCall6Recv_head_eq : (Witnesses.Cheval26WeakStateIdx1.trace.drop 81).headD (.recv []) = .recv (hexBytes (str_of_hex_def schedBCall6RecvBytes)) := rfl
theorem schedBCall6RecvStr_eq : (str_of_hex_def schedBCall6RecvBytes) = String.ofList schedBCall6RecvChars := rfl
theorem schedBCall6RecvBytes_eq : schedBCall6RecvBytes = hexBytes.go hexDigit schedBCall6RecvChars := by rw [schedBCall6RecvBytes, schedBCall6Recv_head_eq, eventBytes_recv, schedBCall6RecvStr_eq, hexBytes_ofList]
def schedBCall6RecvFast : HwBytes := hexBytes.go hexDigit schedBCall6RecvChars
theorem wireMacChainOk_b1 : wireMacChainOk wsMacKey wsPrk schedBCall1SendBytes = true := by rw [schedBCall1SendBytes_eq]; decide +kernel
theorem wireMacChainOk_b2 : wireMacChainOk ws3MacKey ws3Prk schedBCall2SendBytes = true := by rw [schedBCall2SendBytes_eq]; decide +kernel
theorem wireMacChainOk_b5 : wireMacChainOk ws5MacKey ws5Prk schedBCall5SendBytes = true := by rw [schedBCall5SendBytes_eq]; decide +kernel
theorem wireMacChainOk_b6 : wireMacChainOk wsMacKey wsPrk schedBCall6RecvBytes = true := by rw [schedBCall6RecvBytes_eq]; decide +kernel
theorem saltAndSeedPin_s1_1 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA₁ : DY.Libsignal.TripleRatchet.TRState) (cl₁ : Nat) {p : PreKeyFields} (hp : parsePreKeyWire schedBCall1SendBytes = some p ∨ parsePreKeyWire schedBCall6RecvBytes = some p) (hmac : gamma compI0 S g (encMac tr₂ stA₁ cl₁ (tr₂.length + 2)) = msgMac8 p) : gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey = wsMacKey ∧ gamma compI0 S g (encPrk tr₂ stA₁ cl₁ (tr₂.length + 2)) = wsPrk ∧ gamma compI0 S g (encSalt tr₂ stA₁ cl₁ (tr₂.length + 2)) = wsSaltA ∧ gamma compI0 S g (encSeed stA₁) = wsSeed1Bytes := saltAndSeedPin_of_macChainOk S g tr₂ stA₁ cl₁ hmac (hp.elim (macChainOk_of_wire wireMacChainOk_b1) (macChainOk_of_wire wireMacChainOk_b6)) wsPrk_pin
theorem saltAndSeedPin_s1_2 (S : Sem) (g : Ghost) (tr₃ : ExecTrace) (stA₁' : DY.Libsignal.TripleRatchet.TRState) (cl₂ : Nat) {p : PreKeyFields} (hp : parsePreKeyWire schedBCall2SendBytes = some p) (hmac : gamma compI0 S g (encMac tr₃ stA₁' cl₂ (tr₃.length + 2)) = msgMac8 p) : gamma compI0 S g (encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).macKey = ws3MacKey ∧ gamma compI0 S g (encPrk tr₃ stA₁' cl₂ (tr₃.length + 2)) = ws3Prk ∧ gamma compI0 S g (encSalt tr₃ stA₁' cl₂ (tr₃.length + 2)) = wsSaltB ∧ gamma compI0 S g (encSeed stA₁') = wsSeed2Bytes := saltAndSeedPin_of_macChainOk S g tr₃ stA₁' cl₂ hmac (macChainOk_of_wire wireMacChainOk_b2 hp) ws3Prk_pin
theorem saltAndSeedPin_s2_1 (S : Sem) (g : Ghost) (tr₅ : ExecTrace) (stA₂ : DY.Libsignal.TripleRatchet.TRState) (cl₅ : Nat) {p : PreKeyFields} (hp : parsePreKeyWire schedBCall5SendBytes = some p) (hmac : gamma compI0 S g (encMac tr₅ stA₂ cl₅ (tr₅.length + 2)) = msgMac8 p) : gamma compI0 S g (encKeys tr₅ stA₂ cl₅ (tr₅.length + 2)).macKey = ws5MacKey ∧ gamma compI0 S g (encPrk tr₅ stA₂ cl₅ (tr₅.length + 2)) = ws5Prk ∧ gamma compI0 S g (encSalt tr₅ stA₂ cl₅ (tr₅.length + 2)) = wsSaltC ∧ gamma compI0 S g (encSeed stA₂) = wsSeed5Bytes := saltAndSeedPin_of_macChainOk S g tr₅ stA₂ cl₅ hmac (macChainOk_of_wire wireMacChainOk_b5 hp) ws5Prk_pin
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins
