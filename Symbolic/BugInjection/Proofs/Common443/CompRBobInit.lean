/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRBobInit
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443.CompRTag (padTail64 sha256Pad_append64 chunks64_append64 sha256With_take4_fold sha256With_length)
abbrev F0 : ShaState → List (BitVec 8) → ShaState := sha256CompressFunction compI0
def tagW : BitVec 32 := 0xd7d7d7d7#32
def Tagged (x : HwBytes) : Prop := x.length = 32 ∧ x.take 4 = compTag4
theorem compI0_sha256' (st blk : HwBytes) : compI0 sha256CompressSymbol [st, blk] = some (compSha256 st blk) := rfl
theorem F0_eq (s : ShaState) (b : List (BitVec 8)) : F0 s b = shaStateOfBytes (compSha256 (shaStateBytes s) b) := by simp only [F0, sha256CompressFunction, compI0_sha256', Option.getD_some]
theorem head_shaStateOfBytes_tag (x : HwBytes) : (shaStateOfBytes (compTag4 ++ x)).head = tagW := by simp only [shaStateOfBytes, List.Vector.head_ofFn]; simp [compTag4, tagW]
theorem shaStateBytes_take4_of_head (s : ShaState) (h : s.head = tagW) : (shaStateBytes s).take 4 = compTag4 := by
  obtain ⟨l, hl⟩ := s
  match l, hl with | w :: ws, _ => simp only [List.Vector.head] at h; subst h; rfl
theorem F0_head_of_state (s : ShaState) (b : List (BitVec 8)) (h : s.head = tagW) : (F0 s b).head = tagW := by
  rw [F0_eq]; have ht := shaStateBytes_take4_of_head s h
  have : compSha256 (shaStateBytes s) b = compDefaultSha256 (shaStateBytes s) b := by unfold compSha256; simp [ht]
  rw [this]; exact head_shaStateOfBytes_tag _
theorem F0_head_of_block (s : ShaState) (b : List (BitVec 8)) (h : b.take 4 = compTag4 ∨ b.take 4 = compTag4Ipad ∨ b.take 4 = compTag4Opad) : (F0 s b).head = tagW := by
  rw [F0_eq]
  have : compSha256 (shaStateBytes s) b = compDefaultSha256 (shaStateBytes s) b := by unfold compSha256; rcases h with h | h | h <;> simp [h]
  rw [this]; exact head_shaStateOfBytes_tag _
theorem foldl_F0_tagged (l : List (List (BitVec 8))) (s : ShaState) (hs : s.head = tagW) : (l.foldl F0 s).head = tagW := by
  induction l generalizing s with
  | nil => exact hs
  | cons b l ih => exact ih _ (F0_head_of_state s b hs)
theorem toBEBytes_tagW : toBEBytes 4 tagW = compTag4 := by decide
theorem sha256With_F0_tagged (m : List (BitVec 8)) (l₁ : List (List (BitVec 8))) (b : List (BitVec 8)) (l₂ : List (List (BitVec 8))) (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) (hb : (F0 (l₁.foldl F0 sha256IV) b).head = tagW) : Tagged (sha256With F0 m) := by refine ⟨sha256With_length F0 m, ?_⟩; rw [sha256With_take4_fold, hsplit, List.foldl_append, List.foldl_cons, foldl_F0_tagged l₂ _ hb, toBEBytes_tagW]
theorem chunks64_sha256Pad_append64 (x m : List (BitVec 8)) (hx : x.length = 64) : chunks64 (sha256Pad (x ++ m)) = [] ++ x :: chunks64 (padTail64 m) := by rw [sha256Pad_append64 x m hx, chunks64_append64 x _ hx]; rfl
theorem padKey_length (k : List (BitVec 8)) (hk : k.length ≤ 64) : (k ++ List.replicate (64 - k.length) 0).length = 64 := by simp; omega
theorem hmacWith_F0_of_key (k m : List (BitVec 8)) (hk : Tagged k) : Tagged (hmacWith F0 k m) := by
  obtain ⟨hl, ht⟩ := hk; have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ite_false]; have hx := padKey_length k (by omega); refine sha256With_F0_tagged _ [] _ _ (chunks64_sha256Pad_append64 _ _ (by simpa using hx)) ?_; refine F0_head_of_block _ _ (Or.inr (Or.inr ?_)); rw [← List.map_take, List.take_append_of_le_length (by omega), ht]; decide
theorem hmacWith_F0_of_inner (k m : List (BitVec 8)) (hinner : Tagged (sha256With F0 (((if 64 < k.length then sha256With F0 k else k) ++ List.replicate (64 - (if 64 < k.length then sha256With F0 k else k).length) 0).map (· ^^^ 0x36) ++ m))) : Tagged (hmacWith F0 k m) := by
  simp only [hmacWith]; set k' := if 64 < k.length then sha256With F0 k else k with hk'
  have hk'l : k'.length ≤ 64 := by rw [hk']; split <;> [rw [sha256With_length]; skip] <;> omega
  have hx : ((k' ++ List.replicate (64 - k'.length) 0).map (· ^^^ (0x5c : BitVec 8))).length = 64 := by simpa using padKey_length k' hk'l
  set inner := sha256With F0 ((k' ++ List.replicate (64 - k'.length) 0).map (· ^^^ 0x36) ++ m)
  obtain ⟨hil, hit⟩ := hinner
  have hsplit : chunks64 (sha256Pad ((k' ++ List.replicate (64 - k'.length) 0).map (· ^^^ (0x5c : BitVec 8)) ++ inner)) =
      [(k' ++ List.replicate (64 - k'.length) 0).map (· ^^^ (0x5c : BitVec 8))] ++ padTail64 inner :: [] := by
    rw [sha256Pad_append64 _ inner hx, chunks64_append64 _ _ hx, CompRTag.chunks64_padTail64_32 inner hil]; rfl
  refine sha256With_F0_tagged _ _ _ _ hsplit (F0_head_of_block _ _ (Or.inl ?_)); rw [CompRTag.padTail64_take4 inner hil, hit]
theorem sha256With_ipad_tagged (x m : List (BitVec 8)) (hx : x.length = 64) (hm : 64 ≤ m.length) (hb : ∀ s, (F0 s (m.take 64)).head = tagW) : Tagged (sha256With F0 (x ++ m)) := by
  set T : List (BitVec 8) := [0x80] ++ List.replicate ((119 - (64 + m.length) % 64) % 64) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + m.length))) with hTdef
  have hT : padTail64 m = m.take 64 ++ (m.drop 64 ++ T) := by rw [← List.append_assoc, List.take_append_drop]; simp only [padTail64, hTdef, List.append_assoc]
  have ht : (m.take 64).length = 64 := by simp; omega
  have hsplit : chunks64 (sha256Pad (x ++ m)) = [x] ++ m.take 64 :: chunks64 (m.drop 64 ++ T) := (by rw [sha256Pad_append64 x m hx, chunks64_append64 x _ hx, hT, chunks64_append64 _ _ ht]; rfl); exact sha256With_F0_tagged _ _ _ _ hsplit (hb _)
theorem hmacKey_length_le (k : List (BitVec 8)) : (if 64 < k.length then sha256With F0 k else k).length ≤ 64 := by split <;> [rw [sha256With_length]; skip] <;> omega
theorem hmacWith_F0_of_msg32 (k m : List (BitVec 8)) (hm : Tagged m) : Tagged (hmacWith F0 k m) := by
  obtain ⟨hl, ht⟩ := hm; refine hmacWith_F0_of_inner k m ?_; have hx := padKey_length _ (hmacKey_length_le k)
  have hx' : ((((if 64 < k.length then sha256With F0 k else k) ++
      List.replicate (64 - (if 64 < k.length then sha256With F0 k else k).length) 0).map (· ^^^ (0x36 : BitVec 8)))).length = 64 := by simpa using hx
  have hsplit := chunks64_sha256Pad_append64 _ m hx'; rw [CompRTag.chunks64_padTail64_32 m hl] at hsplit; refine sha256With_F0_tagged _ [_] (padTail64 m) [] (hsplit.trans rfl) ?_; refine F0_head_of_block _ _ (Or.inl ?_); rw [CompRTag.padTail64_take4 m hl, ht]
def ffDhBlock : List (BitVec 8) := List.replicate 32 0xFF ++ compDefaultDh
theorem compSha256Rows_no_ffDh : (compSha256Rows.all fun r => r.2.1 != bytesToNat ffDhBlock) = true := by decide
theorem F0_head_ffDh (s : ShaState) : (F0 s ffDhBlock).head = tagW := by
  rw [F0_eq]
  have : compSha256 (shaStateBytes s) ffDhBlock = compDefaultSha256 (shaStateBytes s) ffDhBlock := by
    unfold compSha256; generalize hk : bytesToNat ffDhBlock = kb
    split; · rfl
    · split; · dsimp only; split
               · next k1 k2 outNat hfind =>
                 exfalso; have hmem := List.mem_of_find?_eq_some hfind; have hp := List.find?_some hfind; have hall := List.all_eq_true.mp compSha256Rows_no_ffDh _ hmem; simp only [Bool.and_eq_true, beq_iff_eq] at hp; simp only [hk, hp.2, bne_self_eq_false] at hall; exact Bool.false_ne_true hall
               · rfl
      · rfl
  rw [this]; exact head_shaStateOfBytes_tag _
theorem leBytes_length' (n v : Nat) : (leBytes n v).length = n := by induction n generalizing v <;> simp [leBytes, *]
theorem compDefaultDh_length : compDefaultDh.length = 32 := leBytes_length' _ _
theorem hmacWith_F0_of_ffDh (k rest : List (BitVec 8)) : Tagged (hmacWith F0 k (List.replicate 32 0xFF ++ compDefaultDh ++ rest)) := by
  refine hmacWith_F0_of_inner k _ ?_; have hx := padKey_length _ (hmacKey_length_le k)
  have hlen : (List.replicate 32 (0xFF : BitVec 8) ++ compDefaultDh).length = 64 := by simp [compDefaultDh_length]
  refine sha256With_ipad_tagged _ _ (by simpa using hx) (by simp [compDefaultDh_length]) ?_; intro s; rw [List.take_left' hlen]; exact F0_head_ffDh s
section Terms
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (Sem Ghost gamma gamma' gAll gLit0 gConcat0 gKdf0 gTrunc0 ofByteArray)
variable (S : Sem) (g : Ghost)
theorem gamma_concat0 (a b : DY.Bytes) : gamma compI0 S g (DY.Concat.concat a b) = gamma compI0 S g a ++ gamma compI0 S g b := by unfold gamma gamma'; show ((({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _; rw [DY.Bytes.rec_eq gConcat0 (gAll compI0 S g)]; rfl
theorem gamma_hmac0 (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith F0 (gamma compI0 S g k) (gamma compI0 S g m) := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.hmac
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (gKdf0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_trunc80 (x : DY.Bytes) : gamma compI0 S g (DY.Trunc.trunc8 x) = (gamma compI0 S g x).take 8 := by unfold gamma gamma'; show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _; rw [DY.Bytes.rec_eq gTrunc0 (gAll compI0 S g)]; rfl
theorem gamma_lit0 (b : ByteArray) : gamma compI0 S g (DY.Literal.literalToBytes b) = ofByteArray b := by unfold gamma gamma' DY.Literal.literalToBytes; show ((({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _; rw [DY.Bytes.rec_eq gLit0 (gAll compI0 S g)]; rfl
theorem gamma_discontinuity0 : gamma compI0 S g DY.Libsignal.PQXDH.discontinuity = List.replicate 32 0xFF := by unfold DY.Libsignal.PQXDH.discontinuity; rw [gamma_lit0]; decide
def TT (t : DY.Bytes) : Prop := Tagged (gamma compI0 S g t)
variable {S g}
theorem tt_hmac_key (k m : DY.Bytes) (hk : TT S g k) : TT S g (DY.Libsignal.TripleRatchet.hmac k m) := by unfold TT; rw [gamma_hmac0]; exact hmacWith_F0_of_key _ _ hk
theorem tt_hmac_msg (k m : DY.Bytes) (hm : TT S g m) : TT S g (DY.Libsignal.TripleRatchet.hmac k m) := by unfold TT; rw [gamma_hmac0]; exact hmacWith_F0_of_msg32 _ _ hm
theorem tt_hkdfBlock1 (prk info : DY.Bytes) (hp : TT S g prk) : TT S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := tt_hmac_key _ _ hp
theorem tt_hkdfBlock2 (prk info : DY.Bytes) (hp : TT S g prk) : TT S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := tt_hmac_key _ _ hp
theorem tt_createChain_snd (rk theirPk ourSk : DY.Bytes) (h : TT S g rk) : TT S g (DY.Libsignal.TripleRatchet.createChain rk theirPk ourSk).2 := tt_hkdfBlock2 _ _ (tt_hmac_key _ _ h)
theorem tt_kdfCk_snd (ck : DY.Bytes) (h : TT S g ck) : TT S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := tt_hmac_key _ _ h
theorem tt_trMsgKeys_macKey (salt seed : DY.Bytes) (h : TT S g seed) : TT S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey := tt_hkdfBlock2 _ _ (tt_hmac_msg _ _ h)
theorem computeMac_take4 (mk sIk rIk wire : DY.Bytes) (h : TT S g mk) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk sIk rIk wire)).take 4 = compTag4 := by unfold DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc80, List.take_take, show min 4 8 = 4 from rfl]; exact (tt_hmac_key _ _ h).2
theorem tt_pqxdhKdf_rk (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes) (h1 : gamma compI0 S g dh1 = compDefaultDh) : TT S g (DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 ss)).rk := by unfold DY.Libsignal.PQXDH.pqxdhKdf; refine tt_hkdfBlock1 _ _ ?_; unfold TT DY.Libsignal.PQXDH.pqxdhIkm; rw [gamma_hmac0, gamma_concat0, gamma_concat0, gamma_discontinuity0, h1, ← List.append_assoc]; exact hmacWith_F0_of_ffDh _ _
theorem tt_aliceStart_macKey (ikA ek ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) (e dhsA salt : DY.Bytes) (h1 : gamma compI0 S g (DY.Libsignal.PQXDH.agree spkPk ikA) = compDefaultDh) : TT S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2.rk spkPk dhsA).2).2).macKey := by refine tt_trMsgKeys_macKey _ _ (tt_kdfCk_snd _ (tt_createChain_snd _ _ _ ?_)); unfold DY.Libsignal.PQXDH.aliceAgreement; generalize DY.PQKem.kemEncap pqPk e = p; obtain ⟨ct, ss⟩ := p; exact tt_pqxdhKdf_rk _ _ _ _ _ h1
end Terms
theorem compDhByIdx_34 (i j : Fin 12) (hij : (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3)) : compDhByIdx i j = compDefaultDh := by obtain ⟨hi, hj⟩ | ⟨hi, hj⟩ := hij <;> { unfold compDhByIdx; simp [hi, hj] }
theorem compLookupDh_34 (s p : HwBytes) (i j : Fin 12) (hs : compSecretIdx s = some i) (hp : compPointIdx p = some j) (hlow : DY.X25519.isLowOrderKey (p.map BitVec.toNat) = false) (hij : (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3)) : compLookupDh s p = compDefaultDh := by unfold compLookupDh; rw [hlow, hs, hp]; exact compDhByIdx_34 i j hij
theorem compI0_agreement (s p : HwBytes) : compI0 DY.Libsignal.Refinement.x25519AgreementSymbol [s, p] = some (compLookupDh s p) := rfl
theorem compI0_agreement_34 (s p : HwBytes) (i j : Fin 12) (hs : compSecretIdx s = some i) (hp : compPointIdx p = some j) (hlow : DY.X25519.isLowOrderKey (p.map BitVec.toNat) = false) (hij : (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3)) : (compI0 DY.Libsignal.Refinement.x25519AgreementSymbol [s, p]).getD [] = compDefaultDh := by rw [compI0_agreement, compLookupDh_34 s p i j hs hp hlow hij]; rfl
def hasTag4 : List (BitVec 8) → Bool
  | [] => false
  | x :: rest =>
    (match x :: rest with | a :: b :: c :: d :: _ => a == 0xd7#8 && b == 0xd7#8 && c == 0xd7#8 && d == 0xd7#8 | _ => false) || hasTag4 rest
theorem hasTag4_of_prefix (t : List (BitVec 8)) : hasTag4 (compTag4 ++ t) = true := by simp [compTag4, hasTag4]
theorem hasTag4_append_left (l t : List (BitVec 8)) (h : hasTag4 t = true) : hasTag4 (l ++ t) = true := by
  induction l with
  | nil => exact h
  | cons x l ih => simp only [List.cons_append, hasTag4, ih, Bool.or_true]
theorem hasTag4_of_infix (w : List (BitVec 8)) (h : compTag4 <:+: w) : hasTag4 w = true := by obtain ⟨s, t, rfl⟩ := h; rw [List.append_assoc]; exact hasTag4_append_left s _ (hasTag4_of_prefix t)
section InfixNav
variable {α : Type} {l : List α}
private theorem inf_cons {m : List α} (a : α) (h : l <:+: m) : l <:+: a :: m := by obtain ⟨s, t, rfl⟩ := h; exact ⟨a :: s, t, by simp⟩
private theorem inf_right {b : List α} (a : List α) (h : l <:+: b) : l <:+: a ++ b := by obtain ⟨s, t, rfl⟩ := h; exact ⟨a ++ s, t, by simp⟩
private theorem inf_left {a : List α} (b : List α) (h : l <:+: a) : l <:+: a ++ b := by obtain ⟨s, t, rfl⟩ := h; exact ⟨s, t ++ b, by simp⟩
end InfixNav
theorem infix_preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes) : msg <:+: DY.Libsignal.Composed.Refinement.preKeyWire preKeyId spkId kpkId regId ik ek ct msg := by
  unfold DY.Libsignal.Composed.Refinement.preKeyWire DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode; simp only [CryptoVerification.LibsignalProtoCodec.encodeBytesField, List.append_assoc]
  repeat (first | exact inf_left _ (List.infix_refl _) | exact List.infix_refl _ | apply inf_cons | apply inf_right)
variable {S : DY.Libsignal.Composed.Refinement.Sem} {g : DY.Libsignal.Composed.Refinement.Ghost}
theorem not_sendMatches_of_tagged (r : DY.Libsignal.Composed.Refinement.Records) (b : HwBytes) (ek ct wire mac : DY.Bytes) (hmac : (DY.Libsignal.Composed.Refinement.gamma compI0 S g mac).take 4 = compTag4) (hb : hasTag4 b = false) : ¬ Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.SendMatchesMoves compI0 r S g b [ek, ct, DY.Concat.concat wire mac] := by rintro ⟨_, preKeyId, spkId, kpkId, _, rfl⟩; refine absurd (hasTag4_of_infix _ ?_) (by rw [hb]; decide); refine List.IsInfix.trans ?_ (infix_preKeyWire _ _ _ _ _ _ _ _); rw [gamma_concat0]; refine ⟨DY.Libsignal.Composed.Refinement.gamma compI0 S g wire, (DY.Libsignal.Composed.Refinement.gamma compI0 S g mac).drop 4, ?_⟩; rw [← hmac, List.append_assoc, List.take_append_drop]
theorem compPubOfIdx3_facts : compPointIdx (compPubOfIdx ⟨3, by decide⟩) = some ⟨3, by decide⟩ ∧ DY.X25519.isLowOrderKey ((compPubOfIdx ⟨3, by decide⟩).map BitVec.toNat) = false := by decide
section Compose
open scoped DY.Libsignal.Composed
theorem gamma_agree_bobSelf (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0) (spkPk ikA : DY.Bytes) (hsk : compSecretIdx (DY.Libsignal.Composed.Refinement.clamp (DY.Libsignal.Composed.Refinement.gamma compI0 S g ikA)) = some ⟨4, by decide⟩) (hpk : DY.Libsignal.Composed.Refinement.gamma compI0 S g spkPk = compPubOfIdx ⟨3, by decide⟩) : DY.Libsignal.Composed.Refinement.gamma compI0 S g (DY.Libsignal.PQXDH.agree spkPk ikA) = compDefaultDh := by rw [Symbolic.BugInjection.Proofs.Common443.CompRGamma.gamma_agree compI0 hEq, hpk]; exact compI0_agreement_34 _ _ _ _ hsk compPubOfIdx3_facts.1 compPubOfIdx3_facts.2 (Or.inr ⟨rfl, rfl⟩)
end Compose
end Symbolic.BugInjection.Proofs.Common443.CompRBobInit
