/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes torsionShift)
def IsSetupFresh64Tag (t : Nat) : Prop := t = 11 ∨ t = 16 ∨ t = 17
theorem fillFresh_length (t n : Nat) (hn : 0 < n) : (fillFresh t n).length = n := by simp [fillFresh]; omega
theorem fillFresh64_length (t : Nat) : (fillFresh t 64).length = 64 := rfl
theorem fillFresh64_take32 (t : Nat) : (fillFresh t 64).take 32 = fillFresh t 32 := rfl
theorem fillFresh64_head? (t : Nat) : (fillFresh t 64).head? = some (BitVec.ofNat 8 t) := rfl
theorem ne_fillFresh64_of_length_ne {bs : HwBytes} {t : Nat} (h : bs.length ≠ 64) : bs ≠ fillFresh t 64 := fun heq => h (heq ▸ rfl)
theorem ne_fillFresh64_of_head?_ne {bs : HwBytes} {t : Nat} {b : BitVec 8} (hb : bs.head? = some b) (hne : b ≠ BitVec.ofNat 8 t) : bs ≠ fillFresh t 64 := by intro heq; rw [heq, fillFresh64_head?, Option.some.injEq] at hb; exact hne hb.symm
theorem append_ne_fillFresh64_of_left32 {a b : HwBytes} {t : Nat} (ha_len : a.length = 32) (ha_ne : a ≠ fillFresh t 32) : a ++ b ≠ fillFresh t 64 :=
  fun heq => ha_ne (by have h := congrArg (List.take 32) heq; rwa [List.take_left' ha_len, fillFresh64_take32] at h)
theorem compLookupPub_ne_fillFresh32 (s : HwBytes) {t : Nat} (ht : IsSetupFresh64Tag t) : compLookupPub s ≠ fillFresh t 32 := by unfold compLookupPub; rcases ht with rfl | rfl | rfl <;> (cases compSecretIdx s with | none => decide | some i => revert i; decide)
private theorem compDhByIdx_ne_11 : ∀ i j : Fin 12, compDhByIdx i j ≠ fillFresh 11 32 := by decide
private theorem compDhByIdx_ne_16 : ∀ i j : Fin 12, compDhByIdx i j ≠ fillFresh 16 32 := by decide
private theorem compDhByIdx_ne_17 : ∀ i j : Fin 12, compDhByIdx i j ≠ fillFresh 17 32 := by decide
theorem compLookupDh_ne_fillFresh32 (s p : HwBytes) {t : Nat} (ht : IsSetupFresh64Tag t) : compLookupDh s p ≠ fillFresh t 32 := by
  have hd : compDefaultDh ≠ fillFresh t 32 := by rcases ht with rfl | rfl | rfl <;> decide
  unfold compLookupDh; split
  · rcases ht with rfl | rfl | rfl <;> decide
  · cases compSecretIdx s <;> cases compPointIdx p
    · exact hd
    · exact hd
    · exact hd
    · rcases ht with rfl | rfl | rfl
      exacts [compDhByIdx_ne_11 _ _, compDhByIdx_ne_16 _ _, compDhByIdx_ne_17 _ _]
theorem compI0_sha256Compress (st blk : HwBytes) : compI0 DY.Libsignal.Refinement.sha256CompressSymbol [st, blk] = some (compSha256 st blk) := rfl
theorem sha256CompressFunction_compI0_head (st : ShaState) (blk : HwBytes) : (sha256CompressFunction compI0 st blk).head = (shaStateOfBytes ((compSha256 (shaStateBytes st) blk).take 4)).head := by
  have h4 : ∀ b : HwBytes, (shaStateOfBytes b).head = (shaStateOfBytes (b.take 4)).head := by intro b; rcases b with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  unfold sha256CompressFunction; rw [compI0_sha256Compress, Option.getD_some, h4]
private theorem compDefaultSha256_take4 (st blk : HwBytes) : (compDefaultSha256 st blk).take 4 = compTag4 := rfl
private theorem compSha256Rows_head_be_not_zero_or_fresh : (compSha256Rows.all fun r => let b4 := toBEBytes 4 (shaStateOfBytes (DY.Libsignal.Composed.Refinement.leBytes 4 r.2.2)).head; b4 != [0#8, 0#8, 0#8, 0#8] && b4 != [11#8, 0#8, 0#8, 0#8] && b4 != [16#8, 0#8, 0#8, 0#8] && b4 != [17#8, 0#8, 0#8, 0#8]) = true := by decide
private theorem compTag4_head_be : toBEBytes 4 (shaStateOfBytes compTag4).head = [0xd7#8, 0xd7#8, 0xd7#8, 0xd7#8] := by decide
theorem compSha256_head_be_ne_zero4 (st blk : HwBytes) : toBEBytes 4 (shaStateOfBytes ((compSha256 st blk).take 4)).head ≠ [0#8, 0#8, 0#8, 0#8] := by
  have hdef : toBEBytes 4 (shaStateOfBytes ((compDefaultSha256 st blk).take 4)).head ≠ [0#8, 0#8, 0#8, 0#8] := (by rw [compDefaultSha256_take4, compTag4_head_be]; decide); unfold compSha256; split
  · exact hdef
  · split
    · dsimp only; split
      · next _ _ _ hfind =>
        have hall := List.all_eq_true.mp compSha256Rows_head_be_not_zero_or_fresh _ (List.mem_of_find?_eq_some hfind); dsimp only at hall; change toBEBytes 4 (shaStateOfBytes (leBytes 4 _)).head ≠ _; intro heq; rw [heq] at hall; revert hall; decide
      · exact hdef
    · exact hdef
theorem compSha256_head_be_ne_fresh4 (st blk : HwBytes) {t : Nat} (ht : IsSetupFresh64Tag t) : toBEBytes 4 (shaStateOfBytes ((compSha256 st blk).take 4)).head ≠ [BitVec.ofNat 8 t, 0#8, 0#8, 0#8] := by
  have hdef : toBEBytes 4 (shaStateOfBytes ((compDefaultSha256 st blk).take 4)).head ≠
      [BitVec.ofNat 8 t, 0#8, 0#8, 0#8] := by
    rw [compDefaultSha256_take4, compTag4_head_be]; rcases ht with rfl | rfl | rfl <;> decide
  unfold compSha256; split
  · exact hdef
  · split
    · dsimp only; split
      · next _ _ _ hfind =>
        have hall := List.all_eq_true.mp compSha256Rows_head_be_not_zero_or_fresh _ (List.mem_of_find?_eq_some hfind); dsimp only at hall; change toBEBytes 4 (shaStateOfBytes (leBytes 4 _)).head ≠ _
        intro heq; rw [heq] at hall; rcases ht with rfl | rfl | rfl <;> (revert hall; decide)
      · exact hdef
    · exact hdef
theorem hmacWith_length (F : ShaState → HwBytes → ShaState) (k m : HwBytes) : (hmacWith F k m).length = 32 := sha256With_length F _
theorem hmacWith_compI0_ne_zero32 (k m : HwBytes) : hmacWith (sha256CompressFunction compI0) k m ≠ List.replicate 32 0#8 := fun heq =>
  compSha256_head_be_ne_zero4 _ _ (by
    rw [← sha256CompressFunction_compI0_head, ← sha256With_take4]; exact congrArg (List.take 4) heq)
theorem hmacWith_compI0_ne_fillFresh32 (k m : HwBytes) {t : Nat} (ht : IsSetupFresh64Tag t) : hmacWith (sha256CompressFunction compI0) k m ≠ fillFresh t 32 := fun heq =>
  compSha256_head_be_ne_fresh4 _ _ ht (by
    rw [← sha256CompressFunction_compI0_head, ← sha256With_take4]; exact congrArg (List.take 4) heq)
theorem gamma_lit (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) : gamma i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) = ofByteArray b := by unfold gamma gamma'; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]; rfl
theorem gamma_concat_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (a b : DY.Bytes) : gamma i S g (DY.Concat.concat a b) = gamma i S g a ++ gamma i S g b := by
  unfold gamma gamma'
  show ((({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl
theorem gamma_dhPk_compI0 (S : Sem) (g : Ghost) (sk : DY.Bytes) : gamma compI0 S g (DY.DiffieHellman.dhPk sk) = compLookupPub (clamp (gamma compI0 S g sk)) := by
  unfold gamma gamma'
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)]; rfl
theorem gamma_dh_pack_compI0 (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : gamma compI0 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) = compLookupDh (clamp (gamma compI0 S g sk)) (gamma compI0 S g pk) := by unfold gamma gamma'; rw [DY.Bytes.rec_eq (gDh compI0) (gAll compI0 S g)]; rfl
theorem gamma_hmac_compI0 (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith (sha256CompressFunction compI0) (gamma compI0 S g k) (gamma compI0 S g m) := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.hmac
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gKdf0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_symEnc_compI0 (S : Sem) (g : Ghost) (k iv m : DY.Bytes) : gamma compI0 S g (DY.SymEnc.symEnc k iv m) = compAesPerm (gamma compI0 S g k) ((gamma compI0 S g iv).take 16) (gamma compI0 S g m) := by
  unfold gamma gamma'
  show ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_trunc8_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (a : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 a) = (gamma i S g a).take 8 := by
  unfold gamma gamma'
  show ((({input := a} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl
theorem gamma_variant_pack (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : DY.Bytes) (v : Fin 4) (t : Fin 8) : gamma i S g (({ key := k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack) = variantBytes (torsionShift i (gamma i S g k) t) v := by unfold gamma gamma'; rw [DY.Bytes.rec_eq (gVariant0 i) (gAll i S g)]; rfl
theorem gamma_trWire_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) : gamma i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) = trWireBytes (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev)) ev { version := v.toNat, ratchetKey := gamma i S g rk, counter := c.toNat, previousCounter := pc.toNat, ciphertext := gamma i S g ct } (gamma i S g pq) := by unfold gamma gamma'; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; rfl
private theorem compLookupDh_length_eq (s p : HwBytes) : (compLookupDh s p).length = 32 := by
  have hd : ∀ i j : Fin 12, (compDhByIdx i j).length = 32 := by decide
  unfold compLookupDh; split
  · simp
  · cases compSecretIdx s <;> cases compPointIdx p <;> simp [hd, show compDefaultDh.length = 32 from rfl]
theorem gamma_dhPk_length (S : Sem) (g : Ghost) (sk : DY.Bytes) : (gamma compI0 S g (DY.DiffieHellman.dhPk sk)).length = 32 := by
  rw [gamma_dhPk_compI0]; unfold compLookupPub
  cases compSecretIdx (clamp (gamma compI0 S g sk)) with | none => decide | some i => revert i; decide
theorem gamma_dh_pack_length (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : (gamma compI0 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).length = 32 := by rw [gamma_dh_pack_compI0, compLookupDh_length_eq]
theorem gamma_dh_length (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : (gamma compI0 S g (DY.DiffieHellman.dh pk sk)).length = 32 := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, DY.DiffieHellman.instCanDHBytes]
  split <;> [split <;> exact gamma_dh_pack_length S g _ _; exact gamma_dh_pack_length S g _ _]
theorem gamma_dh_ne_fillFresh32 (S : Sem) (g : Ghost) (pk sk : DY.Bytes) {t : Nat} (ht : IsSetupFresh64Tag t) : gamma compI0 S g (DY.DiffieHellman.dh pk sk) ≠ fillFresh t 32 := by
  have hp : ∀ pk' sk', gamma compI0 S g (({ pk := pk', sk := sk' } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ≠ fillFresh t 32 :=
    fun pk' sk' => by rw [gamma_dh_pack_compI0]; exact compLookupDh_ne_fillFresh32 _ _ ht
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, DY.DiffieHellman.instCanDHBytes]
  split <;> [split <;> exact hp _ _; exact hp _ _]
theorem gamma_hmac_length (S : Sem) (g : Ghost) (k m : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by rw [gamma_hmac_compI0, hmacWith_length]
theorem gamma_hmac_ne_zero32 (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) ≠ List.replicate 32 0#8 := by rw [gamma_hmac_compI0]; exact hmacWith_compI0_ne_zero32 _ _
theorem compAesPerm_ne_fillFresh64 (k iv text : HwBytes) {t : Nat} (_ht : IsSetupFresh64Tag t) : compAesPerm k iv text ≠ fillFresh t 64 :=
  CompI0Laws.compAesPerm_ne_fillFresh64 k iv text t
theorem gamma_concat_dhPk_left_ne_fillFresh64 (S : Sem) (g : Ghost) (sk b : DY.Bytes) {t : Nat} (ht : IsSetupFresh64Tag t) : gamma compI0 S g (DY.Concat.concat (DY.DiffieHellman.dhPk sk) b) ≠ fillFresh t 64 := by
  rw [gamma_concat_eq]
  exact append_ne_fillFresh64_of_left32 (gamma_dhPk_length S g sk)
    (by rw [gamma_dhPk_compI0]; exact compLookupPub_ne_fillFresh32 _ ht)
theorem gamma_concat_dh_left_ne_fillFresh64 (S : Sem) (g : Ghost) (pk sk b : DY.Bytes) {t : Nat} (ht : IsSetupFresh64Tag t) : gamma compI0 S g (DY.Concat.concat (DY.DiffieHellman.dh pk sk) b) ≠ fillFresh t 64 := by rw [gamma_concat_eq]; exact append_ne_fillFresh64_of_left32 (gamma_dh_length S g pk sk) (gamma_dh_ne_fillFresh32 S g pk sk ht)
theorem gamma_concat_hmac_left_ne_fillFresh64 (S : Sem) (g : Ghost) (k m b : DY.Bytes) {t : Nat} (ht : IsSetupFresh64Tag t) : gamma compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.hmac k m) b) ≠ fillFresh t 64 := by
  rw [gamma_concat_eq]
  exact append_ne_fillFresh64_of_left32 (gamma_hmac_length S g k m)
    (by rw [gamma_hmac_compI0]; exact hmacWith_compI0_ne_fillFresh32 _ _ ht)
theorem gamma_concat_head?_ne_fillFresh64 (i : ExternInterpretation) (S : Sem) (g : Ghost) {a b : DY.Bytes} {b0 : BitVec 8} {t : Nat} (ha : (gamma i S g a).head? = some b0) (hne : b0 ≠ BitVec.ofNat 8 t) : gamma i S g (DY.Concat.concat a b) ≠ fillFresh t 64 := by
  refine ne_fillFresh64_of_head?_ne ?_ hne; rw [gamma_concat_eq]
  cases h : gamma i S g a with
  | nil => rw [h] at ha; cases ha
  | cons x xs => rw [h, List.head?_cons, Option.some.injEq] at ha; subst ha; rfl
theorem mem_setupFresh64_iff {t : Nat} : t ∈ ([11, 16, 17] : List Nat) ↔ IsSetupFresh64Tag t := by simp [IsSetupFresh64Tag]
def FreshSafeTerm (i : ExternInterpretation) (S : Sem) (g : Ghost) (u : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g u).memo, ∀ t ∈ ([11, 16, 17] : List Nat), x.2.2 = fillFresh t 64 → x.1 = randTerm t 64 ∧ x.2.1 = randTerm t 64
theorem freshSafeTerm_of_node {i : ExternInterpretation} {S : Sem} {g : Ghost} {self : DY.Bytes} {ts : List DY.Bytes} (hγ : (gamma' i S g self).memo = (self, (gamma' i S g self).shape, (gamma' i S g self).bytes) :: (ts.map (gamma' i S g)).flatMap (·.memo)) (hself : ∀ t, IsSetupFresh64Tag t → gamma i S g self ≠ fillFresh t 64) (hts : ∀ u ∈ ts, FreshSafeTerm i S g u) : FreshSafeTerm i S g self := by
  intro x hx t ht hval; rw [hγ] at hx
  rcases List.mem_cons.mp hx with rfl | hcs
  · exact False.elim (hself t (mem_setupFresh64_iff.mp ht) hval)
  · obtain ⟨c, hc, hx_c⟩ := List.mem_flatMap.mp hcs; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hts u hu x hx_c t ht hval
theorem freshSafeTerm_of_opaqueNode {i : ExternInterpretation} {S : Sem} {g : Ghost} {self : DY.Bytes} {ts : List DY.Bytes} (hγ : (gamma' i S g self).memo = (ts.map (gamma' i S g)).flatMap (·.memo)) (hts : ∀ u ∈ ts, FreshSafeTerm i S g u) : FreshSafeTerm i S g self := by intro x hx t ht hval; rw [hγ] at hx; obtain ⟨c, hc, hx_c⟩ := List.mem_flatMap.mp hx; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hts u hu x hx_c t ht hval
theorem freshSafeTerm_randTerm_of_ne_fillFresh64 (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (hne : ∀ t ∈ ([11, 16, 17] : List Nat), g.σ ts sz ≠ fillFresh t 64) : FreshSafeTerm i S g (randTerm ts sz) := by
  intro x hx t ht hval; unfold gamma' randTerm at hx; change x ∈ ((({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).memo at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx
  by_cases hsz : sz = 0
  · simp [gRandom, concretizeRandom, hsz] at hx
  · simp only [gRandom, concretizeRandom, hsz, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx; subst hx; exact False.elim (hne t ht hval)
theorem freshSafeTerm_randTerm_of_ne_64 (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (hlen : (g.σ ts sz).length ≠ 64) : FreshSafeTerm i S g (randTerm ts sz) :=
  freshSafeTerm_randTerm_of_ne_fillFresh64 i S g ts sz (fun _ _ => ne_fillFresh64_of_length_ne hlen)
theorem freshSafeTerm_randTerm_64_setup (i : ExternInterpretation) (S : Sem) (g : Ghost) {ts : Nat} (hts : ts ∈ ([11, 16, 17] : List Nat)) (hσ : g.σ ts 64 = fillFresh ts 64) : FreshSafeTerm i S g (randTerm ts 64) := by
  intro x hx t ht hval; unfold gamma' randTerm at hx; change x ∈ ((({ timestamp := ts, size := 64 } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).memo at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; simp only [gRandom, concretizeRandom, show (64 : Nat) ≠ 0 by decide, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx; subst hx; dsimp only at hval ⊢; rw [hσ] at hval; have hhead : (fillFresh ts 64).head? = (fillFresh t 64).head? := congrArg List.head? hval; rw [fillFresh64_head?, fillFresh64_head?, Option.some.injEq] at hhead
  have hts_eq : ts = t := by rcases mem_setupFresh64_iff.mp hts with rfl | rfl | rfl <;> rcases mem_setupFresh64_iff.mp ht with rfl | rfl | rfl <;> first | rfl | (revert hhead; decide)
  subst hts_eq; exact ⟨rfl, rfl⟩
theorem freshSafeTerm_lit_of_ne_fillFresh64 (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) (hne : ∀ t, IsSetupFresh64Tag t → ofByteArray b ≠ fillFresh t 64) : FreshSafeTerm i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) := by refine freshSafeTerm_of_node (ts := []) ?_ (fun t ht => by rw [gamma_lit]; exact hne t ht) (fun _ h => by cases h); unfold gamma'; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]; rfl
theorem freshSafeTerm_concat {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} (hself : ∀ t, IsSetupFresh64Tag t → gamma i S g (DY.Concat.concat a b) ≠ fillFresh t 64) (ha : FreshSafeTerm i S g a) (hb : FreshSafeTerm i S g b) : FreshSafeTerm i S g (DY.Concat.concat a b) := by
  refine freshSafeTerm_of_node (ts := [a, b]) ?_ hself (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => List.mem_singleton.mp h ▸ hb))
  unfold gamma'; change ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).memo = (({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack, ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).shape, ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _; rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl
theorem freshSafeTerm_dhPk {S : Sem} {g : Ghost} {sk : DY.Bytes} (hsk : FreshSafeTerm compI0 S g sk) : FreshSafeTerm compI0 S g (DY.DiffieHellman.dhPk sk) := by refine freshSafeTerm_of_node (ts := [sk]) ?_ (fun t _ => ne_fillFresh64_of_length_ne (by rw [gamma_dhPk_length]; decide)) (fun _ hu => List.mem_singleton.mp hu ▸ hsk); unfold gamma'; change ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g)).memo = (({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g)).shape, ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes) :: _; rw [DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)]; rfl
theorem freshSafeTerm_dh_pack {S : Sem} {g : Ghost} {pk sk : DY.Bytes} (hpk : FreshSafeTerm compI0 S g pk) (hsk : FreshSafeTerm compI0 S g sk) : FreshSafeTerm compI0 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  refine freshSafeTerm_of_node (ts := [pk, sk]) ?_ (fun t _ => ne_fillFresh64_of_length_ne (by rw [gamma_dh_pack_length]; decide)) (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ hsk))
  unfold gamma'; rw [DY.Bytes.rec_eq (gDh compI0) (gAll compI0 S g)]; rfl
theorem freshSafeTerm_dh {S : Sem} {g : Ghost} {pk sk : DY.Bytes} (hpk : FreshSafeTerm compI0 S g pk) (hsk : FreshSafeTerm compI0 S g sk) : FreshSafeTerm compI0 S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    have hsk2 : FreshSafeTerm compI0 S g sk2 := fun x hx t ht hval => by
      refine hpk x ?_ t ht hval; unfold gamma' at hx ⊢
      show x ∈ (((({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g))).memo
      rw [DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)]; exact List.mem_cons_of_mem _ (by simpa [node] using hx)
    split <;> [exact freshSafeTerm_dh_pack hpk hsk; exact freshSafeTerm_dh_pack (freshSafeTerm_dhPk hsk) hsk2]
  · exact freshSafeTerm_dh_pack hpk hsk
theorem freshSafeTerm_hmac {S : Sem} {g : Ghost} {k m : DY.Bytes} (hk : FreshSafeTerm compI0 S g k) (hm : FreshSafeTerm compI0 S g m) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) := by
  refine freshSafeTerm_of_node (ts := [k, m]) ?_ (fun t _ => ne_fillFresh64_of_length_ne (by rw [gamma_hmac_length]; decide)) (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hk) (fun h => List.mem_singleton.mp h ▸ hm))
  unfold gamma' DY.Libsignal.TripleRatchet.hmac; change ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).memo = (({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack, ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).shape, ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes) :: _; rw [DY.Bytes.rec_eq (gKdf0 compI0) (gAll compI0 S g)]; rfl
theorem freshSafeTerm_trunc8 {i : ExternInterpretation} {S : Sem} {g : Ghost} {a : DY.Bytes} (ha : FreshSafeTerm i S g a) : FreshSafeTerm i S g (DY.Trunc.trunc8 a) := by refine freshSafeTerm_of_node (ts := [a]) ?_ (fun t _ => ne_fillFresh64_of_length_ne (by rw [gamma_trunc8_eq]; have := List.length_take_le 8 (gamma i S g a); omega)) (fun _ hu => List.mem_singleton.mp hu ▸ ha); unfold gamma'; change ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).memo = (({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack, ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).shape, ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _; rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl
theorem freshSafeTerm_symEnc {S : Sem} {g : Ghost} {k iv m : DY.Bytes} (_hm_len : (gamma compI0 S g m).length ≠ 64) (hk : FreshSafeTerm compI0 S g k) (hiv : FreshSafeTerm compI0 S g iv) (hm : FreshSafeTerm compI0 S g m) : FreshSafeTerm compI0 S g (DY.SymEnc.symEnc k iv m) := by
  refine freshSafeTerm_of_node (ts := [k, iv, m]) ?_ (fun t ht => by rw [gamma_symEnc_compI0]; exact compAesPerm_ne_fillFresh64 _ _ _ ht)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hk) (fun h => (List.mem_cons.mp h).elim (· ▸ hiv) (fun h => List.mem_singleton.mp h ▸ hm)))
  unfold gamma'; change ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll compI0 S g)).memo = (({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack, ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll compI0 S g)).shape, ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes) :: _; rw [DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)]; rfl
theorem freshSafeTerm_kemPk {i : ExternInterpretation} {S : Sem} {g : Ghost} {sk : DY.Bytes} (hsk : FreshSafeTerm i S g sk) : FreshSafeTerm i S g (DY.PQKem.kemPk sk) := by refine freshSafeTerm_of_opaqueNode (ts := [sk]) ?_ (fun _ hu => List.mem_singleton.mp hu ▸ hsk); unfold gamma'; show (((({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _; rw [DY.Bytes.rec_eq (gKemPk S) (gAll i S g)]; rfl
private theorem compKyberEncaps_len (e : HwBytes) : (compKyberEncaps e).length = 1600 := by
  have hlen : ∀ n v, (DY.Libsignal.Composed.Refinement.leBytes n v).length = n := by intro n v; induction n generalizing v with | zero => rfl | succ n ih => simp [DY.Libsignal.Composed.Refinement.leBytes, ih]
  unfold compKyberEncaps compKyberCt0 compKyberCt1 compKyberCt2 compKyberSs0 compKyberSs1 compKyberSs2 compDefaultKyberCt compDefaultKyberSs
  repeat (first | simp only [List.length_append, hlen 1568, hlen 32, List.length_replicate] | split)
private theorem compI0_kyberEncaps_eq (pk e : HwBytes) : compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [pk, e] = some (compKyberEncaps e) := rfl
theorem freshSafeTerm_kemEncap_fst {S : Sem} {g : Ghost} {pk e : DY.Bytes} (hpk : FreshSafeTerm compI0 S g pk) (he : FreshSafeTerm compI0 S g e) : FreshSafeTerm compI0 S g (DY.PQKem.kemEncap pk e).1 := by
  by_cases helen : (gamma' compI0 S g e).bytes.length = 32
  · refine freshSafeTerm_of_node (ts := [pk, e]) ?_ (fun t _ => ?_) (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ he))
    · unfold gamma' at helen ⊢; change (((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll compI0 S g))).memo = (({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack, ((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll compI0 S g)).shape, ((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes) :: _; rw [DY.Bytes.rec_eq (gKemEncap compI0) (gAll compI0 S g)]; simp only [gKemEncap, concretizeKemEncap, gAll, helen, ↓reduceIte]; rfl
    · apply ne_fillFresh64_of_length_ne; unfold gamma; unfold gamma' at helen ⊢
      show (((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll compI0 S g))).bytes.length ≠ 64
      rw [DY.Bytes.rec_eq (gKemEncap compI0) (gAll compI0 S g)]; simp only [gKemEncap, concretizeKemEncap, gAll, helen, ↓reduceIte, node, compI0_kyberEncaps_eq, Option.getD_some, List.length_take, compKyberEncaps_len]; decide
  · refine freshSafeTerm_of_opaqueNode (ts := [pk, e]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ he))
    unfold gamma' at helen ⊢; show (((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll compI0 S g))).memo = _; rw [DY.Bytes.rec_eq (gKemEncap compI0) (gAll compI0 S g)]; simp only [gKemEncap, concretizeKemEncap, gAll, helen, ↓reduceIte]; rfl
theorem freshSafeTerm_kemEncap_snd {S : Sem} {g : Ghost} {pk e : DY.Bytes} (hpk : FreshSafeTerm compI0 S g pk) (he : FreshSafeTerm compI0 S g e) : FreshSafeTerm compI0 S g (DY.PQKem.kemEncap pk e).2 := by
  by_cases helen : (gamma' compI0 S g e).bytes.length = 32
  · refine freshSafeTerm_of_node (ts := [pk, e]) ?_ (fun t _ => ?_) (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ he))
    · unfold gamma' at helen ⊢; change (((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g))).memo = (({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack, ((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g)).shape, ((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes) :: _; rw [DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)]; simp only [gKemSS, concretizeKemSS, gAll, helen, ↓reduceIte]; rfl
    · apply ne_fillFresh64_of_length_ne; unfold gamma; unfold gamma' at helen ⊢
      show (((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g))).bytes.length ≠ 64
      rw [DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)]; simp only [gKemSS, concretizeKemSS, gAll, helen, ↓reduceIte, node, compI0_kyberEncaps_eq, Option.getD_some, List.length_drop, compKyberEncaps_len]; decide
  · refine freshSafeTerm_of_opaqueNode (ts := [pk, e]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ he))
    unfold gamma' at helen ⊢; show (((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g))).memo = _; rw [DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)]; simp only [gKemSS, concretizeKemSS, gAll, helen, ↓reduceIte]; rfl
theorem freshSafeTerm_vk {i : ExternInterpretation} {S : Sem} {g : Ghost} {sk : DY.Bytes} (hsk : FreshSafeTerm i S g sk) : FreshSafeTerm i S g (DY.Signature.vk sk) := by refine freshSafeTerm_of_opaqueNode (ts := [sk]) ?_ (fun _ hu => List.mem_singleton.mp hu ▸ hsk); unfold gamma'; show (((({ sk := sk } : DY.Signature.Vk.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _; rw [DY.Bytes.rec_eq (gVk S) (gAll i S g)]; rfl
theorem freshSafeTerm_sign {i : ExternInterpretation} {S : Sem} {g : Ghost} {sk n m : DY.Bytes} (hsk : FreshSafeTerm i S g sk) (hn : FreshSafeTerm i S g n) (hm : FreshSafeTerm i S g m) : FreshSafeTerm i S g (DY.Signature.sign sk n m) := by
  refine freshSafeTerm_of_opaqueNode (ts := [sk, n, m]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hsk) (fun h => (List.mem_cons.mp h).elim (· ▸ hn) (fun h => List.mem_singleton.mp h ▸ hm)))
  unfold gamma'; show (((({ sk := sk, nonce := n, msg := m } : DY.Signature.Sign.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _; rw [DY.Bytes.rec_eq (gSign S) (gAll i S g)]; rfl
theorem freshSafeTerm_spqrInit {i : ExternInterpretation} {S : Sem} {g : Ghost} {a p : DY.Bytes} (ha : FreshSafeTerm i S g a) (hp : FreshSafeTerm i S g p) : FreshSafeTerm i S g (DY.Spqr.spqrInit a p) := by
  refine freshSafeTerm_of_opaqueNode (ts := [a, p]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => List.mem_singleton.mp h ▸ hp))
  unfold gamma' DY.Spqr.spqrInit; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; rfl
theorem freshSafeTerm_spqrChainKey {i : ExternInterpretation} {S : Sem} {g : Ghost} {a p idx : DY.Bytes} (ha : FreshSafeTerm i S g a) (hp : FreshSafeTerm i S g p) (hidx : FreshSafeTerm i S g idx) : FreshSafeTerm i S g (DY.Spqr.spqrChainKey a p idx) := by
  refine freshSafeTerm_of_opaqueNode (ts := [a, p, idx]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => (List.mem_cons.mp h).elim (· ▸ hp) (fun h => List.mem_singleton.mp h ▸ hidx)))
  unfold gamma' DY.Spqr.spqrChainKey; rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll i S g)]; rfl
theorem freshSafeTerm_spqrSendState {i : ExternInterpretation} {S : Sem} {g : Ghost} {st coins : DY.Bytes} (hst : FreshSafeTerm i S g st) (hc : FreshSafeTerm i S g coins) : FreshSafeTerm i S g (DY.Spqr.spqrSend st coins).1 := by
  refine freshSafeTerm_of_opaqueNode (ts := [st, coins]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
  unfold gamma' DY.Spqr.spqrSend; dsimp only; rw [DY.Bytes.rec_eq (gSpqrSendState S) (gAll i S g)]; rfl
theorem freshSafeTerm_spqrSendMsg {i : ExternInterpretation} {S : Sem} {g : Ghost} {st coins : DY.Bytes} (hst : FreshSafeTerm i S g st) (hc : FreshSafeTerm i S g coins) : FreshSafeTerm i S g (DY.Spqr.spqrSend st coins).2.2 := by
  refine freshSafeTerm_of_opaqueNode (ts := [st, coins]) ?_ (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
  unfold gamma' DY.Spqr.spqrSend; dsimp only; rw [DY.Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)]; rfl
theorem freshSafeTerm_sid {S : Sem} {g : Ghost} {dhs rk : DY.Bytes} (hdhs : FreshSafeTerm compI0 S g dhs) (hrk : FreshSafeTerm compI0 S g rk) : FreshSafeTerm compI0 S g (DY.Concat.concat (DY.DiffieHellman.dhPk dhs) rk) :=
  freshSafeTerm_concat (fun _ ht => gamma_concat_dhPk_left_ne_fillFresh64 S g dhs rk ht) (freshSafeTerm_dhPk hdhs) hrk
private theorem byte_ne_setupFresh {b : BitVec 8} {t : Nat} (hb11 : b ≠ 11#8) (hb16 : b ≠ 16#8) (hb17 : b ≠ 17#8) (ht : IsSetupFresh64Tag t) : b ≠ BitVec.ofNat 8 t := by rcases ht with rfl | rfl | rfl <;> assumption
theorem freshSafeTerm_lit_of_length_ne_64 (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) (hlen : (ofByteArray b).length ≠ 64) : FreshSafeTerm i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) :=
  freshSafeTerm_lit_of_ne_fillFresh64 i S g b (fun _ _ => ne_fillFresh64_of_length_ne hlen)
theorem freshSafeTerm_hkdfBlock1_of_head {S : Sem} {g : Ghost} {prk info : DY.Bytes} {b0 : BitVec 8} (hhead : (gamma compI0 S g info).head? = some b0) (hb11 : b0 ≠ 11#8) (hb16 : b0 ≠ 16#8) (hb17 : b0 ≠ 17#8) (hprk : FreshSafeTerm compI0 S g prk) (hinfo : FreshSafeTerm compI0 S g info) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := freshSafeTerm_hmac hprk (freshSafeTerm_concat
    (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g hhead (byte_ne_setupFresh hb11 hb16 hb17 ht)) hinfo (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide)))
theorem freshSafeTerm_hkdfBlock2_of_head {S : Sem} {g : Ghost} {prk info : DY.Bytes} {b0 : BitVec 8} (hhead : (gamma compI0 S g info).head? = some b0) (hb11 : b0 ≠ 11#8) (hb16 : b0 ≠ 16#8) (hb17 : b0 ≠ 17#8) (hprk : FreshSafeTerm compI0 S g prk) (hinfo : FreshSafeTerm compI0 S g info) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) :=
  freshSafeTerm_hmac hprk (freshSafeTerm_concat (fun _ ht => gamma_concat_hmac_left_ne_fillFresh64 S g _ _ _ ht) (freshSafeTerm_hkdfBlock1_of_head hhead hb11 hb16 hb17 hprk hinfo)
    (freshSafeTerm_concat (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g hhead (byte_ne_setupFresh hb11 hb16 hb17 ht)) hinfo (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide))))
theorem freshSafeTerm_hkdfBlock3_of_head {S : Sem} {g : Ghost} {prk info : DY.Bytes} {b0 : BitVec 8} (hhead : (gamma compI0 S g info).head? = some b0) (hb11 : b0 ≠ 11#8) (hb16 : b0 ≠ 16#8) (hb17 : b0 ≠ 17#8) (hprk : FreshSafeTerm compI0 S g prk) (hinfo : FreshSafeTerm compI0 S g info) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) :=
  freshSafeTerm_hmac hprk (freshSafeTerm_concat (fun _ ht => gamma_concat_hmac_left_ne_fillFresh64 S g _ _ _ ht) (freshSafeTerm_hkdfBlock2_of_head hhead hb11 hb16 hb17 hprk hinfo)
    (freshSafeTerm_concat (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g hhead (byte_ne_setupFresh hb11 hb16 hb17 ht)) hinfo (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide))))
theorem freshSafeTerm_pqxdhKdf_none {S : Sem} {g : Ghost} {pk1 sk1 pk2 sk2 pk3 sk3 ss₀ : DY.Bytes} (hdh1 : FreshSafeTerm compI0 S g (DY.Libsignal.PQXDH.agree pk1 sk1)) (hdh2 : FreshSafeTerm compI0 S g (DY.Libsignal.PQXDH.agree pk2 sk2)) (hdh3 : FreshSafeTerm compI0 S g (DY.Libsignal.PQXDH.agree pk3 sk3)) (hss₀ : FreshSafeTerm compI0 S g ss₀) : let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree pk1 sk1) (DY.Libsignal.PQXDH.agree pk2 sk2) (DY.Libsignal.PQXDH.agree pk3 sk3) none ss₀);
    FreshSafeTerm compI0 S g keys.rk ∧ FreshSafeTerm compI0 S g keys.ck ∧ FreshSafeTerm compI0 S g keys.pqr := by
  have hff_head : (gamma compI0 S g DY.Libsignal.PQXDH.discontinuity).head? = some 0xff#8 := (by change (gamma compI0 S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; decide); have hlbl_head : (gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel).head? = some 0x57#8 := (by change (gamma compI0 S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; exact ofByteArray_pqxdhLabel_props.1); have hsalt : FreshSafeTerm compI0 S g DY.Libsignal.PQXDH.zeroSalt := freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide); have hff : FreshSafeTerm compI0 S g DY.Libsignal.PQXDH.discontinuity := freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide)
  have hprk := freshSafeTerm_hmac hsalt
    (freshSafeTerm_concat (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g hff_head (byte_ne_setupFresh (by decide) (by decide) (by decide) ht)) hff
      (freshSafeTerm_concat (fun _ ht => gamma_concat_dh_left_ne_fillFresh64 S g _ _ _ ht) hdh1
        (freshSafeTerm_concat (fun _ ht => gamma_concat_dh_left_ne_fillFresh64 S g _ _ _ ht) hdh2
          (freshSafeTerm_concat (fun _ ht => gamma_concat_dh_left_ne_fillFresh64 S g _ _ _ ht) hdh3 hss₀))))
  have hinfo : FreshSafeTerm compI0 S g DY.Libsignal.PQXDH.pqxdhLabel := freshSafeTerm_lit_of_length_ne_64 compI0 S g _ ofByteArray_pqxdhLabel_props.2
  exact ⟨freshSafeTerm_hkdfBlock1_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo,
         freshSafeTerm_hkdfBlock2_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo,
         freshSafeTerm_hkdfBlock3_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo⟩
theorem freshSafeTerm_createChain {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} (hrk : FreshSafeTerm compI0 S g rk) (hpk : FreshSafeTerm compI0 S g (DY.X25519.x25519Key pk)) (hsk : FreshSafeTerm compI0 S g sk) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hprk := freshSafeTerm_hmac hrk (freshSafeTerm_dh hpk hsk); have hlbl_head : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")).head? = some 0x57#8 := (by change (gamma compI0 S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; exact ofByteArray_whisperRatchet_props.1); have hinfo : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := freshSafeTerm_lit_of_length_ne_64 compI0 S g _ ofByteArray_whisperRatchet_props.2
  exact ⟨freshSafeTerm_hkdfBlock1_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo,
         freshSafeTerm_hkdfBlock2_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo⟩
theorem freshSafeTerm_kdfCk {S : Sem} {g : Ghost} {ck : DY.Bytes} (hck : FreshSafeTerm compI0 S g ck) : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 :=
  ⟨freshSafeTerm_hmac hck (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide)), freshSafeTerm_hmac hck (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide))⟩
theorem freshSafeTerm_trMsgKeys {S : Sem} {g : Ghost} {salt ck : DY.Bytes} (hsalt : FreshSafeTerm compI0 S g salt) (hck : FreshSafeTerm compI0 S g ck) : let seed := (DY.Libsignal.TripleRatchet.kdfCk ck).2;
    let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
    FreshSafeTerm compI0 S g mk.cipherKey ∧ FreshSafeTerm compI0 S g mk.macKey ∧ FreshSafeTerm compI0 S g mk.iv := by
  have hprk := freshSafeTerm_hmac hsalt (freshSafeTerm_kdfCk hck).2; have hlbl_head : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")).head? = some 0x57#8 := (by change (gamma compI0 S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; exact ofByteArray_whisperMessageKeys_props.1); have hinfo : FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := freshSafeTerm_lit_of_length_ne_64 compI0 S g _ ofByteArray_whisperMessageKeys_props.2
  exact ⟨freshSafeTerm_hkdfBlock1_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo,
         freshSafeTerm_hkdfBlock2_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo,
         freshSafeTerm_hkdfBlock3_of_head hlbl_head (by decide) (by decide) (by decide) hprk hinfo⟩
theorem gamma_serializedIk_head? (i : ExternInterpretation) (S : Sem) (g : Ghost) (ik : DY.Bytes) : (gamma i S g (DY.Libsignal.PQXDH.serializedIk ik)).head? = some 5#8 := by unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC; rw [gamma_concat_eq]; change (gamma i S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack) ++ _).head? = _; rw [gamma_lit]; rfl
theorem freshSafeTerm_serializedIk (i : ExternInterpretation) (S : Sem) (g : Ghost) {ik : DY.Bytes} (hik : FreshSafeTerm i S g ik) : FreshSafeTerm i S g (DY.Libsignal.PQXDH.serializedIk ik) := by
  unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC
  refine freshSafeTerm_concat (fun t ht => gamma_concat_head?_ne_fillFresh64 i S g (b0 := 5#8) ?_ (byte_ne_setupFresh (by decide) (by decide) (by decide) ht))
    (freshSafeTerm_lit_of_length_ne_64 i S g _ (by decide)) hik
  change (gamma i S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; decide
theorem freshSafeTerm_encodeEC (i : ExternInterpretation) (S : Sem) (g : Ghost) {pk : DY.Bytes} (hpk : FreshSafeTerm i S g pk) : FreshSafeTerm i S g (DY.Libsignal.PQXDH.encodeEC pk) := freshSafeTerm_serializedIk i S g hpk
theorem freshSafeTerm_encodeKEM (i : ExternInterpretation) (S : Sem) (g : Ghost) {pk : DY.Bytes} (hpk : FreshSafeTerm i S g pk) : FreshSafeTerm i S g (DY.Libsignal.PQXDH.encodeKEM pk) := by
  unfold DY.Libsignal.PQXDH.encodeKEM
  refine freshSafeTerm_concat (fun t ht => gamma_concat_head?_ne_fillFresh64 i S g (b0 := 8#8) ?_ (byte_ne_setupFresh (by decide) (by decide) (by decide) ht))
    (freshSafeTerm_lit_of_length_ne_64 i S g _ (by decide)) hpk
  change (gamma i S g (({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack)).head? = _; rw [gamma_lit]; decide
end Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
