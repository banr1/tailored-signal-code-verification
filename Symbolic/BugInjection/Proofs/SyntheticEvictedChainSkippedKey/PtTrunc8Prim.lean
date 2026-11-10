/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import DY.Bytes.Basic
import Comparse.Basic
import DY.Comparse
import DY.Actions.PersistentLocalState
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Comparse

/-!
# Term-Algebra Closure for `Trunc8RowOK`

Defines `Trunc8RowOK`, `TermTrunc8OK`, `StateTrunc8`, `EventTrunc8`, and `PQEventTrunc8`, and
proves closure under the composed term-algebra constructors, HKDF and MAC helpers, and `Comparse`
state serialization.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (TRState TREvent lit hmac hkdfBlock1 hkdfBlock2 hkdfBlock3
   kdfRk createChain kdfCk chainKeyAt trMsgKeys computeMac trHonestWireMsg)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost node opaqueNode
   concretizeRandom concretizeTrunc concretizeKemPk
   gAll gRandom gTrunc0 gKemPk
   gamma' gamma randTerm)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (MemoOK memoOK_lit memoOK_concat memoOK_dhPk memoOK_dhPk_elim memoOK_dh_pack
   memoOK_kdfExtract memoOK_symEnc memoOK_x25519Key
   memoOK_spqrInit_elim memoOK_spqrChainKey
   memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg
   memoOK_spqrRecvState_pack memoOK_trWire)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_kdf)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (bytes_rec_gAll memoOK_concat_elim memoOK_symEnc_elim
   memoOK_kemEncap_fst memoOK_kemEncap_fst_elim memoOK_kemEncap_snd memoOK_kemRejKey
   memoOK_spqrRecvKey_pack)
open Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (length_hmacWith_32)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (kemDecap_eq_some_iff)

/-- Invariant on a `gamma'` memo row `(u, sh, v)`: if `u` packs a `Trunc8` term, then `u` is
attacker-known on `T` or `8 ≤ v.length`. -/
def Trunc8RowOK (T : ExecTrace) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop :=
  ∀ t : DY.Trunc.Trunc8.SubF DY.Bytes, x.1 = t.pack → x.1.AttackerKnows T ∨ 8 ≤ x.2.2.length

def TermTrunc8OK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (T : ExecTrace) (b : DY.Bytes) : Prop :=
  MemoOK i S g (Trunc8RowOK T) b

section Algebra
variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {T : ExecTrace}

private theorem noTrunc8Root {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (y : F DY.Bytes)
    (hproj : DY.ALaCarte.SubFunctorTC.proj (f := DY.Trunc.Trunc8.SubF)
      (DY.ALaCarte.SubFunctorTC.inj (f := F) (g := DY.BytesF) y) = none := by rfl) :
    ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = DY.BytesView.pack y → Trunc8RowOK T x :=
  fun _ hx _ ht =>
    False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none (hx.symm.trans ht) hproj)

theorem termTrunc8OK_rand (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (T : ExecTrace) (ts sz : Nat) :
    TermTrunc8OK i S g T (randTerm ts sz) := by
  intro x hx
  unfold randTerm at hx
  rw [ms_pack_random i S g ⟨ts, sz⟩] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx
  · cases hx
  · simp only [node, List.flatMap_nil, List.mem_singleton] at hx
    subst hx
    intro _ ht
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none ht)

theorem termTrunc8OK_lit (bs : ByteArray) :
    TermTrunc8OK i S g T (DY.Literal.literalToBytes bs) :=
  memoOK_lit (noTrunc8Root ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes))

theorem termTrunc8OK_concat {a c : DY.Bytes}
    (ha : TermTrunc8OK i S g T a) (hc : TermTrunc8OK i S g T c) :
    TermTrunc8OK i S g T (DY.Concat.concat a c) :=
  memoOK_concat (noTrunc8Root ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes)) ha hc

theorem termTrunc8OK_dhPk {sk : DY.Bytes} (hsk : TermTrunc8OK i S g T sk) :
    TermTrunc8OK i S g T (DY.DiffieHellman.dhPk sk) :=
  memoOK_dhPk (noTrunc8Root ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)) hsk

private theorem termTrunc8OK_dh_pack {pk sk : DY.Bytes}
    (hpk : TermTrunc8OK i S g T pk) (hsk : TermTrunc8OK i S g T sk) :
    TermTrunc8OK i S g T (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  memoOK_dh_pack (noTrunc8Root ({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes)) hpk hsk

theorem termTrunc8OK_dh {pk sk : DY.Bytes}
    (hpk : TermTrunc8OK i S g T pk) (hsk : TermTrunc8OK i S g T sk) :
    TermTrunc8OK i S g T (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq
    rw [heq] at hv; simp only at hv; subst hv
    split
    · exact termTrunc8OK_dh_pack hpk hsk
    · exact termTrunc8OK_dh_pack (termTrunc8OK_dhPk hsk) (memoOK_dhPk_elim hpk)
  · exact termTrunc8OK_dh_pack hpk hsk

theorem termTrunc8OK_kdfExtract {s ikm : DY.Bytes}
    (hs : TermTrunc8OK i S g T s) (hikm : TermTrunc8OK i S g T ikm) :
    TermTrunc8OK i S g T (DY.KdfExtract.kdfExtract s ikm) :=
  memoOK_kdfExtract
    (noTrunc8Root ({ salt := s, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes)) hs hikm

theorem termTrunc8OK_symEnc {k iv m : DY.Bytes}
    (hk : TermTrunc8OK i S g T k) (hiv : TermTrunc8OK i S g T iv) (hm : TermTrunc8OK i S g T m) :
    TermTrunc8OK i S g T (DY.SymEnc.symEnc k iv m) :=
  memoOK_symEnc
    (noTrunc8Root ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes)) hk hiv hm

theorem termTrunc8OK_symDec {k iv ct m : DY.Bytes}
    (hdec : DY.SymEnc.symDec k iv ct = some m) (hct : TermTrunc8OK i S g T ct) :
    TermTrunc8OK i S g T m := by
  dsimp only [DY.SymEnc.symDec, DY.SymEnc.instCanSymEncBytes] at hdec
  split at hdec <;> try cases hdec
  next key' iv' msg hx =>
    split_ifs at hdec
    cases hdec
    have hpv := DY.Bytes.pack_view? DY.SymEnc.Enc.SubF ct
    change ct.view? DY.SymEnc.Enc.SubF = some { key := key', iv := iv', msg := m } at hx
    rw [hx] at hpv
    rw [← hpv] at hct
    exact memoOK_symEnc_elim (e := ⟨key', iv', m⟩) hct

theorem termTrunc8OK_kemEncap {pk e : DY.Bytes}
    (hpk : TermTrunc8OK i S g T pk) (he : TermTrunc8OK i S g T e) :
    TermTrunc8OK i S g T (DY.PQKem.kemEncap pk e).1 ∧
      TermTrunc8OK i S g T (DY.PQKem.kemEncap pk e).2 :=
  ⟨memoOK_kemEncap_fst
      (noTrunc8Root ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes)) hpk he,
   memoOK_kemEncap_snd
      (noTrunc8Root ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes)) hpk he⟩

theorem termTrunc8OK_kemDecap {sk ct ss : DY.Bytes}
    (hdec : DY.PQKem.kemDecap sk ct = some ss) (hct : TermTrunc8OK i S g T ct) :
    TermTrunc8OK i S g T ss := by
  obtain ⟨e, rfl, rfl⟩ := kemDecap_eq_some_iff.mp hdec
  obtain ⟨hpk, he⟩ := memoOK_kemEncap_fst_elim (c := ⟨DY.PQKem.kemPk sk, e⟩) hct
  exact (termTrunc8OK_kemEncap hpk he).2

theorem termTrunc8OK_kemRejKey {sk ct : DY.Bytes}
    (hsk : TermTrunc8OK i S g T sk) (hct : TermTrunc8OK i S g T ct) :
    TermTrunc8OK i S g T (DY.PQKem.kemRejKey sk ct) :=
  memoOK_kemRejKey
    (noTrunc8Root ({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes)) hsk hct

theorem memoOK_kemPk_elim {sk : DY.Bytes}
    (h : TermTrunc8OK i S g T (DY.PQKem.kemPk sk)) :
    TermTrunc8OK i S g T sk := by
  intro x hx
  apply h x
  unfold gamma' at hx ⊢
  rw [show DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemPk S) (gAll i S g)]
  simp only [gKemPk, concretizeKemPk, opaqueNode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, bytes_rec_gAll]
  exact hx

theorem termTrunc8OK_trWireMsg {v : UInt8} {rk : DY.Bytes} {c pc : UInt32}
    {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation}
    (hrk : TermTrunc8OK i S g T rk) (hct : TermTrunc8OK i S g T ct)
    (hpq : TermTrunc8OK i S g T pq) :
    TermTrunc8OK i S g T (DY.TrWire.trWireMsg v rk c pc ct pq ev) :=
  memoOK_trWire (w := ⟨v, rk, c, pc, ct, pq, ev⟩)
    (noTrunc8Root (⟨v, rk, c, pc, ct, pq, ev⟩ : DY.TrWire.TrWireMsg.SubF DY.Bytes)) hrk hct hpq

theorem termTrunc8OK_spqrSend {st coins : DY.Bytes}
    (hst : TermTrunc8OK i S g T st) (hc : TermTrunc8OK i S g T coins) :
    TermTrunc8OK i S g T (DY.Spqr.spqrSend st coins).1 ∧
      TermTrunc8OK i S g T (DY.Spqr.spqrSend st coins).2.1 ∧
      TermTrunc8OK i S g T (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨memoOK_spqrSendState hst hc, ?_, memoOK_spqrSendMsg hst hc⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrSend
  dsimp only
  split
  · next authKey params hx =>
    have hst' := hst
    rw [hx] at hpv
    rw [← hpv] at hst'
    obtain ⟨ha, hp⟩ := memoOK_spqrInit_elim (s := ⟨authKey, params⟩) hst'
    exact memoOK_spqrChainKey ha hp (termTrunc8OK_lit _)
  · exact memoOK_spqrSendKey_pack hst hc

theorem termTrunc8OK_spqrRecv {st msg st' key : DY.Bytes} {idx : UInt32}
    (hst : TermTrunc8OK i S g T st) (hmsg : TermTrunc8OK i S g T msg)
    (hrecv : DY.Spqr.spqrRecv st msg idx = some (st', key)) :
    TermTrunc8OK i S g T st' ∧ TermTrunc8OK i S g T key := by
  unfold DY.Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
    cases hv : st.view? DY.Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'
      injection hrecv' with hst_eq hkey
      subst hst_eq hkey
      exact ⟨memoOK_spqrRecvState_pack hst hmsg, memoOK_spqrRecvKey_pack hst hmsg⟩
    | some x =>
      rw [hv] at hrecv hp
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv hp
      have hst' := hst
      rw [← hp] at hst'
      obtain ⟨hk, _⟩ := memoOK_spqrInit_elim (s := ⟨authKey, params⟩) hst'
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        injection hrecv' with hst_eq hkey
        subst hst_eq hkey
        refine ⟨memoOK_spqrRecvState_pack hst hmsg, ?_⟩
        split
        · exact termTrunc8OK_lit _
        · exact memoOK_spqrChainKey hk (termTrunc8OK_lit _) (termTrunc8OK_lit _)

theorem termTrunc8OK_hmac {k m : DY.Bytes}
    (hk : TermTrunc8OK i S g T k) (hm : TermTrunc8OK i S g T m) :
    TermTrunc8OK i S g T (hmac k m) :=
  termTrunc8OK_kdfExtract hk hm

theorem termTrunc8OK_hkdfBlock1 {prk info : DY.Bytes}
    (hp : TermTrunc8OK i S g T prk) (hi : TermTrunc8OK i S g T info) :
    TermTrunc8OK i S g T (hkdfBlock1 prk info) :=
  termTrunc8OK_hmac hp (termTrunc8OK_concat hi (termTrunc8OK_lit _))

theorem termTrunc8OK_hkdfBlock2 {prk info : DY.Bytes}
    (hp : TermTrunc8OK i S g T prk) (hi : TermTrunc8OK i S g T info) :
    TermTrunc8OK i S g T (hkdfBlock2 prk info) :=
  termTrunc8OK_hmac hp
    (termTrunc8OK_concat (termTrunc8OK_hkdfBlock1 hp hi) (termTrunc8OK_concat hi (termTrunc8OK_lit _)))

theorem termTrunc8OK_hkdfBlock3 {prk info : DY.Bytes}
    (hp : TermTrunc8OK i S g T prk) (hi : TermTrunc8OK i S g T info) :
    TermTrunc8OK i S g T (hkdfBlock3 prk info) :=
  termTrunc8OK_hmac hp
    (termTrunc8OK_concat (termTrunc8OK_hkdfBlock2 hp hi) (termTrunc8OK_concat hi (termTrunc8OK_lit _)))

theorem termTrunc8OK_kdfRk {rk dhOut : DY.Bytes}
    (hrk : TermTrunc8OK i S g T rk) (hdh : TermTrunc8OK i S g T dhOut) :
    TermTrunc8OK i S g T (kdfRk rk dhOut).1 ∧ TermTrunc8OK i S g T (kdfRk rk dhOut).2 :=
  ⟨termTrunc8OK_hkdfBlock1 (termTrunc8OK_hmac hrk hdh) (termTrunc8OK_lit _),
   termTrunc8OK_hkdfBlock2 (termTrunc8OK_hmac hrk hdh) (termTrunc8OK_lit _)⟩

theorem termTrunc8OK_createChain {rk pk sk : DY.Bytes}
    (hrk : TermTrunc8OK i S g T rk) (hpk : TermTrunc8OK i S g T pk) (hsk : TermTrunc8OK i S g T sk) :
    TermTrunc8OK i S g T (createChain rk pk sk).1 ∧ TermTrunc8OK i S g T (createChain rk pk sk).2 :=
  termTrunc8OK_kdfRk hrk (termTrunc8OK_dh (memoOK_x25519Key hpk) hsk)

theorem termTrunc8OK_kdfCk {ck : DY.Bytes} (hck : TermTrunc8OK i S g T ck) :
    TermTrunc8OK i S g T (kdfCk ck).1 ∧ TermTrunc8OK i S g T (kdfCk ck).2 :=
  ⟨termTrunc8OK_hmac hck (termTrunc8OK_lit _), termTrunc8OK_hmac hck (termTrunc8OK_lit _)⟩

theorem termTrunc8OK_chainKeyAt :
    ∀ {ck : DY.Bytes} (n : Nat), TermTrunc8OK i S g T ck → TermTrunc8OK i S g T (chainKeyAt ck n)
  | _, 0, hck => hck
  | _, n + 1, hck => termTrunc8OK_chainKeyAt n (termTrunc8OK_kdfCk hck).1

theorem termTrunc8OK_trMsgKeys {pqSalt seed : DY.Bytes}
    (hpq : TermTrunc8OK i S g T pqSalt) (hs : TermTrunc8OK i S g T seed) :
    TermTrunc8OK i S g T (trMsgKeys pqSalt seed).cipherKey ∧
      TermTrunc8OK i S g T (trMsgKeys pqSalt seed).macKey ∧
      TermTrunc8OK i S g T (trMsgKeys pqSalt seed).iv := by
  have hp : TermTrunc8OK i S g T (hmac pqSalt seed) := termTrunc8OK_hmac hpq hs
  have hi : TermTrunc8OK i S g T (lit "WhisperMessageKeys") :=
    termTrunc8OK_lit ("WhisperMessageKeys".toUTF8)
  exact ⟨termTrunc8OK_hkdfBlock1 hp hi, termTrunc8OK_hkdfBlock2 hp hi, termTrunc8OK_hkdfBlock3 hp hi⟩

theorem termTrunc8OK_trunc8_hmac {k m : DY.Bytes}
    (hk : TermTrunc8OK i S g T k) (hm : TermTrunc8OK i S g T m) :
    TermTrunc8OK i S g T (DY.Trunc.trunc8 (hmac k m)) := by
  intro x hx
  unfold gamma' at hx
  rw [show DY.Trunc.trunc8 (hmac k m) =
        ({ input := hmac k m } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq gTrunc0 (gAll i S g)] at hx
  simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hchild
  · intro _ _
    right
    dsimp only
    have hlen32 : ((gamma' i S g (hmac k m)).bytes).length = 32 := by
      change (gamma i S g (({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).length = 32
      unfold gamma
      rw [ms_pack_kdf i S g ⟨k, m⟩]
      exact length_hmacWith_32 (sha256CompressFunction i) _ _
    rw [List.length_take, hlen32]
    decide
  · exact termTrunc8OK_hmac hk hm x hchild

theorem termTrunc8OK_computeMac {mk sik rik w : DY.Bytes}
    (hmk : TermTrunc8OK i S g T mk) (hsik : TermTrunc8OK i S g T sik)
    (hrik : TermTrunc8OK i S g T rik) (hw : TermTrunc8OK i S g T w) :
    TermTrunc8OK i S g T (computeMac mk sik rik w) :=
  termTrunc8OK_trunc8_hmac hmk (termTrunc8OK_concat hsik (termTrunc8OK_concat hrik hw))

theorem termTrunc8OK_trHonestWireMsg {rk ct pq : DY.Bytes}
    (hrk : TermTrunc8OK i S g T rk) (c pc : UInt32)
    (hct : TermTrunc8OK i S g T ct) (hpq : TermTrunc8OK i S g T pq) :
    TermTrunc8OK i S g T (trHonestWireMsg rk c pc ct pq) :=
  termTrunc8OK_trWireMsg hrk hct hpq

local instance termTrunc8OK_compat :
    Comparse.BytesCompatiblePred (TermTrunc8OK i S g T) where
  pred_empty := by
    simp only [Comparse.BytesLike.empty]
    exact termTrunc8OK_lit _
  pred_concat := by
    simp only [Comparse.BytesLike.concat]
    intro _ _ h1 h2
    exact termTrunc8OK_concat h1 h2
  pred_split := by
    intro buf j hbuf
    simp only [Comparse.BytesLike.split]
    rcases hsp : DY.Concat.split buf j with _ | ⟨b1, b2⟩
    · trivial
    · rw [← DY.Concat.concat_split buf j b1 b2 hsp] at hbuf
      exact memoOK_concat_elim hbuf
  pred_fromByteArray := by
    intro b
    simp only [Comparse.BytesLike.fromByteArray]
    exact termTrunc8OK_lit b

def StateTrunc8 (st : TRState) : Prop :=
  TermTrunc8OK i S g T st.myIk ∧ TermTrunc8OK i S g T st.peerIk ∧ TermTrunc8OK i S g T st.rk ∧
  TermTrunc8OK i S g T st.dhs ∧ TermTrunc8OK i S g T st.cks ∧ TermTrunc8OK i S g T st.sid ∧
  TermTrunc8OK i S g T st.spqr ∧
  ∀ c ∈ st.recv, TermTrunc8OK i S g T c.ratchetKey ∧ TermTrunc8OK i S g T c.chainKey

theorem termTrunc8OK_serialize_tr (ls : PersistentLocalState.LocalState TRState)
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) ls.state) :
    TermTrunc8OK i S g T (Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
      ← Comparse.ExtensibleMessageFormat.wf_eq _ (TermTrunc8OK i S g T) ls]
  obtain ⟨hmy, hpeer, hrk, hdhs, hcks, hsid, hspqr, hrecv⟩ := hst
  simp [Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf]
  exact ⟨hmy, hpeer, hrk, hdhs, hcks, hsid, hspqr, hrecv⟩

theorem termTrunc8OK_serialize_pq (ls : PersistentLocalState.LocalState PQXDHState)
    (hsk : TermTrunc8OK i S g T ls.state.sk) :
    TermTrunc8OK i S g T (Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
      ← Comparse.ExtensibleMessageFormat.wf_eq _ (TermTrunc8OK i S g T) ls]
  simp [Comparse.ParseableSerializeable.mf]
  exact hsk

def EventTrunc8 : TREvent → Prop
  | .SkippedKeyStored _ pk _ seed _ _ => TermTrunc8OK i S g T seed ∧ TermTrunc8OK i S g T pk
  | .ExposedMK _ seed _ _ => TermTrunc8OK i S g T seed
  | .ExposedSpqr _ spqr _ => TermTrunc8OK i S g T spqr
  | .Received _ _ _ _ m => TermTrunc8OK i S g T m
  | _ => True

def PQEventTrunc8 : PQXDHEvent → Prop
  | .IdentityRegistered _ ikPk vk _ => TermTrunc8OK i S g T ikPk ∧ TermTrunc8OK i S g T vk
  | .BobDone _ _ _ _ _ _ _ ek _ _ => TermTrunc8OK i S g T ek
  | _ => True

end Algebra

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
