/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
import ProofLib.BV.WidthNorm

/-!
# SPQR V1: `Chain`, `Authenticator`, `PolyDecoder`, and `PolyEncoder` Size Bounds

**Checked by Lean.**

Proves `raw*` size bounds across `Chain` (`fromPb`, `new`, `chainFromVersionNegotiation`,
`chainFrom`, `addEpoch`, `sendKey`, `recvKey`), `Authenticator` (`fromPb`, `new`, `update`),
`PolyDecoder` (`fromPb`, `new`, `addChunk`), and `PolyEncoder` (`fromPb`, `encodeBytes`,
`nextChunk`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.StateSize

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.HMAC (toBEBytes)

theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = Except.ok b) : ∃ a, m = Except.ok a ∧ f a = Except.ok b := by
  cases m with
  | error _ => contradiction
  | ok a => exact ⟨a, rfl, h⟩

/-! ## `Chain` Round-Trip and Step Size Bounds -/

private theorem toBEBytes_length {w : Nat} (n : Nat) (x : BitVec w) :
    (toBEBytes n x).length = n := by
  unfold toBEBytes; simp

theorem KeyHistory.add_length_le (kh : KeyHistory) (k : BitVec 32 × Bytes) (params : ChainParamsPB)
    (hk : k.2.length ≤ 32) :
    (kh.add k params).data.length ≤ kh.data.length + 36 := by
  unfold KeyHistory.add; simp only [List.length_append, toBEBytes_length]; omega

theorem KeyHistory.remove_length_le (kh : KeyHistory) (i : Nat) (params : ChainParamsPB) :
    (kh.remove i params).data.length ≤ kh.data.length := by
  unfold KeyHistory.remove; split <;> simp only [List.length_take] <;> omega

theorem KeyHistory.gcLoop_length_le (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB)
    (i : Nat) {kh' : KeyHistory} (h : kh.gcLoop th params i = .ok kh') :
    kh'.data.length ≤ kh.data.length := by
  suffices ∀ n (kh : KeyHistory) i, kh.data.length - i ≤ n → kh.gcLoop th params i = .ok kh' →
      kh'.data.length ≤ kh.data.length from this (kh.data.length - i) kh i (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro kh i hn h; unfold KeyHistory.gcLoop at h; split at h
    · omega
    · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
  | succ n ih =>
    intro kh i hn h; unfold KeyHistory.gcLoop at h; split at h
    · rename_i hi; split at h
      · contradiction
      · dsimp only [] at h; split at h
        · have hlt := KeyHistory.remove_length_lt kh i params hi
          exact Nat.le_trans (ih (kh.remove i params) i (by omega) h) (by omega)
        · exact ih kh (i + KeyHistory.KEY_SIZE) (by simp only [KeyHistory.KEY_SIZE]; omega) h
    · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _

theorem KeyHistory.gc_length_le (kh : KeyHistory) (ck : BitVec 32) (params : ChainParamsPB)
    {kh' : KeyHistory} (h : kh.gc ck params = .ok kh') :
    kh'.data.length ≤ kh.data.length := by
  unfold KeyHistory.gc at h; dsimp only [] at h; split at h
  · split at h
    · contradiction
    · exact KeyHistory.gcLoop_length_le kh _ params 0 h
  · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _

theorem KeyHistory.getLoop_length_le (kh : KeyHistory) (atIdx : BitVec 32) (want : Bytes)
    (params : ChainParamsPB) (i : Nat) {kh' : KeyHistory} {out : Bytes}
    (h : kh.getLoop atIdx want params i = .ok (kh', out)) :
    kh'.data.length ≤ kh.data.length := by
  suffices ∀ n (kh : KeyHistory) i, kh.data.length - i ≤ n →
      kh.getLoop atIdx want params i = .ok (kh', out) → kh'.data.length ≤ kh.data.length from
    this (kh.data.length - i) kh i (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro kh i hn h; unfold KeyHistory.getLoop at h; split at h
    · omega
    · contradiction
  | succ n ih =>
    intro kh i hn h; unfold KeyHistory.getLoop at h; split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; exact KeyHistory.remove_length_le kh i params
      · exact ih kh (i + KeyHistory.KEY_SIZE) (by simp only [KeyHistory.KEY_SIZE]; omega) h
    · contradiction

theorem KeyHistory.get_length_le (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    {kh' : KeyHistory} {out : Bytes} (h : kh.get atIdx ctr params = .ok (kh', out)) :
    kh'.data.length ≤ kh.data.length := by
  unfold KeyHistory.get at h; dsimp only [] at h; split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · exact KeyHistory.getLoop_length_le kh atIdx _ params 0 h

theorem ChainEpochDirection.fromPb_intoPb {pb : EpochDirectionPB} {ed : ChainEpochDirection}
    (h : ChainEpochDirection.fromPb pb = .ok ed) : ed.intoPb = pb := by
  unfold ChainEpochDirection.fromPb at h; split at h
  · contradiction
  · simp only [Except.ok.injEq] at h; subst h; rfl

theorem ChainEpochDirection.nextKeyInternal_length_le (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32)
    {next' : Bytes} {ctr' : BitVec 32} {k : BitVec 32 × Bytes}
    (h : ChainEpochDirection.nextKeyInternal hkdf next ctr = .ok (next', ctr', k)) :
    next'.length ≤ 32 ∧ k.2.length ≤ 32 := by
  unfold ChainEpochDirection.nextKeyInternal at h; split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨List.length_take_le _ _, List.length_take_le _ _⟩

theorem ChainEpochDirection.nextKey_raw_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    {ed' : ChainEpochDirection} {out : BitVec 32 × Bytes}
    (h : ed.nextKey hkdf = .ok (ed', out)) :
    rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 32 := by
  unfold ChainEpochDirection.nextKey at h
  rcases hnk : ChainEpochDirection.nextKeyInternal hkdf ed.next ed.ctr with e | ⟨next', ctr', k⟩
  · simp [hnk, Bind.bind, Except.bind] at h
  · simp only [hnk, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨hn, _⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf ed.next ed.ctr hnk
    simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega

theorem ChainEpochDirection.keyAdvanceLoop_length_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection}
    (h : ed.keyAdvanceLoop hkdf atIdx params = .ok ed') :
    ed'.next.length ≤ max ed.next.length 32 ∧
      ed'.prev.data.length ≤ ed.prev.data.length + 36 * (atIdx.toNat - ed.ctr.toNat) := by
  suffices ∀ n (ed : ChainEpochDirection), atIdx.toNat - ed.ctr.toNat ≤ n →
      ed.keyAdvanceLoop hkdf atIdx params = .ok ed' →
      ed'.next.length ≤ max ed.next.length 32 ∧
        ed'.prev.data.length ≤ ed.prev.data.length + 36 * (atIdx.toNat - ed.ctr.toNat) from
    this (atIdx.toNat - ed.ctr.toNat) ed (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩
  | succ n ih =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · rename_i hlt; split at h
      · contradiction
      · rename_i next' ctr' k hnk
        have hctr' := ChainEpochDirection.nextKeyInternal_ctr hkdf ed.next next' ed.ctr ctr' k hnk
        dsimp only [] at h; split at h
        · contradiction
        · obtain ⟨hnk1, hnk2⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf ed.next ed.ctr hnk
          obtain ⟨ihn, ihp⟩ := ih _ (by dsimp only []; omega) h
          dsimp only [] at ihn ihp
          refine ⟨by omega, ?_⟩
          have hprev : (if ctr' + params.maxOooKeysOrDefault ≥ atIdx then ed.prev.add k params else ed.prev).data.length ≤
              ed.prev.data.length + 36 := by
            split
            · exact KeyHistory.add_length_le ed.prev k params hnk2
            · omega
          have hsub : 36 + 36 * (atIdx.toNat - ctr'.toNat) = 36 * (atIdx.toNat - ed.ctr.toNat) := by
            have : atIdx.toNat - ed.ctr.toNat = (atIdx.toNat - ctr'.toNat) + 1 := by omega
            rw [this, Nat.mul_add]; omega
          omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩

theorem ChainEpochDirection.key_raw_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection} {out : Bytes}
    (h : ed.key hkdf atIdx params = .ok (ed', out)) :
    rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 32 + 36 * 2 ^ 32 := by
  unfold ChainEpochDirection.key at h; dsimp only [] at h; split at h
  · rcases hget : ed.prev.get atIdx ed.ctr params with e | ⟨prev', out'⟩
    · simp [hget, Bind.bind, Except.bind] at h
    · simp only [hget, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hp := KeyHistory.get_length_le ed.prev atIdx ed.ctr params hget
      simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · set self0 := if atIdx > ed.ctr + params.maxOooKeysOrDefault then { ed with prev := ed.prev.clear } else ed
          rcases hadv : self0.keyAdvanceLoop hkdf atIdx params with e | self1
          · simp [self0, hadv, Bind.bind, Except.bind] at h
          · simp only [self0, hadv, Bind.bind, Except.bind] at h
            rcases hgc : ChainResult.ofPanic (self1.prev.gc self1.ctr params) with e | prevGc
            · simp [hgc] at h
            · simp only [hgc] at h
              rcases hnk : ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr) with e | ⟨next', ctr', _, outKey⟩
              · simp [hnk] at h
              · simp only [hnk, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                have h0 : self0.prev.data.length ≤ ed.prev.data.length := by
                  dsimp [self0]; split <;> simp [KeyHistory.clear]
                have ⟨_, hadvp⟩ := ChainEpochDirection.keyAdvanceLoop_length_le hkdf self0 atIdx params hadv
                have hgc' : self1.prev.gc self1.ctr params = .ok prevGc := (ChainResult.ofPanic_eq_ok).mp hgc
                have hgcp := KeyHistory.gc_length_le self1.prev self1.ctr params hgc'
                have hnk' : ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr = .ok (next', ctr', _, outKey) :=
                  (ChainResult.ofPanic_eq_ok).mp hnk
                have ⟨hn, _⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf self1.next self1.ctr hnk'
                have hat : atIdx.toNat - self0.ctr.toNat ≤ 2 ^ 32 := by have := atIdx.isLt; omega
                have hmul : 36 * (atIdx.toNat - self0.ctr.toNat) ≤ 36 * 2 ^ 32 := Nat.mul_le_mul_left 36 hat
                simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega

/-- Model-level per-link weight `rawChainEpoch link.intoPb + 200`. -/
def linkRaw (link : ChainEpoch) : Nat :=
  rawEpochDir link.send.intoPb + rawEpochDir link.recv.intoPb + 200

private theorem map_intoPb_links (links : List ChainEpoch) :
    ((links.map fun link =>
        ({ send := some link.send.intoPb, recv := some link.recv.intoPb } : ChainEpochPB)).map
      (fun e => rawChainEpoch e + 200)) =
    links.map linkRaw := by
  induction links with
  | nil => rfl
  | cons l ls ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl

theorem Chain.cedForDirection_raw_le (genr8r : Bytes) (dir : Direction) :
    rawEpochDir (Chain.cedForDirection genr8r dir).intoPb ≤ 32 := by
  unfold Chain.cedForDirection ChainEpochDirection.new ChainEpochDirection.intoPb KeyHistory.new rawEpochDir
  split <;> simp only [List.length_nil, Nat.add_zero] <;> exact List.length_take_le _ _

theorem Chain.linksFromPb_sum_eq {pbs : List ChainEpochPB} {links : List ChainEpoch}
    (h : Chain.linksFromPb pbs = .ok links) :
    (links.map linkRaw).sum = (pbs.map (fun e => rawChainEpoch e + 200)).sum := by
  induction pbs generalizing links with
  | nil => simp only [Chain.linksFromPb, Except.ok.injEq] at h; subst h; rfl
  | cons pb rest ih =>
    unfold Chain.linksFromPb at h
    cases hs : pb.send with
    | none => simp [hs, Bind.bind, Except.bind] at h
    | some sendPb =>
      simp only [hs, Bind.bind, Except.bind] at h
      rcases hsf : ChainEpochDirection.fromPb sendPb with e | send
      · simp [hsf] at h
      · simp only [hsf] at h
        cases hr : pb.recv with
        | none => simp [hr] at h
        | some recvPb =>
          simp only [hr] at h
          rcases hrf : ChainEpochDirection.fromPb recvPb with e | recv
          · simp [hrf] at h
          · simp only [hrf] at h
            rcases htail : Chain.linksFromPb rest with e | tail
            · simp [htail] at h
            · simp only [htail, pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp only [List.map_cons, List.sum_cons, linkRaw,
                ChainEpochDirection.fromPb_intoPb hsf, ChainEpochDirection.fromPb_intoPb hrf,
                ih htail, rawChainEpoch, hs, hr, optRaw]

theorem Chain.fromPb_raw_eq {pb : ChainPB} {c : Chain} (h : Chain.fromPb pb = .ok c) :
    rawChain c.intoPb = rawChain pb := by
  unfold Chain.fromPb at h
  cases hd : Direction.fromI32? pb.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some d =>
    simp only [hd, Bind.bind, Except.bind] at h
    rcases hl : Chain.linksFromPb pb.links with e | links
    · simp [hl] at h
    · simp only [hl] at h
      cases hp : pb.params with
      | none => simp [hp] at h
      | some p =>
        simp only [hp, pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Chain.intoPb, rawChain, map_intoPb_links, Chain.linksFromPb_sum_eq hl]

theorem Chain.new_raw_le (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction)
    (params : ChainParamsPB) {c : Chain} (h : Chain.new hkdf initialKey dir params = .ok c) :
    rawChain c.intoPb ≤ 296 := by
  unfold Chain.new at h; simp only [Except.ok.injEq] at h; subst h
  have hs := Chain.cedForDirection_raw_le (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir
  have hr := Chain.cedForDirection_raw_le (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir.switch
  have hroot : ((hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96).take 32).length ≤ 32 := List.length_take_le _ _
  simp only [Chain.intoPb, rawChain, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rawChainEpoch, optRaw]
  omega

theorem chainFromVersionNegotiation_raw_le (hkdf : HkdfFn) (vn : VersionNegotiationPB) {c : Chain}
    (h : chainFromVersionNegotiation hkdf vn = .ok c) :
    rawChain c.intoPb ≤ 296 := by
  unfold chainFromVersionNegotiation at h
  cases hd : Direction.fromI32? vn.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some d =>
    simp only [hd, Bind.bind, Except.bind] at h
    cases hp : vn.chainParams with
    | none => simp [hp] at h
    | some p => simp only [hp] at h; exact Chain.new_raw_le hkdf vn.authKey d p h

theorem chainFrom_raw_le (hkdf : HkdfFn) (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    {c : Chain} (h : chainFrom hkdf pb vn = .ok c) :
    rawChain c.intoPb ≤ optRaw rawChain pb + 296 := by
  unfold chainFrom at h
  cases pb with
  | some cpb => have heq := Chain.fromPb_raw_eq h; simp only [optRaw]; omega
  | none =>
    cases vn with
    | none => contradiction
    | some vnpb => have hle := chainFromVersionNegotiation_raw_le hkdf vnpb h; simp only [optRaw]; omega

theorem Chain.addEpoch_raw_le (hkdf : HkdfFn) (c : Chain) (es : EpochSecret) {c' : Chain}
    (h : c.addEpoch hkdf es = .ok c') :
    rawChain c'.intoPb ≤ rawChain c.intoPb + 296 := by
  unfold Chain.addEpoch at h; split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Except.ok.injEq] at h; subst h
      have hs := Chain.cedForDirection_raw_le (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir
      have hr := Chain.cedForDirection_raw_le (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir.switch
      have hroot : ((hkdf c.nextRoot es.secret chainAddEpochInfo 96).take 32).length ≤ 32 := List.length_take_le _ _
      simp only [Chain.intoPb, rawChain, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, rawChainEpoch, optRaw]; omega

private theorem sum_map_drop_le {α : Type} (f : α → Nat) (n : Nat) (l : List α) :
    ((l.drop n).map f).sum ≤ (l.map f).sum := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons x xs => simp only [List.drop_succ_cons, List.map_cons, List.sum_cons]; have := ih xs; omega

private theorem clearSendNextPrefix_sum_le (n : Nat) (l : List ChainEpoch) :
    ((Chain.clearSendNextPrefix n l).map linkRaw).sum ≤ (l.map linkRaw).sum := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x xs =>
      simp only [Chain.clearSendNextPrefix, List.map_cons, List.sum_cons, linkRaw,
        ChainEpochDirection.clearNext, ChainEpochDirection.intoPb, rawEpochDir, List.length_nil]
      have := ih xs; omega

theorem sum_map_set_le {α : Type} (f : α → Nat) (l : List α) (i : Nat) (x y : α) (d : Nat)
    (hi : l[i]? = some x) (hy : f y ≤ f x + d) :
    ((l.set i y).map f).sum ≤ (l.map f).sum + d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      have := ih i hi; omega

private theorem sendKey_tail_raw_le (hkdf : HkdfFn) {self1 : Chain} {epochIndex : Nat}
    {c' : Chain} {out : BitVec 32 × Bytes}
    (h : (match self1.links[epochIndex]? with
      | none => .error (.panic .linksOutOfBounds)
      | some link => do
        let (send', out) ← ChainResult.ofPanic (link.send.nextKey hkdf)
        let links' := self1.links.set epochIndex { link with send := send' }
        return ({ self1 with links := links' }, out) : ChainResult (Chain × (BitVec 32 × Bytes))) = .ok (c', out)) :
    rawChain c'.intoPb ≤ rawChain self1.intoPb + 32 := by
  cases hlink : self1.links[epochIndex]? with
  | none => simp [hlink] at h
  | some link =>
    simp only [hlink] at h
    rcases hnk : ChainResult.ofPanic (link.send.nextKey hkdf) with e | ⟨send', out'⟩
    · simp [hnk, Bind.bind, Except.bind] at h
    · simp only [hnk, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hnk' : link.send.nextKey hkdf = .ok (send', out') := (ChainResult.ofPanic_eq_ok).mp hnk
      have hsend := ChainEpochDirection.nextKey_raw_le hkdf link.send hnk'
      have hset := sum_map_set_le linkRaw self1.links epochIndex link { link with send := send' } 32 hlink
        (by simp only [linkRaw]; omega)
      simp only [Chain.intoPb, rawChain, map_intoPb_links]; omega

theorem Chain.sendKey_raw_le (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) {c' : Chain}
    {out : BitVec 32 × Bytes} (h : c.sendKey hkdf epoch = .ok (c', out)) :
    rawChain c'.intoPb ≤ rawChain c.intoPb + 32 := by
  unfold Chain.sendKey at h; split at h
  · contradiction
  · rcases heidx : ChainResult.ofError (c.epochIdx epoch) with e | epochIndex0
    · simp [heidx, Bind.bind, Except.bind] at h
    · simp only [heidx, Bind.bind, Except.bind] at h
      have htail := sendKey_tail_raw_le hkdf h
      by_cases hne : c.sendEpoch != epoch
      · simp only [hne, ↓reduceIte, Chain.intoPb, rawChain, map_intoPb_links] at htail
        have h1 := clearSendNextPrefix_sum_le
          (epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
          (c.links.drop (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        have h2 := sum_map_drop_le linkRaw (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH) c.links
        simp only [Chain.intoPb, rawChain, map_intoPb_links]; omega
      · simp only [hne, Bool.false_eq_true, ↓reduceIte] at htail; exact htail

theorem Chain.recvKey_raw_le (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) (index : BitVec 32)
    {c' : Chain} {out : Bytes} (h : c.recvKey hkdf epoch index = .ok (c', out)) :
    rawChain c'.intoPb ≤ rawChain c.intoPb + 32 + 36 * 2 ^ 32 := by
  unfold Chain.recvKey at h; split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; omega
  · rcases heidx : ChainResult.ofError (c.epochIdx epoch) with e | epochIndex
    · simp [heidx, Bind.bind, Except.bind] at h
    · simp only [heidx, Bind.bind, Except.bind] at h
      cases hlink : c.links[epochIndex]? with
      | none => simp [hlink] at h
      | some link =>
        simp only [hlink] at h
        rcases hkey : link.recv.key hkdf index c.params with e | ⟨recv', out'⟩
        · simp [hkey] at h
        · simp only [hkey, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hrecv := ChainEpochDirection.key_raw_le hkdf link.recv index c.params hkey
          have hset := sum_map_set_le linkRaw c.links epochIndex link { link with recv := recv' }
            (32 + 36 * 2 ^ 32) hlink (by simp only [linkRaw]; omega)
          simp only [Chain.intoPb, rawChain, map_intoPb_links]; omega

/-! ## `Authenticator`, `PolyDecoder`, and `PolyEncoder` Bounds -/

@[simp] theorem Authenticator.rawAuth_intoPb_fromPb (pb : ProtoAuthenticator) :
    rawAuth (Authenticator.fromPb pb).intoPb = rawAuth pb := rfl

theorem Authenticator.update_rawAuth_le (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (self : Authenticator) (ep : Epoch) (k : Bytes) :
    rawAuth (self.update F ep k).intoPb ≤ 64 := by
  unfold Authenticator.update Authenticator.intoPb rawAuth; dsimp only []
  have h2 : (hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
      (Authenticator.updateLabel ++ toBEBytes 8 ep) 64).length ≤ 64 := List.length_take_le _ _
  generalize hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
      (Authenticator.updateLabel ++ toBEBytes 8 ep) 64 = kdfOut at h2 ⊢
  have h1 : (kdfOut.take 32).length ≤ 32 := List.length_take_le _ _
  simp only [List.length_drop]; omega

theorem Authenticator.new_rawAuth_le (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (rootKey : Bytes) (ep : Epoch) :
    rawAuth (Authenticator.new F rootKey ep).intoPb ≤ 64 :=
  Authenticator.update_rawAuth_le F _ ep rootKey

private theorem flatMap_ptSerialize_length (l : List Pt) :
    (l.flatMap Pt.serialize).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (Pt.serialize p).length = 4 := rfl; omega

def ptSetRaw (s : SortedSetPt) : Nat := 4 * s.vec.length + 22

private theorem map_intoPb_decoder_pts (pts : List SortedSetPt) :
    ((pts.map (fun s => s.vec.flatMap Pt.serialize)).map (fun b => b.length + 22)) =
    pts.map ptSetRaw := by
  induction pts with
  | nil => rfl
  | cons s ss ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [ptSetRaw, flatMap_ptSerialize_length]

theorem SortedSetPt.replace_length_le (s : SortedSetPt) (el : Pt) :
    (s.replace el).1.vec.length ≤ s.vec.length + 1 := by
  unfold SortedSetPt.replace; split
  · simp
  · simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]; omega

theorem SortedSetPt.push_length_le (s : SortedSetPt) (el : Pt) :
    (s.push el).1.vec.length ≤ s.vec.length + 1 := by
  unfold SortedSetPt.push; split
  · split
    · simp
    · simp only [List.length_append, List.length_dropLast, List.length_singleton]; omega
    · exact SortedSetPt.replace_length_le s el
  · simp

theorem PolyDecoder.pushChunksExact4_length_le (bs : List (BitVec 8)) (v : SortedSetPt)
    {v' : SortedSetPt} (h : PolyDecoder.pushChunksExact4 bs v = .ok v') :
    4 * v'.vec.length ≤ 4 * v.vec.length + bs.length := by
  suffices ∀ n (bs : List (BitVec 8)) (v : SortedSetPt), bs.length ≤ n →
      PolyDecoder.pushChunksExact4 bs v = .ok v' →
      4 * v'.vec.length ≤ 4 * v.vec.length + bs.length from
    this bs.length bs v (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro bs v hn h; cases bs with
    | nil => unfold PolyDecoder.pushChunksExact4 at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro bs v hn h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
    · unfold PolyDecoder.pushChunksExact4 at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h
      simp only [Pt.deserialize, Bind.bind, Except.bind] at h
      have hpush := SortedSetPt.push_length_le v
        { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
      have hih := ih rest _ (by simp only [List.length_cons] at hn; omega) h
      simp only [List.length_cons]; omega

theorem PolyDecoder.decodeDecoderPbPts_sum_le {pbs : List (List (BitVec 8))}
    {outPts : List SortedSetPt}
    (h : PolyDecoder.decodeDecoderPbPts pbs = .ok (.ok outPts)) :
    (outPts.map ptSetRaw).sum ≤ (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing outPts with
  | nil => unfold PolyDecoder.decodeDecoderPbPts at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons pts rest ih =>
    unfold PolyDecoder.decodeDecoderPbPts at h; split at h
    · simp [pure, Except.pure] at h
    · rcases hv : PolyDecoder.pushChunksExact4 pts (SortedSetPt.withCapacity (pts.length / 4)) with e | v
      · simp [hv, Bind.bind, Except.bind] at h
      · simp only [hv, Bind.bind, Except.bind] at h
        rcases htail : PolyDecoder.decodeDecoderPbPts rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            have hvle := PolyDecoder.pushChunksExact4_length_le pts (SortedSetPt.withCapacity (pts.length / 4)) hv
            have hcap : (SortedSetPt.withCapacity (pts.length / 4)).vec.length = 0 := rfl
            have hih := ih htail
            simp only [List.map_cons, List.sum_cons, ptSetRaw]; omega

theorem PolyDecoder.fromPb_raw_le {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ rawPolyDec pb := by
  unfold PolyDecoder.fromPb at h; split at h
  · simp [pure, Except.pure] at h
  · rcases hpts : PolyDecoder.decodeDecoderPbPts (pbToProtoPolyDecoder pb).pts with e | ptsRes
    · simp [hpts, Bind.bind, Except.bind] at h
    · simp only [hpts, Bind.bind, Except.bind] at h
      cases ptsRes with
      | error e => simp [pure, Except.pure] at h
      | ok outPts =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := PolyDecoder.decodeDecoderPbPts_sum_le hpts
        simp only [PolyDecoder.intoPb, protoPolyDecoderToPb, rawPolyDec, map_intoPb_decoder_pts]
        exact hsum

theorem PolyDecoder.new_raw_le {lenBytes : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.new lenBytes = .ok (.ok dec)) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ 352 := by
  unfold PolyDecoder.new PolyDecoder.newWithPolyCount at h; split at h
  · simp [pure, Except.pure] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have : rawPolyDec (protoPolyDecoderToPb ({ ptsNeeded := lenBytes / 2, pts := List.replicate 16 SortedSetPt.new, isComplete := false } : PolyDecoder).intoPb) = 352 := rfl
    omega

private theorem ptSetRaw_push_le (s : SortedSetPt) (el : Pt) :
    ptSetRaw (s.push el).1 ≤ ptSetRaw s + 4 := by
  have := SortedSetPt.push_length_le s el; simp only [ptSetRaw]; omega

theorem PolyDecoder.addChunkLoop_sum_le (chunk : Chunk) (i rem : Nat) (self : PolyDecoder)
    {self' : PolyDecoder} (h : PolyDecoder.addChunkLoop chunk i rem self = .ok self') :
    (self'.pts.map ptSetRaw).sum ≤ (self.pts.map ptSetRaw).sum + 4 * rem := by
  induction rem generalizing i self with
  | zero => unfold PolyDecoder.addChunkLoop at h; simp only [Except.ok.injEq] at h; subst h; omega
  | succ rem ih =>
    unfold PolyDecoder.addChunkLoop at h; dsimp only [] at h; split at h
    · rename_i polyPts hpoly
      have hih := ih (i + 1) _ h; split at hih
      · dsimp only [] at hih
        have hset := Nat.le_trans hih (Nat.add_le_add_right
          (sum_map_set_le ptSetRaw self.pts _ polyPts _ 4 hpoly (ptSetRaw_push_le polyPts _)) (4 * rem))
        omega
      · omega
    · contradiction

theorem PolyDecoder.addChunk_raw_le {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : dec.addChunk chunk = .ok dec') :
    rawPolyDec (protoPolyDecoderToPb dec'.intoPb) ≤ rawPolyDec (protoPolyDecoderToPb dec.intoPb) + 64 := by
  have hsum := PolyDecoder.addChunkLoop_sum_le chunk 0 16 dec h
  simp only [PolyDecoder.intoPb, protoPolyDecoderToPb, rawPolyDec, map_intoPb_decoder_pts]; omega

private theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl; omega

private theorem Poly.serialize_length (p : Poly) :
    p.serialize.length = 2 * p.coefficients.length :=
  flatMap_u16ToBeBytes_length p.coefficients

def pointRaw (pt : Point) : Nat := 2 * pt.value.length + 22
def polyRaw (p : Poly) : Nat := 2 * p.coefficients.length + 22

private theorem map_intoPb_encoder_pts (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) =
    pts.map pointRaw := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [pointRaw, flatMap_u16ToBeBytes_length]

private theorem map_intoPb_encoder_polys (polys : List Poly) :
    ((polys.map Poly.serialize).map (fun b => b.length + 22)) =
    polys.map polyRaw := by
  induction polys with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [polyRaw, Poly.serialize_length]

theorem Poly.bytesToGF16List_length {bs : List (BitVec 8)} {gs : List GF16}
    (h : Poly.bytesToGF16List bs = .ok gs) : 2 * gs.length = bs.length := by
  suffices ∀ n (bs : List (BitVec 8)) (gs : List GF16), bs.length ≤ n →
      Poly.bytesToGF16List bs = .ok gs → 2 * gs.length = bs.length from
    this bs.length bs gs (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro bs gs hn h; cases bs with
    | nil => unfold Poly.bytesToGF16List at h; simp only [Except.ok.injEq] at h; subst h; rfl
    | cons _ _ => simp at hn
  | succ n ih =>
    intro bs gs hn h
    rcases bs with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    · unfold Poly.bytesToGF16List at h; simp only [Except.ok.injEq] at h; subst h; rfl
    · unfold Poly.bytesToGF16List at h; contradiction
    · unfold Poly.bytesToGF16List at h
      rcases htail : Poly.bytesToGF16List rest with e | tail
      · simp [htail, Bind.bind, Except.bind] at h
      · simp only [htail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hih := ih rest tail (by simp only [List.length_cons] at hn; omega) htail
        simp only [List.length_cons]; omega

theorem Poly.deserialize_length {bs : List (BitVec 8)} {p : Poly}
    (h : Poly.deserialize bs = .ok (.ok p)) : 2 * p.coefficients.length = bs.length := by
  unfold Poly.deserialize at h; split at h
  · simp [pure, Except.pure] at h
  · rcases hgs : Poly.bytesToGF16List bs with e | gs
    · simp [hgs, Bind.bind, Except.bind] at h
    · simp only [hgs, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact Poly.bytesToGF16List_length hgs

theorem PolyEncoder.decodePbPoints_sum_eq {pbs : List Bytes} {out : List Point}
    (h : PolyEncoder.decodePbPoints pbs = .ok (.ok out)) :
    (out.map pointRaw).sum = (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing out with
  | nil => unfold PolyEncoder.decodePbPoints at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons pts rest ih =>
    unfold PolyEncoder.decodePbPoints at h; split at h
    · simp [pure, Except.pure] at h
    · rcases hv : Poly.bytesToGF16List pts with e | v
      · simp [hv, Bind.bind, Except.bind] at h
      · simp only [hv, Bind.bind, Except.bind] at h
        rcases htail : PolyEncoder.decodePbPoints rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            simp only [List.map_cons, List.sum_cons, pointRaw, Poly.bytesToGF16List_length hv, ih htail]

theorem PolyEncoder.decodePbPolys_sum_eq {pbs : List Bytes} {out : List Poly}
    (h : PolyEncoder.decodePbPolys pbs = .ok (.ok out)) :
    (out.map polyRaw).sum = (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing out with
  | nil => unfold PolyEncoder.decodePbPolys at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons polyBytes rest ih =>
    unfold PolyEncoder.decodePbPolys at h
    rcases hp : Poly.deserialize polyBytes with e | pRes
    · simp [hp, Bind.bind, Except.bind] at h
    · simp only [hp, Bind.bind, Except.bind] at h
      cases pRes with
      | error e => simp [pure, Except.pure] at h
      | ok p =>
        simp only [] at h
        rcases htail : PolyEncoder.decodePbPolys rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            simp only [List.map_cons, List.sum_cons, polyRaw, Poly.deserialize_length hp, ih htail]

theorem PolyEncoder.fromPb_raw_le {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ rawPolyEnc pb := by
  unfold PolyEncoder.fromPb at h; split at h
  · split at h
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · rcases hpts : PolyEncoder.decodePbPoints (pbToProtoPolyEncoder pb).pts with e | ptsRes
        · simp [hpts, Bind.bind, Except.bind] at h
        · simp only [hpts, Bind.bind, Except.bind] at h
          cases ptsRes with
          | error e => simp [pure, Except.pure] at h
          | ok out =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            have hsum := PolyEncoder.decodePbPoints_sum_eq hpts
            simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, pbToProtoPolyEncoder, rawPolyEnc,
              map_intoPb_encoder_pts, List.map_nil, List.sum_nil] at hsum ⊢; omega
  · split at h
    · rcases hpolys : PolyEncoder.decodePbPolys (pbToProtoPolyEncoder pb).polys with e | polysRes
      · simp [hpolys, Bind.bind, Except.bind] at h
      · simp only [hpolys, Bind.bind, Except.bind] at h
        cases polysRes with
        | error e => simp [pure, Except.pure] at h
        | ok out =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hsum := PolyEncoder.decodePbPolys_sum_eq hpolys
          simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, pbToProtoPolyEncoder, rawPolyEnc,
            map_intoPb_encoder_polys, List.map_nil, List.sum_nil] at hsum ⊢; omega
    · simp [pure, Except.pure] at h

theorem PolyEncoder.distributeMsgChunks_sum_le (i : Nat) (msg : List (BitVec 8)) (pts : List Point)
    {pts' : List Point} (h : PolyEncoder.distributeMsgChunks i msg pts = .ok pts') :
    (pts'.map pointRaw).sum ≤ (pts.map pointRaw).sum + msg.length := by
  suffices ∀ n i (msg : List (BitVec 8)) (pts : List Point), msg.length ≤ n →
      PolyEncoder.distributeMsgChunks i msg pts = .ok pts' →
      (pts'.map pointRaw).sum ≤ (pts.map pointRaw).sum + msg.length from
    this msg.length i msg pts (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro i msg pts hn h; cases msg with
    | nil => unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro i msg pts hn h
    rcases msg with _ | ⟨c0, _ | ⟨c1, rest⟩⟩
    · unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyEncoder.distributeMsgChunks at h; contradiction
    · unfold PolyEncoder.distributeMsgChunks at h; dsimp only [] at h; split at h
      · rename_i pt hpt
        have hih := ih (i + 1) rest _ (by simp only [List.length_cons] at hn; omega) h
        have hset := sum_map_set_le pointRaw pts (i % pts.length) pt
          { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] } 2 hpt
          (by simp only [pointRaw, List.length_append, List.length_singleton]; omega)
        simp only [List.length_cons]; omega
      · contradiction

theorem PolyEncoder.encodeBytes_raw_le {msg : List (BitVec 8)} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ 1048928 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h; split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · rename_i hlen
      rcases hpts : PolyEncoder.distributeMsgChunks 0 msg (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := PolyEncoder.distributeMsgChunks_sum_le 0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw).sum = 352 := rfl
        have hnp : (1 <<< 16) * NUM_POLYS = 1048576 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc,
          map_intoPb_encoder_pts, List.map_nil, List.sum_nil]; omega

private theorem parallelMult_length (a : GF16) (l : List GF16) :
    (parallelMult a l).length = l.length := by
  fun_induction parallelMult a l with
  | case1 => rfl
  | case2 _ => rfl
  | case3 _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

private theorem addAssignCoeffs_length (l1 l2 : List GF16) :
    (Poly.addAssignCoeffs l1 l2).length = max l1.length l2.length := by
  fun_induction Poly.addAssignCoeffs l1 l2 with
  | case1 _ => simp
  | case2 _ _ => simp
  | case3 _ _ _ _ ih => simp only [List.length_cons, ih]; omega

private theorem mem_zip_snd {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x rest ih =>
    cases ys with
    | nil => simp at h
    | cons y yrest =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)

private theorem lagrangeSum_foldl_length_le (pairs : List (Pt × Poly)) (acc : Poly) (n : Nat)
    (hacc : acc.coefficients.length ≤ n)
    (hpairs : ∀ pair ∈ pairs, pair.2.coefficients.length ≤ n) :
    (pairs.foldl (fun out (pt, poly) =>
      let p := poly.multAssign pt.y
      out.addAssign p) acc).coefficients.length ≤ n := by
  induction pairs generalizing acc with
  | nil => exact hacc
  | cons pair rest ih =>
    simp only [List.foldl_cons]; apply ih
    · have hp : pair.2.coefficients.length ≤ n := hpairs pair (List.Mem.head _)
      simp only [Poly.addAssign, Poly.multAssign, addAssignCoeffs_length, parallelMult_length]; omega
    · intro p hp; exact hpairs p (List.Mem.tail _ hp)

private theorem Poly.lagrangeSum_length_le (pts : List Pt) (polys : List Poly) (n : Nat)
    (h : ∀ p ∈ polys, p.coefficients.length ≤ n) :
    (Poly.lagrangeSum pts polys).coefficients.length ≤ n := by
  apply lagrangeSum_foldl_length_le (pts.zip polys) (Poly.zero pts.length) n
  · simp [Poly.zero]
  · intro pair hp; exact h pair.2 (mem_zip_snd hp)

private theorem PolyConst.multXdiff_length_le {n : Nat} {self p' : PolyConst n} {diff : GF16}
    (h : self.multXdiff diff = .ok p') :
    p'.coefficients.length ≤ n := by
  unfold PolyConst.multXdiff at h; split at h
  · contradiction
  · rename_i hn0; have hn : n ≠ 0 := by simpa using hn0
    split at h
    · split at h
      · contradiction
      · dsimp only [] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [List.length_map, List.length_zip, List.length_cons, List.length_take]; omega
    · contradiction

private theorem PolyConst.lagrangeInterpolatePtLoop_length_le (n : Nat) (pts : List Pt) (pix : GF16)
    (j rem : Nat) (p : PolyConst n) (denom : GF16) {p' : PolyConst n} {denom' : GF16}
    (hp : p.coefficients.length ≤ n)
    (h : PolyConst.lagrangeInterpolatePtLoop n pts pix j rem p denom = .ok (p', denom')) :
    p'.coefficients.length ≤ n := by
  induction rem generalizing j p denom with
  | zero =>
    unfold PolyConst.lagrangeInterpolatePtLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; exact hp
  | succ rem ih =>
    unfold PolyConst.lagrangeInterpolatePtLoop at h; split at h
    · split at h
      · exact ih (j + 1) p denom hp h
      · rcases except_bind_eq_ok h with ⟨p1, hp1, h⟩
        exact ih (j + 1) p1 _ (PolyConst.multXdiff_length_le hp1) h
    · contradiction

private theorem PolyConst.lagrangeInterpolatePt_length_le (n : Nat) (pts : List Pt) (i : Nat)
    {cp : PolyConst n} (h : PolyConst.lagrangeInterpolatePt n pts i = .ok cp) :
    cp.coefficients.length ≤ n := by
  unfold PolyConst.lagrangeInterpolatePt at h; split at h
  · split at h
    · contradiction
    · rename_i hn0; have hn : n ≠ 0 := by simpa using hn0
      rcases except_bind_eq_ok h with ⟨⟨p, denom⟩, hloop, h⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      have hp0 : ({ coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO } : PolyConst n).coefficients.length ≤ n := by
        simp only [List.length_cons, List.length_replicate]; omega
      have hpl := PolyConst.lagrangeInterpolatePtLoop_length_le n pts _ 0 n _ GF16.ONE hp0 hloop
      simpa [PolyConst.mult] using hpl
  · contradiction

private theorem forall_mem_of_mapM_ok {ε α β : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    {P : β → Prop} (h : xs.mapM f = .ok ys) (hP : ∀ x y, f x = .ok y → P y) :
    ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ hm; nomatch hm
  | cons x rest ih =>
    simp only [List.mapM_cons] at h
    rcases except_bind_eq_ok h with ⟨y0, hy0, h⟩
    rcases except_bind_eq_ok h with ⟨tail, htail, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro y hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hP x y hy0
    · exact ih htail y hm

private theorem lagrangePolysForCompletePoints_length_le (n : Nat) {cps : List (PolyConst n)}
    (h : lagrangePolysForCompletePoints n = .ok cps) :
    ∀ p ∈ constPolysToPolys cps, p.coefficients.length ≤ n := by
  unfold lagrangePolysForCompletePoints at h
  have hcps := forall_mem_of_mapM_ok h (fun i cp hi => PolyConst.lagrangeInterpolatePt_length_le n _ i hi)
  intro p hp; simp only [constPolysToPolys, List.mem_map] at hp
  rcases hp with ⟨cp, hcp, rfl⟩; exact hcps cp hcp

private theorem Poly.multXdiffAssignTrailingLoop_length (diff : GF16) (i rem : Nat) (coeffs : List GF16)
    {coeffs' : List GF16} (h : Poly.multXdiffAssignTrailingLoop diff i rem coeffs = .ok coeffs') :
    coeffs'.length = coeffs.length := by
  induction rem generalizing i coeffs with
  | zero => unfold Poly.multXdiffAssignTrailingLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.multXdiffAssignTrailingLoop at h; split at h
    · contradiction
    · split at h
      · rw [ih (i + 1) _ h, List.length_set]
      · contradiction

private theorem Poly.multXdiffAssignTrailing_length (self : Poly) (start : Nat) (diff : GF16)
    {p' : Poly} (h : self.multXdiffAssignTrailing start diff = .ok p') :
    p'.coefficients.length = self.coefficients.length := by
  unfold Poly.multXdiffAssignTrailing at h; dsimp only [] at h; split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · rcases except_bind_eq_ok h with ⟨coeffs', hloop, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact Poly.multXdiffAssignTrailingLoop_length diff start _ self.coefficients hloop

private theorem Poly.lagrangeInterpolatePrepareLoop_length (pts : List Pt) (offset i rem : Nat) (p : Poly)
    {p' : Poly} (h : Poly.lagrangeInterpolatePrepareLoop pts offset i rem p = .ok p') :
    p'.coefficients.length = p.coefficients.length := by
  induction rem generalizing i p with
  | zero => unfold Poly.lagrangeInterpolatePrepareLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.lagrangeInterpolatePrepareLoop at h; split at h
    · split at h
      · contradiction
      · rcases except_bind_eq_ok h with ⟨p1, hp1, h⟩
        rw [ih (i + 1) p1 h, Poly.multXdiffAssignTrailing_length p _ _ hp1]
    · contradiction

private theorem Poly.lagrangeInterpolatePrepare_length (pts : List Pt) {p : Poly}
    (h : Poly.lagrangeInterpolatePrepare pts = .ok p) :
    p.coefficients.length = pts.length + 1 := by
  unfold Poly.lagrangeInterpolatePrepare at h; dsimp only [] at h; split at h
  · contradiction
  · rw [Poly.lagrangeInterpolatePrepareLoop_length pts pts.length 0 pts.length _ h]; simp

private theorem Poly.lagrangeCompleteDivLoop_length (pix scale : GF16) (len j rem : Nat) (coeffs : List GF16)
    {coeffs' : List GF16} (h : Poly.lagrangeCompleteDivLoop pix scale len j rem coeffs = .ok coeffs') :
    coeffs'.length = coeffs.length := by
  induction rem generalizing j coeffs with
  | zero => unfold Poly.lagrangeCompleteDivLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.lagrangeCompleteDivLoop at h; split at h
    · contradiction
    · dsimp only [] at h; split at h
      · contradiction
      · split at h
        · rw [ih (j + 1) _ h, List.length_set, List.length_set]
        · contradiction

private theorem Poly.lagrangeInterpolateComplete_length (self : Poly) (pts : List Pt) (i : Nat)
    {p' : Poly} (h : self.lagrangeInterpolateComplete pts i = .ok p') :
    p'.coefficients.length = self.coefficients.length := by
  unfold Poly.lagrangeInterpolateComplete at h; split at h
  · dsimp only [] at h; split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
    · rcases except_bind_eq_ok h with ⟨coeffs', hloop, h⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact Poly.lagrangeCompleteDivLoop_length _ _ _ 1 _ self.coefficients hloop
  · contradiction

private theorem Poly.lagrangeInterpolatePt_length_le (pts : List Pt) (i : Nat) {p : Poly}
    (h : Poly.lagrangeInterpolatePt pts i = .ok p) :
    p.coefficients.length ≤ pts.length := by
  unfold Poly.lagrangeInterpolatePt at h
  rcases except_bind_eq_ok h with ⟨r1, hr1, h⟩
  rcases except_bind_eq_ok h with ⟨r2, hr2, h⟩
  have hlen1 := Poly.lagrangeInterpolatePrepare_length pts hr1
  have hlen2 := Poly.lagrangeInterpolateComplete_length r1 pts i hr2
  cases hc : r2.coefficients with
  | nil => simp [hc] at h
  | cons c rest =>
    simp only [hc, pure, Except.pure, Except.ok.injEq] at h; subst h
    simp only [hc, List.length_cons] at hlen2; dsimp only; omega

private theorem fromCompletePoints_const_branch {pts : List Pt} {m : Nat} {p : Poly}
    (hm : pts.length = m)
    (h : ((do
      let cps ← lagrangePolysForCompletePoints m
      let polys ← pure (constPolysToPolys cps)
      pure (Except.ok (Poly.lagrangeSum pts polys))) : Except PolyPanic (Except Unit Poly)) = Except.ok (Except.ok p)) :
    p.coefficients.length ≤ pts.length := by
  rcases except_bind_eq_ok h with ⟨cps, hcps, h⟩
  simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h; rw [hm]
  exact Poly.lagrangeSum_length_le pts _ m (lagrangePolysForCompletePoints_length_le m hcps)

theorem Poly.fromCompletePoints_length_le (pts : List Pt) {p : Poly}
    (h : Poly.fromCompletePoints pts = .ok (.ok p)) :
    p.coefficients.length ≤ pts.length := by
  unfold Poly.fromCompletePoints at h; split at h
  · simp [pure, Except.pure] at h
  · dsimp only [] at h; split at h
    · simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; apply Poly.lagrangeSum_length_le; intro _ hm; nomatch hm
    · split at h
      · rename_i _ hn1; exact fromCompletePoints_const_branch (of_decide_eq_true hn1) h
      · split at h
        · rename_i _ _ hn3; exact fromCompletePoints_const_branch (of_decide_eq_true hn3) h
        · split at h
          · rename_i _ _ _ hn5; exact fromCompletePoints_const_branch (of_decide_eq_true hn5) h
          · split at h
            · rename_i _ _ _ _ hn30; exact fromCompletePoints_const_branch (of_decide_eq_true hn30) h
            · split at h
              · rename_i _ _ _ _ _ hn34; exact fromCompletePoints_const_branch (of_decide_eq_true hn34) h
              · split at h
                · rename_i _ _ _ _ _ _ hn36; exact fromCompletePoints_const_branch (of_decide_eq_true hn36) h
                · rcases except_bind_eq_ok h with ⟨polys, hpolys, h⟩
                  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
                  apply Poly.lagrangeSum_length_le
                  have hall := forall_mem_of_mapM_ok hpolys (fun i q hq => Poly.lagrangeInterpolatePt_length_le _ i hq)
                  simpa using hall

private theorem enumeratePts_length (x : Nat) (l : List GF16) :
    (PolyEncoder.enumeratePts x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons _ rest ih => simp [PolyEncoder.enumeratePts, ih]

private theorem sum_map_drop_of_getElem? {α : Type} (f : α → Nat) (xs : List α) (i : Nat) (x : α)
    (h : xs[i]? = some x) :
    ((xs.drop i).map f).sum = f x + ((xs.drop (i + 1)).map f).sum := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp
    | succ i' => simp only [List.getElem?_cons_succ] at h; simpa [List.drop_succ_cons] using ih i' h

private theorem PolyEncoder.pointsToPolysLoop_sum_le (pts : List Point) (i rem : Nat) (acc : List Poly)
    {polys : List Poly} (h : PolyEncoder.pointsToPolysLoop pts i rem acc = .ok polys) :
    (polys.map polyRaw).sum ≤ (acc.map polyRaw).sum + ((pts.drop i).map pointRaw).sum := by
  induction rem generalizing i acc with
  | zero => unfold PolyEncoder.pointsToPolysLoop at h; simp only [Except.ok.injEq] at h; subst h; omega
  | succ rem ih =>
    unfold PolyEncoder.pointsToPolysLoop at h; split at h
    · rename_i ptList hpt; dsimp only [] at h
      rcases except_bind_eq_ok h with ⟨res, hres, h⟩
      cases res with
      | error _ => contradiction
      | ok p =>
        have hp := Poly.fromCompletePoints_length_le _ hres
        rw [enumeratePts_length] at hp
        have hih := ih (i + 1) (acc ++ [p]) h
        have hdrop := sum_map_drop_of_getElem? pointRaw pts i ptList hpt
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_cons, List.sum_nil] at hih
        simp only [polyRaw, pointRaw] at hp hih hdrop; omega
    · contradiction

private theorem PolyEncoder.pointAt_raw_le (self : PolyEncoder) (poly idx : Nat)
    {self' : PolyEncoder} {val : GF16} (h : self.pointAt poly idx = .ok (self', val)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  unfold PolyEncoder.pointAt at h
  cases hs : self.s with
  | points pts =>
    simp only [hs] at h; split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; exact Nat.le_refl _
      · rcases hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] with e | polys
        · simp [hloop, Bind.bind, Except.bind] at h
        · simp only [hloop, Bind.bind, Except.bind, pure, Except.pure] at h; split at h
          · rcases except_bind_eq_ok h with ⟨_, _, h⟩
            simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
            have hsum := PolyEncoder.pointsToPolysLoop_sum_le pts 0 NUM_POLYS [] hloop
            simp only [List.map_nil, List.sum_nil, List.drop_zero, Nat.zero_add] at hsum
            simp only [PolyEncoder.intoPb, hs, protoPolyEncoderToPb, rawPolyEnc,
              map_intoPb_encoder_pts, map_intoPb_encoder_polys, List.map_nil, List.sum_nil]; omega
          · contradiction
    · simp [Bind.bind, Except.bind] at h
  | polys polys =>
    simp only [hs, Bind.bind, Except.bind, pure, Except.pure] at h; split at h
    · rcases except_bind_eq_ok h with ⟨_, _, h⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
      simp [PolyEncoder.intoPb, hs]
    · contradiction

private theorem PolyEncoder.chunkAtLoop_raw_le (idx : BitVec 16) (i rem : Nat) (self : PolyEncoder)
    {self' : PolyEncoder} {vec : List.Vector (BitVec 8) (2 * rem)}
    (h : PolyEncoder.chunkAtLoop idx i rem self = .ok (self', vec)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  induction rem generalizing i self with
  | zero =>
    unfold PolyEncoder.chunkAtLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; exact Nat.le_refl _
  | succ rem ih =>
    unfold PolyEncoder.chunkAtLoop at h; dsimp only [] at h
    rcases except_bind_eq_ok h with ⟨⟨self1, p⟩, hp, h⟩
    rcases except_bind_eq_ok h with ⟨⟨self2, tail⟩, htail, h⟩
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
    exact Nat.le_trans (ih (i + 1) self1 htail) (PolyEncoder.pointAt_raw_le self _ _ hp)

theorem PolyEncoder.nextChunk_raw_le (self : PolyEncoder) {self' : PolyEncoder} {chunk : Chunk}
    (h : self.nextChunk = .ok (self', chunk)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt at h
  rcases except_bind_eq_ok h with ⟨⟨self1, out⟩, hchunk, h⟩
  rcases except_bind_eq_ok hchunk with ⟨⟨self2, data⟩, hloop, hchunk⟩
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h hchunk
  rcases hchunk with ⟨rfl, _⟩; rcases h with ⟨rfl, _⟩
  have hle := PolyEncoder.chunkAtLoop_raw_le (self.idx.setWidth 16) 0 16 self hloop
  cases hs : self2.s <;> simpa [PolyEncoder.intoPb, hs, protoPolyEncoderToPb, rawPolyEnc] using hle

end CryptoVerification.SpqrV1.Top.StateSize

