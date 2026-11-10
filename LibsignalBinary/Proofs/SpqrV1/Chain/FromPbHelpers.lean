/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.Repr
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap

/-!
# Helper Lemmas for `<spqr::chain::Chain>::from_pb` (`0x60074`, 296 instructions)

Bit-level characterizations of `Direction.fromI32?`, `ChainEpochDirection.fromPb`, and
`Chain.fromPb`; stride-112 division via `(x >>> 4) * 0x6db6db6db6db6db7#64`; stack/output-slot
splitting; and separation-logic bridges between `ChainPB` and `Chain` epoch representations.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Pure Lemmas for `Direction.fromI32?`, `ChainEpochDirection.fromPb`, and `Chain.fromPb` -/

theorem direction_fromI32_of_uge_two {w : BitVec 32} (h : BitVec.ule 2#32 w = true) :
    Direction.fromI32? w = none := by
  have hle : 2 ≤ w.toNat := by simpa [BitVec.ule] using h
  have h0 : w ≠ 0#32 := by intro heq; subst heq; simp at hle
  have h1 : w ≠ 1#32 := by intro heq; subst heq; simp at hle
  simp [Direction.fromI32?, h0, h1]

theorem chainFromPb_of_direction_uge_two {pb : ChainPB}
    (h : BitVec.ule 2#32 pb.direction = true) :
    Chain.fromPb pb = .error .stateDecode := by
  unfold Chain.fromPb
  rw [direction_fromI32_of_uge_two h]
  rfl

theorem direction_fromI32_of_ult_two {w : BitVec 32} (h : BitVec.ule 2#32 w = false) :
    ∃ dir : Direction, Direction.fromI32? w = some dir ∧ dir.toI32 = w := by
  have hlt : w.toNat < 2 := by
    have : ¬(2 ≤ w.toNat) := by simpa [BitVec.ule] using h
    omega
  by_cases h0 : w = 0#32
  · subst h0
    exact ⟨.a2b, rfl, rfl⟩
  · have hne0 : w.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
    have h1 : w = 1#32 := BitVec.eq_of_toNat_eq (show w.toNat = (1#32).toNat by simp; omega)
    subst h1
    exact ⟨.b2a, rfl, rfl⟩

/-- `tst x, #0xffffffffffffffdf` (`x &&& 0xffffffffffffffdf#64 == 0#64`) holds iff `x = 0#64 ∨ x = 32#64`. -/
theorem bv64_and_not32_beq_zero_iff (x : BitVec 64) :
    (x &&& 0xffffffffffffffdf#64 == 0#64) = true ↔ (x = 0#64 ∨ x = 32#64) := by
  constructor
  · intro h
    have h0 : x &&& 0xffffffffffffffdf#64 = 0#64 := eq_of_beq h
    by_cases hx : x = 0#64
    · exact Or.inl hx
    · exact Or.inr (by bv_bits)
  · rintro (rfl | rfl) <;> rfl

theorem ofNat_len_and_not32_true {bs : Bytes} (hlen : bs.length < 2 ^ 63)
    (h : (BitVec.ofNat 64 bs.length &&& 0xffffffffffffffdf#64 == 0#64) = true) :
    (!bs.isEmpty && (bs.length != 32)) = false := by
  have h64 : bs.length < 18446744073709551616 := by omega
  rcases (bv64_and_not32_beq_zero_iff (BitVec.ofNat 64 bs.length)).mp h with h0 | h32
  · have htn := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at htn
    have hemp : bs.isEmpty = true := List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero htn)
    simp [hemp]
  · have htn := congrArg BitVec.toNat h32
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at htn
    simp [htn]

theorem ofNat_len_and_not32_false {bs : Bytes} (hlen : bs.length < 2 ^ 63)
    (h : (BitVec.ofNat 64 bs.length &&& 0xffffffffffffffdf#64 == 0#64) = false) :
    (!bs.isEmpty && (bs.length != 32)) = true := by
  by_cases h0 : bs.length = 0
  · exfalso
    rw [h0] at h
    contradiction
  · by_cases h32 : bs.length = 32
    · exfalso
      rw [h32] at h
      contradiction
    · have hemp : bs.isEmpty = false := by
        cases bs with
        | nil => contradiction
        | cons _ _ => rfl
      simp [hemp, h32]

theorem ced_fromPb_of_tst_true {d : EpochDirectionPB} (hlen : d.next.length < 2 ^ 63)
    (h : (BitVec.ofNat 64 d.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true) :
    ChainEpochDirection.fromPb d =
      .ok { ctr := d.ctr, next := d.next, prev := { data := d.prev } } := by
  unfold ChainEpochDirection.fromPb
  rw [ofNat_len_and_not32_true hlen h]
  rfl

theorem ced_fromPb_of_tst_false {d : EpochDirectionPB} (hlen : d.next.length < 2 ^ 63)
    (h : (BitVec.ofNat 64 d.next.length &&& 0xffffffffffffffdf#64 == 0#64) = false) :
    ChainEpochDirection.fromPb d = .error .stateDecode := by
  unfold ChainEpochDirection.fromPb
  rw [ofNat_len_and_not32_false hlen h]
  rfl

theorem linksFromPb_append_of_ok {prefPB restPB : List ChainEpochPB} {pref : List ChainEpoch}
    (hpref : Chain.linksFromPb prefPB = .ok pref) :
    Chain.linksFromPb (prefPB ++ restPB) =
      match Chain.linksFromPb restPB with
      | .ok tail => .ok (pref ++ tail)
      | .error e => .error e := by
  induction prefPB generalizing pref with
  | nil =>
    simp only [Chain.linksFromPb] at hpref
    cases hpref
    simp only [List.nil_append]
    cases Chain.linksFromPb restPB <;> rfl
  | cons link tl ih =>
    rw [List.cons_append]
    simp only [Chain.linksFromPb, Bind.bind, Except.bind, Pure.pure, Except.pure] at hpref ⊢
    cases hsend : link.send with
    | none => simp [hsend] at hpref
    | some sendPb =>
      simp only [hsend] at hpref ⊢
      cases hsendFrom : ChainEpochDirection.fromPb sendPb with
      | error e => simp [hsendFrom] at hpref
      | ok send =>
        simp only [hsendFrom] at hpref ⊢
        cases hrecv : link.recv with
        | none => simp [hrecv] at hpref
        | some recvPb =>
          simp only [hrecv] at hpref ⊢
          cases hrecvFrom : ChainEpochDirection.fromPb recvPb with
          | error e => simp [hrecvFrom] at hpref
          | ok recv =>
            simp only [hrecvFrom] at hpref ⊢
            cases htl : Chain.linksFromPb tl with
            | error e => simp [htl] at hpref
            | ok tailPref =>
              simp only [htl] at hpref
              injection hpref with hpref_eq
              subst hpref_eq
              rw [ih htl]
              cases Chain.linksFromPb restPB <;> rfl

theorem linksFromPb_cons_send_none (rest : List ChainEpochPB)
    (recv : Option EpochDirectionPB) :
    Chain.linksFromPb ({ send := none, recv := recv } :: rest) = .error .stateDecode := rfl

theorem linksFromPb_cons_send_err (sendPb : EpochDirectionPB)
    (recv : Option EpochDirectionPB) (rest : List ChainEpochPB)
    (herr : ChainEpochDirection.fromPb sendPb = .error .stateDecode) :
    Chain.linksFromPb ({ send := some sendPb, recv := recv } :: rest) = .error .stateDecode := by
  simp [Chain.linksFromPb, Bind.bind, Except.bind, herr]

theorem linksFromPb_cons_recv_none (sendPb : EpochDirectionPB) (send : ChainEpochDirection)
    (rest : List ChainEpochPB)
    (hok : ChainEpochDirection.fromPb sendPb = .ok send) :
    Chain.linksFromPb ({ send := some sendPb, recv := none } :: rest) = .error .stateDecode := by
  simp [Chain.linksFromPb, Bind.bind, Except.bind, hok]

theorem linksFromPb_cons_recv_err (sendPb recvPb : EpochDirectionPB) (send : ChainEpochDirection)
    (rest : List ChainEpochPB)
    (hsend : ChainEpochDirection.fromPb sendPb = .ok send)
    (hrecv : ChainEpochDirection.fromPb recvPb = .error .stateDecode) :
    Chain.linksFromPb ({ send := some sendPb, recv := some recvPb } :: rest) = .error .stateDecode := by
  simp [Chain.linksFromPb, Bind.bind, Except.bind, hsend, hrecv]

theorem linksFromPb_cons_ok (sendPb recvPb : EpochDirectionPB) (send recv : ChainEpochDirection)
    (rest : List ChainEpochPB)
    (hsend : ChainEpochDirection.fromPb sendPb = .ok send)
    (hrecv : ChainEpochDirection.fromPb recvPb = .ok recv) :
    Chain.linksFromPb ({ send := some sendPb, recv := some recvPb } :: rest) =
      match Chain.linksFromPb rest with
      | .ok tail => .ok ({ send := send, recv := recv } :: tail)
      | .error e => .error e := by
  simp only [Chain.linksFromPb, Bind.bind, Except.bind, Pure.pure, Except.pure, hsend, hrecv]
  cases Chain.linksFromPb rest <;> rfl

theorem chainFromPb_of_links_err {pb : ChainPB} {dir : Direction}
    (hdir : Direction.fromI32? pb.direction = some dir)
    (hl : Chain.linksFromPb pb.links = .error .stateDecode) :
    Chain.fromPb pb = .error .stateDecode := by
  unfold Chain.fromPb
  simp [Bind.bind, Except.bind, hdir, hl]

theorem chainFromPb_of_params_none {pb : ChainPB} {dir : Direction} {links : List ChainEpoch}
    (hdir : Direction.fromI32? pb.direction = some dir)
    (hl : Chain.linksFromPb pb.links = .ok links)
    (hp : pb.params = none) :
    Chain.fromPb pb = .error .stateDecode := by
  unfold Chain.fromPb
  simp [Bind.bind, Except.bind, hdir, hl, hp]

theorem chainFromPb_of_ok {pb : ChainPB} {dir : Direction} {links : List ChainEpoch}
    {params : ChainParamsPB}
    (hdir : Direction.fromI32? pb.direction = some dir)
    (hl : Chain.linksFromPb pb.links = .ok links)
    (hp : pb.params = some params) :
    Chain.fromPb pb = .ok {
      dir := dir
      currentEpoch := pb.currentEpoch
      sendEpoch := pb.sendEpoch
      nextRoot := pb.nextRoot
      links := links
      params := params
    } := by
  unfold Chain.fromPb
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, hdir, hl, hp]

/-! ## Stride-112 Arithmetic and Magic Constant `0x6db6db6db6db6db7#64` -/

theorem mul_112_shift_eq (n : Nat) (h : n * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 n <<< 7#64) - (BitVec.ofNat 64 n <<< 4#64) =
      BitVec.ofNat 64 (n * 112) := by
  have hn64 : n < 18446744073709551616 := by omega
  change (BitVec.ofNat 64 n <<< 7) - (BitVec.ofNat 64 n <<< 4) = BitVec.ofNat 64 (n * 112)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.shiftLeft_eq]
  omega

theorem cap_mul_112_shift_eq (cap : BitVec 64) (h : cap.toNat * 112 < 2 ^ 63) :
    (cap <<< 7#64) - (cap <<< 4#64) = BitVec.ofNat 64 (cap.toNat * 112) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using mul_112_shift_eq cap.toNat h

private theorem magic_div7_mul (x : BitVec 64) :
    (x * 7#64) * 0x6db6db6db6db6db7#64 = x := by
  rw [BitVec.mul_assoc]
  change x * 1#64 = x
  exact BitVec.mul_one x

private theorem ofNat_mul_112_lsr_4 {k : Nat} (hk : k * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (k * 112)) >>> 4 = BitVec.ofNat 64 k * 7#64 := by
  have hk64 : k * 112 < 18446744073709551616 := by omega
  have hk7 : k * 7 < 18446744073709551616 := by omega
  have hk0 : k < 18446744073709551616 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_mul,
    Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hk0, Nat.shiftRight_eq_div_pow]
  have hdiv : k * 112 / 16 = k * 7 := by omega
  rw [hdiv, Nat.mod_eq_of_lt hk7]

/-- At `+792` (`0x6038c`), `((BitVec.ofNat 64 (k * 112)) >>> 4) * 0x6db6db6db6db6db7#64 = BitVec.ofNat 64 k`. -/
theorem div_112_magic_eq {k : Nat} (hk : k * 112 < 2 ^ 63) :
    ((BitVec.ofNat 64 (k * 112)) >>> 4#64) * 0x6db6db6db6db6db7#64 =
      BitVec.ofNat 64 k := by
  change ((BitVec.ofNat 64 (k * 112)) >>> 4) * 0x6db6db6db6db6db7#64 = BitVec.ofNat 64 k
  rw [ofNat_mul_112_lsr_4 hk, magic_div7_mul]

theorem sub_ptr_add_mul_112 (ptr : BitVec 64) (a b : Nat) (h : b ≤ a) :
    (ptr + BitVec.ofNat 64 (a * 112)) - (ptr + BitVec.ofNat 64 (b * 112)) =
      BitVec.ofNat 64 ((a - b) * 112) := by
  have ha : a * 112 = b * 112 + (a - b) * 112 := by
    rw [← Nat.add_mul, Nat.add_sub_of_le h]
  rw [ha, BitVec.ofNat_add]
  bv_lin

theorem sub_ptr_self_add_mul_112 (ptr : BitVec 64) (k : Nat) :
    (ptr + BitVec.ofNat 64 (k * 112)) - ptr = BitVec.ofNat 64 (k * 112) := by
  bv_lin

theorem add_one_beq_zero_of_lt_pow63 {c : BitVec 64} (hlt : c.toNat < 2 ^ 63) :
    (c + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hc : c = 0xffffffffffffffff#64 := by
    change c = 0#64 - 1#64
    rw [← heq]
    bv_omega
  rw [hc] at hlt
  change 0xffffffffffffffff < 2 ^ 63 at hlt
  omega

theorem ult_cap_ofNat_of_le {k : Nat} {cap : BitVec 64}
    (hle : k ≤ cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    BitVec.ult cap (BitVec.ofNat 64 k) = false := by
  have hk64 : k < 18446744073709551616 := by omega
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

/-! ## Separation-Logic Bridges for `FromPb` -/

def toChainEpochDirectionGhost (g : EpochDirectionPBGhost) : ChainEpochDirectionGhost :=
  { next := ⟨g.next.cap, g.next.ptr⟩
    prev := ⟨g.prev.cap, g.prev.ptr⟩ }

def toChainEpochGhost (g : ChainEpochPBGhost) : ChainEpochGhost :=
  { send := toChainEpochDirectionGhost g.send
    recv := toChainEpochDirectionGhost g.recv }

theorem epochDirectionPBAt_eq_chainEpochDirectionAt (A : RustAlloc)
    (g : EpochDirectionPBGhost) (a : BitVec 64) (d : EpochDirectionPB) :
    epochDirectionPBAt A g a d =
      chainEpochDirectionAt A a (toChainEpochDirectionGhost g)
        { ctr := d.ctr, next := d.next, prev := { data := d.prev } } := rfl

theorem chainEpochPBAt_some_some_eq_chainEpochAt (A : RustAlloc)
    (g : ChainEpochPBGhost) (a : BitVec 64) (s r : EpochDirectionPB) :
    chainEpochPBAt A (g, { send := some s, recv := some r }) a =
      chainEpochAt A (toChainEpochGhost g,
        { send := { ctr := s.ctr, next := s.next, prev := { data := s.prev } }
          recv := { ctr := r.ctr, next := r.next, prev := { data := r.prev } } }) a := rfl

/-- `arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links)` entails the unpinned
    `arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 ptr links`
    expected by `dropProtoEpochSliceSpec`. -/
theorem arrayAt_chainEpochPBAt_entails_protoRepr (A : RustAlloc) :
    ∀ (epochs : List ChainEpochPBGhost) (links : List ChainEpochPB) (ptr : BitVec 64),
      epochs.length = links.length →
      arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links) ⊢
        arrayAt (fun ep addr => CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A addr ep)
          112 ptr links
  | [], [], _, _ => Entails.refl _
  | _ :: _, [], _, h => by cases h
  | [], _ :: _, _, h => by cases h
  | g :: gs, ep :: eps, ptr, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    dsimp only [List.zip_cons_cons, arrayAt]
    have hhead : chainEpochPBAt A (g, ep) ptr ⊢
        CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A ptr ep := by
      rw [chainEpochPBAt_protoRepr_eq_exists A ptr ep]
      exact Entails.sepExists_intro (P := fun g' => chainEpochPBAt A (g', ep) ptr) g
    exact sepConj_mono hhead (arrayAt_chainEpochPBAt_entails_protoRepr A gs eps (ptr + 112#64) hlen)

/-- `arrayAt (chainEpochAt A) 112 ptr (epochs.zip links)` entails the unpinned
    `arrayAt (chainEpoch A) 112 ptr links` expected by `dropChainEpochSliceSpec`. -/
theorem arrayAt_chainEpochAt_entails_unpinned (A : RustAlloc) :
    ∀ (epochs : List ChainEpochGhost) (links : List ChainEpoch) (ptr : BitVec 64),
      epochs.length = links.length →
      arrayAt (chainEpochAt A) 112 ptr (epochs.zip links) ⊢
        arrayAt (chainEpoch A) 112 ptr links
  | [], [], _, _ => Entails.refl _
  | _ :: _, [], _, h => by cases h
  | [], _ :: _, _, h => by cases h
  | g :: gs, ep :: eps, ptr, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    dsimp only [List.zip_cons_cons, arrayAt]
    exact sepConj_mono (chainEpochAt_entails_chainEpoch A (g, ep) ptr)
      (arrayAt_chainEpochAt_entails_unpinned A gs eps (ptr + 112#64) hlen)

private theorem arrayAt_append_eq {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    ∀ (xs ys : List α) (ptr : BitVec 64),
      arrayAt elem stride ptr (xs ++ ys) =
        arrayAt elem stride ptr xs ∗
          arrayAt elem stride (ptr + BitVec.ofNat 64 (xs.length * stride)) ys
  | [], ys, ptr => by
    dsimp only [List.nil_append, List.length_nil, arrayAt]
    rw [Nat.zero_mul, BitVec.add_zero, emp_sepConj]
  | x :: xs, ys, ptr => by
    dsimp only [List.cons_append, arrayAt]
    rw [arrayAt_append_eq elem stride xs ys (ptr + BitVec.ofNat 64 stride), sepConj_assoc]
    have hadj : ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 (xs.length * stride) =
        ptr + BitVec.ofNat 64 ((x :: xs).length * stride) := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
      bv_omega
    rw [hadj]

theorem arrayAt_chainEpochAt_snoc (A : RustAlloc) (ptr : BitVec 64)
    (prefG : List ChainEpochGhost) (pref : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (hlen : prefG.length = pref.length) :
    arrayAt (chainEpochAt A) 112 ptr (prefG.zip pref) ∗
      chainEpochAt A (g, ep) (ptr + BitVec.ofNat 64 (pref.length * 112)) ⊢
      arrayAt (chainEpochAt A) 112 ptr ((prefG ++ [g]).zip (pref ++ [ep])) := by
  have hzip : (prefG ++ [g]).zip (pref ++ [ep]) = prefG.zip pref ++ [(g, ep)] :=
    List.zip_append hlen
  have hzlen : (prefG.zip pref).length = pref.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  refine Entails.of_eq ?_
  rw [hzip, arrayAt_append_eq, hzlen]
  dsimp only [arrayAt]
  rw [sepConj_emp]

/-! ## `chainPBAt` Unpacking and Raw Heap Helpers -/

/-- All 80 bytes of `ChainPB` header cells at `a`. -/
def chainPBHeadersAt (a : BitVec 64) (g : ChainPBGhost) (pb : ChainPB) : SepProp :=
  (a ↦₆₄ g.linksCap) ∗
  ((a + 8#64) ↦₆₄ g.linksPtr) ∗
  ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.links.length) ∗
  ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
  ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
  ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
  ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
  ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
  optChainParamsPBAt (a + 64#64) pb.params ∗
  ((a + 76#64) ↦₃₂ pb.direction)

theorem optChainParamsPBAt_entails_memRegion_12 (a : BitVec 64) (opt : Option ChainParamsPB) :
    optChainParamsPBAt a opt ⊢ memRegion a 12 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 8) (b' := a + 4#64) rfl rfl (by decide)]
  cases opt with
  | none =>
    exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion a 0#32)
  | some cp =>
    rw [ProofLib.memRegion_split' (b := a + 4#64) (n := 4) (k := 4)
      (b' := a + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion a 1#32)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion (a + 4#64) cp.maxJump)
        (ProofLib.pointsTo32_entails_memRegion (a + 8#64) cp.maxOooKeys))

theorem chainPBHeadersAt_entails_memRegion_80 (a : BitVec 64) (g : ChainPBGhost) (pb : ChainPB) :
    chainPBHeadersAt a g pb ⊢ memRegion a 80 := by
  unfold chainPBHeadersAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 12) (k := 4) (b' := a + 76#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (optChainParamsPBAt_entails_memRegion_12 _ _)
                    (ProofLib.pointsTo32_entails_memRegion _ _)))))))))

/-- Raw allocation + spare capacity for a stride-112 `Vec` buffer at `ptr` of length `n`. -/
def linksRawAllocAt (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * 112) 8 ∗
    memRegion (ptr + BitVec.ofNat 64 (n * 112)) ((cap.toNat - n) * 112)

/-- Heap buffer of a `Vec<u8>` at `(cap, ptr)` holding `bs`. -/
def vecU8BufAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8BufAt_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    vecU8BufAt A cap ptr bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold vecU8BufAt vecCapPtrDealloc
  by_cases hc : cap = 0
  · subst hc
    simp only [↓reduceIte, beq_self_eq_true]
    exact Entails.refl _
  · have hcb : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
    simp only [hc, hcb, ↓reduceIte, Bool.false_eq_true]
    refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
    have hsplit := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat) (n := bs.length)
      (k := cap.toNat - bs.length) (b' := ptr + BitVec.ofNat 64 bs.length)
      (by omega) rfl (by omega)
    exact Entails.of_eq hsplit.symm

theorem linksRawAllocAt_combine_memRegion (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    memRegion ptr (n * 112) ∗ linksRawAllocAt A cap ptr n ⊢
      if (cap == 0#64) = true then emp
      else A.live ptr (cap.toNat * 112) 8 ∗ memRegion ptr (cap.toNat * 112) := by
  unfold linksRawAllocAt
  by_cases hc : cap = 0
  · subst hc
    have hn0 : n = 0 := by simpa using hle
    subst hn0
    simp only [Nat.zero_mul, memRegion_zero, ↓reduceIte, beq_self_eq_true, sepConj_emp]
    exact Entails.refl _
  · have hcb : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
    simp only [hc, hcb, ↓reduceIte, Bool.false_eq_true]
    rw [← sepConj_assoc, sepConj_comm (memRegion ptr (n * 112)), sepConj_assoc]
    refine sepConj_mono_right ?_
    have hsplit := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat * 112) (n := n * 112)
      (k := (cap.toNat - n) * 112) (b' := ptr + BitVec.ofNat 64 (n * 112))
      (by rw [← Nat.add_mul, Nat.add_sub_of_le hle]) rfl (by omega)
    exact Entails.of_eq hsplit.symm

theorem memRegion_join_three_112 (ptr : BitVec 64) (a b : Nat) (h : (a + 1 + b) * 112 < 2 ^ 63) :
    memRegion ptr (a * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 (a * 112)) 112 ∗
      memRegion (ptr + BitVec.ofNat 64 ((a + 1) * 112)) (b * 112) ⊢
      memRegion ptr ((a + 1 + b) * 112) := by
  have h1 := ProofLib.memRegion_split' (b := ptr) (N := (a + 1) * 112) (n := a * 112) (k := 112)
    (b' := ptr + BitVec.ofNat 64 (a * 112))
    (show (a + 1) * 112 = a * 112 + 112 by rw [Nat.add_mul, Nat.one_mul]) rfl (by omega)
  have h2 := ProofLib.memRegion_split' (b := ptr) (N := (a + 1 + b) * 112) (n := (a + 1) * 112) (k := b * 112)
    (b' := ptr + BitVec.ofNat 64 ((a + 1) * 112))
    (show (a + 1 + b) * 112 = (a + 1) * 112 + b * 112 by rw [Nat.add_mul]) rfl (by omega)
  refine Entails.of_eq ?_
  rw [← sepConj_assoc, ← h1, ← h2]

theorem chainPBAt_unpack (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    chainPBAt A g a pb ⊢
      ⌜g.epochs.length = pb.links.length ∧
        pb.links.length ≤ g.linksCap.toNat ∧
        g.linksCap.toNat * 112 < 2 ^ 63 ∧
        g.linksPtr ≠ 0 ∧
        pb.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
        g.nextRoot.cap.toNat < 2 ^ 63 ∧
        g.nextRoot.ptr ≠ 0⌝ ∗
      chainPBHeadersAt a g pb ∗
      arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
      linksRawAllocAt A g.linksCap g.linksPtr pb.links.length ∗
      vecU8BufAt A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot := by
  unfold chainPBAt vecAt vecBuf vecU8At vecHeader chainPBHeadersAt linksRawAllocAt vecU8BufAt
    chainEpochSize chainEpochAlign
  refine Entails.pure_left fun hlen => ?_
  have hzlen : (g.epochs.zip pb.links).length = pb.links.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  rw [hzlen]
  rw [show
    ((a ↦₆₄ g.linksCap ∗ (a + 8#64) ↦₆₄ g.linksPtr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.links.length) ∗
      ⌜pb.links.length ≤ g.linksCap.toNat ∧
          g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0⌝ ∗
      if g.linksCap = 0 then emp
      else
        A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
          arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
          memRegion (g.linksPtr + BitVec.ofNat 64 (pb.links.length * 112))
            ((g.linksCap.toNat - pb.links.length) * 112)) ∗
    (((a + 24#64) ↦₆₄ g.nextRoot.cap ∗ (a + 24#64 + 8#64) ↦₆₄ g.nextRoot.ptr ∗
        (a + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ⌜pb.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
          g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
      if g.nextRoot.cap = 0 then emp
      else
        A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ pb.nextRoot ∗
          memRegion (g.nextRoot.ptr + BitVec.ofNat 64 pb.nextRoot.length)
            (g.nextRoot.cap.toNat - pb.nextRoot.length)) ∗
    (a + 48#64) ↦₆₄ pb.currentEpoch ∗ (a + 56#64) ↦₆₄ pb.sendEpoch ∗
    optChainParamsPBAt (a + 64#64) pb.params ∗ (a + 76#64) ↦₃₂ pb.direction =
    ⌜pb.links.length ≤ g.linksCap.toNat ∧
        g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0⌝ ∗
    ⌜pb.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
        g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
    ((a ↦₆₄ g.linksCap ∗ (a + 8#64) ↦₆₄ g.linksPtr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.links.length ∗
        (a + 24#64) ↦₆₄ g.nextRoot.cap ∗ (a + 32#64) ↦₆₄ g.nextRoot.ptr ∗
        (a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length ∗
        (a + 48#64) ↦₆₄ pb.currentEpoch ∗ (a + 56#64) ↦₆₄ pb.sendEpoch ∗
        optChainParamsPBAt (a + 64#64) pb.params ∗ (a + 76#64) ↦₃₂ pb.direction) ∗
      (if g.linksCap = 0 then emp
       else
         A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
           arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
           memRegion (g.linksPtr + BitVec.ofNat 64 (pb.links.length * 112))
             ((g.linksCap.toNat - pb.links.length) * 112)) ∗
      (if g.nextRoot.cap = 0 then emp
       else
         A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ pb.nextRoot ∗
           memRegion (g.nextRoot.ptr + BitVec.ofNat 64 pb.nextRoot.length)
             (g.nextRoot.cap.toNat - pb.nextRoot.length))) by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl]
  refine Entails.pure_left fun ⟨hl_le, hl_lt, hl_ne⟩ => ?_
  refine Entails.pure_left fun ⟨hn_le, hn_lt, hn_ne⟩ => ?_
  refine Entails.pure_right ⟨hlen, hl_le, hl_lt, hl_ne, hn_le, hn_lt, hn_ne⟩ ?_
  have hlinks :
      (if g.linksCap = 0 then emp
       else
         A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
           arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
           memRegion (g.linksPtr + BitVec.ofNat 64 (pb.links.length * 112))
             ((g.linksCap.toNat - pb.links.length) * 112)) =
      (arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
        if g.linksCap = 0 then emp
        else
          A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
            memRegion (g.linksPtr + BitVec.ofNat 64 (pb.links.length * 112))
              ((g.linksCap.toNat - pb.links.length) * 112)) := by
    by_cases hc : g.linksCap = 0
    · rw [hc] at hl_le ⊢
      have hnil : pb.links = [] := List.eq_nil_of_length_eq_zero (by simpa using hl_le)
      have henil : g.epochs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hnil]; rfl)
      rw [hnil, henil]
      simp only [List.zip_nil_right, arrayAt, ↓reduceIte, sepConj_emp]
    · simp only [hc, ↓reduceIte]
      ac_rfl
  rw [hlinks]
  exact Entails.of_eq (by ac_rfl)

/-! ## Loop-Element (`chainEpochPBAt`) Unpack, Repack, and Dealloc Lemmas -/

def epochDirPBCellsAt (a : BitVec 64) (g : EpochDirectionPBGhost) (d : EpochDirectionPB) : SepProp :=
  (a ↦₆₄ g.next.cap) ∗
  ((a + 8#64) ↦₆₄ g.next.ptr) ∗
  ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
  ((a + 24#64) ↦₆₄ g.prev.cap) ∗
  ((a + 32#64) ↦₆₄ g.prev.ptr) ∗
  ((a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
  ((a + 48#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 52#64) 4

theorem epochDirPBCellsAt_entails_memRegion_56 (a : BitVec 64) (g : EpochDirectionPBGhost)
    (d : EpochDirectionPB) :
    epochDirPBCellsAt a g d ⊢ memRegion a 56 := by
  unfold epochDirPBCellsAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 4) (k := 4) (b' := a + 52#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)))))))

theorem optEpochDirectionPBAt_none_unpack (A : RustAlloc) (g : EpochDirectionPBGhost)
    (a : BitVec 64) :
    optEpochDirectionPBAt A g a none =
      (∃∗ u1 : BitVec 64, (a + 8#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (a + 24#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (a + 32#64) ↦₆₄ u4) ∗
      (a ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (a + 40#64) 16 := by
  dsimp only [optEpochDirectionPBAt, CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBPinnedAt]
  change (a ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 8#64) 48 = _
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64)]
  ac_rfl

theorem optEpochDirectionPB_none_cells_entails_memRegion_56 (a u0 u1 u2 u3 u4 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
      ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ memRegion (a + 40#64) 16 ⊢
      memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))

theorem optEpochDirectionPBAt_some_unpack (A : RustAlloc) (g : EpochDirectionPBGhost)
    (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A g a (some d) ⊢
      ⌜d.next.length ≤ g.next.cap.toNat ∧
        g.next.cap.toNat < 2 ^ 63 ∧
        g.next.ptr ≠ 0 ∧
        d.prev.length ≤ g.prev.cap.toNat ∧
        g.prev.cap.toNat < 2 ^ 63 ∧
        g.prev.ptr ≠ 0⌝ ∗
      epochDirPBCellsAt a g d ∗
      vecU8BufAt A g.next.cap g.next.ptr d.next ∗
      vecU8BufAt A g.prev.cap g.prev.ptr d.prev := by
  dsimp only [optEpochDirectionPBAt, CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBPinnedAt,
    CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBPinnedAt]
  unfold vecU8At vecHeader epochDirPBCellsAt vecU8BufAt
  rw [show
    ((a ↦₆₄ g.next.cap ∗ (a + 8#64) ↦₆₄ g.next.ptr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      ⌜d.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      if g.next.cap = 0 then emp
      else
        A.live g.next.ptr g.next.cap.toNat 1 ∗ g.next.ptr ↦ₛ d.next ∗
          memRegion (g.next.ptr + BitVec.ofNat 64 d.next.length)
            (g.next.cap.toNat - d.next.length)) ∗
    (((a + 24#64) ↦₆₄ g.prev.cap ∗ (a + 24#64 + 8#64) ↦₆₄ g.prev.ptr ∗
        (a + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
      ⌜d.prev.length ≤ g.prev.cap.toNat ∧ g.prev.cap.toNat < 2 ^ 63 ∧ g.prev.ptr ≠ 0⌝ ∗
      if g.prev.cap = 0 then emp
      else
        A.live g.prev.ptr g.prev.cap.toNat 1 ∗ g.prev.ptr ↦ₛ d.prev ∗
          memRegion (g.prev.ptr + BitVec.ofNat 64 d.prev.length)
            (g.prev.cap.toNat - d.prev.length)) ∗
    (a + 48#64) ↦₃₂ d.ctr ∗ memRegion (a + 52#64) 4 =
    ⌜d.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
    ⌜d.prev.length ≤ g.prev.cap.toNat ∧ g.prev.cap.toNat < 2 ^ 63 ∧ g.prev.ptr ≠ 0⌝ ∗
    ((a ↦₆₄ g.next.cap ∗ (a + 8#64) ↦₆₄ g.next.ptr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length ∗
        (a + 24#64) ↦₆₄ g.prev.cap ∗ (a + 32#64) ↦₆₄ g.prev.ptr ∗
        (a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length ∗
        (a + 48#64) ↦₃₂ d.ctr ∗ memRegion (a + 52#64) 4) ∗
      (if g.next.cap = 0 then emp
       else
         A.live g.next.ptr g.next.cap.toNat 1 ∗ g.next.ptr ↦ₛ d.next ∗
           memRegion (g.next.ptr + BitVec.ofNat 64 d.next.length)
             (g.next.cap.toNat - d.next.length)) ∗
      (if g.prev.cap = 0 then emp
       else
         A.live g.prev.ptr g.prev.cap.toNat 1 ∗ g.prev.ptr ↦ₛ d.prev ∗
           memRegion (g.prev.ptr + BitVec.ofNat 64 d.prev.length)
             (g.prev.cap.toNat - d.prev.length))) by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl]
  refine Entails.pure_left fun ⟨hn1, hn2, hn3⟩ => ?_
  refine Entails.pure_left fun ⟨hp1, hp2, hp3⟩ => ?_
  exact Entails.pure_right ⟨hn1, hn2, hn3, hp1, hp2, hp3⟩ (Entails.refl _)

theorem epochDirPBCellsAt_repack_ced (A : RustAlloc) (a : BitVec 64)
    (g : EpochDirectionPBGhost) (d : EpochDirectionPB)
    (hn1 : d.next.length ≤ g.next.cap.toNat) (hn2 : g.next.cap.toNat < 2 ^ 63) (hn3 : g.next.ptr ≠ 0)
    (hp1 : d.prev.length ≤ g.prev.cap.toNat) (hp2 : g.prev.cap.toNat < 2 ^ 63) (hp3 : g.prev.ptr ≠ 0) :
    epochDirPBCellsAt a g d ∗
      vecU8BufAt A g.next.cap g.next.ptr d.next ∗
      vecU8BufAt A g.prev.cap g.prev.ptr d.prev ⊢
      chainEpochDirectionAt A a (toChainEpochDirectionGhost g)
        { ctr := d.ctr, next := d.next, prev := { data := d.prev } } := by
  unfold epochDirPBCellsAt vecU8BufAt chainEpochDirectionAt keyHistoryAt vecU8At vecHeader
    toChainEpochDirectionGhost
  dsimp only
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [show
    ((a ↦₆₄ g.next.cap ∗ (a + 8#64) ↦₆₄ g.next.ptr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      ⌜d.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      if g.next.cap = 0 then emp
      else
        A.live g.next.ptr g.next.cap.toNat 1 ∗ g.next.ptr ↦ₛ d.next ∗
          memRegion (g.next.ptr + BitVec.ofNat 64 d.next.length)
            (g.next.cap.toNat - d.next.length)) ∗
    (((a + 24#64) ↦₆₄ g.prev.cap ∗ (a + 32#64) ↦₆₄ g.prev.ptr ∗
        (a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
      ⌜d.prev.length ≤ g.prev.cap.toNat ∧ g.prev.cap.toNat < 2 ^ 63 ∧ g.prev.ptr ≠ 0⌝ ∗
      if g.prev.cap = 0 then emp
      else
        A.live g.prev.ptr g.prev.cap.toNat 1 ∗ g.prev.ptr ↦ₛ d.prev ∗
          memRegion (g.prev.ptr + BitVec.ofNat 64 d.prev.length)
            (g.prev.cap.toNat - d.prev.length)) ∗
    (a + 48#64) ↦₃₂ d.ctr ∗ memRegion (a + 52#64) 4 =
    ⌜d.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
    ⌜d.prev.length ≤ g.prev.cap.toNat ∧ g.prev.cap.toNat < 2 ^ 63 ∧ g.prev.ptr ≠ 0⌝ ∗
    ((a ↦₆₄ g.next.cap ∗ (a + 8#64) ↦₆₄ g.next.ptr ∗
        (a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length ∗
        (a + 24#64) ↦₆₄ g.prev.cap ∗ (a + 32#64) ↦₆₄ g.prev.ptr ∗
        (a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length ∗
        (a + 48#64) ↦₃₂ d.ctr ∗ memRegion (a + 52#64) 4) ∗
      (if g.next.cap = 0 then emp
       else
         A.live g.next.ptr g.next.cap.toNat 1 ∗ g.next.ptr ↦ₛ d.next ∗
           memRegion (g.next.ptr + BitVec.ofNat 64 d.next.length)
             (g.next.cap.toNat - d.next.length)) ∗
      (if g.prev.cap = 0 then emp
       else
         A.live g.prev.ptr g.prev.cap.toNat 1 ∗ g.prev.ptr ↦ₛ d.prev ∗
           memRegion (g.prev.ptr + BitVec.ofNat 64 d.prev.length)
             (g.prev.cap.toNat - d.prev.length))) by ac_rfl]
  exact Entails.pure_right ⟨hn1, hn2, hn3⟩ (Entails.pure_right ⟨hp1, hp2, hp3⟩ (Entails.refl _))

theorem memRegion_56_56_to_112 (cur : BitVec 64) :
    memRegion cur 56 ∗ memRegion (cur + 56#64) 56 ⊢ memRegion cur 112 := by
  exact Entails.of_eq (ProofLib.memRegion_split' (b := cur) (n := 56) (k := 56)
    (b' := cur + 56#64) rfl rfl (by decide)).symm

/-! ## Output Slot (`88` Bytes) and `chainResultAt` Packing -/

theorem memRegion_88_words4_rest (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      memRegion (out + 32#64) 56 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 80)
      (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 72)
      (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64)
      (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 56)
      (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

theorem memRegion_56_split_chainTail (out : BitVec 64) :
    memRegion (out + 32#64) 56 =
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (out + 56#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (out + 64#64) ↦₆₄ d8) ∗
      (∃∗ p0 : BitVec 32, (out + 72#64) ↦₃₂ p0) ∗
      (∃∗ p1 : BitVec 32, (out + 76#64) ↦₃₂ p1) ∗
      (∃∗ p2 : BitVec 32, (out + 80#64) ↦₃₂ p2) ∗
      memRegion (out + 84#64) 4 := by
  rw [ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 48)
      (b' := out + 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 40#64) (n := 8) (k := 40)
      (b' := out + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 48#64) (n := 8) (k := 32)
      (b' := out + 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 56#64) (n := 8) (k := 24)
      (b' := out + 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 64#64) (n := 8) (k := 16)
      (b' := out + 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 72#64) (n := 4) (k := 12)
      (b' := out + 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 76#64) (n := 4) (k := 8)
      (b' := out + 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 80#64) (n := 4) (k := 4)
      (b' := out + 84#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (out + 32#64),
    ProofLib.memRegion_eight (out + 40#64),
    ProofLib.memRegion_eight (out + 48#64),
    ProofLib.memRegion_eight (out + 56#64),
    ProofLib.memRegion_eight (out + 64#64),
    ProofLib.memRegion_four (out + 72#64),
    ProofLib.memRegion_four (out + 76#64),
    ProofLib.memRegion_four (out + 80#64)]

theorem chainErrorAt_stateDecode_of_lowByte_zero (A : RustAlloc) (out w1 w2 w3 : BitVec 64)
    (h0 : w1.extractLsb' 0 8 = 0#8) :
    (out ↦₆₄ 0xffffffffffffffff#64) ∗
      ((out + 8#64) ↦₆₄ w1) ∗
      ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ w3) ∗
      memRegion (out + 32#64) 56 ⊢
      chainResultAt A out (.error .stateDecode) := by
  dsimp only [chainResultAt, chainErrorAt]
  refine Entails.sepExists_right (w2 ++ w1) (Entails.sepExists_right w3 ?_)
  have htag : BitVec.truncate 8 (w2 ++ w1) = spqrErrorTag .stateDecode := by
    have htr : BitVec.truncate 8 (w2 ++ w1) = w1.extractLsb' 0 8 := by bv_kernel
    rw [htr, h0]
    rfl
  refine Entails.pure_right htag ?_
  unfold pointsTo128 noneCap
  have hlo : (w2 ++ w1).extractLsb' 0 64 = w1 := by bv_kernel
  have hhi : (w2 ++ w1).extractLsb' 64 64 = w2 := by bv_kernel
  rw [hlo, hhi]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem arrayAt_linksRawAllocAt_entails_vecDequeRingBuf (A : RustAlloc)
    (lcap lptr : BitVec 64) (epochs' : List ChainEpochGhost) (links : List ChainEpoch)
    (hlen : epochs'.length = links.length)
    (hl_le : links.length ≤ lcap.toNat)
    (hl_lt : lcap.toNat * 112 < 2 ^ 63)
    (hl_ne : lptr ≠ 0) :
    arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links) ∗
      linksRawAllocAt A lcap lptr links.length ⊢
      vecDequeRingBuf A 112 8 (chainEpochAt A) lcap lptr 0#64 (epochs'.zip links) := by
  unfold vecDequeRingBuf linksRawAllocAt
  have hzlen : (epochs'.zip links).length = links.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hp : (epochs'.zip links).length ≤ lcap.toNat ∧ lcap.toNat * 112 < 2 ^ 63 ∧ lptr ≠ 0 ∧
      (if lcap = 0 then (0#64 : BitVec 64) = 0 else (0#64 : BitVec 64).toNat < lcap.toNat) := by
    rw [hzlen]
    refine ⟨hl_le, hl_lt, hl_ne, ?_⟩
    by_cases hc : lcap = 0
    · simp [hc]
    · simp only [hc, ↓reduceIte, BitVec.toNat_zero]
      exact Nat.pos_of_ne_zero fun hz => hc (BitVec.eq_of_toNat_eq (by simpa using hz))
  refine Entails.pure_right hp ?_
  by_cases hc : lcap = 0
  · rw [hc] at hl_le ⊢
    have hnil : links = [] := List.eq_nil_of_length_eq_zero (by simpa using hl_le)
    have henil : epochs' = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hnil]; rfl)
    rw [hnil, henil]
    change emp ∗ emp ⊢ emp
    rw [sepConj_emp]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links)),
      sepConj_assoc]
    refine sepConj_mono_right ?_
    have hslots_split :
        vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat (0#64).toNat lptr (epochs'.zip links)
          0 lcap.toNat =
        vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat 0 lptr (epochs'.zip links)
          0 links.length ∗
        vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat 0 lptr (epochs'.zip links)
          (0 + links.length) (lcap.toNat - links.length) := by
      change vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat 0 lptr (epochs'.zip links)
          0 lcap.toNat = _
      rw [← vecDequeSlotsAt_add]
      congr 1
      omega
    have hslots1 :
        vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat 0 lptr (epochs'.zip links)
          0 links.length =
        arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links) := by
      rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 lcap.toNat 0 lptr
        (epochs'.zip links) 0 0 links.length (by omega)]
      · have htake : ((epochs'.zip links).drop 0).take links.length = epochs'.zip links := by
          rw [List.drop_zero, ← hzlen, List.take_length]
        rw [Nat.zero_mul, htake, BitVec.add_zero]
      · intro k _
        simp [vecDequeLogIdx]
    have hslots2 :
        memRegion (lptr + BitVec.ofNat 64 (links.length * 112))
          ((lcap.toNat - links.length) * 112) ⊢
        vecDequeSlotsAt (chainEpochAt A) 112 lcap.toNat 0 lptr (epochs'.zip links)
          (0 + links.length) (lcap.toNat - links.length) := by
      rw [Nat.zero_add]
      refine memRegion_entails_vecDequeSlotsAt_uninit (chainEpochAt A) 112 lcap.toNat 0 lptr
        (epochs'.zip links) links.length (lcap.toNat - links.length) (by omega) ?_
      intro k _
      simp only [vecDequeLogIdx, Nat.zero_le, ↓reduceIte, Nat.sub_zero, hzlen]
      omega
    rw [hslots_split, hslots1]
    exact sepConj_mono_right hslots2

theorem chainResultAt_ok_pack (A : RustAlloc) (out : BitVec 64)
    (lcap lptr ncap nptr : BitVec 64)
    (epochs' : List ChainEpochGhost) (links : List ChainEpoch)
    (nextRoot : Bytes) (curEp sendEp : BitVec 64)
    (params : ChainParamsPB) (dir : Direction)
    (hlen : epochs'.length = links.length)
    (hl_le : links.length ≤ lcap.toNat)
    (hl_lt : lcap.toNat * 112 < 2 ^ 63)
    (hl_ne : lptr ≠ 0)
    (hn_le : nextRoot.length ≤ ncap.toNat)
    (hn_lt : ncap.toNat < 2 ^ 63)
    (hn_ne : nptr ≠ 0) :
    (out ↦₆₄ lcap) ∗
      ((out + 8#64) ↦₆₄ lptr) ∗
      ((out + 16#64) ↦₆₄ 0#64) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
      ((out + 32#64) ↦₆₄ ncap) ∗
      ((out + 40#64) ↦₆₄ nptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ curEp) ∗
      ((out + 64#64) ↦₆₄ sendEp) ∗
      ((out + 72#64) ↦₃₂ params.maxJump) ∗
      ((out + 76#64) ↦₃₂ params.maxOooKeys) ∗
      ((out + 80#64) ↦₃₂ dir.toI32) ∗
      memRegion (out + 84#64) 4 ∗
      arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links) ∗
      linksRawAllocAt A lcap lptr links.length ∗
      vecU8BufAt A ncap nptr nextRoot ⊢
      chainResultAt A out (.ok {
        dir := dir
        currentEpoch := curEp
        sendEpoch := sendEp
        nextRoot := nextRoot
        links := links
        params := params
      }) := by
  dsimp only [chainResultAt, chainRepr]
  refine Entails.sepExists_right ⟨lcap, lptr, 0#64, epochs', ⟨ncap, nptr⟩⟩ ?_
  unfold chainAt vecDequeAt vecDequeHeader vecU8At vecHeader chainParamsAt directionAt vecU8BufAt
  dsimp only [chainEpochSize, chainEpochAlign]
  have hzlen : (epochs'.zip links).length = links.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  rw [hzlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.pure_right hlen ?_
  have hrb := arrayAt_linksRawAllocAt_entails_vecDequeRingBuf A lcap lptr epochs' links
    hlen hl_le hl_lt hl_ne
  have hn :
      ((out + 32#64) ↦₆₄ ncap ∗ (out + 40#64) ↦₆₄ nptr ∗
        (out + 48#64) ↦₆₄ BitVec.ofNat 64 nextRoot.length) ∗
        (if ncap = 0 then emp
         else
           A.live nptr ncap.toNat 1 ∗ nptr ↦ₛ nextRoot ∗
             memRegion (nptr + BitVec.ofNat 64 nextRoot.length) (ncap.toNat - nextRoot.length)) ⊢
      ((out + 32#64) ↦₆₄ ncap ∗ (out + 40#64) ↦₆₄ nptr ∗
        (out + 48#64) ↦₆₄ BitVec.ofNat 64 nextRoot.length) ∗
        ⌜nextRoot.length ≤ ncap.toNat ∧ ncap.toNat < 2 ^ 63 ∧ nptr ≠ 0⌝ ∗
        if ncap = 0 then emp
        else
          A.live nptr ncap.toNat 1 ∗ nptr ↦ₛ nextRoot ∗
            memRegion (nptr + BitVec.ofNat 64 nextRoot.length) (ncap.toNat - nextRoot.length) := by
    exact sepConj_mono_right (Entails.pure_right ⟨hn_le, hn_lt, hn_ne⟩ (Entails.refl _))
  rw [show
    (out ↦₆₄ lcap) ∗ ((out + 8#64) ↦₆₄ lptr) ∗ ((out + 16#64) ↦₆₄ 0#64) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
      ((out + 32#64) ↦₆₄ ncap) ∗ ((out + 40#64) ↦₆₄ nptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ curEp) ∗ ((out + 64#64) ↦₆₄ sendEp) ∗
      ((out + 72#64) ↦₃₂ params.maxJump) ∗ ((out + 76#64) ↦₃₂ params.maxOooKeys) ∗
      ((out + 80#64) ↦₃₂ dir.toI32) ∗ memRegion (out + 84#64) 4 ∗
      arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links) ∗
      linksRawAllocAt A lcap lptr links.length ∗
      (if ncap = 0 then emp
       else
         A.live nptr ncap.toNat 1 ∗ nptr ↦ₛ nextRoot ∗
           memRegion (nptr + BitVec.ofNat 64 nextRoot.length) (ncap.toNat - nextRoot.length)) =
    ((out ↦₆₄ lcap ∗ (out + 8#64) ↦₆₄ lptr ∗ (out + 16#64) ↦₆₄ 0#64 ∗
        (out + 24#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
      (arrayAt (chainEpochAt A) 112 lptr (epochs'.zip links) ∗
        linksRawAllocAt A lcap lptr links.length)) ∗
    (((out + 32#64) ↦₆₄ ncap ∗ (out + 40#64) ↦₆₄ nptr ∗
        (out + 48#64) ↦₆₄ BitVec.ofNat 64 nextRoot.length) ∗
      (if ncap = 0 then emp
       else
         A.live nptr ncap.toNat 1 ∗ nptr ↦ₛ nextRoot ∗
           memRegion (nptr + BitVec.ofNat 64 nextRoot.length) (ncap.toNat - nextRoot.length))) ∗
    (out + 56#64) ↦₆₄ curEp ∗ (out + 64#64) ↦₆₄ sendEp ∗
    ((out + 72#64) ↦₃₂ params.maxJump ∗ (out + 76#64) ↦₃₂ params.maxOooKeys) ∗
    (out + 80#64) ↦₃₂ dir.toI32 ∗ memRegion (out + 84#64) 4 by ac_rfl]
  exact sepConj_mono (sepConj_mono_right hrb) (sepConj_mono_left hn)

/-! ## Stack Frame Split and Join (`chainFromPbStackX = 16800` B) -/

theorem stackAt_chainFromPb_split (sp : BitVec 64) :
    stackAt sp chainFromPbStackX =
      memRegion (sp - 16800#64) 12480 ∗
      stackAt (sp - 192#64) dropStack32 ∗
      (∃∗ s00 : BitVec 64, (sp - 192#64) ↦₆₄ s00) ∗
      (∃∗ s08 : BitVec 64, (sp - 184#64) ↦₆₄ s08) ∗
      (∃∗ s10 : BitVec 64, (sp - 176#64) ↦₆₄ s10) ∗
      (∃∗ s18 : BitVec 64, (sp - 168#64) ↦₆₄ s18) ∗
      (∃∗ s20 : BitVec 64, (sp - 160#64) ↦₆₄ s20) ∗
      memRegion (sp - 152#64) 4 ∗
      (∃∗ s2c : BitVec 32, (sp - 148#64) ↦₃₂ s2c) ∗
      (∃∗ s30 : BitVec 64, (sp - 144#64) ↦₆₄ s30) ∗
      (∃∗ s38 : BitVec 64, (sp - 136#64) ↦₆₄ s38) ∗
      (∃∗ s40 : BitVec 64, (sp - 128#64) ↦₆₄ s40) ∗
      (∃∗ s48 : BitVec 64, (sp - 120#64) ↦₆₄ s48) ∗
      (∃∗ s50 : BitVec 64, (sp - 112#64) ↦₆₄ s50) ∗
      (∃∗ s58 : BitVec 64, (sp - 104#64) ↦₆₄ s58) ∗
      (∃∗ s60 : BitVec 64, (sp - 96#64) ↦₆₄ s60) ∗
      (∃∗ s68 : BitVec 64, (sp - 88#64) ↦₆₄ s68) ∗
      (∃∗ s70 : BitVec 64, (sp - 80#64) ↦₆₄ s70) ∗
      (∃∗ s78 : BitVec 64, (sp - 72#64) ↦₆₄ s78) ∗
      (∃∗ s80 : BitVec 64, (sp - 64#64) ↦₆₄ s80) ∗
      (∃∗ s88 : BitVec 64, (sp - 56#64) ↦₆₄ s88) ∗
      (∃∗ s90 : BitVec 64, (sp - 48#64) ↦₆₄ s90) ∗
      (∃∗ s98 : BitVec 64, (sp - 40#64) ↦₆₄ s98) ∗
      (∃∗ sa0 : BitVec 64, (sp - 32#64) ↦₆₄ sa0) ∗
      (∃∗ sa8 : BitVec 64, (sp - 24#64) ↦₆₄ sa8) ∗
      (∃∗ sb0 : BitVec 64, (sp - 16#64) ↦₆₄ sb0) ∗
      (∃∗ sb8 : BitVec 64, (sp - 8#64) ↦₆₄ sb8) := by
  unfold stackAt
  change memRegion (sp - 16800#64) 16800 =
    memRegion (sp - 16800#64) 12480 ∗
      memRegion (sp - 192#64 - 4128#64) 4128 ∗ _
  have hsub : sp - 192#64 - 4128#64 = sp - 4320#64 := by bv_omega
  rw [hsub,
    ProofLib.memRegion_split' (b := sp - 16800#64) (n := 12480) (k := 4320)
      (b' := sp - 4320#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4320#64) (n := 4128) (k := 192)
      (b' := sp - 192#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 192#64) (n := 8) (k := 184) (b' := sp - 184#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 184#64) (n := 8) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 168#64) (n := 8) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 152) (b' := sp - 152#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 152#64) (n := 4) (k := 148) (b' := sp - 148#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 148#64) (n := 4) (k := 144) (b' := sp - 144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136) (b' := sp - 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 128) (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120) (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 8) (k := 104) (b' := sp - 104#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 104#64) (n := 8) (k := 96) (b' := sp - 96#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72) (b' := sp - 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40) (b' := sp - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32) (b' := sp - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24) (b' := sp - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16) (b' := sp - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8) (b' := sp - 8#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (sp - 192#64),
    ProofLib.memRegion_eight (sp - 184#64),
    ProofLib.memRegion_eight (sp - 176#64),
    ProofLib.memRegion_eight (sp - 168#64),
    ProofLib.memRegion_eight (sp - 160#64),
    ProofLib.memRegion_four (sp - 148#64),
    ProofLib.memRegion_eight (sp - 144#64),
    ProofLib.memRegion_eight (sp - 136#64),
    ProofLib.memRegion_eight (sp - 128#64),
    ProofLib.memRegion_eight (sp - 120#64),
    ProofLib.memRegion_eight (sp - 112#64),
    ProofLib.memRegion_eight (sp - 104#64),
    ProofLib.memRegion_eight (sp - 96#64),
    ProofLib.memRegion_eight (sp - 88#64),
    ProofLib.memRegion_eight (sp - 80#64),
    ProofLib.memRegion_eight (sp - 72#64),
    ProofLib.memRegion_eight (sp - 64#64),
    ProofLib.memRegion_eight (sp - 56#64),
    ProofLib.memRegion_eight (sp - 48#64),
    ProofLib.memRegion_eight (sp - 40#64),
    ProofLib.memRegion_eight (sp - 32#64),
    ProofLib.memRegion_eight (sp - 24#64),
    ProofLib.memRegion_eight (sp - 16#64),
    ProofLib.memRegion_eight (sp - 8#64)]

theorem stackAt_chainFromPb_join (sp : BitVec 64)
    (s00 s08 s10 s18 s20 : BitVec 64) (s2c : BitVec 32)
    (s30 s38 s40 s48 s50 s58 s60 s68 s70 s78 s80 s88 s90 s98 sa0 sa8 sb0 sb8 : BitVec 64) :
    memRegion (sp - 16800#64) 12480 ∗
      stackAt (sp - 192#64) dropStack32 ∗
      ((sp - 192#64) ↦₆₄ s00) ∗
      ((sp - 184#64) ↦₆₄ s08) ∗
      ((sp - 176#64) ↦₆₄ s10) ∗
      ((sp - 168#64) ↦₆₄ s18) ∗
      ((sp - 160#64) ↦₆₄ s20) ∗
      memRegion (sp - 152#64) 4 ∗
      ((sp - 148#64) ↦₃₂ s2c) ∗
      ((sp - 144#64) ↦₆₄ s30) ∗
      ((sp - 136#64) ↦₆₄ s38) ∗
      ((sp - 128#64) ↦₆₄ s40) ∗
      ((sp - 120#64) ↦₆₄ s48) ∗
      ((sp - 112#64) ↦₆₄ s50) ∗
      ((sp - 104#64) ↦₆₄ s58) ∗
      ((sp - 96#64) ↦₆₄ s60) ∗
      ((sp - 88#64) ↦₆₄ s68) ∗
      ((sp - 80#64) ↦₆₄ s70) ∗
      ((sp - 72#64) ↦₆₄ s78) ∗
      ((sp - 64#64) ↦₆₄ s80) ∗
      ((sp - 56#64) ↦₆₄ s88) ∗
      ((sp - 48#64) ↦₆₄ s90) ∗
      ((sp - 40#64) ↦₆₄ s98) ∗
      ((sp - 32#64) ↦₆₄ sa0) ∗
      ((sp - 24#64) ↦₆₄ sa8) ∗
      ((sp - 16#64) ↦₆₄ sb0) ∗
      ((sp - 8#64) ↦₆₄ sb8) ⊢
      stackAt sp chainFromPbStackX := by
  rw [stackAt_chainFromPb_split sp]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_right s00 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s08 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s10 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s18 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s20 (Entails.refl _)) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right s2c (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s30 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s38 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s40 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s48 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s50 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s58 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s60 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s68 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s70 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s78 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s80 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s88 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s90 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s98 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sa0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sa8 (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right sb0 (Entails.refl _))
    (Entails.sepExists_right sb8 (Entails.refl _))

theorem stackAt_chainFromPb_split_allocHook (sp : BitVec 64) :
    stackAt sp chainFromPbStackX =
      memRegion (sp - 16800#64) 12704 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 12704 (by decide)

end CryptoVerification.SpqrV1.ChainProofs
