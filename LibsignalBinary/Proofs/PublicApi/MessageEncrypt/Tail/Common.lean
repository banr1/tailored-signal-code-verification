/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Common Tail Definitions and `SepWP` / `SegExit` Bridges for `MessageEncrypt`
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

/-- `session_message_encrypt_with_stores` (`encryptWithStoresName`) starts at image offset `0x3caf4`
(= 248564). -/
theorem libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff encryptWithStoresName = num% (ls_off% "session_message_encrypt") :=
  (ls_lemma% fnOff "session_message_encrypt")

theorem entryOf_encEntry {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img) :
    encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName := by
  unfold encEntry
  exact entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg
    encryptWithStoresName

open Lean Elab Tactic in
/-- `messageEncrypt_code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "messageEncrypt_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

def words64At : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ words64At (a + 8#64) ws

/-- 48-byte `SignalProtocolError` layout at `a` for an `encrypt` error. -/
def encErrAt (A : RustAlloc) (a : BitVec 64) : ApiError AddrVal Unit → SepProp
  | .protocol p => speAt A (utf8 "encrypt") a p
  | e => apiErrAt A a e

theorem apiEncResultAt_error (A : RustAlloc) (r : BitVec 64) (e : ApiError AddrVal Unit) :
    apiEncResultAt A r (.error e) =
      ((r ↦₆₄ errTag) ∗ encErrAt A (r + 8#64) e ∗ memRegion (r + 56#64) 192) := by
  cases e <;> rfl

/-- Staged 48-byte `SignalProtocolError`: six 64-bit words `ws` plus owned heap assertions `H`. -/
def SpeStaged (A : RustAlloc) (ret : BitVec 64) (e : ApiError AddrVal Unit) (ws : List (BitVec 64))
    (H : SepProp) : Prop :=
  e ≠ .panic ∧ ws.length = 6 ∧ (words64At (ret + 8#64) ws ∗ H ⊢ encErrAt A (ret + 8#64) e)

/-- Staged 248-byte `apiEncResultAt`: four 64-bit header words `ws`, `0xd8` payload bytes `bs`,
and owned heap assertions `H`. -/
def ResStaged (A : RustAlloc) (ret : BitVec 64) (res : Except (ApiError AddrVal Unit) CiphertextMessage)
    (ws : List (BitVec 64)) (bs : List (BitVec 8)) (H : SepProp) : Prop :=
  res ≠ .error .panic ∧ ws.length = 4 ∧ bs.length = 0xd8 ∧
    (words64At ret ws ∗ ((ret + 0x20#64) ↦ₛ bs) ∗ H ⊢ apiEncResultAt A ret res)

/-- Poll and staging region `sp + 0x46a .. sp + 0xb80` with `ws` exposed at `sp + off`. -/
def pollWith (sp : BitVec 64) (off : Nat) (ws : List (BitVec 64)) : SepProp :=
  memRegion (sp + 0x46a#64) (off - 0x46a) ∗ words64At (sp + BitVec.ofNat 64 off) ws ∗
    memRegion (sp + BitVec.ofNat 64 (off + 8 * ws.length)) (0xb80 - (off + 8 * ws.length))

/-- `OutgoingTripleRatchet` slot `sp + 0x288 .. sp + 0x350` and its `pqr_state` drop flag at
`sp + 0x469`. -/
def otrSlotAt (A : RustAlloc) (sp : BitVec 64) :
    Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))) → SepProp
  | some (pqCap, pqPtr, ot) => otrAt A (sp + 0x288#64) pqCap pqPtr ot ∗ ((sp + 0x469#64) ↦₈ 1#8)
  | none => memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)

/-- Key and `CiphertextMessage` slots `sp + 0x350 .. sp + 0x469`. -/
def cmSlotAt (A : RustAlloc) (sp : BitVec 64) : Option CiphertextMessage → SepProp
  | some m => memRegion (sp + 0x350#64) 0x20 ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      memRegion (sp + 0x468#64) 1
  | none => memRegion (sp + 0x350#64) 0x119

/-- Stack frame layout at a `T1`-family record-drop entry. -/
def dropRecordSlots (A : RustAlloc) (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) : SepProp :=
  scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
    otrSlotAt A sp ot ∗ cmSlotAt A sp cm ∗ poll

/-- Callee-saved register pins at a staged-error tail entry. -/
def tailRegs (w0 w1 w2 : BitVec 64) (sp : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w0 ∧
    s.readReg64 .x21 = w1 ∧ s.readReg64 .x23 = w2

/-- Machine and memory state at an `encrypt` error/result tail entry. -/
def EncTailV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMeta img x s0 s ∧ regs sp s ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗
      (encStoreExtra kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R))

abbrev EncTail (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (img : Obj.Image) (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  EncTailV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    C ctl parse S x answers pc regs slots R s0 s

/-- Pure model and trace relation at an `encrypt` tail entry. -/
def TailModel {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (x : WithStoresEncGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (s0 s : State) : Prop :=
  ((x.model C S parse answers).1 = res ∧
    kit.callsRel st0 answers (x.model C S parse answers).2 ∧
    ikit.idCallsRel ist0 answers (x.model C S parse answers).2) ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2

/-! ## `words64At`, `unpack64List`, and `memRegion` Lemmas -/

def unpack64List : List (BitVec 64) → List (BitVec 8)
  | [] => []
  | w :: ws => unpack64 w ++ unpack64List ws

@[simp]
theorem unpack64List_length (ws : List (BitVec 64)) :
    (unpack64List ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [unpack64List, List.length_append, unpack64_length, List.length_cons, ih]
    omega

theorem words64At_eq_pointsToBytes (a : BitVec 64) (ws : List (BitVec 64)) :
    words64At a ws = (a ↦ₛ unpack64List ws) := by
  induction ws generalizing a with
  | nil =>
    simp only [words64At, unpack64List, pointsToBytes_nil]
  | cons w ws ih =>
    simp only [words64At, unpack64List, pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, ih (a + 8#64)]

theorem exists_unpack64List :
    ∀ (n : Nat) {bs : List (BitVec 8)}, bs.length = 8 * n →
      ∃ ws : List (BitVec 64), ws.length = n ∧ bs = unpack64List ws
  | 0, bs, h => by
    have h0 : bs = [] := List.eq_nil_of_length_eq_zero h
    exact ⟨[], rfl, h0⟩
  | n + 1, bs, h => by
    have htake : (bs.take 8).length = 8 := by
      rw [List.length_take]
      omega
    have hdrop : (bs.drop 8).length = 8 * n := by
      rw [List.length_drop]
      omega
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 htake
    obtain ⟨ws, hlen, hws⟩ := exists_unpack64List n hdrop
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    rw [← List.take_append_drop 8 bs, hw, hws, unpack64List]

theorem words64At_entails_memRegion (a : BitVec 64) (ws : List (BitVec 64))
    (h : 8 * ws.length ≤ 2 ^ 64) :
    words64At a ws ⊢ memRegion a (8 * ws.length) := by
  let _ := h
  rw [words64At_eq_pointsToBytes, ← unpack64List_length ws]
  exact pointsToBytes_entails_memRegion a (unpack64List ws)

theorem encSpillsAtV_entails_memRegion (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAtV ss_vt id_vt sp x ⊢ memRegion (sp + 0x58#64) 0xb8 := by
  unfold encSpillsAtV
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))))))))))))))))))))) ?_
  have join (off n k : Nat) (h : n + k ≤ 2 ^ 64) :
      memRegion (sp + BitVec.ofNat 64 off) n ∗
        memRegion (sp + BitVec.ofNat 64 (off + n)) k =
      memRegion (sp + BitVec.ofNat 64 off) (n + k) :=
    (memRegion_split' (b := sp + BitVec.ofNat 64 off)
      (b' := sp + BitVec.ofNat 64 (off + n)) (n := n) (k := k) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 0x58 8 4 (by decide), join 0x58 12 4 (by decide),
      join 0x58 16 8 (by decide), join 0x58 24 8 (by decide),
      join 0x58 32 8 (by decide), join 0x58 40 8 (by decide),
      join 0x58 48 8 (by decide), join 0x58 56 8 (by decide),
      join 0x58 64 8 (by decide), join 0x58 72 8 (by decide),
      join 0x58 80 8 (by decide), join 0x58 88 8 (by decide),
      join 0x58 96 8 (by decide), join 0x58 104 8 (by decide),
      join 0x58 112 8 (by decide), join 0x58 120 8 (by decide),
      join 0x58 128 8 (by decide), join 0x58 136 8 (by decide),
      join 0x58 144 8 (by decide), join 0x58 152 8 (by decide),
      join 0x58 160 4 (by decide), join 0x58 164 4 (by decide),
      join 0x58 168 8 (by decide), join 0x58 176 8 (by decide)]
  exact Entails.refl _

theorem encSpillsAt_entails_memRegion (b sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAt b sp x ⊢ memRegion (sp + 0x58#64) 0xb8 :=
  encSpillsAtV_entails_memRegion (ssVtable b) (idVtable b) sp x

theorem encSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    encSavedRegs sp0 s0 ⊢ memRegion (sp0 - 0x60#64) 0x60 := by
  unfold encSavedRegs
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h1 : n + 8 ≤ 96) :
      memRegion (sp0 - 96#64) n ∗ memRegion (sp0 - BitVec.ofNat 64 (96 - n)) 8 =
      memRegion (sp0 - 96#64) (n + 8) :=
    (memRegion_split' (b := sp0 - 96#64) (b' := sp0 - BitVec.ofNat 64 (96 - n))
      (n := n) (k := 8) rfl (by bv_omega) (by omega)).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide),
      join 32 (by decide), join 40 (by decide), join 48 (by decide),
      join 56 (by decide), join 64 (by decide), join 72 (by decide),
      join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

theorem writeResult_frame_entails_stackAtV (ss_vt id_vt : BitVec 64) (x : WithStoresEncGhost)
    (s0 : State) (bs : List (BitVec 8)) (hbs : bs.length = 0xd8) :
    let sp := s0.sp - 0xbe0#64
    memRegion sp 0x58 ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
      ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
      encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack ⊢
      stackAt s0.sp withStoresEncStack := by
  intro sp
  have hspills := encSpillsAtV_entails_memRegion ss_vt id_vt sp x
  have hbs_mem : ((sp + 0x4a0#64) ↦ₛ bs) ⊢ memRegion (sp + 0x4a0#64) 0xd8 := by
    rw [← hbs]
    exact pointsToBytes_entails_memRegion (sp + 0x4a0#64) bs
  have hsaved : encSavedRegs s0.sp s0 ⊢ memRegion (sp + 0xb80#64) 0x60 := by
    have heq : sp + 0xb80#64 = s0.sp - 0x60#64 := by dsimp [sp]; bv_omega
    rw [heq]
    exact encSavedRegs_entails_memRegion s0.sp s0
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hspills (sepConj_mono_right
      (sepConj_mono hbs_mem (sepConj_mono_right (sepConj_mono_left hsaved)))))) ?_
  have hframe :
      memRegion sp 0xbe0 =
        memRegion sp 0x58 ∗ (memRegion (sp + 0x58#64) 0xb8 ∗
          (memRegion (sp + 0x110#64) 0x390 ∗
            (memRegion (sp + 0x4a0#64) 0xd8 ∗
              (memRegion (sp + 0x578#64) 0x608 ∗ memRegion (sp + 0xb80#64) 0x60)))) := by
    rw [memRegion_split' (b := sp) (b' := sp + 0x58#64) (n := 0x58) (k := 0xb88)
        (by decide) rfl (by decide),
      memRegion_split' (b := sp + 0x58#64) (b' := sp + 0x110#64) (n := 0xb8) (k := 0xad0)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x110#64) (b' := sp + 0x4a0#64) (n := 0x390) (k := 0x740)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x578#64) (n := 0xd8) (k := 0x668)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x578#64) (b' := sp + 0xb80#64) (n := 0x608) (k := 0x60)
        (by decide) (by bv_omega) (by decide)]
  have hstack :
      stackAt s0.sp withStoresEncStack = stackAt sp encSubStack ∗ memRegion sp 0xbe0 := by
    unfold stackAt
    have h1 : s0.sp - BitVec.ofNat 64 withStoresEncStack = sp - BitVec.ofNat 64 encSubStack := by
      dsimp [sp, withStoresEncStack, entryStack, encSubStack, encFrameSize]
      bv_omega
    rw [h1,
      memRegion_split' (b := sp - BitVec.ofNat 64 encSubStack) (b' := sp)
        (n := encSubStack) (k := 0xbe0) (by decide)
        (by dsimp [encSubStack, withStoresEncStack, entryStack, encFrameSize]; bv_omega)
        (by decide)]
  rw [hstack, hframe, sepConj_comm (stackAt sp encSubStack)]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem writeResult_frame_entails_stackAt (b : BitVec 64) (x : WithStoresEncGhost) (s0 : State)
    (bs : List (BitVec 8)) (hbs : bs.length = 0xd8) :
    let sp := s0.sp - 0xbe0#64
    memRegion sp 0x58 ∗ encSpillsAt b sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
      ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
      encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack ⊢
      stackAt s0.sp withStoresEncStack :=
  writeResult_frame_entails_stackAtV (ssVtable b) (idVtable b) x s0 bs hbs

theorem segExit_of_sepWP_ret {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) ∧
        (P_f ⊢ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).post x s0 sf))) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf⟩, hent⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩)⟩
  exact Satisfies.mono (sepConj_mono_left hent) hmf

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
