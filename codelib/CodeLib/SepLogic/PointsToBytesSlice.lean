import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.SmallStepState
import CodeLib.RustStd.U64.AbsDiff

/-!
# Byte-range `pointsToBytes` slicing

Borrow/update a single byte of an owned byte range and get a wand that
restores it (`pointsToBytes_focus`/`_focus_update`), split and rejoin a
range (`pointsToBytes_slice`/`_take_drop`/`_take_drop_join`), view a u64 as
its four bytes (`pointsTo_u64_as_bytes`), and the four consecutive
`(ptr + n).toNat` address facts (`wordAccessFacts`) — all bv-decide-free.
-/

namespace Wasm.SepLogic

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

/-- Four-byte address facts obtained without bit-vector automation. -/
theorem wordAccessFacts (ptr : UInt32) (offset : Nat)
    (hfit : ptr.toNat + offset + 4 < UInt32.size) :
    (ptr + UInt32.ofNat offset).toNat = ptr.toNat + offset ∧
    ((ptr + UInt32.ofNat offset) + 1).toNat =
      (ptr + UInt32.ofNat offset).toNat + 1 ∧
    ((ptr + UInt32.ofNat offset) + 2).toNat =
      (ptr + UInt32.ofNat offset).toNat + 2 ∧
    ((ptr + UInt32.ofNat offset) + 3).toNat =
      (ptr + UInt32.ofNat offset).toNat + 3 := by
  have hadd (n : Nat) (hn : n ≤ offset + 3) :
      (ptr + UInt32.ofNat n).toNat = ptr.toNat + n :=
    Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr n
      (by simp only [UInt32.size] at hfit ⊢; omega)
      (by simp only [UInt32.size] at hfit ⊢; omega)
  refine ⟨hadd offset (by omega), ?_, ?_, ?_⟩
  · rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 1) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (2 : UInt32) = UInt32.ofNat 2 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 2) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (3 : UInt32) = UInt32.ofNat 3 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 3) (by omega),
      hadd offset (by omega)]
    omega

/-- Borrow one byte from an owned byte range and return a wand that restores
the original range. -/
theorem pointsToBytes_focus {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ byte : UInt8,
        (⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) ∗
        (((⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) -∗
          pointsToBytes memId addr bytes) ∗
        ⌜bytes[i]? = some byte⌝)) := by
  induction bytes generalizing addr i with
  | nil => simp at hi
  | cons head tail ih =>
      iintro Hbytes
      ihave Hsplit := (pointsToBytes_cons memId addr head tail).mp $$ Hbytes
      icases Hsplit with ⟨Hhead, Htail⟩
      cases i with
      | zero =>
          have hzero : UInt32.ofNat 0 = 0 := by decide
          iexists head
          isplitl [Hhead]
          · rw [hzero, UInt32.add_zero]
            iexact Hhead
          · isplitl [Htail]
            · rw [hzero, UInt32.add_zero]
              iintro Hhead
              iapply (pointsToBytes_cons memId addr head tail).mpr
              iframe
            · ipureintro
              rfl
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          ihave Hfocus := ih (addr + 1) j hi $$ Htail
          icases Hfocus with ⟨%byte, Hbyte, Hput, %hbyte⟩
          iexists byte
          rw [← byte_offset_succ addr j]
          isplitl [Hbyte]
          · iexact Hbyte
          · isplitl [Hhead Hput]
            · iintro Hbyte
              iapply (pointsToBytes_cons memId addr head tail).mpr
              isplitl [Hhead]
              · iexact Hhead
              · iapply Hput
                rw [byte_offset_succ addr j]
                iexact Hbyte
            · ipureintro
              simpa only [List.getElem?_cons_succ] using hbyte

/-- Borrow one byte and rebuild the range with an updated byte. -/
theorem pointsToBytes_focus_update {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ byte : UInt8,
        (⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) ∗
        ((∀ newByte : UInt8,
          (⟨memId, addr + UInt32.ofNat i⟩ ↦w newByte) -∗
          pointsToBytes memId addr (bytes.set i newByte)) ∗
        ⌜bytes[i]? = some byte⌝)) := by
  induction bytes generalizing addr i with
  | nil => simp at hi
  | cons head tail ih =>
      iintro Hbytes
      ihave Hsplit := (pointsToBytes_cons memId addr head tail).mp $$ Hbytes
      icases Hsplit with ⟨Hhead, Htail⟩
      cases i with
      | zero =>
          have hzero : UInt32.ofNat 0 = 0 := by decide
          iexists head
          isplitl [Hhead]
          · rw [hzero, UInt32.add_zero]
            iexact Hhead
          · isplitl [Htail]
            · iintro %newByte Hnew
              simp only [List.set]
              iapply (pointsToBytes_cons memId addr newByte tail).mpr
              isplitl [Hnew]
              · rw [hzero, UInt32.add_zero]
                iexact Hnew
              · iexact Htail
            · ipureintro
              rfl
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          ihave Hfocus := ih (addr + 1) j hi $$ Htail
          icases Hfocus with ⟨%byte, Hbyte, Hput, %hbyte⟩
          iexists byte
          rw [← byte_offset_succ addr j]
          isplitl [Hbyte]
          · iexact Hbyte
          · isplitl [Hhead Hput]
            · iintro %newByte Hnew
              simp only [List.set]
              iapply (pointsToBytes_cons memId addr head
                (tail.set j newByte)).mpr
              isplitl [Hhead]
              · iexact Hhead
              · ispecialize Hput $$ %newByte
                iapply Hput
                rw [byte_offset_succ addr j]
                iexact Hnew
            · ipureintro
              simpa only [List.getElem?_cons_succ] using hbyte

/-- Split an owned byte range after `n` bytes. -/
theorem pointsToBytes_take_drop {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% pointsToBytes memId addr (bytes.take n) ∗
        pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) := by
  have hlen : (bytes.take n).length = n := List.length_take_of_le hn
  iintro Hbytes
  ihave Hbytes' : pointsToBytes memId addr
      (bytes.take n ++ bytes.drop n) $$ [Hbytes]
  · rw [List.take_append_drop]
    iexact Hbytes
  ihave Hsplit := (pointsToBytes_append memId addr
    (bytes.take n) (bytes.drop n)).mp $$ Hbytes'
  have haddr : addr + UInt32.ofNat (bytes.take n).length =
      addr + UInt32.ofNat n := by rw [hlen]
  ihave Hsplit' : (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) $$ [Hsplit]
  · rw [← haddr]
    iexact Hsplit
  iexact Hsplit'

/-- Reassemble the halves produced by `pointsToBytes_take_drop`. -/
theorem pointsToBytes_take_drop_join {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) ⊢
      pointsToBytes (α := α) memId addr bytes := by
  have hlen : (bytes.take n).length = n := List.length_take_of_le hn
  have haddr : addr + UInt32.ofNat (bytes.take n).length =
      addr + UInt32.ofNat n := by rw [hlen]
  iintro Hsplit
  ihave Hsplit' : (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId
        (addr + UInt32.ofNat (bytes.take n).length) (bytes.drop n)) $$ [Hsplit]
  · rw [haddr]
    iexact Hsplit
  ihave Hbytes := (pointsToBytes_append memId addr
    (bytes.take n) (bytes.drop n)).mpr $$ Hsplit'
  have heq : pointsToBytes (α := α) memId addr
      (bytes.take n ++ bytes.drop n) = pointsToBytes memId addr bytes := by
    rw [List.take_append_drop]
  ihave Hbytes' : pointsToBytes memId addr bytes $$ [Hbytes]
  · rw [← heq]
    iexact Hbytes
  iexact Hbytes'

/-- Split out a contiguous slice while retaining both surrounding ranges. -/
theorem pointsToBytes_slice {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (start count : Nat)
    (hstart : start ≤ bytes.length)
    (hcount : count ≤ (bytes.drop start).length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% pointsToBytes memId addr (bytes.take start) ∗
        pointsToBytes memId (addr + UInt32.ofNat start)
          ((bytes.drop start).take count) ∗
        pointsToBytes memId
          ((addr + UInt32.ofNat start) + UInt32.ofNat count)
          ((bytes.drop start).drop count)) := by
  iintro Hbytes
  ihave Hfirst := pointsToBytes_take_drop memId addr bytes start hstart $$ Hbytes
  icases Hfirst with ⟨Hbefore, Htail⟩
  ihave Hsecond := pointsToBytes_take_drop memId
    (addr + UInt32.ofNat start) (bytes.drop start) count hcount $$ Htail
  icases Hsecond with ⟨Hmiddle, Hafter⟩
  iframe

/-- A little-endian u64 assertion is the corresponding eight-byte slice. -/
theorem pointsTo_u64_as_bytes {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32) (word : UInt64) :
    pointsTo_u64 memId addr word ⊣⊢
      pointsToBytes memId addr
        [u64Byte word 0, u64Byte word 1, u64Byte word 2, u64Byte word 3,
         u64Byte word 4, u64Byte word 5, u64Byte word 6, u64Byte word 7] := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; congr 1
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; congr 1
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; congr 1
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; congr 1
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; congr 1
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; congr 1
  simp only [pointsTo_u64, pointsToBytes, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

/-- Borrow an eight-byte word from a byte window and return a wand restoring
the unchanged range. -/
theorem pointsToBytes_focus_u64 {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (base : UInt32)
    (bytes : List UInt8) (i : Nat) (word : UInt64)
    (hi : i + 8 ≤ bytes.length)
    (hword : (bytes.drop i).take 8 =
      [u64Byte word 0, u64Byte word 1, u64Byte word 2, u64Byte word 3,
       u64Byte word 4, u64Byte word 5, u64Byte word 6, u64Byte word 7]) :
    pointsToBytes (α := α) memId base bytes ⊢
      (iprop% pointsTo_u64 memId (base + UInt32.ofNat i) word ∗
        (pointsTo_u64 memId (base + UInt32.ofNat i) word -∗
          pointsToBytes memId base bytes)) := by
  iintro Hbytes
  ihave ⟨Hpre, Hmid, Hpost⟩ := pointsToBytes_slice memId base bytes i 8
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  isplitl [Hmid]
  · iapply (pointsTo_u64_as_bytes memId
      (base + UInt32.ofNat i) word).mpr
    irw_exact [← hword] with Hmid
  iintro Hword
  ihave Hmid := (pointsTo_u64_as_bytes memId
    (base + UInt32.ofNat i) word).mp $$ Hword
  isimp only [← hword] at Hmid
  iapply_frame pointsToBytes_take_drop_join memId base bytes i (by omega)
  iapply_frame pointsToBytes_take_drop_join memId
    (base + UInt32.ofNat i) (bytes.drop i) 8
    (by simp [List.length_drop]; omega)

/-! ## Word windows -/

/-- The four little-endian bytes of a `UInt32`. -/
def u32Bytes (word : UInt32) : List UInt8 :=
  [u32Byte word 0, u32Byte word 1, u32Byte word 2, u32Byte word 3]

/-- Replace an arbitrary four-byte window by a little-endian word. -/
def replaceU32Window (bytes : List UInt8) (start : Nat) (word : UInt32) :
    List UInt8 :=
  bytes.take start ++ u32Bytes word ++ (bytes.drop start).drop 4

/-- Replace two adjacent little-endian words in an arbitrary byte range. -/
def replaceU32PairWindow (bytes : List UInt8) (start : Nat)
    (first second : UInt32) : List UInt8 :=
  bytes.take start ++ u32Bytes first ++ u32Bytes second ++
    (bytes.drop start).drop 8

private def packU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

private theorem packU32_bytes (b0 b1 b2 b3 : UInt8) :
    u32Bytes (packU32 b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h0 : u32Byte (packU32 b0 b1 b2 b3) 0 = b0 := by
    simpa only [u32Byte, packU32] using UInt32.packBytes_byte0 b0 b1 b2 b3
  have h1 : u32Byte (packU32 b0 b1 b2 b3) 1 = b1 := by
    simpa only [u32Byte, packU32] using UInt32.packBytes_byte1 b0 b1 b2 b3
  have h2 : u32Byte (packU32 b0 b1 b2 b3) 2 = b2 := by
    simpa only [u32Byte, packU32] using UInt32.packBytes_byte2 b0 b1 b2 b3
  have h3 : u32Byte (packU32 b0 b1 b2 b3) 3 = b3 := by
    simpa only [u32Byte, packU32] using UInt32.packBytes_byte3 b0 b1 b2 b3
  simp only [u32Bytes, h0, h1, h2, h3]

private theorem four_bytes_of_length (xs : List UInt8) (h : xs.length = 4) :
    ∃ b0 b1 b2 b3, xs = [b0, b1, b2, b3] := by
  rcases xs with _ | ⟨b0, xs⟩; · simp at h
  rcases xs with _ | ⟨b1, xs⟩; · simp at h
  rcases xs with _ | ⟨b2, xs⟩; · simp at h
  rcases xs with _ | ⟨b3, xs⟩; · simp at h
  rcases xs with _ | ⟨b4, xs⟩
  · exact ⟨b0, b1, b2, b3, rfl⟩
  · simp at h

private theorem eight_bytes_of_length (xs : List UInt8) (h : xs.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7,
      xs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rcases xs with _ | ⟨b0, xs⟩; · simp at h
  rcases xs with _ | ⟨b1, xs⟩; · simp at h
  rcases xs with _ | ⟨b2, xs⟩; · simp at h
  rcases xs with _ | ⟨b3, xs⟩; · simp at h
  rcases xs with _ | ⟨b4, xs⟩; · simp at h
  rcases xs with _ | ⟨b5, xs⟩; · simp at h
  rcases xs with _ | ⟨b6, xs⟩; · simp at h
  rcases xs with _ | ⟨b7, xs⟩; · simp at h
  rcases xs with _ | ⟨b8, xs⟩
  · exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  · simp at h

/-- Focus an arbitrary four-byte window as a `UInt32`; the returned wand
accepts any replacement word and rejoins the complete byte range. -/
theorem pointsToBytes_focus_u32_window {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (start : Nat) (hfit : start + 4 ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ old : UInt32,
        pointsTo_u32 memId (addr + UInt32.ofNat start) old ∗
        (∀ new : UInt32,
          pointsTo_u32 memId (addr + UInt32.ofNat start) new -∗
          pointsToBytes memId addr (replaceU32Window bytes start new)) ∗
        ⌜(bytes.drop start).take 4 = u32Bytes old⌝) := by
  iintro Hbytes
  ihave Hparts := pointsToBytes_slice memId addr bytes start 4
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  icases Hparts with ⟨Hbefore, Hmiddle, Hafter⟩
  have hmiddle : ((bytes.drop start).take 4).length = 4 := by
    rw [List.length_take_of_le]
    simp [List.length_drop]
    omega
  obtain ⟨b0, b1, b2, b3, hm⟩ :=
    four_bytes_of_length ((bytes.drop start).take 4) hmiddle
  isimp only [hm] at Hmiddle
  let old := packU32 b0 b1 b2 b3
  have holdBytes := packU32_bytes b0 b1 b2 b3
  iexists old
  isplitl [Hmiddle]
  · ihave Hmiddle' : pointsToBytes memId (addr + UInt32.ofNat start)
        (u32Bytes old) $$ [Hmiddle]
    · rw [holdBytes]
      iexact Hmiddle
    iapply (pointsTo_u32_as_bytes memId
      (addr + UInt32.ofNat start) old).mpr
    isimp only [u32Bytes] at Hmiddle'
    iexact Hmiddle'
  · isplitl [Hbefore Hafter]
    · iintro %new Hnew
      ihave HnewBytes : pointsToBytes memId (addr + UInt32.ofNat start)
          (u32Bytes new) $$ [Hnew]
      · isimp only [u32Bytes]
        iapply (pointsTo_u32_as_bytes memId
          (addr + UInt32.ofNat start) new).mp
        iexact Hnew
      have hbeforeLen : (bytes.take start).length = start :=
        List.length_take_of_le (by omega)
      have hadd : (addr + UInt32.ofNat start) + UInt32.ofNat 4 =
          addr + UInt32.ofNat (start + 4) := by
        rw [UInt32.add_assoc, ← UInt32.ofNat_add]
      ihave HtailPair :
        (iprop% pointsToBytes memId (addr + UInt32.ofNat start)
            (u32Bytes new) ∗
          pointsToBytes memId
            ((addr + UInt32.ofNat start) + UInt32.ofNat (u32Bytes new).length)
            ((bytes.drop start).drop 4)) $$ [HnewBytes Hafter]
      · simp only [u32Bytes, List.length_cons, List.length_nil]
        rw [hadd]
        iframe
      ihave Htail := (pointsToBytes_append memId
        (addr + UInt32.ofNat start) (u32Bytes new)
        ((bytes.drop start).drop 4)).mpr $$ HtailPair
      ihave HallPair :
        (iprop% pointsToBytes memId addr (bytes.take start) ∗
          pointsToBytes memId
            (addr + UInt32.ofNat (bytes.take start).length)
            (u32Bytes new ++ (bytes.drop start).drop 4)) $$ [Hbefore Htail]
      · rw [hbeforeLen]
        iframe
      rw [replaceU32Window, List.append_assoc]
      iapply (pointsToBytes_append memId addr (bytes.take start)
        (u32Bytes new ++ (bytes.drop start).drop 4)).mpr
      iexact HallPair
    · ipureintro
      exact hm.trans holdBytes.symm

/-- Focus two adjacent words in an arbitrary byte range and return a wand
that rejoins arbitrary replacements for both words. -/
theorem pointsToBytes_focus_u32_pair_window {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (start : Nat) (hfit : start + 8 ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ first second : UInt32,
        pointsTo_u32 memId (addr + UInt32.ofNat start) first ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) second ∗
        ⌜((bytes.drop start).take 8).take 4 = u32Bytes first⌝ ∗
        ⌜(((bytes.drop start).take 8).drop 4).take 4 = u32Bytes second⌝ ∗
        (∀ newFirst : UInt32, ∀ newSecond : UInt32,
          pointsTo_u32 memId (addr + UInt32.ofNat start) newFirst -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) newSecond -∗
          pointsToBytes memId addr
            (replaceU32PairWindow bytes start newFirst newSecond))) := by
  iintro Hbytes
  ihave Hparts := pointsToBytes_slice memId addr bytes start 8
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  icases Hparts with ⟨Hbefore, Hmiddle, Hafter⟩
  have hmiddle : ((bytes.drop start).take 8).length = 8 := by
    rw [List.length_take_of_le]
    simp [List.length_drop]
    omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hm⟩ :=
    eight_bytes_of_length ((bytes.drop start).take 8) hmiddle
  isimp only [hm] at Hmiddle
  have hsplit : [b0, b1, b2, b3, b4, b5, b6, b7] =
      [b0, b1, b2, b3] ++ [b4, b5, b6, b7] := rfl
  isimp only [hsplit] at Hmiddle
  ihave Hwords := (pointsToBytes_append memId
    (addr + UInt32.ofNat start) [b0, b1, b2, b3]
    [b4, b5, b6, b7]).mp $$ Hmiddle
  icases Hwords with ⟨HfirstBytes, HsecondBytes⟩
  let first := packU32 b0 b1 b2 b3
  let second := packU32 b4 b5 b6 b7
  have hfirst := packU32_bytes b0 b1 b2 b3
  have hsecond := packU32_bytes b4 b5 b6 b7
  iexists first
  iexists second
  isplitl [HfirstBytes]
  · iapply (pointsTo_u32_as_bytes memId
      (addr + UInt32.ofNat start) first).mpr
    ihave Hfirst' : pointsToBytes memId (addr + UInt32.ofNat start)
        (u32Bytes first) $$ [HfirstBytes]
    · rw [hfirst]
      iexact HfirstBytes
    isimp only [u32Bytes] at Hfirst'
    iexact Hfirst'
  · isplitl [HsecondBytes]
    · iapply (pointsTo_u32_as_bytes memId
        ((addr + UInt32.ofNat start) + 4) second).mpr
      ihave Hsecond' : pointsToBytes memId
          ((addr + UInt32.ofNat start) + 4) (u32Bytes second) $$ [HsecondBytes]
      · rw [hsecond]
        iexact HsecondBytes
      isimp only [u32Bytes] at Hsecond'
      iexact Hsecond'
    · isplit
      · ipureintro
        exact (congrArg (List.take 4) hm).trans hfirst.symm
      isplit
      · ipureintro
        exact (congrArg (fun xs : List UInt8 => (xs.drop 4).take 4) hm).trans
          hsecond.symm
      iintro %newFirst %newSecond HnewFirst HnewSecond
      ihave Hfirst' : pointsToBytes memId (addr + UInt32.ofNat start)
          (u32Bytes newFirst) $$ [HnewFirst]
      · isimp only [u32Bytes]
        iapply (pointsTo_u32_as_bytes memId
          (addr + UInt32.ofNat start) newFirst).mp
        iexact HnewFirst
      ihave Hsecond' : pointsToBytes memId
          ((addr + UInt32.ofNat start) + 4) (u32Bytes newSecond) $$ [HnewSecond]
      · isimp only [u32Bytes]
        iapply (pointsTo_u32_as_bytes memId
          ((addr + UInt32.ofNat start) + 4) newSecond).mp
        iexact HnewSecond
      ihave Hpair : (iprop% pointsToBytes memId
          (addr + UInt32.ofNat start) (u32Bytes newFirst) ∗
          pointsToBytes memId
            ((addr + UInt32.ofNat start) + UInt32.ofNat (u32Bytes newFirst).length)
            (u32Bytes newSecond)) $$ [Hfirst' Hsecond']
      · simp only [u32Bytes, List.length_cons, List.length_nil]
        iframe
      ihave Hmiddle' := (pointsToBytes_append memId
        (addr + UInt32.ofNat start) (u32Bytes newFirst)
        (u32Bytes newSecond)).mpr $$ Hpair
      have hbeforeLen : (bytes.take start).length = start :=
        List.length_take_of_le (by omega)
      have hadd : (addr + UInt32.ofNat start) + UInt32.ofNat 8 =
          addr + UInt32.ofNat (start + 8) := by
        rw [UInt32.add_assoc, ← UInt32.ofNat_add]
      ihave HtailPair : (iprop% pointsToBytes memId
          (addr + UInt32.ofNat start) (u32Bytes newFirst ++ u32Bytes newSecond) ∗
          pointsToBytes memId
            ((addr + UInt32.ofNat start) +
              UInt32.ofNat (u32Bytes newFirst ++ u32Bytes newSecond).length)
            ((bytes.drop start).drop 8)) $$ [Hmiddle' Hafter]
      · simp only [List.length_append, u32Bytes, List.length_cons,
          List.length_nil]
        rw [show 4 + 4 = 8 by omega, hadd]
        iframe
      ihave Htail := (pointsToBytes_append memId
        (addr + UInt32.ofNat start) (u32Bytes newFirst ++ u32Bytes newSecond)
        ((bytes.drop start).drop 8)).mpr $$ HtailPair
      ihave HallPair : (iprop% pointsToBytes memId addr (bytes.take start) ∗
          pointsToBytes memId (addr + UInt32.ofNat (bytes.take start).length)
            (u32Bytes newFirst ++ u32Bytes newSecond ++
              (bytes.drop start).drop 8)) $$ [Hbefore Htail]
      · rw [hbeforeLen]
        iframe
      ihave Hall := (pointsToBytes_append memId addr (bytes.take start)
        (u32Bytes newFirst ++ u32Bytes newSecond ++
          (bytes.drop start).drop 8)).mpr $$ HallPair
      simp only [replaceU32PairWindow, List.append_assoc]
      iexact Hall

@[simp] theorem u32Bytes_length (word : UInt32) : (u32Bytes word).length = 4 := by
  simp [u32Bytes]

/-- Replace three adjacent little-endian words in an arbitrary byte range. -/
def replaceU32TripleWindow (bytes : List UInt8) (start : Nat)
    (first second third : UInt32) : List UInt8 :=
  bytes.take start ++ (u32Bytes first ++ (u32Bytes second ++
    replaceU32Window ((bytes.drop start).drop 8) 0 third))

/-- Replace six adjacent little-endian words in an arbitrary byte range. -/
def replaceU32SixWindow (bytes : List UInt8) (start : Nat)
    (w0 w1 w2 w3 w4 w5 : UInt32) : List UInt8 :=
  bytes.take start ++ (u32Bytes w0 ++ (u32Bytes w1 ++
    (u32Bytes w2 ++ (u32Bytes w3 ++
      replaceU32PairWindow ((bytes.drop start).drop 16) 0 w4 w5))))

/-- The fourth word selected by the six-word window decomposition. -/
def u32SixReadWord3 (bytes : List UInt8) (start : Nat) : List UInt8 :=
  List.take 4 (List.drop 4 (List.take 8
    (List.drop 0 (List.take 8 (List.drop 8 (List.drop start bytes))))))

/-- The fifth word selected by the six-word window decomposition. -/
def u32SixReadWord4 (bytes : List UInt8) (start : Nat) : List UInt8 :=
  List.take 4 (List.take 8
    (List.drop 0 (List.drop 8 (List.drop 8 (List.drop start bytes)))))

/-- The sixth word selected by the six-word window decomposition. -/
def u32SixReadWord5 (bytes : List UInt8) (start : Nat) : List UInt8 :=
  List.take 4 (List.drop 4 (List.take 8
    (List.drop 0 (List.drop 8 (List.drop 8 (List.drop start bytes))))))

theorem pointsToBytes_focus_u32_triple_window {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (start : Nat) (hfit : start + 12 ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ first second third : UInt32,
        pointsTo_u32 memId (addr + UInt32.ofNat start) first ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) second ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 8) third ∗
        (∀ newFirst : UInt32, ∀ newSecond : UInt32, ∀ newThird : UInt32,
          pointsTo_u32 memId (addr + UInt32.ofNat start) newFirst -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) newSecond -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 8) newThird -∗
          pointsToBytes memId addr
            (replaceU32TripleWindow bytes start newFirst newSecond newThird))) := by
  iintro Hbytes
  ihave Hparts := pointsToBytes_slice memId addr bytes start 8
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  icases Hparts with ⟨Hbefore, Hmiddle, Hafter⟩
  ihave Hpair := pointsToBytes_focus_u32_pair_window memId
    (addr + UInt32.ofNat start) ((bytes.drop start).take 8) 0
    (by simp [List.length_drop]; omega) $$ Hmiddle
  icases Hpair with ⟨%first, %second, Hfirst, Hsecond,
    %_HreadFirst, %_HreadSecond, HputPair⟩
  ihave Hthird := pointsToBytes_focus_u32_window memId
    ((addr + UInt32.ofNat start) + UInt32.ofNat 8)
    ((bytes.drop start).drop 8) 0 (by simp [List.length_drop]; omega) $$ Hafter
  icases Hthird with ⟨%third, Hthird, HputThird, %_HreadThird⟩
  iexists first
  iexists second
  iexists third
  isimp only [show UInt32.ofNat 0 = (0 : UInt32) by decide,
    UInt32.add_zero] at Hfirst Hsecond HputPair Hthird HputThird
  have h8 : (addr + UInt32.ofNat start) + UInt32.ofNat 8 =
      (addr + UInt32.ofNat start) + 8 := by rfl
  isimp only [h8] at Hthird HputThird
  iframe
  iintro %newFirst %newSecond %newThird HnewFirst HnewSecond HnewThird
  ispecialize HputPair $$ %newFirst %newSecond HnewFirst HnewSecond
  ispecialize HputThird $$ %newThird HnewThird
  have heq : replaceU32PairWindow ((bytes.drop start).take 8) 0
      newFirst newSecond = u32Bytes newFirst ++ u32Bytes newSecond := by
    simp [replaceU32PairWindow]
  ihave HpairBytes : pointsToBytes memId (addr + UInt32.ofNat start)
      (u32Bytes newFirst ++ u32Bytes newSecond) $$ [HputPair]
  · rw [← heq]
    iexact HputPair
  ihave Hsplit := (pointsToBytes_append memId (addr + UInt32.ofNat start)
      (u32Bytes newFirst) (u32Bytes newSecond)).mp $$ HpairBytes
  icases Hsplit with ⟨HfirstBytes, HsecondBytes⟩
  isimp only [u32Bytes_length,
    show UInt32.ofNat 4 = (4 : UInt32) by decide] at HsecondBytes
  ihave HsecondThird : pointsToBytes memId
      ((addr + UInt32.ofNat start) + 4)
      (u32Bytes newSecond ++
        replaceU32Window ((bytes.drop start).drop 8) 0 newThird) $$
      [HsecondBytes HputThird]
  · iapply (pointsToBytes_append memId ((addr + UInt32.ofNat start) + 4)
      (u32Bytes newSecond)
      (replaceU32Window ((bytes.drop start).drop 8) 0 newThird)).mpr
    isimp only [u32Bytes_length,
      show UInt32.ofNat 4 = (4 : UInt32) by decide]
    have hadd : (addr + UInt32.ofNat start) + 4 + 4 =
        (addr + UInt32.ofNat start) + 8 := by
      rw [UInt32.add_assoc]
      congr 1
    rw [hadd]
    iframe
  ihave Htail : pointsToBytes memId (addr + UInt32.ofNat start)
      (u32Bytes newFirst ++ (u32Bytes newSecond ++
        replaceU32Window ((bytes.drop start).drop 8) 0 newThird)) $$
      [HfirstBytes HsecondThird]
  · iapply (pointsToBytes_append memId (addr + UInt32.ofNat start)
      (u32Bytes newFirst) (u32Bytes newSecond ++
        replaceU32Window ((bytes.drop start).drop 8) 0 newThird)).mpr
    isimp only [u32Bytes_length,
      show UInt32.ofNat 4 = (4 : UInt32) by decide]
    iframe
  unfold replaceU32TripleWindow
  have hbeforeLen : (bytes.take start).length = start :=
    List.length_take_of_le (by omega)
  iapply (pointsToBytes_append memId addr (bytes.take start)
      (u32Bytes newFirst ++ (u32Bytes newSecond ++
        replaceU32Window ((bytes.drop start).drop 8) 0 newThird))).mpr
  rw [hbeforeLen]
  iframe

theorem pointsToBytes_focus_u32_six_window {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (start : Nat) (hfit : start + 24 ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ w0 w1 w2 w3 w4 w5 : UInt32,
        pointsTo_u32 memId (addr + UInt32.ofNat start) w0 ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) w1 ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 8) w2 ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 12) w3 ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 16) w4 ∗
        pointsTo_u32 memId ((addr + UInt32.ofNat start) + 20) w5 ∗
        ⌜u32SixReadWord3 bytes start = u32Bytes w3⌝ ∗
        ⌜u32SixReadWord4 bytes start = u32Bytes w4⌝ ∗
        ⌜u32SixReadWord5 bytes start = u32Bytes w5⌝ ∗
        (∀ (n0 : UInt32), ∀ (n1 : UInt32), ∀ (n2 : UInt32),
          ∀ (n3 : UInt32), ∀ (n4 : UInt32), ∀ (n5 : UInt32),
          pointsTo_u32 memId (addr + UInt32.ofNat start) n0 -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 4) n1 -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 8) n2 -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 12) n3 -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 16) n4 -∗
          pointsTo_u32 memId ((addr + UInt32.ofNat start) + 20) n5 -∗
          pointsToBytes memId addr
            (replaceU32SixWindow bytes start n0 n1 n2 n3 n4 n5))) := by
  iintro Hbytes
  ihave Hparts := pointsToBytes_slice memId addr bytes start 8
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  icases Hparts with ⟨Hbefore, Hpair0, Hafter0⟩
  ihave Hparts1 := pointsToBytes_slice memId
    ((addr + UInt32.ofNat start) + UInt32.ofNat 8)
    ((bytes.drop start).drop 8) 0 8
    (by simp) (by simp [List.length_drop]; omega) $$ Hafter0
  icases Hparts1 with ⟨_Hzero, Hpair1, Hafter1⟩
  iclear _Hzero
  isimp only [List.drop_zero, show UInt32.ofNat 0 = (0 : UInt32) by decide,
    UInt32.add_zero] at Hpair1 Hafter1
  ihave Hp0 := pointsToBytes_focus_u32_pair_window memId
    (addr + UInt32.ofNat start) ((bytes.drop start).take 8) 0
    (by simp [List.length_drop]; omega) $$ Hpair0
  ihave Hp1 := pointsToBytes_focus_u32_pair_window memId
    ((addr + UInt32.ofNat start) + UInt32.ofNat 8)
    (((bytes.drop start).drop 8).take 8) 0
    (by simp [List.length_drop]; omega) $$ Hpair1
  ihave Hp2 := pointsToBytes_focus_u32_pair_window memId
    (((addr + UInt32.ofNat start) + UInt32.ofNat 8) + UInt32.ofNat 8)
    (((bytes.drop start).drop 8).drop 8) 0
    (by simp [List.length_drop]; omega) $$ Hafter1
  icases Hp0 with ⟨%w0, %w1, Hw0, Hw1, %hr0, %hr1, Hput0⟩
  icases Hp1 with ⟨%w2, %w3, Hw2, Hw3, %hr2, %hr3, Hput1⟩
  icases Hp2 with ⟨%w4, %w5, Hw4, Hw5, %hr4, %hr5, Hput2⟩
  iexists w0; iexists w1; iexists w2; iexists w3; iexists w4; iexists w5
  isimp only [show UInt32.ofNat 0 = (0 : UInt32) by decide,
    UInt32.add_zero] at Hw0 Hw1 Hput0 Hw2 Hw3 Hput1 Hw4 Hw5 Hput2
  have h8 : (addr + UInt32.ofNat start) + UInt32.ofNat 8 =
      (addr + UInt32.ofNat start) + 8 := by rfl
  isimp only [h8] at Hw2 Hw3 Hput1
  have h16 : (addr + UInt32.ofNat start) + 8 + UInt32.ofNat 8 =
      (addr + UInt32.ofNat start) + 16 := by
    rw [UInt32.add_assoc]
    congr 1
  have h12 : (addr + UInt32.ofNat start) + 8 + 4 =
      (addr + UInt32.ofNat start) + 12 := by
    rw [UInt32.add_assoc]
    congr 1
  have h20 : (addr + UInt32.ofNat start) + 16 + 4 =
      (addr + UInt32.ofNat start) + 20 := by
    rw [UInt32.add_assoc]
    congr 1
  have h16' : (addr + UInt32.ofNat start) + UInt32.ofNat 8 +
      UInt32.ofNat 8 = (addr + UInt32.ofNat start) + 16 := by
    simpa using h16
  isimp only [h12] at Hw3 Hput1
  isimp only [h16', h20] at Hw4 Hw5 Hput2
  isplitl [Hw0]
  · iexact Hw0
  isplitl [Hw1]
  · iexact Hw1
  isplitl [Hw2]
  · iexact Hw2
  isplitl [Hw3]
  · iexact Hw3
  isplitl [Hw4]
  · iexact Hw4
  isplitl [Hw5]
  · iexact Hw5
  isplit
  · ipureintro
    exact hr3
  isplit
  · ipureintro
    exact hr4
  isplit
  · ipureintro
    exact hr5
  iintro %n0 %n1 %n2 %n3 %n4 %n5 Hn0 Hn1 Hn2 Hn3 Hn4 Hn5
  ispecialize Hput0 $$ %n0 %n1 Hn0 Hn1
  ispecialize Hput1 $$ %n2 %n3 Hn2 Hn3
  ispecialize Hput2 $$ %n4 %n5 Hn4 Hn5
  have hp0 : replaceU32PairWindow ((bytes.drop start).take 8) 0 n0 n1 =
      u32Bytes n0 ++ u32Bytes n1 := by simp [replaceU32PairWindow]
  have hp1 : replaceU32PairWindow
      (((bytes.drop start).drop 8).take 8) 0 n2 n3 =
      u32Bytes n2 ++ u32Bytes n3 := by simp [replaceU32PairWindow]
  ihave Hput0Bytes : pointsToBytes memId (addr + UInt32.ofNat start)
      (u32Bytes n0 ++ u32Bytes n1) $$ [Hput0]
  · rw [← hp0]
    iexact Hput0
  ihave Hput1Bytes : pointsToBytes memId
      ((addr + UInt32.ofNat start) + 8)
      (u32Bytes n2 ++ u32Bytes n3) $$ [Hput1]
  · rw [← hp1]
    iexact Hput1
  ihave Htail1 : pointsToBytes memId ((addr + UInt32.ofNat start) + 8)
      ((u32Bytes n2 ++ u32Bytes n3) ++
        replaceU32PairWindow (((bytes.drop start).drop 8).drop 8) 0 n4 n5) $$
      [Hput1Bytes Hput2]
  · iapply (pointsToBytes_append memId ((addr + UInt32.ofNat start) + 8)
      (u32Bytes n2 ++ u32Bytes n3)
      (replaceU32PairWindow (((bytes.drop start).drop 8).drop 8) 0 n4 n5)).mpr
    simp only [List.length_append, u32Bytes_length]
    rw [show 4 + 4 = 8 by omega, h16]
    iframe
  ihave Htail0 : pointsToBytes memId (addr + UInt32.ofNat start)
      ((u32Bytes n0 ++ u32Bytes n1) ++
        ((u32Bytes n2 ++ u32Bytes n3) ++
          replaceU32PairWindow (((bytes.drop start).drop 8).drop 8) 0 n4 n5)) $$
      [Hput0Bytes Htail1]
  · iapply (pointsToBytes_append memId (addr + UInt32.ofNat start)
      (u32Bytes n0 ++ u32Bytes n1)
      ((u32Bytes n2 ++ u32Bytes n3) ++
        replaceU32PairWindow (((bytes.drop start).drop 8).drop 8) 0 n4 n5)).mpr
    simp only [List.length_append, u32Bytes_length]
    rw [show 4 + 4 = 8 by omega]
    iframe
  have hdrop : ((bytes.drop start).drop 8).drop 8 =
      (bytes.drop start).drop 16 := by rw [List.drop_drop]
  isimp only [hdrop] at Htail0
  unfold replaceU32SixWindow
  have hbeforeLen : (bytes.take start).length = start :=
    List.length_take_of_le (by omega)
  iapply (pointsToBytes_append memId addr (bytes.take start)
      (u32Bytes n0 ++ (u32Bytes n1 ++
        (u32Bytes n2 ++ (u32Bytes n3 ++
          replaceU32PairWindow ((bytes.drop start).drop 16) 0 n4 n5))))).mpr
  rw [hbeforeLen]
  isimp only [List.append_assoc] at Htail0
  iframe

end Wasm.SepLogic
