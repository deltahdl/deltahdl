#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §21.4: a number in the load file carries neither a length nor a base; the
// task name fixes the radix (binary for $readmemb, hexadecimal for $readmemh).
// The unknown value (x), the high-impedance value (z), and underscores may
// appear within a number, so the token is parsed into a 4-state element value
// rather than a plain integer. Underscores are discarded separators; x/z
// preserve their per-bit nature in the loaded word.
// §21.4: decodes one character of a memory-load number into its (aval, bval)
// pair. A digit fixes aval; x/z/? set the unknown/high-impedance pattern across
// the character's bit span (4 bits for hex, 1 for binary). Returns false when
// the character is not part of a number (any non-digit/x/z/? such as '_'), in
// which case the caller skips it; out-args are unchanged on a false return.
static bool DecodeMemNumberChar(char c, bool is_hex, uint8_t& aval,
                                uint8_t& bval) {
  aval = 0;
  bval = 0;
  if (c == 'x' || c == 'X') {
    aval = is_hex ? 0xF : 0x1;
    bval = aval;
    return true;
  }
  if (c == 'z' || c == 'Z' || c == '?') {
    bval = is_hex ? 0xF : 0x1;
    return true;
  }
  int digit = -1;
  if (c >= '0' && c <= '9') {
    digit = c - '0';
  } else if (c >= 'a' && c <= 'f') {
    digit = c - 'a' + 10;
  } else if (c >= 'A' && c <= 'F') {
    digit = c - 'A' + 10;
  }
  if (digit < 0) return false;
  aval = static_cast<uint8_t>(digit);
  return true;
}

static Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok,
                                bool is_hex, uint32_t width) {
  std::vector<std::pair<bool, bool>> bits;  // (aval, bval), least bit first
  int per_char = is_hex ? 4 : 1;
  for (auto it = tok.rbegin(); it != tok.rend(); ++it) {
    char c = *it;
    if (c == '_') continue;
    uint8_t aval = 0;
    uint8_t bval = 0;
    if (!DecodeMemNumberChar(c, is_hex, aval, bval)) continue;
    for (int b = 0; b < per_char; ++b) {
      bits.push_back({(aval >> b) & 1, (bval >> b) & 1});
    }
  }
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < width && i < bits.size(); ++i) {
    if (bits[i].first) vec.words[i / 64].aval |= uint64_t{1} << (i % 64);
    if (bits[i].second) vec.words[i / 64].bval |= uint64_t{1} << (i % 64);
  }
  return vec;
}

// §21.4.2: a 2-state destination — such as an int or bit vector, or an
// enumerated type with a 2-state base — cannot hold x or z, so any unknown or
// high-impedance bit read from the load file is turned into 0. In the 4-state
// encoding an x bit is aval=bval=1 and a z bit is aval=0/bval=1; clearing every
// bit whose bval is set and then dropping bval reduces both to a plain 0, while
// 0 and 1 bits are left unchanged. Reading otherwise proceeds exactly as for a
// 4-state element type.
static void CoerceToTwoState(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// §21.4.2: file data for an enumerated destination is the numeric value of one
// of the type's elements (see 6.19). A number matching no element is out of
// range for the type.
static bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v) {
  uint64_t val = v.ToUint64();
  for (const auto& m : info->members) {
    if (m.value == val) return true;
  }
  return false;
}

// §21.4: walks a memory-load text file in file order. White space and both
// comment styles separate tokens. Each @-address (a hexadecimal index with no
// intervening white space) is handed to on_addr; each unsized number is handed
// to on_word (see ParseMemNumber for its grammar). Either callback returns
// false to abort the scan (an out-of-range address, for example).
// §21.4: true for the white space that separates load-file tokens.
static bool IsMemFileSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

// §21.4: when `pos` sits at the start of a comment, advances it past the whole
// comment and returns true; otherwise leaves `pos` untouched and returns false.
// Both the // line form and the /* */ block form are recognized.
static bool SkipMemFileComment(const std::string& content, size_t n,
                               size_t& pos) {
  char c = content[pos];
  if (c == '/' && pos + 1 < n && content[pos + 1] == '/') {
    pos += 2;
    while (pos < n && content[pos] != '\n') ++pos;
    return true;
  }
  if (c == '/' && pos + 1 < n && content[pos + 1] == '*') {
    pos += 2;
    while (pos + 1 < n && (content[pos] != '*' || content[pos + 1] != '/')) {
      ++pos;
    }
    pos = (pos + 1 < n) ? pos + 2 : n;
    return true;
  }
  return false;
}

// §21.4: reads a token starting at `pos` — a maximal run of characters bounded
// by white space or the start of a comment — advancing `pos` past it.
static std::string ScanMemFileToken(const std::string& content, size_t n,
                                    size_t& pos) {
  size_t begin = pos;
  while (pos < n) {
    char t = content[pos];
    if (IsMemFileSpace(t)) break;
    if (t == '/' && pos + 1 < n &&
        (content[pos + 1] == '/' || content[pos + 1] == '*')) {
      break;
    }
    ++pos;
  }
  return content.substr(begin, pos - begin);
}

// §21.4: dispatches one scanned token to the address or word callback. Returns
// false (to stop the scan) only when the chosen callback asks to abort.
template <class AddrFn, class WordFn>
static bool DispatchMemFileToken(const std::string& tok, AddrFn& on_addr,
                                 WordFn& on_word) {
  if (tok[0] == '@') {
    // §21.4: an @-address is a hexadecimal index that repositions the load
    // cursor; no white space separates the '@' from its digits.
    auto addr =
        static_cast<int64_t>(std::strtoull(tok.c_str() + 1, nullptr, 16));
    return on_addr(addr);
  }
  return on_word(tok);
}

template <class AddrFn, class WordFn>
static void ScanMemFile(const std::string& content, AddrFn on_addr,
                        WordFn on_word) {
  size_t pos = 0;
  size_t n = content.size();
  while (pos < n) {
    char c = content[pos];
    if (IsMemFileSpace(c)) {
      ++pos;
      continue;
    }
    // §21.4: both comment forms are permitted between numbers.
    if (SkipMemFileComment(content, n, pos)) continue;
    // A token is a maximal run of characters bounded by white space or a
    // comment.
    std::string tok = ScanMemFileToken(content, n, pos);
    if (tok.empty()) continue;

    if (!DispatchMemFileToken(tok, on_addr, on_word)) return;
  }
}

// §21.4: drives the address-windowed load shared by an ordinary unpacked array
// and by the §21.4.1 dynamic-array / queue forms. The window [low_addr,
// high_addr] is the set of addresses that may receive data; `store` deposits a
// parsed word at an address already known to lie within the window. The
// optional start_addr / finish_addr arguments fix the initial cursor, the load
// direction, and (with no file address) the expected word count.
// §21.4 / §21.4.2: parses one load-file token into a word for an element of the
// given width, applying the destination's two-state coercion and enumerated-
// range check. On an out-of-range enumerated value it emits the diagnostic and
// returns false (the load must stop); otherwise it fills `out` and returns
// true.
static bool ParseReadmemWord(SimContext& ctx, Arena& arena, bool is_hex,
                             const std::string& tok, uint32_t elem_width,
                             bool two_state, const EnumTypeInfo* enum_info,
                             Logic4Vec& out) {
  out = ParseMemNumber(arena, tok, is_hex, elem_width);
  // §21.4.2: a 2-state element retains no x/z; convert them to 0.
  if (two_state) CoerceToTwoState(out);
  // §21.4.2 (shall): a value outside the range of the enumerated element type
  // is an error, and no further data is read.
  if (enum_info && !EnumValueInRange(enum_info, out)) {
    ctx.GetDiag().Error({}, "$readmem" + std::string(is_hex ? "h" : "b") +
                                ": value out of range for the enumerated type");
    return false;
  }
  return true;
}

// §21.4: when slice syntax names the memory, the task's start/finish addresses
// must fall within the slice's bounds. Emits the diagnostic and returns false
// when they do not (the load should then abort); returns true otherwise.
static bool CheckReadmemSliceBounds(SimContext& ctx, bool is_hex, bool is_slice,
                                    bool has_start, bool has_finish,
                                    int64_t start_addr, int64_t finish_addr,
                                    int64_t low_addr, int64_t high_addr) {
  if (is_slice && has_start &&
      (start_addr < low_addr || start_addr > high_addr ||
       (has_finish && (finish_addr < low_addr || finish_addr > high_addr)))) {
    ctx.GetDiag().Error({},
                        "$readmem" + std::string(is_hex ? "h" : "b") +
                            ": start/finish address outside the slice bounds");
    return false;
  }
  return true;
}

// §21.4: with an explicit start-through-finish window and no addresses in the
// file, the data-word count must match the window size, else a warning is
// issued. Addresses not covered by the file are left unmodified by the caller.
static void WarnReadmemWordCount(SimContext& ctx, bool is_hex, bool has_start,
                                 bool has_finish, bool addr_in_file,
                                 uint64_t data_words, int64_t task_lo,
                                 int64_t task_hi) {
  if (has_start && has_finish && !addr_in_file) {
    auto span = static_cast<uint64_t>(task_hi - task_lo + 1);
    if (data_words != span) {
      ctx.GetDiag().Warning(
          {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                  ": number of data words differs from the address range");
    }
  }
}

// §21.4: the mutable cursor state carried through an indexed (windowed) load:
// the running address, whether any @-address was seen, the parsed-word count,
// and an abort flag set when a callback ends the scan early.
struct IndexedLoadState {
  int64_t cursor = 0;
  bool addr_in_file = false;
  bool aborted = false;
  uint64_t data_words = 0;
};

// §21.4: handles an @-address during an indexed load. A file address outside
// the task-specified window is an error that ends the load; otherwise the
// cursor jumps to the address. Returns false to stop the scan.
static bool HandleIndexedAddr(SimContext& ctx, bool is_hex, bool has_start,
                              int64_t task_lo, int64_t task_hi, int64_t addr,
                              IndexedLoadState& st) {
  st.addr_in_file = true;
  if (has_start && (addr < task_lo || addr > task_hi)) {
    ctx.GetDiag().Error(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": file address outside the range given by the task");
    st.aborted = true;
    return false;
  }
  st.cursor = addr;
  return true;
}

// §21.4: handles one data word during an indexed load: parses the token, writes
// it through `write_word` when the cursor lies inside the load window, then
// advances the cursor in the load direction. Returns false to stop the scan.
template <class WriteFn>
static bool HandleIndexedWord(SimContext& ctx, Arena& arena, bool is_hex,
                              uint32_t elem_width, bool two_state,
                              const EnumTypeInfo* enum_info, bool descending,
                              const std::string& tok, WriteFn& write_word,
                              IndexedLoadState& st) {
  Logic4Vec word;
  if (!ParseReadmemWord(ctx, arena, is_hex, tok, elem_width, two_state,
                        enum_info, word)) {
    st.aborted = true;
    return false;
  }
  write_word(st.cursor, word);
  ++st.data_words;
  st.cursor += descending ? -1 : 1;
  return true;
}

template <class StoreFn>
static void EvalReadmemIndexed(SimContext& ctx, Arena& arena, bool is_hex,
                               const std::string& content, int64_t low_addr,
                               int64_t high_addr, bool is_slice,
                               uint32_t elem_width, bool two_state,
                               const EnumTypeInfo* enum_info, bool has_start,
                               bool has_finish, int64_t start_arg,
                               int64_t finish_arg, StoreFn store) {
  // The window arguments are resolved by the caller because $readmem and
  // $sreadmem (§D.14) carry them at different argument positions; an absent
  // start/finish falls back to the memory's own bounds.
  int64_t start_addr = has_start ? start_arg : low_addr;
  int64_t finish_addr = has_finish ? finish_arg : high_addr;

  // §21.4: the direction of the highest dimension's entries follows the
  // relative magnitudes of start_addr and finish_addr. Loading runs downward
  // only when both bounds are supplied and start exceeds finish; otherwise it
  // runs upward. The chosen direction persists even past an @-address.
  bool descending = has_start && has_finish && start_addr > finish_addr;

  // The address window the system-task arguments permit. When the task names a
  // start (and optionally a finish), addresses appearing in the file must lie
  // within this window.
  int64_t task_lo = has_finish ? std::min(start_addr, finish_addr) : start_addr;
  int64_t task_hi = has_finish ? std::max(start_addr, finish_addr) : high_addr;

  // §21.4: when slice syntax names the memory, the start_addr and finish_addr
  // arguments must fall within the slice's bounds.
  if (!CheckReadmemSliceBounds(ctx, is_hex, is_slice, has_start, has_finish,
                               start_addr, finish_addr, low_addr, high_addr)) {
    return;
  }

  auto write_word = [&](int64_t addr, const Logic4Vec& v) {
    if (addr < low_addr || addr > high_addr) return;
    store(addr, v);
  };

  IndexedLoadState st;
  st.cursor = has_start ? start_addr : low_addr;
  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        return HandleIndexedAddr(ctx, is_hex, has_start, task_lo, task_hi, addr,
                                 st);
      },
      [&](const std::string& tok) -> bool {
        return HandleIndexedWord(ctx, arena, is_hex, elem_width, two_state,
                                 enum_info, descending, tok, write_word, st);
      });

  // §21.4: with an explicit start-through-finish window and no addresses in the
  // file, the data-word count must match the window size. Addresses not covered
  // by the file are left unmodified, which the write loop above guarantees.
  if (!st.aborted) {
    WarnReadmemWordCount(ctx, is_hex, has_start, has_finish, st.addr_in_file,
                         st.data_words, task_lo, task_hi);
  }
}

// §21.4.1: loads an associative array. Each address — the start_addr default,
// the running cursor, or an @-address in the file — names an integral key, and
// depositing a word at a key creates the element when it does not already
// exist. The pattern file addresses elements numerically; when the index is an
// enumerated type, that number is the underlying numeric value of the
// enumeration element (see 6.19).
// §21.4.1: handles one data word during an associative-array load: parses the
// token, deposits it at the running key (creating the element if absent), then
// advances the cursor in the load direction. Returns false to stop the scan.
static bool HandleAssocWord(SimContext& ctx, Arena& arena, bool is_hex,
                            AssocArrayObject* aa, bool two_state,
                            const EnumTypeInfo* enum_info, bool descending,
                            const std::string& tok, int64_t& cursor) {
  Logic4Vec word;
  if (!ParseReadmemWord(ctx, arena, is_hex, tok, aa->elem_width, two_state,
                        enum_info, word)) {
    return false;
  }
  // §21.4.1: loading an address creates its element if absent.
  aa->int_data[cursor] = word;
  cursor += descending ? -1 : 1;
  return true;
}

static void EvalReadmemAssoc(SimContext& ctx, Arena& arena, bool is_hex,
                             const std::string& content, AssocArrayObject* aa,
                             bool two_state, const EnumTypeInfo* enum_info,
                             bool has_start, bool has_finish, int64_t start_arg,
                             int64_t finish_arg) {
  // §21.4.1: the index of an associative array loaded this way shall be of an
  // integral type. A string-keyed array has no numeric address form, so it
  // cannot be loaded.
  if (aa->is_string_key) {
    ctx.GetDiag().Error(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": associative array index must be of an integral type");
    return;
  }

  // The window arguments are resolved by the caller (their position differs
  // between $readmem and the §D.14 $sreadmem forms).
  int64_t start_addr = has_start ? start_arg : 0;
  int64_t finish_addr = has_finish ? finish_arg : 0;
  bool descending = has_start && has_finish && start_addr > finish_addr;
  int64_t cursor = start_addr;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        return HandleAssocWord(ctx, arena, is_hex, aa, two_state, enum_info,
                               descending, tok, cursor);
      });
}

// §21.4.3: loads a multidimensional unpacked array. The file is read in
// row-major order: the lowest (rightmost-declared) dimension varies the most
// rapidly, and each higher dimension's word entirely encloses the lower-
// dimension words beneath it. Every dimension's entries run from low to high
// address, so reversing the ascending/descending sense of a dimension's
// declaration does not change the file layout. An @-address in the file
// exclusively names a word of the highest (leftmost-declared) dimension and
// repositions the load to the first subword of that word. With or without
// addresses, when the file runs out of data the load stops and any array words
// or subwords not yet reached are left unchanged.
// §21.4.3: maps a row-major global element position to its element name. A
// sequential file fills element 0, 1, 2, ... regardless of how the dimensions
// nest; the name carries one bracketed subscript per dimension
// (mem[i0][i1]...), each running from its dimension's low address. `inner` is
// the subword count enclosed by one highest-dimension word.
static std::string MultiDimElementName(const std::string& mem_name,
                                       const std::vector<uint32_t>& los,
                                       const std::vector<uint32_t>& sizes,
                                       size_t ndim, uint64_t inner,
                                       int64_t top_lo, uint64_t global) {
  uint64_t top = global / inner;
  uint64_t flat = global % inner;
  std::string nm =
      mem_name + "[" + std::to_string(top_lo + static_cast<int64_t>(top)) + "]";
  // Decompose the within-word position into per-dimension subscripts, innermost
  // first (it varies fastest), then emit them outer-to-inner.
  std::vector<int64_t> subs(ndim - 1);
  for (size_t d = ndim - 1; d >= 1; --d) {
    subs[d - 1] =
        static_cast<int64_t>(los[d]) + static_cast<int64_t>(flat % sizes[d]);
    flat /= sizes[d];
  }
  for (size_t d = 1; d < ndim; ++d) {
    nm += "[" + std::to_string(subs[d - 1]) + "]";
  }
  return nm;
}

// §21.4.3: handles an @-address during a multidimensional load. The address
// names a highest-dimension word; loading resumes at the first subword it
// encloses. An address outside the highest dimension's range is an error.
// Returns false to stop the scan.
static bool HandleMultiDimAddr(SimContext& ctx, bool is_hex, int64_t top_lo,
                               int64_t top_hi, uint64_t inner, int64_t addr,
                               uint64_t& cursor) {
  if (addr < top_lo || addr > top_hi) {
    ctx.GetDiag().Error(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": file address outside the highest dimension's range");
    return false;
  }
  cursor = static_cast<uint64_t>(addr - top_lo) * inner;
  return true;
}

// §21.4.3: handles one data word during a multidimensional load: stops when the
// array is already full, otherwise parses the token, writes it to the element
// named by the running row-major position, and advances the cursor. Returns
// false to stop the scan.
static bool HandleMultiDimWord(SimContext& ctx, Arena& arena, bool is_hex,
                               const std::string& mem_name, const ArrayInfo* ai,
                               const std::vector<uint32_t>& los,
                               const std::vector<uint32_t>& sizes, size_t ndim,
                               uint64_t inner, int64_t top_lo, uint64_t total,
                               bool two_state, const EnumTypeInfo* enum_info,
                               const std::string& tok, uint64_t& cursor) {
  if (cursor >= total) return false;  // array full; nothing more to fill
  Logic4Vec word;
  if (!ParseReadmemWord(ctx, arena, is_hex, tok, ai->elem_width, two_state,
                        enum_info, word)) {
    return false;
  }
  std::string elem =
      MultiDimElementName(mem_name, los, sizes, ndim, inner, top_lo, cursor);
  if (auto* var = ctx.FindVariable(elem)) var->value = word;
  ++cursor;
  return true;
}

static void EvalReadmemMultiDim(SimContext& ctx, Arena& arena, bool is_hex,
                                const std::string& content,
                                const std::string& mem_name,
                                const ArrayInfo* ai, bool two_state,
                                const EnumTypeInfo* enum_info) {
  const std::vector<uint32_t>& los = ai->dim_los;
  const std::vector<uint32_t>& sizes = ai->dim_sizes;
  const size_t kNdim = sizes.size();

  // §21.4.3: the number of subwords enclosed by a single highest-dimension word
  // is the product of every lower dimension's extent.
  uint64_t inner = 1;
  for (size_t d = 1; d < kNdim; ++d) inner *= sizes[d];
  if (inner == 0) return;

  const auto kTopLo = static_cast<int64_t>(los[0]);
  const int64_t kTopHi = kTopLo + static_cast<int64_t>(sizes[0]) - 1;

  const uint64_t kTotal = static_cast<uint64_t>(sizes[0]) * inner;
  uint64_t cursor = 0;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        return HandleMultiDimAddr(ctx, is_hex, kTopLo, kTopHi, inner, addr,
                                  cursor);
      },
      [&](const std::string& tok) -> bool {
        return HandleMultiDimWord(ctx, arena, is_hex, mem_name, ai, los, sizes,
                                  kNdim, inner, kTopLo, kTotal, two_state,
                                  enum_info, tok, cursor);
      });
}

// §21.4: deposits a block of load text into a memory, sharing the addressing
// rules across $readmemb / $readmemh and the §D.14 $sreadmemb / $sreadmemh
// string forms. `mn` is the destination memory_name expression (a bare unpacked
// array or a slice of one); `content` is the text whose tokens are parsed with
// the §21.4 grammar. The optional start/finish window arguments are resolved by
// the caller, since the two task families place them at different argument
// positions.
// §21.4: resolves the memory_name expression — a bare unpacked array or a slice
// of one (the lowest dimension may use slice syntax, see 7.4.5). On a bare
// identifier `is_slice` is left false; on a slice it is set and
// slice_lo/slice_hi are evaluated (low/high ordered). Returns false for an
// unsupported expression form, in which case the caller should do nothing.
static bool ResolveMemName(SimContext& ctx, Arena& arena, const Expr* mn,
                           const Expr*& base_id, bool& is_slice,
                           int64_t& slice_lo, int64_t& slice_hi) {
  if (mn->kind == ExprKind::kIdentifier) {
    base_id = mn;
    return true;
  }
  if (mn->kind == ExprKind::kSelect && mn->index_end != nullptr &&
      !mn->is_part_select_plus && !mn->is_part_select_minus &&
      mn->base != nullptr && mn->base->kind == ExprKind::kIdentifier) {
    base_id = mn->base;
    is_slice = true;
    int64_t a =
        static_cast<int64_t>(EvalExpr(mn->index, ctx, arena).ToUint64());
    int64_t b =
        static_cast<int64_t>(EvalExpr(mn->index_end, ctx, arena).ToUint64());
    slice_lo = std::min(a, b);
    slice_hi = std::max(a, b);
    return true;
  }
  return false;
}

// §21.4.1: loads a dynamic array or queue, whose size is fixed for the load (an
// address beyond the last element is dropped, never resized to make room). A
// slice narrows the address window to its own bounds, clamped to the array.
static void LoadMemQueue(SimContext& ctx, Arena& arena, bool is_hex,
                         const std::string& content, QueueObject* q,
                         const EnumTypeInfo* enum_info, bool is_slice,
                         int64_t slice_lo, int64_t slice_hi, bool has_start,
                         bool has_finish, int64_t start_arg,
                         int64_t finish_arg) {
  int64_t low_addr = 0;
  int64_t high_addr = static_cast<int64_t>(q->elements.size()) - 1;
  if (is_slice) {
    low_addr = std::max(slice_lo, low_addr);
    high_addr = std::min(slice_hi, high_addr);
  }
  EvalReadmemIndexed(ctx, arena, is_hex, content, low_addr, high_addr, is_slice,
                     q->elem_width, !q->is_4state, enum_info, has_start,
                     has_finish, start_arg, finish_arg,
                     [&](int64_t addr, const Logic4Vec& v) {
                       q->elements[static_cast<size_t>(addr)] = v;
                     });
}

// §21.4: loads a single-dimension unpacked array (or one lower dimension named
// by a slice, see §7.4.5). A slice narrows the load window to its own bounds,
// clamped to the array.
static void LoadMemSingleDim(SimContext& ctx, Arena& arena, bool is_hex,
                             const std::string& content,
                             const std::string& mem_name, const ArrayInfo* ai,
                             const EnumTypeInfo* enum_info, bool is_slice,
                             int64_t slice_lo, int64_t slice_hi, bool has_start,
                             bool has_finish, int64_t start_arg,
                             int64_t finish_arg) {
  int64_t arr_lo = ai->lo;
  int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
  // A slice narrows the load window to its own bounds (clamped to the array).
  int64_t low_addr = is_slice ? std::max(slice_lo, arr_lo) : arr_lo;
  int64_t high_addr = is_slice ? std::min(slice_hi, arr_hi) : arr_hi;

  EvalReadmemIndexed(
      ctx, arena, is_hex, content, low_addr, high_addr, is_slice,
      ai->elem_width, !ai->is_4state, enum_info, has_start, has_finish,
      start_arg, finish_arg, [&](int64_t addr, const Logic4Vec& v) {
        std::string elem = mem_name + "[" + std::to_string(addr) + "]";
        if (auto* var = ctx.FindVariable(elem)) var->value = v;
      });
}

static void DoMemLoad(SimContext& ctx, Arena& arena, bool is_hex,
                      const std::string& content, const Expr* mn,
                      bool has_start, bool has_finish, int64_t start_arg,
                      int64_t finish_arg) {
  // §21.4: memory_name is a bare unpacked array or a slice of one (the lowest
  // dimension may be written with slice syntax, see 7.4.5). The selected index
  // range is the address space the load works over.
  const Expr* base_id = nullptr;
  bool is_slice = false;
  int64_t slice_lo = 0;
  int64_t slice_hi = 0;
  if (!ResolveMemName(ctx, arena, mn, base_id, is_slice, slice_lo, slice_hi)) {
    return;
  }
  std::string mem_name(base_id->text);

  // §21.4.2: when the memory's element type is enumerated, the file numbers are
  // the underlying numeric values of the type's elements and each must name a
  // valid element. A null result means the destination is not enum-typed.
  const EnumTypeInfo* enum_info = ctx.GetVariableEnumType(mem_name);

  // §21.4.1: an associative array is addressed by an integral key; addresses
  // create their elements on demand rather than indexing a fixed window.
  if (AssocArrayObject* aa = ctx.FindAssocArray(mem_name)) {
    EvalReadmemAssoc(ctx, arena, is_hex, content, aa, !aa->is_4state, enum_info,
                     has_start, has_finish, start_arg, finish_arg);
    return;
  }

  // §21.4.1: a dynamic array or queue loads into its existing elements.
  if (QueueObject* q = ctx.FindQueue(mem_name)) {
    LoadMemQueue(ctx, arena, is_hex, content, q, enum_info, is_slice, slice_lo,
                 slice_hi, has_start, has_finish, start_arg, finish_arg);
    return;
  }

  const ArrayInfo* ai = ctx.FindArrayInfo(mem_name);
  if (!ai) return;

  // §21.4.3: a memory with more than one unpacked dimension is filled in
  // row-major order, with @-addresses naming highest-dimension words. (A slice
  // memory_name resolves to a single lower dimension, see §7.4.5, and is
  // handled by the single-dimension path below.)
  if (!is_slice && ai->dim_sizes.size() >= 2) {
    EvalReadmemMultiDim(ctx, arena, is_hex, content, mem_name, ai,
                        !ai->is_4state, enum_info);
    return;
  }

  LoadMemSingleDim(ctx, arena, is_hex, content, mem_name, ai, enum_info,
                   is_slice, slice_lo, slice_hi, has_start, has_finish,
                   start_arg, finish_arg);
}

// §21.4: $readmemb / $readmemh read a text file of white space, comments, and
// unsized numbers into the word elements of an unpacked array. §21.4.1 extends
// the same tasks to dynamic arrays and queues (whose size is fixed for the
// load) and to associative arrays (addressed by an integral key).
Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                      bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  // §21.4: the filename may be a string literal, a string-typed value, or an
  // integral value whose bytes spell the name; EvalStringArg covers all three.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

  std::ifstream ifs(filename);
  if (!ifs.is_open()) {
    ctx.GetDiag().Warning({}, "$readmem" + std::string(is_hex ? "h" : "b") +
                                  ": cannot open file: " + filename);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string content((std::istreambuf_iterator<char>(ifs)),
                      std::istreambuf_iterator<char>());

  // §21.4: the optional start_addr (arg 2) and finish_addr (arg 3) follow the
  // memory_name.
  bool has_start = expr->args.size() >= 3;
  bool has_finish = expr->args.size() >= 4;
  int64_t start_arg =
      has_start
          ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
          : 0;
  int64_t finish_arg =
      has_finish
          ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
          : 0;

  DoMemLoad(ctx, arena, is_hex, content, expr->args[1], has_start, has_finish,
            start_arg, finish_arg);
  return MakeLogic4VecVal(arena, 1, 0);
}

// §D.14: $sreadmemb / $sreadmemh mirror $readmemb / $readmemh but take their
// load data from string arguments rather than a file. The argument order
// differs: the destination memory_name comes first, followed by the start and
// finish addresses that bound where the data is stored, then one or more
// strings. The strings carry the same token format as a $readmem load file, so
// the data is concatenated and handed to the shared loader; a newline between
// adjacent strings keeps their tokens separated.
Logic4Vec EvalSreadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex) {
  // mem_name, start_address, finish_address, and at least one data string.
  if (expr->args.size() < 4) return MakeLogic4VecVal(arena, 1, 0);
  int64_t start_arg =
      static_cast<int64_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  int64_t finish_arg =
      static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());

  std::string content;
  for (size_t i = 3; i < expr->args.size(); ++i) {
    if (i > 3) content += '\n';
    content += EvalStringArg(expr->args[i], ctx, arena);
  }

  DoMemLoad(ctx, arena, is_hex, content, expr->args[0], /*has_start=*/true,
            /*has_finish=*/true, start_arg, finish_arg);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
