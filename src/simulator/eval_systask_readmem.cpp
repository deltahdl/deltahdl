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
static Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok,
                                bool is_hex, uint32_t width) {
  std::vector<std::pair<bool, bool>> bits;  // (aval, bval), least bit first
  int per_char = is_hex ? 4 : 1;
  for (auto it = tok.rbegin(); it != tok.rend(); ++it) {
    char c = *it;
    if (c == '_') continue;
    uint8_t aval = 0;
    uint8_t bval = 0;
    if (c == 'x' || c == 'X') {
      aval = is_hex ? 0xF : 0x1;
      bval = aval;
    } else if (c == 'z' || c == 'Z' || c == '?') {
      bval = is_hex ? 0xF : 0x1;
    } else {
      int digit = -1;
      if (c >= '0' && c <= '9') {
        digit = c - '0';
      } else if (c >= 'a' && c <= 'f') {
        digit = c - 'a' + 10;
      } else if (c >= 'A' && c <= 'F') {
        digit = c - 'A' + 10;
      }
      if (digit < 0) continue;
      aval = static_cast<uint8_t>(digit);
    }
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
template <class AddrFn, class WordFn>
static void ScanMemFile(const std::string& content, AddrFn on_addr,
                        WordFn on_word) {
  auto is_space = [](char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
           c == '\v';
  };
  size_t pos = 0;
  size_t n = content.size();
  while (pos < n) {
    char c = content[pos];
    if (is_space(c)) {
      ++pos;
      continue;
    }
    // §21.4: both comment forms are permitted between numbers.
    if (c == '/' && pos + 1 < n && content[pos + 1] == '/') {
      pos += 2;
      while (pos < n && content[pos] != '\n') ++pos;
      continue;
    }
    if (c == '/' && pos + 1 < n && content[pos + 1] == '*') {
      pos += 2;
      while (pos + 1 < n && (content[pos] != '*' || content[pos + 1] != '/')) {
        ++pos;
      }
      pos = (pos + 1 < n) ? pos + 2 : n;
      continue;
    }
    // A token is a maximal run of characters bounded by white space or a
    // comment.
    size_t begin = pos;
    while (pos < n) {
      char t = content[pos];
      if (is_space(t)) break;
      if (t == '/' && pos + 1 < n &&
          (content[pos + 1] == '/' || content[pos + 1] == '*')) {
        break;
      }
      ++pos;
    }
    std::string tok = content.substr(begin, pos - begin);
    if (tok.empty()) continue;

    if (tok[0] == '@') {
      // §21.4: an @-address is a hexadecimal index that repositions the load
      // cursor; no white space separates the '@' from its digits.
      auto addr =
          static_cast<int64_t>(std::strtoull(tok.c_str() + 1, nullptr, 16));
      if (!on_addr(addr)) return;
    } else {
      if (!on_word(tok)) return;
    }
  }
}

// §21.4: drives the address-windowed load shared by an ordinary unpacked array
// and by the §21.4.1 dynamic-array / queue forms. The window [low_addr,
// high_addr] is the set of addresses that may receive data; `store` deposits a
// parsed word at an address already known to lie within the window. The
// optional start_addr / finish_addr arguments fix the initial cursor, the load
// direction, and (with no file address) the expected word count.
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
  int64_t cursor = has_start ? start_addr : low_addr;

  // The address window the system-task arguments permit. When the task names a
  // start (and optionally a finish), addresses appearing in the file must lie
  // within this window.
  int64_t task_lo = has_finish ? std::min(start_addr, finish_addr) : start_addr;
  int64_t task_hi = has_finish ? std::max(start_addr, finish_addr) : high_addr;

  // §21.4: when slice syntax names the memory, the start_addr and finish_addr
  // arguments must fall within the slice's bounds.
  if (is_slice && has_start &&
      (start_addr < low_addr || start_addr > high_addr ||
       (has_finish && (finish_addr < low_addr || finish_addr > high_addr)))) {
    ctx.GetDiag().Error({},
                        "$readmem" + std::string(is_hex ? "h" : "b") +
                            ": start/finish address outside the slice bounds");
    return;
  }

  auto write_word = [&](int64_t addr, const Logic4Vec& v) {
    if (addr < low_addr || addr > high_addr) return;
    store(addr, v);
  };

  bool addr_in_file = false;
  bool aborted = false;
  uint64_t data_words = 0;
  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        addr_in_file = true;
        if (has_start && (addr < task_lo || addr > task_hi)) {
          // §21.4: a file address outside the task-specified window is an error
          // and ends the load.
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": file address outside the range given by the task");
          aborted = true;
          return false;
        }
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, elem_width);
        // §21.4.2: a 2-state element retains no x/z; convert them to 0.
        if (two_state) CoerceToTwoState(word);
        // §21.4.2 (shall): a value outside the range of the enumerated element
        // type is an error, and no further data is read.
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          aborted = true;
          return false;
        }
        write_word(cursor, word);
        ++data_words;
        cursor += descending ? -1 : 1;
        return true;
      });

  // §21.4: with an explicit start-through-finish window and no addresses in the
  // file, the data-word count must match the window size, else a warning is
  // issued. Addresses not covered by the file are left unmodified, which the
  // write loop above already guarantees.
  if (!aborted && has_start && has_finish && !addr_in_file) {
    auto span = static_cast<uint64_t>(task_hi - task_lo + 1);
    if (data_words != span) {
      ctx.GetDiag().Warning(
          {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                  ": number of data words differs from the address range");
    }
  }
}

// §21.4.1: loads an associative array. Each address — the start_addr default,
// the running cursor, or an @-address in the file — names an integral key, and
// depositing a word at a key creates the element when it does not already
// exist. The pattern file addresses elements numerically; when the index is an
// enumerated type, that number is the underlying numeric value of the
// enumeration element (see 6.19).
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
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, aa->elem_width);
        // §21.4.2: a 2-state element retains no x/z; convert them to 0.
        if (two_state) CoerceToTwoState(word);
        // §21.4.2 (shall): an out-of-range value for an enumerated element type
        // is an error that ends the load.
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          return false;
        }
        // §21.4.1: loading an address creates its element if absent.
        aa->int_data[cursor] = word;
        cursor += descending ? -1 : 1;
        return true;
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
static void EvalReadmemMultiDim(SimContext& ctx, Arena& arena, bool is_hex,
                                const std::string& content,
                                const std::string& mem_name,
                                const ArrayInfo* ai, bool two_state,
                                const EnumTypeInfo* enum_info) {
  const std::vector<uint32_t>& los = ai->dim_los;
  const std::vector<uint32_t>& sizes = ai->dim_sizes;
  const size_t ndim = sizes.size();

  // §21.4.3: the number of subwords enclosed by a single highest-dimension word
  // is the product of every lower dimension's extent.
  uint64_t inner = 1;
  for (size_t d = 1; d < ndim; ++d) inner *= sizes[d];
  if (inner == 0) return;

  const auto top_lo = static_cast<int64_t>(los[0]);
  const int64_t top_hi = top_lo + static_cast<int64_t>(sizes[0]) - 1;

  // §21.4.3: a global position numbers every element of the array in row-major
  // order, so a sequential file fills element 0, 1, 2, ... regardless of how
  // the dimensions nest. The element name carries one bracketed subscript per
  // dimension (mem[i0][i1]...), each running from its dimension's low address.
  auto element_at = [&](uint64_t global) -> std::string {
    uint64_t top = global / inner;
    uint64_t flat = global % inner;
    std::string nm = mem_name + "[" +
                     std::to_string(top_lo + static_cast<int64_t>(top)) + "]";
    // Decompose the within-word position into per-dimension subscripts,
    // innermost first (it varies fastest), then emit them outer-to-inner.
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
  };

  const uint64_t total = static_cast<uint64_t>(sizes[0]) * inner;
  uint64_t cursor = 0;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        // §21.4.3: an address entry names a highest-dimension word. Loading
        // resumes at the first subword enclosed by that word.
        if (addr < top_lo || addr > top_hi) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": file address outside the highest dimension's range");
          return false;
        }
        cursor = static_cast<uint64_t>(addr - top_lo) * inner;
        return true;
      },
      [&](const std::string& tok) -> bool {
        if (cursor >= total) return false;  // array full; nothing more to fill
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, ai->elem_width);
        if (two_state) CoerceToTwoState(word);
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          return false;
        }
        if (auto* var = ctx.FindVariable(element_at(cursor))) var->value = word;
        ++cursor;
        return true;
      });
}

// §21.4: deposits a block of load text into a memory, sharing the addressing
// rules across $readmemb / $readmemh and the §D.14 $sreadmemb / $sreadmemh
// string forms. `mn` is the destination memory_name expression (a bare unpacked
// array or a slice of one); `content` is the text whose tokens are parsed with
// the §21.4 grammar. The optional start/finish window arguments are resolved by
// the caller, since the two task families place them at different argument
// positions.
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
  if (mn->kind == ExprKind::kIdentifier) {
    base_id = mn;
  } else if (mn->kind == ExprKind::kSelect && mn->index_end != nullptr &&
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
  } else {
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

  // §21.4.1: a dynamic array or queue loads into its existing elements. The
  // current size is fixed for the load, so an address beyond the last element
  // is simply dropped — the array is never resized to make room.
  if (QueueObject* q = ctx.FindQueue(mem_name)) {
    int64_t low_addr = 0;
    int64_t high_addr = static_cast<int64_t>(q->elements.size()) - 1;
    if (is_slice) {
      low_addr = std::max(slice_lo, low_addr);
      high_addr = std::min(slice_hi, high_addr);
    }
    EvalReadmemIndexed(ctx, arena, is_hex, content, low_addr, high_addr,
                       is_slice, q->elem_width, !q->is_4state, enum_info,
                       has_start, has_finish, start_arg, finish_arg,
                       [&](int64_t addr, const Logic4Vec& v) {
                         q->elements[static_cast<size_t>(addr)] = v;
                       });
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

// §21.5: $writememb / $writememh dump a memory array's words to a file in a
// form the matching $readmemb / $readmemh can load back. Each word is written
// on its own line in binary ($writememb) or hexadecimal ($writememh).
// §21.5.3 fixes whether @-address specifiers accompany the words: an unpacked
// or dynamic array is written as a bare sequence (a sequential read reloads
// it), while an associative array prefixes every entry with its @-address.
Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  if (expr->args[1]->kind != ExprKind::kIdentifier) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string mem_name(expr->args[1]->text);

  // §21.5: an existing file is overwritten; there is no append mode, so open
  // with truncation and discard any prior contents.
  std::ofstream ofs(filename, std::ios::out | std::ios::trunc);
  if (!ofs.is_open()) {
    std::cerr << "WARNING: $writemem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // Render one word in the radix the companion read task expects. FormatArg
  // carries arbitrary widths and preserves x/z bits, so the output stays
  // readable for vectors wider than a machine word.
  auto emit = [&](const Logic4Vec& v) {
    ofs << FormatArg(v, is_hex ? 'h' : 'b') << "\n";
  };

  // §21.5.3: an associative array's keys are sparse, so a plain sequential read
  // could not place its words. Each entry is therefore written with an
  // @-address ahead of its value. The keys are integral (§21.4.1) and emitted
  // in ascending order as hexadecimal, matching the @-address form $readmem
  // parses.
  if (const AssocArrayObject* aa = ctx.FindAssocArray(mem_name)) {
    for (const auto& entry : aa->int_data) {
      char addr_buf[20];
      std::snprintf(addr_buf, sizeof(addr_buf), "%llx",
                    static_cast<unsigned long long>(entry.first));
      ofs << "@" << addr_buf << "\n";
      emit(entry.second);
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §21.5.3: a dynamic array or queue is written as a bare sequence of words
  // with no @-address specifiers, exactly like a fixed unpacked array, so a
  // sequential $readmem reloads it. The optional start_addr / finish_addr
  // bound the element indices that are written.
  if (const QueueObject* q = ctx.FindQueue(mem_name)) {
    int64_t arr_lo = 0;
    int64_t arr_hi = static_cast<int64_t>(q->elements.size()) - 1;
    bool has_start = expr->args.size() >= 3;
    bool has_finish = expr->args.size() >= 4;
    int64_t start_addr =
        has_start ? static_cast<int64_t>(
                        EvalExpr(expr->args[2], ctx, arena).ToUint64())
                  : arr_lo;
    int64_t finish_addr =
        has_finish ? static_cast<int64_t>(
                         EvalExpr(expr->args[3], ctx, arena).ToUint64())
                   : arr_hi;
    if (arr_hi < arr_lo) return MakeLogic4VecVal(arena, 1, 0);
    int64_t step = (start_addr <= finish_addr) ? 1 : -1;
    for (int64_t addr = start_addr;; addr += step) {
      if (addr >= arr_lo && addr <= arr_hi) {
        emit(q->elements[static_cast<size_t>(addr)]);
      }
      if (addr == finish_addr) break;
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (const ArrayInfo* ai = ctx.FindArrayInfo(mem_name)) {
    int64_t arr_lo = ai->lo;
    int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
    // The optional start_addr / finish_addr bound the range that is written;
    // a finish below start emits the words in descending address order.
    bool has_start = expr->args.size() >= 3;
    bool has_finish = expr->args.size() >= 4;
    int64_t start_addr =
        has_start ? static_cast<int64_t>(
                        EvalExpr(expr->args[2], ctx, arena).ToUint64())
                  : arr_lo;
    int64_t finish_addr =
        has_finish ? static_cast<int64_t>(
                         EvalExpr(expr->args[3], ctx, arena).ToUint64())
                   : arr_hi;
    int64_t step = (start_addr <= finish_addr) ? 1 : -1;
    for (int64_t addr = start_addr;; addr += step) {
      if (addr >= arr_lo && addr <= arr_hi) {
        std::string elem = mem_name + "[" + std::to_string(addr) + "]";
        if (auto* var = ctx.FindVariable(elem)) emit(var->value);
      }
      if (addr == finish_addr) break;
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // A plain variable names a single memory word.
  if (auto* target = ctx.FindVariable(mem_name)) emit(target->value);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
