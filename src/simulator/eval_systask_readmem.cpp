#include <algorithm>
#include <cstddef>
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
#include "simulator/eval_systask_readmem_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §21.4: the invariant environment of one $readmem / $sreadmem invocation: the
// simulation context, the arena that owns parsed words, and the radix selected
// by the task name (hexadecimal for the *h forms, binary for the *b forms),
// together with where the call was written. Carried as one unit because every
// step of a load needs all four. A load reports against the file contents and
// the destination array rather than against an expression, so the call is the
// position every one of its reports names.
struct ReadmemEnv {
  SimContext& ctx;
  Arena& arena;
  bool is_hex;
  SourceLoc loc;
};

// §21.4.2: the destination element's declared type, which governs how a parsed
// number is fitted to an element: its bit width, whether it is 2-state (so x/z
// collapse to 0), and, when it is an enumerated type, the element list used to
// range-check each loaded value.
struct ReadmemElemType {
  uint32_t elem_width;
  bool two_state;
  const EnumTypeInfo* enum_info;
};

// §21.4: the optional start_addr / finish_addr task arguments. They fix the
// initial load cursor, the load direction, and (with no @-address in the file)
// the expected word count. `has_start` / `has_finish` record which were given;
// $sreadmem (§D.14) always supplies both.
struct ReadmemWindow {
  bool has_start;
  bool has_finish;
  int64_t start_arg;
  int64_t finish_arg;
};

// §21.4 / §7.4.5: a memory_name written as a slice of an unpacked array. When
// `is_slice` is set, [slice_lo, slice_hi] (low/high ordered) narrows the load
// window; on a bare identifier the bounds are unused.
struct MemSlice {
  bool is_slice;
  int64_t slice_lo;
  int64_t slice_hi;
};

// §21.4: dispatches one scanned token to the address or word callback. Returns
// false (to stop the scan) only when the chosen callback asks to abort.
template <class AddrFn, class WordFn>
bool DispatchMemFileToken(const std::string& tok, AddrFn& on_addr,
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
void ScanMemFile(const std::string& content, AddrFn on_addr, WordFn on_word) {
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
static bool ParseReadmemWord(const ReadmemEnv& env, const std::string& tok,
                             const ReadmemElemType& et, Logic4Vec& out) {
  out = ParseMemNumber(env.arena, tok, env.is_hex, et.elem_width);
  // §21.4.2: a 2-state element retains no x/z; convert them to 0.
  if (et.two_state) CoerceToTwoState(out);
  // §21.4.2 (shall): a value outside the range of the enumerated element type
  // is an error, and no further data is read.
  if (et.enum_info && !EnumValueInRange(et.enum_info, out)) {
    env.ctx.GetDiag().Error(env.loc,
                            "$readmem" + std::string(env.is_hex ? "h" : "b") +
                                ": value out of range for the enumerated type",
                            Subclause("21.4.2"));
    return false;
  }
  return true;
}

// §21.4: the addressable window of an indexed (windowed) destination — the
// low/high address bounds the load may write, and whether the memory_name named
// a slice (§7.4.5), which both narrows the window and triggers the slice-bounds
// check on the task's start/finish addresses.
struct MemWindow {
  int64_t low_addr;
  int64_t high_addr;
  bool is_slice;
};

// §21.4: when slice syntax names the memory, the task's resolved start/finish
// addresses (carried in `w`) must fall within the slice's bounds (`mw`). Emits
// the diagnostic and returns false when they do not (the load should then
// abort); returns true otherwise.
static bool CheckReadmemSliceBounds(const ReadmemEnv& env, const MemWindow& mw,
                                    const ReadmemWindow& w) {
  auto outside = [&](int64_t a) { return a < mw.low_addr || a > mw.high_addr; };
  if (mw.is_slice && w.has_start &&
      (outside(w.start_arg) || (w.has_finish && outside(w.finish_arg)))) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": start/finish address outside the slice bounds",
        Subclause("21.4"));
    return false;
  }
  return true;
}

// §21.4: the address window the system-task arguments permit during an indexed
// load. When the task names a start (and optionally a finish), an @-address in
// the file must lie within [task_lo, task_hi]; the flags record which task
// arguments were supplied.
struct TaskAddrRange {
  bool has_start;
  bool has_finish;
  int64_t task_lo;
  int64_t task_hi;
};

// §21.4: the mutable cursor state carried through an indexed (windowed) load:
// the running address, whether any @-address was seen, the parsed-word count,
// and an abort flag set when a callback ends the scan early.
struct IndexedLoadState {
  int64_t cursor = 0;
  bool addr_in_file = false;
  bool aborted = false;
  uint64_t data_words = 0;
};

// §21.4: with an explicit start-through-finish window and no addresses in the
// file, the data-word count must match the window size, else a warning is
// issued. Addresses not covered by the file are left unmodified by the caller.
static void WarnReadmemWordCount(const ReadmemEnv& env,
                                 const TaskAddrRange& range,
                                 const IndexedLoadState& st) {
  if (range.has_start && range.has_finish && !st.addr_in_file) {
    auto span = static_cast<uint64_t>(range.task_hi - range.task_lo + 1);
    if (st.data_words != span) {
      env.ctx.GetDiag().Warning(
          env.loc,
          "$readmem" + std::string(env.is_hex ? "h" : "b") +
              ": number of data words differs from the address range",
          Subclause("21.4"));
    }
  }
}

// §21.4: handles an @-address during an indexed load. A file address outside
// the task-specified window is an error that ends the load; otherwise the
// cursor jumps to the address. Returns false to stop the scan.
static bool HandleIndexedAddr(const ReadmemEnv& env, const TaskAddrRange& range,
                              int64_t addr, IndexedLoadState& st) {
  st.addr_in_file = true;
  if (range.has_start && (addr < range.task_lo || addr > range.task_hi)) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": file address outside the range given by the task",
        Subclause("21.4"));
    st.aborted = true;
    return false;
  }
  st.cursor = addr;
  return true;
}

// §21.4: the per-load constants an indexed-word handler needs beyond the
// environment: the destination element type and the load direction (downward
// only when both task bounds are given and start exceeds finish).
struct IndexedWordCtx {
  ReadmemElemType et;
  bool descending;
};

// §21.4: handles one data word during an indexed load: parses the token, writes
// it through `write_word` when the cursor lies inside the load window, then
// advances the cursor in the load direction. Returns false to stop the scan.
template <class WriteFn>
static bool HandleIndexedWord(const ReadmemEnv& env, const IndexedWordCtx& iwc,
                              const std::string& tok, WriteFn& write_word,
                              IndexedLoadState& st) {
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, iwc.et, word)) {
    st.aborted = true;
    return false;
  }
  write_word(st.cursor, word);
  ++st.data_words;
  st.cursor += iwc.descending ? -1 : 1;
  return true;
}

// §21.4 / §21.4.1: a complete indexed-load request: the destination's address
// window (and slice flag), its declared element type, and the optional task
// start/finish window arguments. Shared by the unpacked-array and the dynamic-
// array / queue forms, which differ only in how they compute the window and
// store a word.
struct IndexedLoadReq {
  MemWindow mw;
  ReadmemElemType et;
  ReadmemWindow w;
};

template <class StoreFn>
static void EvalReadmemIndexed(const ReadmemEnv& env,
                               const std::string& content,
                               const IndexedLoadReq& req, StoreFn store) {
  const MemWindow& mw = req.mw;
  const ReadmemWindow& w = req.w;

  // The window arguments are resolved by the caller because $readmem and
  // $sreadmem (§D.14) carry them at different argument positions; an absent
  // start/finish falls back to the memory's own bounds.
  int64_t start_addr = w.has_start ? w.start_arg : mw.low_addr;
  int64_t finish_addr = w.has_finish ? w.finish_arg : mw.high_addr;

  // §21.4: the direction of the highest dimension's entries follows the
  // relative magnitudes of start_addr and finish_addr. Loading runs downward
  // only when both bounds are supplied and start exceeds finish; otherwise it
  // runs upward. The chosen direction persists even past an @-address.
  bool descending = w.has_start && w.has_finish && start_addr > finish_addr;

  // The address window the system-task arguments permit. When the task names a
  // start (and optionally a finish), addresses appearing in the file must lie
  // within this window.
  TaskAddrRange range;
  range.has_start = w.has_start;
  range.has_finish = w.has_finish;
  range.task_lo = w.has_finish ? std::min(start_addr, finish_addr) : start_addr;
  range.task_hi =
      w.has_finish ? std::max(start_addr, finish_addr) : mw.high_addr;

  // §21.4: when slice syntax names the memory, the resolved start_addr and
  // finish_addr must fall within the slice's bounds.
  ReadmemWindow resolved{w.has_start, w.has_finish, start_addr, finish_addr};
  if (!CheckReadmemSliceBounds(env, mw, resolved)) {
    return;
  }

  auto write_word = [&](int64_t addr, const Logic4Vec& v) {
    if (addr < mw.low_addr || addr > mw.high_addr) return;
    store(addr, v);
  };

  IndexedWordCtx iwc{req.et, descending};
  IndexedLoadState st;
  st.cursor = w.has_start ? start_addr : mw.low_addr;
  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        return HandleIndexedAddr(env, range, addr, st);
      },
      [&](const std::string& tok) -> bool {
        return HandleIndexedWord(env, iwc, tok, write_word, st);
      });

  // §21.4: with an explicit start-through-finish window and no addresses in the
  // file, the data-word count must match the window size. Addresses not covered
  // by the file are left unmodified, which the write loop above guarantees.
  if (!st.aborted) {
    WarnReadmemWordCount(env, range, st);
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
static bool HandleAssocWord(const ReadmemEnv& env, const IndexedWordCtx& iwc,
                            AssocArrayObject* aa, const std::string& tok,
                            int64_t& cursor) {
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, iwc.et, word)) {
    return false;
  }
  // §21.4.1: loading an address creates its element if absent.
  aa->int_data[cursor] = word;
  cursor += iwc.descending ? -1 : 1;
  return true;
}

static void EvalReadmemAssoc(const ReadmemEnv& env, const std::string& content,
                             AssocArrayObject* aa, const ReadmemElemType& et,
                             const ReadmemWindow& w) {
  // §21.4.1: the index of an associative array loaded this way shall be of an
  // integral type. A string-keyed array has no numeric address form, so it
  // cannot be loaded.
  if (aa->is_string_key) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": associative array index must be of an integral type",
        Subclause("21.4.1"));
    return;
  }

  // The window arguments are resolved by the caller (their position differs
  // between $readmem and the §D.14 $sreadmem forms).
  int64_t start_addr = w.has_start ? w.start_arg : 0;
  int64_t finish_addr = w.has_finish ? w.finish_arg : 0;
  bool descending = w.has_start && w.has_finish && start_addr > finish_addr;
  int64_t cursor = start_addr;

  IndexedWordCtx iwc{et, descending};
  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        return HandleAssocWord(env, iwc, aa, tok, cursor);
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
// §21.4.3: the row-major geometry of a multidimensional unpacked array load.
// `los` / `sizes` are the per-dimension low addresses and extents (highest
// dimension first); `ndim` is their count; `inner` is the subword count one
// highest-dimension word encloses (the product of the lower extents); `top_lo`
// / `top_hi` bound the highest dimension; `total` is the element count. The
// vectors are borrowed from the destination's ArrayInfo for the load's
// duration.
struct MultiDimGeom {
  const std::string& mem_name;
  const std::vector<uint32_t>& los;
  const std::vector<uint32_t>& sizes;
  size_t ndim;
  uint64_t inner;
  int64_t top_lo;
  int64_t top_hi;
  uint64_t total;
};

// §21.4.3: maps a row-major global element position to its element name. A
// sequential file fills element 0, 1, 2, ... regardless of how the dimensions
// nest; the name carries one bracketed subscript per dimension
// (mem[i0][i1]...), each running from its dimension's low address.
static std::string MultiDimElementName(const MultiDimGeom& g, uint64_t global) {
  uint64_t top = global / g.inner;
  uint64_t flat = global % g.inner;
  std::string nm = g.mem_name + "[" +
                   std::to_string(g.top_lo + static_cast<int64_t>(top)) + "]";
  // Decompose the within-word position into per-dimension subscripts, innermost
  // first (it varies fastest), then emit them outer-to-inner.
  std::vector<int64_t> subs(g.ndim - 1);
  for (size_t d = g.ndim - 1; d >= 1; --d) {
    subs[d - 1] = static_cast<int64_t>(g.los[d]) +
                  static_cast<int64_t>(flat % g.sizes[d]);
    flat /= g.sizes[d];
  }
  for (size_t d = 1; d < g.ndim; ++d) {
    nm += "[" + std::to_string(subs[d - 1]) + "]";
  }
  return nm;
}

// §21.4.3: handles an @-address during a multidimensional load. The address
// names a highest-dimension word; loading resumes at the first subword it
// encloses. An address outside the highest dimension's range is an error.
// Returns false to stop the scan.
static bool HandleMultiDimAddr(const ReadmemEnv& env, const MultiDimGeom& g,
                               int64_t addr, uint64_t& cursor) {
  if (addr < g.top_lo || addr > g.top_hi) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": file address outside the highest dimension's range",
        Subclause("21.4.3"));
    return false;
  }
  cursor = static_cast<uint64_t>(addr - g.top_lo) * g.inner;
  return true;
}

// §21.4.3: handles one data word during a multidimensional load: stops when the
// array is already full, otherwise parses the token, writes it to the element
// named by the running row-major position, and advances the cursor. Returns
// false to stop the scan.
static bool HandleMultiDimWord(const ReadmemEnv& env, const MultiDimGeom& g,
                               const ReadmemElemType& et,
                               const std::string& tok, uint64_t& cursor) {
  if (cursor >= g.total) return false;  // array full; nothing more to fill
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, et, word)) {
    return false;
  }
  std::string elem = MultiDimElementName(g, cursor);
  if (auto* var = env.ctx.FindVariable(elem)) var->value = word;
  ++cursor;
  return true;
}

static void EvalReadmemMultiDim(const ReadmemEnv& env,
                                const std::string& content,
                                const std::string& mem_name,
                                const ArrayInfo* ai,
                                const ReadmemElemType& et) {
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

  MultiDimGeom geom{mem_name, los, sizes, kNdim, inner, kTopLo, kTopHi, kTotal};
  uint64_t cursor = 0;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        return HandleMultiDimAddr(env, geom, addr, cursor);
      },
      [&](const std::string& tok) -> bool {
        return HandleMultiDimWord(env, geom, et, tok, cursor);
      });
}

// §21.4: deposits a block of load text into a memory, sharing the addressing
// rules across $readmemb / $readmemh and the §D.14 $sreadmemb / $sreadmemh
// string forms. `mn` is the destination memory_name expression (a bare unpacked
// array, a partially indexed multidimensional array, or a lowest-dimension
// slice of one); `content` is the text whose tokens are parsed with the §21.4
// grammar. The optional start/finish window arguments are resolved by the
// caller, since the two task families place them at different argument
// positions.
// §21.4 / §7.4.5: one subscript written after the memory_name identifier — a
// plain index selecting a single position of a higher-order dimension, or (only
// on the lowest dimension) a slice range. A slice's bounds are stored low/high
// ordered.
struct MemSubscript {
  bool is_slice;
  int64_t a;
  int64_t b;
};

// §21.4 / §7.4.5: unwinds a memory_name expression into its base array
// identifier and the subscripts written after it, ordered leftmost (highest-
// order) dimension first. A memory_name is a bare identifier or a chain of
// index / slice selects rooted at one; returns false for any other expression
// form (in which case the caller does nothing).
static bool CollectMemSubscripts(const ReadmemEnv& env, const Expr* mn,
                                 const Expr*& base_id,
                                 std::vector<MemSubscript>& subs) {
  std::vector<MemSubscript>
      rev;  // outermost (rightmost) subscript collected first
  const Expr* e = mn;
  while (e != nullptr && e->kind == ExprKind::kSelect &&
         !e->is_part_select_plus && !e->is_part_select_minus &&
         e->base != nullptr) {
    int64_t a =
        static_cast<int64_t>(EvalExpr(e->index, env.ctx, env.arena).ToUint64());
    if (e->index_end != nullptr) {
      int64_t b = static_cast<int64_t>(
          EvalExpr(e->index_end, env.ctx, env.arena).ToUint64());
      rev.push_back({true, std::min(a, b), std::max(a, b)});
    } else {
      rev.push_back({false, a, a});
    }
    e = e->base;
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return false;
  base_id = e;
  subs.assign(rev.rbegin(), rev.rend());
  return true;
}

// §21.4.3: the address low bound and extent of dimension `d` (dimension 0 is
// the highest / leftmost in the declaration) of a possibly multidimensional
// array. A single-dimension array keeps its extent in lo/size rather than the
// per- dimension vectors.
static void DimBounds(const ArrayInfo* ai, size_t d, int64_t& lo,
                      int64_t& size) {
  if (ai->dim_sizes.empty()) {
    lo = ai->lo;
    size = ai->size;
  } else {
    lo = ai->dim_los[d];
    size = ai->dim_sizes[d];
  }
}

// §21.4: the user-facing inputs of a load request after the memory_name is
// resolved: how the name was written (bare or a slice, with its bounds) and the
// optional start/finish window arguments. Threaded together because each
// destination form (queue, single-dimension array) consumes both.
struct MemLoadArgs {
  MemSlice slice;
  ReadmemWindow w;
};

// §21.4: the resolved destination unpacked array: its name (used to build per-
// element variable names) and its ArrayInfo (bounds and element type).
struct DestArray {
  const std::string& mem_name;
  const ArrayInfo* ai;
};

// §21.4.1: loads a dynamic array or queue, whose size is fixed for the load (an
// address beyond the last element is dropped, never resized to make room). A
// slice narrows the address window to its own bounds, clamped to the array.
static void LoadMemQueue(const ReadmemEnv& env, const std::string& content,
                         QueueObject* q, const EnumTypeInfo* enum_info,
                         const MemLoadArgs& args) {
  const MemSlice& slice = args.slice;
  int64_t low_addr = 0;
  int64_t high_addr = static_cast<int64_t>(q->elements.size()) - 1;
  if (slice.is_slice) {
    low_addr = std::max(slice.slice_lo, low_addr);
    high_addr = std::min(slice.slice_hi, high_addr);
  }
  IndexedLoadReq req{{low_addr, high_addr, slice.is_slice},
                     {q->elem_width, !q->is_4state, enum_info},
                     args.w};
  EvalReadmemIndexed(env, content, req, [&](int64_t addr, const Logic4Vec& v) {
    q->elements[static_cast<size_t>(addr)] = v;
  });
}

// §21.4: loads a single-dimension unpacked array (or one lower dimension named
// by a slice, see §7.4.5). A slice narrows the load window to its own bounds,
// clamped to the array.
static void LoadMemSingleDim(const ReadmemEnv& env, const std::string& content,
                             const DestArray& dest,
                             const EnumTypeInfo* enum_info,
                             const MemLoadArgs& args) {
  const ArrayInfo* ai = dest.ai;
  const MemSlice& slice = args.slice;
  int64_t arr_lo = ai->lo;
  int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
  // A slice narrows the load window to its own bounds (clamped to the array).
  int64_t low_addr = slice.is_slice ? std::max(slice.slice_lo, arr_lo) : arr_lo;
  int64_t high_addr =
      slice.is_slice ? std::min(slice.slice_hi, arr_hi) : arr_hi;

  IndexedLoadReq req{{low_addr, high_addr, slice.is_slice},
                     {ai->elem_width, !ai->is_4state, enum_info},
                     args.w};
  EvalReadmemIndexed(env, content, req, [&](int64_t addr, const Logic4Vec& v) {
    std::string elem = dest.mem_name + "[" + std::to_string(addr) + "]";
    if (auto* var = env.ctx.FindVariable(elem)) var->value = v;
  });
}

// §21.4: routes a memory_name to the loader for the container kind it names.
// An associative array keyed by an integral address and a queue of fixed size
// (§21.4.1) are each loaded here and consume the name, so nullptr is returned.
// A plain unpacked array is left to the caller, which knows whether a slice or
// a higher dimension narrows the load, so its ArrayInfo is returned; a name
// that resolves to no array at all also yields nullptr.
static const ArrayInfo* LoadMemContainerOrArray(const ReadmemEnv& env,
                                                const std::string& content,
                                                const std::string& mem_name,
                                                const EnumTypeInfo* enum_info,
                                                const MemLoadArgs& args) {
  if (AssocArrayObject* aa = env.ctx.FindAssocArray(mem_name)) {
    EvalReadmemAssoc(env, content, aa,
                     {aa->elem_width, !aa->is_4state, enum_info}, args.w);
    return nullptr;
  }
  if (QueueObject* q = env.ctx.FindQueue(mem_name)) {
    LoadMemQueue(env, content, q, enum_info, args);
    return nullptr;
  }
  return env.ctx.FindArrayInfo(mem_name);
}

// §21.4: loads a bare-identifier memory_name (no subscripts). Beyond the
// container kinds every memory_name shares, a bare name may also be a
// multidimensional unpacked array, which is filled row-major (§21.4.3).
static void LoadBareMemName(const ReadmemEnv& env, const std::string& content,
                            const std::string& mem_name,
                            const EnumTypeInfo* enum_info,
                            const ReadmemWindow& w) {
  MemLoadArgs args{MemSlice{false, 0, 0}, w};
  const ArrayInfo* ai =
      LoadMemContainerOrArray(env, content, mem_name, enum_info, args);
  if (!ai) return;
  if (ai->dim_sizes.size() >= 2) {
    EvalReadmemMultiDim(env, content, mem_name, ai,
                        {ai->elem_width, !ai->is_4state, enum_info});
    return;
  }
  LoadMemSingleDim(env, content, {mem_name, ai}, enum_info, args);
}

// §21.4: one $readmem load request -- the file text to load, the memory the
// task names, the enumeration type its elements carry (null when they are not
// enumerated), and the optional start/finish address window.
struct MemLoadRequest {
  const std::string& content;
  const std::string& mem_name;
  const EnumTypeInfo* enum_info;
  const ReadmemWindow& window;
};

// Report a $readmem load error under the task name the caller invoked.
static void ReportMemLoadError(const ReadmemEnv& env, const std::string& msg) {
  env.ctx.GetDiag().Error(
      env.loc, "$readmem" + std::string(env.is_hex ? "h" : "b") + ": " + msg,
      Subclause("21.4"));
}

// §21.4 / §7.4.5: loads a lowest-dimension slice, `mem[a:b]`, where that is the
// only slice syntax and nothing higher is indexed -- a whole single-dimension
// array (or queue) narrowed to a sub-range. The slice bounds narrow the load
// window; an associative array has no bounded window to narrow, so it loads as
// a bare name.
static void LoadSlicedMemName(const ReadmemEnv& env, const MemLoadRequest& req,
                              const MemSubscript& s) {
  MemLoadArgs args{MemSlice{true, s.a, s.b}, req.window};
  const ArrayInfo* ai = LoadMemContainerOrArray(env, req.content, req.mem_name,
                                                req.enum_info, args);
  if (!ai) return;
  LoadMemSingleDim(env, req.content, {req.mem_name, ai}, req.enum_info, args);
}

// §21.4: higher-order dimensions shall be specified with an index rather than a
// range, so only the lowest (last) subscript may be a slice, and a name may
// carry no more subscripts than the array has dimensions.
static bool CheckMemSubscriptShape(const ReadmemEnv& env, const ArrayInfo* ai,
                                   const std::vector<MemSubscript>& subs) {
  size_t total_dims = ai->dim_sizes.empty() ? 1 : ai->dim_sizes.size();
  if (subs.size() > total_dims) {
    ReportMemLoadError(env, "more subscripts than the array has dimensions");
    return false;
  }
  for (size_t i = 0; i + 1 < subs.size(); ++i) {
    if (subs[i].is_slice) {
      ReportMemLoadError(env,
                         "a higher-order dimension must be indexed, not "
                         "sliced");
      return false;
    }
  }
  return true;
}

// Build the element-name prefix from the leading index subscripts, checking
// each index against the bounds of its dimension.
static bool BuildIndexedMemPrefix(const ReadmemEnv& env, const ArrayInfo* ai,
                                  const std::vector<MemSubscript>& subs,
                                  size_t index_count, std::string& prefix) {
  for (size_t d = 0; d < index_count; ++d) {
    int64_t lo = 0;
    int64_t size = 0;
    DimBounds(ai, d, lo, size);
    if (subs[d].a < lo || subs[d].a >= lo + size) {
      ReportMemLoadError(env, "index outside the bounds of its dimension");
      return false;
    }
    prefix += "[" + std::to_string(subs[d].a) + "]";
  }
  return true;
}

// The one-dimensional sub-array a resolved prefix names: dimension `dim` of the
// enclosing array, carrying its element width and 4-state-ness.
static ArrayInfo SubArrayAtDim(const ArrayInfo* ai, size_t dim) {
  int64_t lo = 0;
  int64_t size = 0;
  DimBounds(ai, dim, lo, size);
  ArrayInfo sub;
  sub.lo = static_cast<uint32_t>(lo);
  sub.size = static_cast<uint32_t>(size);
  sub.elem_width = ai->elem_width;
  sub.is_4state = ai->is_4state;
  return sub;
}

// §21.4.3: the sub-array still has two or more dimensions; fill it row-major
// over the remaining (inner) dimensions, addressed under the resolved prefix.
static void LoadRemainingMemDims(const ReadmemEnv& env,
                                 const MemLoadRequest& req, const ArrayInfo* ai,
                                 const std::string& prefix,
                                 size_t index_count) {
  ArrayInfo sub;
  sub.elem_width = ai->elem_width;
  sub.is_4state = ai->is_4state;
  auto skipped = static_cast<std::ptrdiff_t>(index_count);
  sub.dim_los.assign(ai->dim_los.begin() + skipped, ai->dim_los.end());
  sub.dim_sizes.assign(ai->dim_sizes.begin() + skipped, ai->dim_sizes.end());
  sub.lo = sub.dim_los[0];
  sub.size = sub.dim_sizes[0];
  EvalReadmemMultiDim(env, req.content, prefix, &sub,
                      {ai->elem_width, !ai->is_4state, req.enum_info});
}

// §21.4 / §7.4.5: loads a partially indexed multidimensional unpacked array.
// The leading subscripts index higher-order dimensions -- each shall be a
// single index, not a range -- naming a lower-dimensioned sub-array; an
// optional trailing slice narrows the lowest named dimension. The resolved
// element-name prefix and the remaining dimensions are then handed to the same
// single- or multi- dimension loader a bare array would use.
static void LoadPartiallyIndexedMemName(const ReadmemEnv& env,
                                        const MemLoadRequest& req,
                                        const std::vector<MemSubscript>& subs) {
  const ArrayInfo* ai = env.ctx.FindArrayInfo(req.mem_name);
  if (ai == nullptr) return;
  if (!CheckMemSubscriptShape(env, ai, subs)) return;

  size_t total_dims = ai->dim_sizes.empty() ? 1 : ai->dim_sizes.size();
  bool last_slice = subs.back().is_slice;
  size_t index_count = last_slice ? subs.size() - 1 : subs.size();

  std::string prefix = req.mem_name;
  if (!BuildIndexedMemPrefix(env, ai, subs, index_count, prefix)) return;
  size_t remaining = total_dims - index_count;

  if (last_slice) {
    // §21.4: a slice is legal only on the lowest dimension, so every dimension
    // above the sliced one must already have been indexed.
    if (remaining != 1) {
      ReportMemLoadError(env,
                         "a slice is allowed only on the lowest dimension");
      return;
    }
    ArrayInfo sub = SubArrayAtDim(ai, index_count);
    MemLoadArgs args{MemSlice{true, subs.back().a, subs.back().b}, req.window};
    LoadMemSingleDim(env, req.content, {prefix, &sub}, req.enum_info, args);
    return;
  }

  // §21.4: a fully indexed name selects a single element, not a memory.
  if (remaining == 0) {
    ReportMemLoadError(env,
                       "memory_name resolves to a single element, not an "
                       "array");
    return;
  }

  if (remaining == 1) {
    ArrayInfo sub = SubArrayAtDim(ai, index_count);
    MemLoadArgs args{MemSlice{false, 0, 0}, req.window};
    LoadMemSingleDim(env, req.content, {prefix, &sub}, req.enum_info, args);
    return;
  }

  LoadRemainingMemDims(env, req, ai, prefix, index_count);
}

static void DoMemLoad(const ReadmemEnv& env, const std::string& content,
                      const Expr* mn, const ReadmemWindow& w) {
  // §21.4 / §7.4.5: memory_name is a bare unpacked array, a partially indexed
  // multidimensional array that resolves to a lesser-dimensioned array, or a
  // lowest-dimension slice of one. Unwind it to a base identifier and the
  // subscripts written after it.
  const Expr* base_id = nullptr;
  std::vector<MemSubscript> subs;
  if (!CollectMemSubscripts(env, mn, base_id, subs)) {
    return;
  }
  std::string mem_name(base_id->text);

  // §21.4.2: when the memory's element type is enumerated, the file numbers are
  // the underlying numeric values of the type's elements and each must name a
  // valid element. A null result means the destination is not enum-typed.
  const EnumTypeInfo* enum_info = env.ctx.GetVariableEnumType(mem_name);

  if (subs.empty()) {
    LoadBareMemName(env, content, mem_name, enum_info, w);
    return;
  }
  if (subs.size() == 1 && subs[0].is_slice) {
    LoadSlicedMemName(env, {content, mem_name, enum_info, w}, subs[0]);
    return;
  }
  LoadPartiallyIndexedMemName(env, {content, mem_name, enum_info, w}, subs);
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
    ctx.GetDiag().Warning(expr->args[0]->range.start,
                          "$readmem" + std::string(is_hex ? "h" : "b") +
                              ": cannot open file: " + filename,
                          Subclause::None());
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

  ReadmemEnv env{ctx, arena, is_hex, expr->range.start};
  DoMemLoad(env, content, expr->args[1],
            {has_start, has_finish, start_arg, finish_arg});
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

  ReadmemEnv env{ctx, arena, is_hex, expr->range.start};
  DoMemLoad(env, content, expr->args[0],
            {/*has_start=*/true, /*has_finish=*/true, start_arg, finish_arg});
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
