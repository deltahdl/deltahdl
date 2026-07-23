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

// §21.5.3: an associative array's keys are sparse, so a plain sequential read
// could not place its words. Each entry is written with an @-address ahead of
// its value. The keys are integral (§21.4.1) and emitted in ascending order as
// hexadecimal, matching the @-address form $readmem parses.
static void WriteAssocMem(std::ofstream& ofs, bool is_hex,
                          const AssocArrayObject* aa) {
  for (const auto& entry : aa->int_data) {
    char addr_buf[20];
    std::snprintf(addr_buf, sizeof(addr_buf), "%llx",
                  static_cast<unsigned long long>(entry.first));
    ofs << "@" << addr_buf << "\n";
    ofs << FormatArg(entry.second, is_hex ? 'h' : 'b') << "\n";
  }
}

// §21.5: the $writememb / $writememh call under evaluation. The system-task
// expression carries the file/memory operands plus the optional start_addr /
// finish_addr arguments, and ctx / arena are the evaluation environment those
// argument expressions are resolved against. These three always travel together
// across the array-shape writers, so they ride as one entity.
struct WritememEval {
  const Expr* expr;
  SimContext& ctx;
  Arena& arena;
};

// §21.5: resolves the optional start_addr (arg 2) / finish_addr (arg 3) that
// bound which element indices a $writemem writes. An absent argument falls back
// to the array's own low / high bound.
static void ResolveWritememRange(const WritememEval& eval, int64_t arr_lo,
                                 int64_t arr_hi, int64_t& start_addr,
                                 int64_t& finish_addr) {
  const Expr* expr = eval.expr;
  bool has_start = expr->args.size() >= 3;
  bool has_finish = expr->args.size() >= 4;
  start_addr =
      has_start ? static_cast<int64_t>(
                      EvalExpr(expr->args[2], eval.ctx, eval.arena).ToUint64())
                : arr_lo;
  finish_addr =
      has_finish ? static_cast<int64_t>(
                       EvalExpr(expr->args[3], eval.ctx, eval.arena).ToUint64())
                 : arr_hi;
}

// §21.5: writes the address range [start, finish] (descending when finish is
// below start) by handing each in-bounds address to `emit`. An address outside
// [arr_lo, arr_hi] is skipped; the loop always covers through `finish`.
template <class EmitFn>
static void WriteMemAddressRange(int64_t start_addr, int64_t finish_addr,
                                 int64_t arr_lo, int64_t arr_hi, EmitFn emit) {
  int64_t step = (start_addr <= finish_addr) ? 1 : -1;
  for (int64_t addr = start_addr;; addr += step) {
    if (addr >= arr_lo && addr <= arr_hi) emit(addr);
    if (addr == finish_addr) break;
  }
}

// §21.5: $writememb / $writememh dump a memory array's words to a file in a
// form the matching $readmemb / $readmemh can load back. Each word is written
// on its own line in binary ($writememb) or hexadecimal ($writememh).
// §21.5.3 fixes whether @-address specifiers accompany the words: an unpacked
// or dynamic array is written as a bare sequence (a sequential read reloads
// it), while an associative array prefixes every entry with its @-address.
// §21.5.3: writes a dynamic array or queue as a bare sequence of words with no
// @-address specifiers, exactly like a fixed unpacked array, so a sequential
// $readmem reloads it. The optional start_addr / finish_addr bound the element
// indices that are written.
template <class EmitFn>
static void WriteMemQueue(const WritememEval& eval, const QueueObject* q,
                          EmitFn emit) {
  int64_t arr_lo = 0;
  int64_t arr_hi = static_cast<int64_t>(q->elements.size()) - 1;
  int64_t start_addr = 0;
  int64_t finish_addr = 0;
  ResolveWritememRange(eval, arr_lo, arr_hi, start_addr, finish_addr);
  if (arr_hi < arr_lo) return;
  WriteMemAddressRange(
      start_addr, finish_addr, arr_lo, arr_hi,
      [&](int64_t addr) { emit(q->elements[static_cast<size_t>(addr)]); });
}

// §21.5: writes a fixed unpacked array as a bare sequence of words. The
// optional start_addr / finish_addr bound the range that is written; a finish
// below start emits the words in descending address order.
template <class EmitFn>
static void WriteMemArray(const WritememEval& eval, const std::string& mem_name,
                          const ArrayInfo* ai, EmitFn emit) {
  int64_t arr_lo = ai->lo;
  int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
  int64_t start_addr = 0;
  int64_t finish_addr = 0;
  ResolveWritememRange(eval, arr_lo, arr_hi, start_addr, finish_addr);
  SimContext& ctx = eval.ctx;
  WriteMemAddressRange(
      start_addr, finish_addr, arr_lo, arr_hi, [&](int64_t addr) {
        std::string elem = mem_name + "[" + std::to_string(addr) + "]";
        if (auto* var = ctx.FindVariable(elem)) {
          emit(var->value);
        }
      });
}

// §21.4.3: emits every element beneath one already-subscripted prefix of a
// multidimensional array, walking the remaining dimensions in row-major order —
// each dimension's entries from low to high address, the lowest (rightmost-
// declared) dimension varying most rapidly — so the dump mirrors the file
// organization the matching $readmem load expects.
template <class EmitFn>
static void EmitMultiDimSubwords(SimContext& ctx, const std::string& prefix,
                                 const ArrayInfo* ai, size_t d, EmitFn& emit) {
  if (d == ai->dim_sizes.size()) {
    if (auto* var = ctx.FindVariable(prefix)) emit(var->value);
    return;
  }
  auto lo = static_cast<int64_t>(ai->dim_los[d]);
  for (uint32_t i = 0; i < ai->dim_sizes[d]; ++i) {
    EmitMultiDimSubwords(
        ctx, prefix + "[" + std::to_string(lo + static_cast<int64_t>(i)) + "]",
        ai, d + 1, emit);
  }
}

// §21.4.3: $writememb / $writememh work with multidimensional unpacked arrays,
// writing the words in the same row-major organization §21.4.3 defines for the
// load file. The optional start_addr / finish_addr bound the highest
// dimension's words, matching the read side where addresses name only
// highest-dimension words.
template <class EmitFn>
static void WriteMemMultiDim(const WritememEval& eval,
                             const std::string& mem_name, const ArrayInfo* ai,
                             EmitFn emit) {
  auto arr_lo = static_cast<int64_t>(ai->dim_los[0]);
  int64_t arr_hi = arr_lo + static_cast<int64_t>(ai->dim_sizes[0]) - 1;
  int64_t start_addr = 0;
  int64_t finish_addr = 0;
  ResolveWritememRange(eval, arr_lo, arr_hi, start_addr, finish_addr);
  SimContext& ctx = eval.ctx;
  WriteMemAddressRange(
      start_addr, finish_addr, arr_lo, arr_hi, [&](int64_t addr) {
        EmitMultiDimSubwords(ctx, mem_name + "[" + std::to_string(addr) + "]",
                             ai, 1, emit);
      });
}

Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  // §21.5: the filename operand takes the same forms as the §21.4 read side —
  // a string literal, a string-typed value, or an integral value whose packed
  // bytes spell the name; EvalStringArg covers all three.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

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

  // §21.5.3: an associative array's keys are sparse, so its words carry an
  // @-address prefix; the keys are emitted in ascending order.
  if (const AssocArrayObject* aa = ctx.FindAssocArray(mem_name)) {
    WriteAssocMem(ofs, is_hex, aa);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  WritememEval eval{expr, ctx, arena};

  if (const QueueObject* q = ctx.FindQueue(mem_name)) {
    WriteMemQueue(eval, q, emit);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (const ArrayInfo* ai = ctx.FindArrayInfo(mem_name)) {
    // §21.4.3: a multidimensional unpacked array's elements are named with one
    // subscript per dimension, so it takes the row-major walk rather than the
    // single-subscript address loop.
    if (ai->dim_sizes.size() >= 2) {
      WriteMemMultiDim(eval, mem_name, ai, emit);
    } else {
      WriteMemArray(eval, mem_name, ai, emit);
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // A plain variable names a single memory word.
  if (auto* target = ctx.FindVariable(mem_name)) emit(target->value);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
