#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
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
// below start emits the words in descending address order. Every registration
// of a one-dimensional array creates a variable for each address in
// [arr_lo, arr_hi] under the key built here, so each lookup finds one.
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
        emit(ctx.FindVariable(elem)->value);
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

// §21.5 with §8.5: the words of an unpacked array property of a class
// object, named bare inside one of its methods or through a handle or `this`,
// in the address window the task's arguments give.
template <class EmitFn>
static void WriteMemClassArray(const WritememEval& eval,
                               const ClassArrayRef& ref, EmitFn emit) {
  int64_t arr_hi = ref.lo + static_cast<int64_t>(ref.size) - 1;
  if (arr_hi < ref.lo) return;
  int64_t start_addr = 0;
  int64_t finish_addr = 0;
  ResolveWritememRange(eval, ref.lo, arr_hi, start_addr, finish_addr);
  WriteMemAddressRange(
      start_addr, finish_addr, ref.lo, arr_hi, [&](int64_t addr) {
        emit(ReadClassArrayElement(ref, addr, eval.ctx, eval.arena));
      });
}

// §21.5: write the words of the queue or the fixed or dynamic unpacked array
// `mem_name` names; EvalWritemem has already found it to be one. §21.4.3: a
// multidimensional unpacked array's elements are named with one subscript per
// dimension, so it takes the row-major walk rather than the single-subscript
// address loop.
template <class EmitFn>
static void WriteMemContainer(const WritememEval& eval,
                              const std::string& mem_name, EmitFn emit) {
  SimContext& ctx = eval.ctx;
  if (const QueueObject* q = ctx.FindQueue(mem_name)) {
    WriteMemQueue(eval, q, emit);
    return;
  }
  const ArrayInfo* ai = ctx.FindArrayInfo(mem_name);
  if (ai->dim_sizes.size() >= 2) {
    WriteMemMultiDim(eval, mem_name, ai, emit);
  } else {
    WriteMemArray(eval, mem_name, ai, emit);
  }
}

// §21.5: the memory is named by an identifier, bare, hierarchical (§23.6) or
// qualified by the package declaring it (§26.3); false for any other form of
// `mem`. A package's data is held under "pkg.name", the path FlattenHierPath
// gives `pkg::name`.
static bool MemoryName(const Expr* mem, std::string& name) {
  if (mem->kind == ExprKind::kIdentifier) {
    name = std::string(mem->text);
    return true;
  }
  if (mem->kind == ExprKind::kMemberAccess) {
    name = FlattenHierPath(mem);
    return true;
  }
  return false;
}

// §21.5 with §7.4: whether `name` names an unpacked array the task can dump --
// an associative array, a queue or dynamic array, or a fixed-size array.
static bool NamesUnpackedArray(SimContext& ctx, const std::string& name) {
  return ctx.FindAssocArray(name) != nullptr ||
         ctx.FindQueue(name) != nullptr || ctx.FindArrayInfo(name) != nullptr;
}

// §21.5: the memory a $writemem call dumps -- a class's array property, or
// the container its memory_name names, with the associative array that name
// denotes when it is one.
struct WritememTarget {
  ClassArrayRef class_array;
  bool is_class_array = false;
  std::string mem_name;
  const AssocArrayObject* aa = nullptr;
};

// Resolves the memory_name operand of `eval.expr` into `target`, reporting
// and returning false when it names nothing the task can dump. Both checks run
// before the file is opened, so an illegal call leaves any existing file as
// it was.
static bool ResolveWritememTarget(const WritememEval& eval, bool is_hex,
                                  WritememTarget& target) {
  const Expr* mem = eval.expr->args[1];
  SimContext& ctx = eval.ctx;
  std::string task = "$writemem" + std::string(is_hex ? "h" : "b");
  target.is_class_array =
      ResolveClassArray(mem, ctx, eval.arena, target.class_array);
  // §21.5: the tasks dump a memory array (§7.4.3), so a memory_name naming
  // anything else -- a plain variable, a literal -- is reported.
  bool names_memory =
      target.is_class_array || (MemoryName(mem, target.mem_name) &&
                                NamesUnpackedArray(ctx, target.mem_name));
  if (!names_memory) {
    ctx.GetDiag().Error(mem->range.start,
                        task + ": memory_name is not an unpacked array",
                        Subclause("21.5"));
    return false;
  }
  // §21.5.3: an associative array is a legal $writemem argument only when its
  // index type is integral (see §21.4.1) — a string-keyed array has no numeric
  // @-address form.
  target.aa = ctx.FindAssocArray(target.mem_name);
  if (target.aa != nullptr && target.aa->is_string_key) {
    ctx.GetDiag().Error(
        mem->range.start,
        task + ": associative array index must be of an integral type",
        Subclause("21.5.3"));
    return false;
  }
  return true;
}

Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex) {
  // §21.5's syntax: a filename and a memory_name, each required. A call short
  // of both names no memory to dump, or no file to dump it to, and is reported
  // rather than left doing nothing.
  if (expr->args.size() < 2) {
    ctx.GetDiag().Error(expr->range.start,
                        std::string(is_hex ? "$writememh" : "$writememb") +
                            " takes a file name and a memory name, and this "
                            "call has fewer",
                        Subclause("21.5"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §21.5: the filename operand takes the same forms as the §21.4 read side —
  // a string literal, a string-typed value, or an integral value whose packed
  // bytes spell the name; EvalStringArg covers all three.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

  WritememEval eval{expr, ctx, arena};
  WritememTarget target;
  if (!ResolveWritememTarget(eval, is_hex, target)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

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
  if (target.aa != nullptr) {
    WriteAssocMem(ofs, is_hex, target.aa);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (target.is_class_array) {
    WriteMemClassArray(eval, target.class_array, emit);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  WriteMemContainer(eval, target.mem_name, emit);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
