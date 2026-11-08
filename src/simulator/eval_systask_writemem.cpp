#include <cstdint>
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
#include "simulator/assoc_index.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static void WriteAssocMem(std::ofstream& ofs, bool is_hex,
                          const AssocArrayObject* aa, Arena& arena) {
  for (const auto& entry : aa->int_data) {
    Logic4Vec key = aa->is_wildcard ? entry.first.ToSignedVec(arena)
                                    : entry.first.ToVec(arena, aa->index_width,
                                                        aa->is_index_signed);
    ofs << "@" << FormatDisplay("%0h", {key}) << "\n";
    ofs << FormatArg(entry.second, is_hex ? 'h' : 'b') << "\n";
  }
}

struct WritememEval {
  const Expr* expr;
  SimContext& ctx;
  Arena& arena;
};

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

template <class EmitFn>
static void WriteMemAddressRange(int64_t start_addr, int64_t finish_addr,
                                 int64_t arr_lo, int64_t arr_hi, EmitFn emit) {
  int64_t step = (start_addr <= finish_addr) ? 1 : -1;
  for (int64_t addr = start_addr;; addr += step) {
    if (addr >= arr_lo && addr <= arr_hi) emit(addr);
    if (addr == finish_addr) break;
  }
}

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
        std::string elem =
            mem_name + "[" + std::to_string(static_cast<uint32_t>(addr)) + "]";
        emit(ctx.FindVariable(elem)->value);
      });
}

template <class EmitFn>
static void EmitMultiDimSubwords(SimContext& ctx, const std::string& prefix,
                                 const ArrayInfo* ai, size_t d, EmitFn& emit) {
  if (d == ai->dim_sizes.size()) {
    emit(ctx.FindVariable(prefix)->value);
    return;
  }
  uint32_t lo = ai->dim_los[d];
  for (uint32_t i = 0; i < ai->dim_sizes[d]; ++i) {
    EmitMultiDimSubwords(ctx, prefix + "[" + std::to_string(lo + i) + "]", ai,
                         d + 1, emit);
  }
}

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
        EmitMultiDimSubwords(
            ctx,
            mem_name + "[" + std::to_string(static_cast<uint32_t>(addr)) + "]",
            ai, 1, emit);
      });
}

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

static bool NamesUnpackedArray(SimContext& ctx, const std::string& name) {
  return ctx.FindAssocArray(name) != nullptr ||
         ctx.FindQueue(name) != nullptr || ctx.FindArrayInfo(name) != nullptr;
}

struct WritememTarget {
  ClassArrayRef class_array;
  bool is_class_array = false;
  std::string mem_name;
  const AssocArrayObject* aa = nullptr;
};

static bool ResolveWritememTarget(const WritememEval& eval, bool is_hex,
                                  WritememTarget& target) {
  const Expr* mem = eval.expr->args[1];
  SimContext& ctx = eval.ctx;
  std::string task = "$writemem" + std::string(is_hex ? "h" : "b");
  target.is_class_array =
      ResolveClassArray(mem, ctx, eval.arena, target.class_array);
  bool names_memory =
      target.is_class_array || (MemoryName(mem, target.mem_name) &&
                                NamesUnpackedArray(ctx, target.mem_name));
  if (!names_memory) {
    ctx.GetDiag().Error(mem->range.start,
                        task + ": memory_name is not an unpacked array",
                        Subclause("21.5"));
    return false;
  }
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
  if (expr->args.size() < 2) {
    ctx.GetDiag().Error(expr->range.start,
                        std::string(is_hex ? "$writememh" : "$writememb") +
                            " takes a file name and a memory name, and this "
                            "call has fewer",
                        Subclause("21.5"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

  WritememEval eval{expr, ctx, arena};
  WritememTarget target;
  if (!ResolveWritememTarget(eval, is_hex, target)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  std::ofstream ofs(filename, std::ios::out | std::ios::trunc);
  if (!ofs.is_open()) {
    std::cerr << "WARNING: $writemem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  auto emit = [&](const Logic4Vec& v) {
    ofs << FormatArg(v, is_hex ? 'h' : 'b') << "\n";
  };

  if (target.aa != nullptr) {
    WriteAssocMem(ofs, is_hex, target.aa, arena);
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
