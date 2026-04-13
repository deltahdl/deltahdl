#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

// Clear x/z bits when writing to a 2-state variable.
static void CoerceTo2State(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// Write to a variable and notify watchers.
static void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

// Handle indexed/select LHS in blocking assignments.
static bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                                    SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) {
    WriteVar(elem, rhs_val, arena);
    return true;
  }
  if (TryQueueIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryAssocIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (auto* compound = TryResolveCompoundElement(lhs, ctx, arena)) {
    WriteVar(compound, rhs_val, arena);
    return true;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    WriteBitSelect(var, lhs, rhs_val, ctx, arena);
    var->NotifyWatchers();
  }
  return true;
}

// §7.9.9: Associative array whole-array copy assignment.
static bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (stmt->rhs->kind != ExprKind::kIdentifier) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  auto* src = ctx.FindAssocArray(stmt->rhs->text);
  if (!dst || !src) return false;
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

// §8: Try to handle class `new` in a blocking assignment.
static bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto type_name = ctx.GetVariableClassType(stmt->lhs->text);
  if (type_name.empty()) return false;

  // §8.12: shallow copy — `p2 = new p1;`
  if (stmt->rhs->lhs && stmt->rhs->lhs->kind == ExprKind::kIdentifier) {
    auto src_val = EvalExpr(stmt->rhs->lhs, ctx, arena);
    auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
    if (src_obj) {
      auto* copy = src_obj->ShallowCopy(arena);
      auto copy_handle = ctx.AllocateClassObject(copy);
      auto* var = ctx.FindVariable(stmt->lhs->text);
      if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
      return true;
    }
  }

  // §8.30.2: weak_reference new(T referent).
  if (type_name == "weak_reference") {
    uint64_t referent = kNullClassHandle;
    if (!stmt->rhs->args.empty()) {
      auto val = EvalExpr(stmt->rhs->args[0], ctx, arena);
      referent = val.ToUint64();
    }
    auto wr_handle = ctx.AllocateWeakReference(referent, arena);
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
    return true;
  }

  auto handle = EvalClassNew(type_name, stmt->rhs, ctx, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->lhs->text, handle.ToUint64(), ctx, arena);
  return true;
}

// §8.8: Try to handle typed constructor call `D::new` (no parens) in a
// blocking assignment.  The with-parens form `D::new(args)` is a kCall and
// is handled by the expression evaluator via TryEvalClassScopeCall.
static bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->rhs->rhs || stmt->rhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (stmt->rhs->rhs->text != "new") return false;
  if (!ctx.FindClassType(stmt->rhs->lhs->text)) return false;
  auto handle =
      EvalClassNew(stmt->rhs->lhs->text, nullptr, ctx, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) var->value = handle;
  return true;
}

// §A.6.7.1: Unwrap typed assignment pattern expression (kCast wrapping
// pattern).
static const Expr* UnwrapTypedPattern(const Expr* expr) {
  if (expr->kind == ExprKind::kCast && expr->lhs &&
      expr->lhs->kind == ExprKind::kAssignmentPattern)
    return expr->lhs;
  return expr;
}

// §11.6: Determine the context width from the LHS of an assignment.
static uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx) {
  if (!lhs) return 0;
  auto* var = ResolveLhsVariable(lhs, ctx);
  return var ? var->value.width : 0;
}

// Execute a blocking assignment with full LHS support.
// §10.9.2: Evaluate RHS as named struct pattern if applicable.
static Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                          Arena& arena) {
  // §11.6: LHS width determines context for RHS expression evaluation.
  uint32_t ctx_width = LhsContextWidth(stmt->lhs, ctx);
  if (!stmt->rhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  }
  auto* inner = UnwrapTypedPattern(stmt->rhs);
  bool named = inner->kind == ExprKind::kAssignmentPattern &&
               !inner->pattern_keys.empty();
  if (!named) return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text);
  if (!sinfo) return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  return EvalStructPattern(inner, sinfo, ctx, arena);
}

// §7.4.3: Compute (lo, count) for an unpacked array slice expression.
static std::pair<uint32_t, uint32_t> ComputeSliceRange(const Expr* expr,
                                                       SimContext& ctx,
                                                       Arena& arena) {
  auto start =
      static_cast<uint32_t>(EvalExpr(expr->index, ctx, arena).ToUint64());
  auto end_val =
      static_cast<uint32_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
  if (expr->is_part_select_plus) return {start, end_val};
  if (expr->is_part_select_minus) return {start - end_val + 1, end_val};
  auto lo = std::min(start, end_val);
  return {lo, std::max(start, end_val) - lo + 1};
}

// §7.4.3: Collect elements from a source unpacked array slice.
static void CollectSliceSourceElements(const Expr* rhs, SimContext& ctx,
                                       Arena& arena,
                                       std::vector<Logic4Vec>& out) {
  if (rhs->kind != ExprKind::kSelect || !rhs->index_end) return;
  if (!rhs->base || rhs->base->kind != ExprKind::kIdentifier) return;
  auto* info = ctx.FindArrayInfo(rhs->base->text);
  if (!info) return;
  auto [lo, count] = ComputeSliceRange(rhs, ctx, arena);
  for (uint32_t i = 0; i < count; ++i) {
    auto n = std::string(rhs->base->text) + "[" + std::to_string(lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    out.push_back(v ? v->value : MakeLogic4VecVal(arena, info->elem_width, 0));
  }
}

// §7.4.3/§7.4.6: Unpacked array slice assignment (arr_b[5:3] = arr_a[2:0]).
static bool TryUnpackedSliceAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* lhs = stmt->lhs;
  if (lhs->kind != ExprKind::kSelect || !lhs->index_end) return false;
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* dst_info = ctx.FindArrayInfo(lhs->base->text);
  if (!dst_info) return false;
  auto [dst_lo, dst_count] = ComputeSliceRange(lhs, ctx, arena);
  std::vector<Logic4Vec> src;
  CollectSliceSourceElements(stmt->rhs, ctx, arena, src);
  if (src.empty()) {
    auto val = EvalExpr(stmt->rhs, ctx, arena);
    uint32_t ew = dst_info->elem_width;
    uint64_t mask = (ew >= 64) ? ~uint64_t{0} : (uint64_t{1} << ew) - 1;
    for (uint32_t i = 0; i < dst_count; ++i)
      src.push_back(
          MakeLogic4VecVal(arena, ew, (val.ToUint64() >> (i * ew)) & mask));
  }
  for (uint32_t i = 0; i < dst_count && i < src.size(); ++i) {
    auto n =
        std::string(lhs->base->text) + "[" + std::to_string(dst_lo + i) + "]";
    auto* var = ctx.FindVariable(n);
    if (!var) continue;
    var->value = ResizeToWidth(src[i], var->value.width, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  }
  return true;
}

// Find or lazily create a compound element variable.
static Variable* FindOrCreateElement(const std::string& name, uint32_t width,
                                     SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(name);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(name), width);
}

// §7.4.5: Check if an expression is a compound array select (e.g., A[0][2]).
static bool IsCompoundSelect(const Expr* expr) {
  return expr && expr->kind == ExprKind::kSelect && expr->base &&
         expr->base->kind == ExprKind::kSelect && !expr->index_end;
}

// §7.4.5: Multi-dimensional sub-array copy (B[1][1] = A[0][2]).
static bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!IsCompoundSelect(stmt->lhs) || !IsCompoundSelect(stmt->rhs))
    return false;
  std::string dst_prefix, src_prefix;
  if (!BuildCompoundLhsName(stmt->lhs, ctx, arena, dst_prefix)) return false;
  if (!BuildCompoundLhsName(stmt->rhs, ctx, arena, src_prefix)) return false;
  std::string match = src_prefix + "[";
  std::vector<std::pair<std::string, Logic4Vec>> elems;
  for (const auto& [vname, vptr] : ctx.GetVariables()) {
    if (vname.starts_with(match))
      elems.emplace_back(std::string(vname.substr(src_prefix.size())),
                         vptr->value);
  }
  if (elems.empty()) return false;
  for (const auto& [suffix, val] : elems) {
    auto* dst = FindOrCreateElement(dst_prefix + suffix, val.width, ctx, arena);
    dst->value = val;
    dst->NotifyWatchers();
  }
  return true;
}

// §10.10/A.8.1: Concatenation as LHS — unpack RHS across elements.
static void UnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                            SimContext& ctx, Arena& arena) {
  uint64_t rhs_raw = rhs_val.ToUint64();
  uint32_t bit_offset = 0;
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    auto* var = ResolveLhsVariable(*it, ctx);
    if (!var) continue;
    uint32_t w = var->value.width;
    uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
    uint64_t slice = (rhs_raw >> bit_offset) & mask;
    var->value = MakeLogic4VecVal(arena, w, slice);
    var->NotifyWatchers();
    bit_offset += w;
  }
}

// §11.4.14.3: Parse a digit-string identifier as an integer.
static uint32_t ParseDigitIdentifier(std::string_view text) {
  uint32_t n = 0;
  for (char c : text) {
    if (c >= '0' && c <= '9') n = n * 10 + (c - '0');
  }
  return n > 0 ? n : 1;
}

// §11.4.14.3: Map a type name to its bit width for streaming slicing.
static uint32_t TypeNameToSliceWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "int" || t == "integer") return 32;
  if (t == "longint") return 64;
  if (t == "real" || t == "realtime") return 64;
  if (t == "shortreal") return 32;
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  return 32;
}

// §11.4.14.3: Determine streaming slice size from optional type/expression.
static uint32_t StreamSliceSizeForUnpack(const Expr* size_expr, SimContext& ctx,
                                         Arena& arena) {
  if (!size_expr) return 1;
  if (size_expr->kind == ExprKind::kIdentifier) {
    if (!size_expr->text.empty() && size_expr->text[0] >= '0' &&
        size_expr->text[0] <= '9') {
      return ParseDigitIdentifier(size_expr->text);
    }
    return TypeNameToSliceWidth(size_expr->text);
  }
  auto val = EvalExpr(size_expr, ctx, arena).ToUint64();
  auto sval = static_cast<int64_t>(val);
  if (val == 0 || sval < 0) {
    ctx.GetDiag().Error({}, "slice_size for streaming operator must be positive");
    return 1;
  }
  return static_cast<uint32_t>(val);
}

// §11.4.14.3: Element info for streaming unpack.
struct StreamElemInfo {
  const Expr* expr;
  uint32_t width;
  std::string target_name;  // §11.4.14.4: set for expanded array elements.
};

// §11.4.14.4: Resolve a with-clause range into (start, count) indices.
static bool ResolveWithRangeForUnpack(const Expr* with_expr, SimContext& ctx,
                                      Arena& arena, uint32_t array_size,
                                      uint32_t array_lo, uint32_t& out_start,
                                      uint32_t& out_count) {
  if (!with_expr || with_expr->kind != ExprKind::kSelect) {
    out_start = 0;
    out_count = array_size;
    return true;
  }
  int64_t idx =
      static_cast<int64_t>(EvalExpr(with_expr->index, ctx, arena).ToUint64());
  if (!with_expr->index_end) {
    int64_t rel = idx - static_cast<int64_t>(array_lo);
    if (rel < 0 || static_cast<uint32_t>(rel) >= array_size) {
      out_start = 0;
      out_count = 0;
      return false;
    }
    out_start = static_cast<uint32_t>(rel);
    out_count = 1;
    return true;
  }
  int64_t idx2 =
      static_cast<int64_t>(EvalExpr(with_expr->index_end, ctx, arena).ToUint64());
  if (with_expr->is_part_select_plus) {
    int64_t rel = idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
  } else if (with_expr->is_part_select_minus) {
    uint32_t width = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
    int64_t lo_idx = idx - static_cast<int64_t>(width) + 1;
    int64_t rel = lo_idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = width;
  } else {
    int64_t lo = idx, hi = idx2;
    if (lo > hi) std::swap(lo, hi);
    int64_t rel_lo = lo - static_cast<int64_t>(array_lo);
    out_start = (rel_lo < 0) ? 0 : static_cast<uint32_t>(rel_lo);
    out_count = static_cast<uint32_t>(hi - lo + 1);
  }
  return true;
}

// §11.4.14.3/§11.4.14.4: Collect LHS elements and compute total width.
// rhs_width is needed for §11.4.14.4 greedy unpacking of dynamically sized types.
static uint32_t CollectStreamElements(const Expr* lhs, SimContext& ctx,
                                      Arena& arena,
                                      std::vector<StreamElemInfo>& elems,
                                      uint32_t rhs_width) {
  // §11.4.14.4: Detect dynamically sized items (queues without with_expr).
  bool has_dynamic = false;
  for (auto* elem : lhs->elements) {
    if (elem->with_expr) continue;
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text)) {
      has_dynamic = true;
      break;
    }
  }

  // §11.4.14.4: Pre-scan to compute total fixed-size width for greedy sizing.
  uint32_t fixed_sum = 0;
  if (has_dynamic) {
    for (auto* elem : lhs->elements) {
      if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
        if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
          uint32_t start = 0, count = 0;
          ResolveWithRangeForUnpack(elem->with_expr, ctx, arena,
                                    ainfo->size, ainfo->lo, start, count);
          if (start + count > ainfo->size)
            count = (start < ainfo->size) ? ainfo->size - start : 0;
          fixed_sum += count * ainfo->elem_width;
        } else if (auto* queue = ctx.FindQueue(elem->text)) {
          uint32_t start = 0, count = 0;
          ResolveWithRangeForUnpack(
              elem->with_expr, ctx, arena,
              static_cast<uint32_t>(queue->elements.size()), 0, start, count);
          fixed_sum += count * queue->elem_width;
        }
        continue;
      }
      if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text))
        continue;
      auto* var = ResolveLhsVariable(elem, ctx);
      if (var) fixed_sum += var->value.width;
    }
  }

  uint32_t total_width = 0;
  bool first_dynamic_consumed = false;
  for (auto* elem : lhs->elements) {
    // §11.4.14.4: If the element has a with-clause and is an array, expand
    // only the selected positions as individual targets.
    if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
      if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
        uint32_t start = 0, count = 0;
        bool in_range = ResolveWithRangeForUnpack(
            elem->with_expr, ctx, arena, ainfo->size, ainfo->lo, start, count);
        if (!in_range || start + count > ainfo->size) {
          uint32_t clamped = (start < ainfo->size) ? ainfo->size - start : 0;
          ctx.GetDiag().Error(
              {}, "streaming unpack with-range exceeds fixed array bounds");
          count = clamped;
        }
        for (uint32_t i = 0; i < count; ++i) {
          uint32_t abs_idx = ainfo->lo + start + i;
          std::string name =
              std::string(elem->text) + "[" + std::to_string(abs_idx) + "]";
          elems.push_back({elem, ainfo->elem_width, std::move(name)});
          total_width += ainfo->elem_width;
        }
        continue;
      }
      if (auto* queue = ctx.FindQueue(elem->text)) {
        uint32_t start = 0, count = 0;
        ResolveWithRangeForUnpack(
            elem->with_expr, ctx, arena,
            static_cast<uint32_t>(queue->elements.size()), 0, start, count);
        uint32_t needed = start + count;
        while (queue->elements.size() < needed) {
          queue->elements.push_back(
              MakeLogic4Vec(arena, queue->elem_width));
        }
        for (uint32_t i = 0; i < count; ++i) {
          std::string name = std::string(elem->text) + "__q__" +
                             std::to_string(start + i);
          elems.push_back({elem, queue->elem_width, std::move(name)});
          total_width += queue->elem_width;
        }
        continue;
      }
    }
    // §11.4.14.4: Queue without with_expr — greedy unpacking.
    if (has_dynamic && !elem->with_expr &&
        elem->kind == ExprKind::kIdentifier) {
      auto* queue = ctx.FindQueue(elem->text);
      if (queue) {
        if (!first_dynamic_consumed) {
          first_dynamic_consumed = true;
          uint32_t remaining =
              (rhs_width > fixed_sum) ? rhs_width - fixed_sum : 0;
          uint32_t count =
              queue->elem_width > 0 ? remaining / queue->elem_width : 0;
          queue->elements.clear();
          for (uint32_t i = 0; i < count; ++i) {
            queue->elements.push_back(
                MakeLogic4Vec(arena, queue->elem_width));
          }
          for (uint32_t i = 0; i < count; ++i) {
            std::string name = std::string(elem->text) + "__q__" +
                               std::to_string(i);
            elems.push_back({elem, queue->elem_width, std::move(name)});
            total_width += queue->elem_width;
          }
        } else {
          // §11.4.14.4: Subsequent dynamic items are left empty.
          queue->elements.clear();
        }
        continue;
      }
    }
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    elems.push_back({elem, var->value.width, {}});
    total_width += var->value.width;
  }
  return total_width;
}

// §11.4.14.3: Reverse slice order for left-shift streaming (<<).
static Logic4Vec ReverseStreamSlices(const Logic4Vec& stream,
                                     uint32_t total_width, uint32_t ss,
                                     Arena& arena) {
  uint32_t nslices = (total_width + ss - 1) / ss;
  auto reordered = MakeLogic4Vec(arena, total_width);
  for (uint32_t i = 0; i < nslices; ++i) {
    uint32_t src_start = i * ss;
    uint32_t dst_start =
        total_width > (i + 1) * ss ? total_width - (i + 1) * ss : 0;
    uint32_t bits_to_copy = ss;
    if (src_start + bits_to_copy > total_width)
      bits_to_copy = total_width - src_start;
    for (uint32_t b = 0; b < bits_to_copy; ++b) {
      uint32_t sbit = src_start + b;
      uint32_t dbit = dst_start + b;
      if (dbit >= total_width) break;
      uint32_t sw = sbit / 64, sb = sbit % 64;
      uint32_t dw = dbit / 64, db = dbit % 64;
      if (sw < stream.nwords) {
        if ((stream.words[sw].aval >> sb) & 1)
          reordered.words[dw].aval |= uint64_t{1} << db;
        if ((stream.words[sw].bval >> sb) & 1)
          reordered.words[dw].bval |= uint64_t{1} << db;
      }
    }
  }
  return reordered;
}

// §11.4.14.3: Extract a bit-field from a stream vector.
static Logic4Vec ExtractStreamBits(const Logic4Vec& stream,
                                   uint32_t bit_offset, uint32_t width,
                                   uint32_t total_width, Arena& arena) {
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t sbit = bit_offset + b;
    if (sbit >= total_width) break;
    uint32_t sw = sbit / 64, sb = sbit % 64;
    uint32_t dw = b / 64, db = b % 64;
    if (sw < stream.nwords) {
      if ((stream.words[sw].aval >> sb) & 1)
        result.words[dw].aval |= uint64_t{1} << db;
      if ((stream.words[sw].bval >> sb) & 1)
        result.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return result;
}

// §11.4.14.3: Streaming concatenation as LHS — unpack RHS into elements.
static void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                                     SimContext& ctx, Arena& arena) {
  std::vector<StreamElemInfo> elems;
  uint32_t total_width = CollectStreamElements(lhs, ctx, arena, elems,
                                                 rhs_val.width);
  if (total_width == 0 || elems.empty()) return;

  if (rhs_val.width < total_width) {
    ctx.GetDiag().Error({}, "too few bits in stream for streaming unpack");
    return;
  }

  Logic4Vec stream;
  if (rhs_val.width > total_width) {
    uint32_t shift = rhs_val.width - total_width;
    stream = MakeLogic4Vec(arena, total_width);
    for (uint32_t b = 0; b < total_width; ++b) {
      uint32_t sbit = shift + b;
      uint32_t sw = sbit / 64, sb = sbit % 64;
      uint32_t dw = b / 64, db = b % 64;
      if (sw < rhs_val.nwords) {
        if ((rhs_val.words[sw].aval >> sb) & 1)
          stream.words[dw].aval |= uint64_t{1} << db;
        if ((rhs_val.words[sw].bval >> sb) & 1)
          stream.words[dw].bval |= uint64_t{1} << db;
      }
    }
  } else {
    stream = rhs_val;
  }

  if (lhs->op == TokenKind::kLtLt) {
    uint32_t ss = StreamSliceSizeForUnpack(lhs->lhs, ctx, arena);
    stream = ReverseStreamSlices(stream, total_width, ss, arena);
  }

  uint32_t bit_offset = total_width;
  for (auto& ei : elems) {
    bit_offset -= ei.width;
    if (!ei.target_name.empty()) {
      // §11.4.14.4: Expanded array element — write to specific position.
      // Check for queue pseudo-name (name__q__index).
      auto qpos = ei.target_name.find("__q__");
      if (qpos != std::string::npos) {
        auto qname = std::string_view(ei.target_name).substr(0, qpos);
        auto idx_str = ei.target_name.substr(qpos + 5);
        uint32_t idx = static_cast<uint32_t>(std::stoul(idx_str));
        auto* queue = ctx.FindQueue(qname);
        if (queue && idx < queue->elements.size()) {
          queue->elements[idx] =
              ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
        }
      } else {
        auto* var = ctx.FindVariable(ei.target_name);
        if (!var) {
          var = ctx.CreateVariable(
              *arena.Create<std::string>(ei.target_name), ei.width);
        }
        var->value =
            ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
        if (!var->is_4state) CoerceTo2State(var->value);
        var->NotifyWatchers();
      }
    } else {
      auto* var = ResolveLhsVariable(ei.expr, ctx);
      if (!var) continue;
      var->value =
          ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
    }
  }
}

// §6.12.1: Get the base identifier name from an LHS expression.
static std::string_view LhsIdentName(const Expr* lhs) {
  while (lhs) {
    if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
    if (lhs->kind == ExprKind::kSelect && lhs->base) {
      lhs = lhs->base;
      continue;
    }
    break;
  }
  return {};
}

// §6.12.1: Implicit real↔integer conversion on assignment.
static Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                                     uint32_t target_width, SimContext& ctx,
                                     Arena& arena) {
  auto name = LhsIdentName(lhs);
  if (name.empty()) return ResizeToWidth(rhs_val, target_width, arena);
  bool lhs_is_real = ctx.IsRealVariable(name);
  if (rhs_val.is_real && !lhs_is_real) {
    double d = 0.0;
    uint64_t bits = rhs_val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    auto ival = static_cast<uint64_t>(
        static_cast<int64_t>(std::llround(d)));
    auto result = MakeLogic4VecVal(arena, target_width, ival);
    result.is_signed = true;
    return result;
  }
  if (!rhs_val.is_real && lhs_is_real) {
    uint64_t raw =
        rhs_val.nwords > 0
            ? (rhs_val.words[0].aval & ~rhs_val.words[0].bval)
            : 0;
    auto d = static_cast<double>(raw);
    uint64_t dbits = 0;
    std::memcpy(&dbits, &d, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, dbits);
    result.is_real = true;
    return result;
  }
  return ResizeToWidth(rhs_val, target_width, arena);
}

static void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val,
                              SimContext& ctx, Arena& arena) {
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    // §10.6.2: While forced, procedural assigns do not change the value.
    if (var->is_forced) return;
    rhs_val = ConvertRealOnAssign(rhs_val, stmt->lhs, var->value.width, ctx,
                                  arena);
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
    // §7.3.2: Set tag when RHS is a tagged expression.
    if (stmt->rhs && stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs)
      ctx.SetVariableTag(stmt->lhs->text, stmt->rhs->rhs->text);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(stmt->lhs, rhs_val, ctx, arena);
  }
}

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;

  if (TryClassNewAssign(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryTypedClassNewAssign(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryAssocCopyAssign(stmt, ctx)) return StmtResult::kDone;
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;
  // §15.5.5.2: Assigning null breaks the event synchronization association.
  if (stmt->lhs->kind == ExprKind::kIdentifier &&
      stmt->rhs && stmt->rhs->kind == ExprKind::kIdentifier &&
      stmt->rhs->text == "null") {
    auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
    if (lhs_var && lhs_var->is_event) {
      ctx.NullifyEventVariable(stmt->lhs->text);
      return StmtResult::kDone;
    }
  }
  // §15.5.5: Event-to-event assignment shares the synchronization queue.
  if (stmt->lhs->kind == ExprKind::kIdentifier &&
      stmt->rhs && stmt->rhs->kind == ExprKind::kIdentifier) {
    auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
    auto* rhs_var = ctx.FindVariable(stmt->rhs->text);
    if (lhs_var && lhs_var->is_event && rhs_var && rhs_var->is_event) {
      ctx.AliasVariable(stmt->lhs->text, stmt->rhs->text);
      return StmtResult::kDone;
    }
  }
  // §7.4.3: Unpacked array slice assignment (arr_b[5:3] = arr_a[2:0]).
  if (TryUnpackedSliceAssign(stmt, ctx, arena)) return StmtResult::kDone;
  // §7.4.5: Multi-dimensional sub-array copy (B[1][1] = A[0][2]).
  if (TrySubarrayAssign(stmt, ctx, arena)) return StmtResult::kDone;

  // §11.4.1: Compound assignment — evaluate the LHS index only once.
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(stmt->rhs->op)) {
    auto base_op = CompoundAssignBaseOp(stmt->rhs->op);
    auto actual_rhs = EvalExpr(stmt->rhs->rhs, ctx, arena);

    if (stmt->lhs->kind == ExprKind::kIdentifier) {
      auto* var = ResolveLhsVariable(stmt->lhs, ctx);
      if (var) {
        auto result = EvalBinaryOp(base_op, var->value, actual_rhs, arena);
        WriteVar(var, result, arena);
      }
    } else if (stmt->lhs->kind == ExprKind::kSelect) {
      if (auto* elem = TryResolveArrayElement(stmt->lhs, ctx)) {
        auto result = EvalBinaryOp(base_op, elem->value, actual_rhs, arena);
        WriteVar(elem, result, arena);
      } else {
        auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
        auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
        TrySelectBlockingAssign(stmt->lhs, result, ctx, arena);
      }
    } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
      auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
      auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
      WriteStructField(stmt->lhs, result, ctx, arena);
    } else {
      auto result = EvalExpr(stmt->rhs, ctx, arena);
      AssignToScalarLhs(stmt, result, ctx, arena);
    }
    return StmtResult::kDone;
  }

  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kConcatenation ||
      stmt->lhs->kind == ExprKind::kAssignmentPattern) {
    UnpackConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return StmtResult::kDone;
  }

  // §11.4.14.3: Streaming concatenation as assignment target (unpack).
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return StmtResult::kDone;
  }

  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return StmtResult::kDone;
  }

  if (TryArrayBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;

  AssignToScalarLhs(stmt, rhs_val, ctx, arena);
  return StmtResult::kDone;
}

// §10.10.2: Schedule per-element NBA events for array concatenation targets.
static bool TryArrayConcatNba(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kConcatenation) return false;

  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!ainfo && !q) return false;

  // Collect flattened elements from the concatenation.
  std::vector<Logic4Vec> elems;
  for (auto* item : stmt->rhs->elements) {
    if (item->kind == ExprKind::kIdentifier) {
      auto* src_arr = ctx.FindArrayInfo(item->text);
      if (src_arr) {
        for (uint32_t i = 0; i < src_arr->size; ++i) {
          uint32_t idx = src_arr->is_descending
                             ? (src_arr->lo + src_arr->size - 1 - i)
                             : (src_arr->lo + i);
          auto name =
              std::string(item->text) + "[" + std::to_string(idx) + "]";
          auto* v = ctx.FindVariable(name);
          if (v) elems.push_back(v->value);
        }
        continue;
      }
      auto* src_q = ctx.FindQueue(item->text);
      if (src_q) {
        elems.insert(elems.end(), src_q->elements.begin(),
                     src_q->elements.end());
        continue;
      }
    }
    elems.push_back(EvalExpr(item, ctx, arena));
  }

  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  auto schedule_time = ctx.CurrentTime() + SimTime{delay};

  if (ainfo) {
    if (elems.size() != ainfo->size) {
      ctx.GetDiag().Error(
          {}, "unpacked array concatenation size mismatch: expected " +
                  std::to_string(ainfo->size) + " elements, got " +
                  std::to_string(elems.size()));
      return true;
    }
    for (uint32_t i = 0; i < ainfo->size; ++i) {
      uint32_t idx = ainfo->is_descending
                         ? (ainfo->lo + ainfo->size - 1 - i)
                         : (ainfo->lo + i);
      auto name =
          std::string(stmt->lhs->text) + "[" + std::to_string(idx) + "]";
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      auto val = ResizeToWidth(elems[i], ainfo->elem_width, arena);
      auto* event = ctx.GetScheduler().GetEventPool().Acquire();
      SetupWholeVarNbaCallback(event, var, val);
      ctx.GetScheduler().ScheduleEvent(schedule_time, nba_region, event);
    }
  } else {
    // Queue target: schedule a single callback that replaces all elements.
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [q, elems = std::move(elems)]() {
      q->elements = elems;
      q->element_ids.clear();
      ++q->generation;
    };
    ctx.GetScheduler().ScheduleEvent(schedule_time, nba_region, event);
  }
  return true;
}

StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  // §10.10.2: Concatenation targeting an unpacked array acts as array concat.
  if (TryArrayConcatNba(stmt, ctx, arena)) return StmtResult::kDone;

  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);
  // §10.4.2: Intra-assignment delay offsets the NBA schedule time.
  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  ScheduleNonblockingAssign(stmt, rhs_val, delay, ctx, arena);
  return StmtResult::kDone;
}

// §10.4.1: Assign a pre-evaluated value to a blocking assignment LHS.
void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena) {
  if (!lhs) return;
  if (lhs->kind == ExprKind::kConcatenation ||
      lhs->kind == ExprKind::kAssignmentPattern) {
    UnpackConcatLhs(lhs, rhs_val, ctx, arena);
    return;
  }
  // §11.4.14.3: Streaming concatenation as assignment target (unpack).
  if (lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(lhs, rhs_val, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    Logic4Vec mutable_val = rhs_val;
    TrySelectBlockingAssign(lhs, mutable_val, ctx, arena);
    return;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    // §10.6.2: While forced, procedural assigns do not change the value.
    if (var->is_forced) return;
    auto converted = ConvertRealOnAssign(rhs_val, lhs, var->value.width, ctx,
                                         arena);
    var->value = converted;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  } else if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, rhs_val, ctx, arena);
  }
}

// §10.4.2: Create a whole-variable NBA callback.
static void SetupWholeVarNbaCallback(Event* event, Variable* var,
                                     const Logic4Vec& rhs_val) {
  var->pending_nba = rhs_val;
  var->has_pending_nba = true;
  event->callback = [var]() {
    if (var->has_pending_nba) {
      if (!var->is_forced) {
        var->value = var->pending_nba;
        if (!var->is_4state) CoerceTo2State(var->value);
        var->NotifyWatchers();
      }
      var->has_pending_nba = false;
    }
  };
}

// §10.4.2: Schedule an NBA event at current_time + delay_ticks.
void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena) {
  if (!stmt->lhs) return;
  bool is_select = (stmt->lhs->kind == ExprKind::kSelect);
  auto* elem = is_select ? TryResolveArrayElement(stmt->lhs, ctx) : nullptr;
  auto* var = elem ? elem : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return;

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  if (is_select && !elem) {
    // §10.4.2: Evaluate LHS index at schedule time, not at callback time.
    const Expr* lhs = stmt->lhs;
    auto idx_val = EvalExpr(lhs->index, ctx, arena);
    if (HasUnknownBits(idx_val)) return;
    uint32_t idx = static_cast<uint32_t>(idx_val.ToUint64());

    if (!lhs->index_end) {
      // Single bit-select: capture evaluated index.
      event->callback = [var, idx, rhs_val, &arena]() {
        if (idx >= var->value.width) return;
        uint64_t old_val = var->value.ToUint64();
        uint64_t bit = rhs_val.ToUint64() & 1;
        uint64_t cleared = old_val & ~(uint64_t{1} << idx);
        var->value =
            MakeLogic4VecVal(arena, var->value.width, cleared | (bit << idx));
        var->NotifyWatchers();
      };
    } else {
      // Part-select: compute lo and width at schedule time.
      uint32_t end_val = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      uint32_t lo = idx;
      uint32_t w = end_val;
      if (lhs->is_part_select_plus) {
        // [idx +: w] — lo stays idx.
      } else if (lhs->is_part_select_minus) {
        lo = (idx >= w - 1) ? idx - w + 1 : 0;
      } else {
        lo = std::min(idx, end_val);
        w = std::max(idx, end_val) - lo + 1;
      }
      if (w == 0 || lo >= var->value.width) return;
      if (lo + w > var->value.width) w = var->value.width - lo;
      event->callback = [var, lo, w, rhs_val, &arena]() {
        uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
        uint64_t old_val = var->value.ToUint64();
        uint64_t new_bits = (rhs_val.ToUint64() & mask) << lo;
        uint64_t cleared = old_val & ~(mask << lo);
        var->value =
            MakeLogic4VecVal(arena, var->value.width, cleared | new_bits);
        var->NotifyWatchers();
      };
    }
  } else {
    auto converted = ConvertRealOnAssign(rhs_val, stmt->lhs, var->value.width,
                                         ctx, arena);
    SetupWholeVarNbaCallback(event, var, converted);
  }
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  auto schedule_time = ctx.CurrentTime() + SimTime{delay_ticks};
  ctx.GetScheduler().ScheduleEvent(schedule_time, nba_region, event);
}

StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto result = EvalExpr(stmt->expr, ctx, arena);
  // §6.24.2: Task-form $cast issues a runtime error on invalid assignment.
  if (stmt->expr && stmt->expr->kind == ExprKind::kSystemCall &&
      stmt->expr->callee == "$cast" && result.ToUint64() == 0) {
    ctx.GetDiag().Error({}, "runtime error: $cast failed — invalid assignment");
  }
  return StmtResult::kDone;
}

// --- Block-level variable declaration (IEEE §9.3.1) ---

// §7.4: Create unpacked array elements for block-level variable declarations.
static void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                                     SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  auto* dim = stmt->var_unpacked_dims[0];
  if (!dim || dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return;
  auto left = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
  auto right = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  auto lo = static_cast<uint32_t>(std::min(left, right));
  auto size = static_cast<uint32_t>(std::abs(left - right) + 1);
  ArrayInfo info;
  info.lo = lo;
  info.size = size;
  info.elem_width = elem_width;
  info.is_descending = (left > right);
  ctx.RegisterArray(stmt->var_name, info);
  for (uint32_t i = 0; i < size; ++i) {
    uint32_t idx = lo + i;
    auto name = std::string(stmt->var_name) + "[" + std::to_string(idx) + "]";
    ctx.CreateVariable(*arena.Create<std::string>(std::move(name)), elem_width);
  }
}

// §8.30.2: Handle weak_reference variable declaration with optional new().
static bool TryExecWeakRefVarDecl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->var_decl_type.type_name != "weak_reference") return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, "weak_reference");
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init || stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new")
    return true;
  uint64_t referent = kNullClassHandle;
  if (!stmt->var_init->args.empty()) {
    auto val = EvalExpr(stmt->var_init->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
  return true;
}

// §8: Handle block-level class-typed variable declaration.
static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  auto class_type = stmt->var_decl_type.type_name;
  if (class_type.empty() || !ctx.FindClassType(class_type)) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);
  // §8.5: Store specialization value expressions for parameter access.
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init) return true;
  if (stmt->var_init->kind != ExprKind::kCall) return true;
  if (stmt->var_init->text != "new") return true;

  // §8.12: shallow copy — `C c2 = new c1;`
  if (stmt->var_init->lhs &&
      stmt->var_init->lhs->kind == ExprKind::kIdentifier) {
    auto src_val = EvalExpr(stmt->var_init->lhs, ctx, arena);
    auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
    if (src_obj) {
      auto* copy = src_obj->ShallowCopy(arena);
      auto copy_handle = ctx.AllocateClassObject(copy);
      auto* var = ctx.FindVariable(stmt->var_name);
      if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
      return true;
    }
  }

  auto handle = EvalClassNew(class_type, stmt->var_init, ctx, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->var_name, handle.ToUint64(), ctx, arena);
  return true;
}

// §13.3.1: Create a variable in the appropriate scope.
static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  SimContext& ctx) {
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  if (width == 0 && stmt->var_decl_type.kind == DataTypeKind::kString) {
    CreateVarInScope(stmt->var_name, 0, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    CreateVarInScope(stmt->var_name, width, ctx);
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    CreateBlockArrayElements(stmt, width, ctx, arena);
  }
}

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TryExecWeakRefVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  // §13.3.1: Explicit static qualifier — reuse persistent variable.
  auto func_name = ctx.CurrentFuncName();
  if (stmt->var_is_static && !func_name.empty()) {
    auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
    if (existing) {
      ctx.AliasLocalVariable(stmt->var_name, existing);
      return StmtResult::kDone;
    }
  } else if (!stmt->var_is_automatic) {
    // Default lifetime: skip re-creation if the variable already exists locally.
    if (ctx.HasLocalScope() && ctx.FindLocalVariable(stmt->var_name)) {
      return StmtResult::kDone;
    }
  }
  // var_is_automatic: always create fresh.
  uint32_t width = EvalTypeWidth(stmt->var_decl_type);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    var->is_4state = Is4stateType(stmt->var_decl_type.kind);
    if (!var->is_4state) CoerceTo2State(var->value);
    if (stmt->var_init) {
      var->value = EvalExpr(stmt->var_init, ctx, arena);
      if (!var->is_4state) CoerceTo2State(var->value);
    }
    // §13.3.1: Save newly created static var to persistent frame.
    if (stmt->var_is_static && !func_name.empty()) {
      ctx.SaveStaticFuncVar(func_name, stmt->var_name, var);
    }
  }
  return StmtResult::kDone;
}

// --- Force / Release (IEEE §10.6) ---

// §10.6: Collect all Variable* referenced by identifiers in an expression tree.
static void CollectExprVars(const Expr* expr, SimContext& ctx,
                            std::vector<Variable*>& vars) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->text);
    if (var) vars.push_back(var);
    return;
  }
  CollectExprVars(expr->lhs, ctx, vars);
  CollectExprVars(expr->rhs, ctx, vars);
  CollectExprVars(expr->condition, ctx, vars);
  CollectExprVars(expr->true_expr, ctx, vars);
  CollectExprVars(expr->false_expr, ctx, vars);
  CollectExprVars(expr->base, ctx, vars);
  CollectExprVars(expr->index, ctx, vars);
  CollectExprVars(expr->index_end, ctx, vars);
  CollectExprVars(expr->with_expr, ctx, vars);
  CollectExprVars(expr->repeat_count, ctx, vars);
  for (auto* e : expr->elements) CollectExprVars(e, ctx, vars);
  for (auto* a : expr->args) CollectExprVars(a, ctx, vars);
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  var->is_forced = true;
  var->forced_value = rhs_val;
  var->value = rhs_val;
  if (!var->is_4state) CoerceTo2State(var->value);
  var->proc_cont_rhs = stmt->rhs;
  if (stmt->kind == StmtKind::kAssign)
    var->assign_cont_rhs = stmt->rhs;
  var->NotifyWatchers();

  // §10.6: Set up continuous reevaluation — if any RHS variable changes,
  // reevaluate the expression and update the target while active.
  std::vector<Variable*> rhs_vars;
  CollectExprVars(stmt->rhs, ctx, rhs_vars);
  // Deduplicate and exclude the target variable itself.
  std::sort(rhs_vars.begin(), rhs_vars.end());
  rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()), rhs_vars.end());
  rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), var),
                 rhs_vars.end());

  const Expr* rhs = stmt->rhs;
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : rhs_vars) {
    rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr]() {
      if (!var->is_forced || var->proc_cont_rhs != rhs) return true;
      auto new_val = EvalExpr(rhs, *ctx_ptr, *arena_ptr);
      var->forced_value = new_val;
      var->value = new_val;
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
      return false;
    });
  }

  return StmtResult::kDone;
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  var->proc_cont_rhs = nullptr;

  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
  } else if (var->assign_cont_rhs) {
    // Reestablish the active assign procedural continuous assignment.
    auto rhs_val = EvalExpr(var->assign_cont_rhs, ctx, arena);
    var->is_forced = true;
    var->forced_value = rhs_val;
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->proc_cont_rhs = var->assign_cont_rhs;
    var->NotifyWatchers();

    std::vector<Variable*> rhs_vars;
    CollectExprVars(var->assign_cont_rhs, ctx, rhs_vars);
    std::sort(rhs_vars.begin(), rhs_vars.end());
    rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()),
                   rhs_vars.end());
    rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), var),
                   rhs_vars.end());
    const Expr* rhs = var->assign_cont_rhs;
    auto* ctx_ptr = &ctx;
    auto* arena_ptr = &arena;
    for (auto* rhs_var : rhs_vars) {
      rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr]() {
        if (!var->is_forced || var->proc_cont_rhs != rhs) return true;
        auto new_val = EvalExpr(rhs, *ctx_ptr, *arena_ptr);
        var->forced_value = new_val;
        var->value = new_val;
        if (!var->is_4state) CoerceTo2State(var->value);
        var->NotifyWatchers();
        return false;
      });
    }
  }

  return StmtResult::kDone;
}

}  // namespace delta
