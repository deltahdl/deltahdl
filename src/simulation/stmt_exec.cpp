#include "simulation/stmt_exec.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Leaf executors (regular functions, no coroutine frame) ---

// --- LHS resolution helpers ---

// Build a dotted name from a MemberAccess expression tree (e.g., "s.a.b").
static void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

// §7.4: Try to resolve an array element variable (e.g. "A[0]").
// Returns the element variable if found, null otherwise.
static Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->base->kind != ExprKind::kIdentifier) return nullptr;
  if (lhs->index_end) return nullptr;  // Part-select, not array index.
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  auto elem_name =
      std::string(lhs->base->text) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

// §7.4: Build a compound name from chained selects (e.g., mem[i][j]).
static bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx = EvalExpr(expr->index, ctx, arena).ToUint64();
  name += "[" + std::to_string(idx) + "]";
  return true;
}

// §7.4: Multi-dim array element write — create element lazily.
static Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                           Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  auto* var = ctx.FindVariable(compound);
  if (var) return var;
  // Lazily create the element for multi-dim arrays.
  return ctx.CreateVariable(*arena.Create<std::string>(std::move(compound)),
                            32);
}

// Find the target variable for a compound LHS expression.
static Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindVariable(lhs->text);
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    return ctx.FindVariable(name);
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

// §7.2: Write to a packed struct/union field by name.
static bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena) {
  std::string name;
  BuildLhsName(lhs, name);
  auto dot = name.find('.');
  if (dot == std::string::npos) return false;
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return false;
  auto* info = ctx.GetVariableStructType(base_name);
  if (info) {
    for (const auto& f : info->fields) {
      if (f.name != field_name) continue;
      uint64_t old_val = base_var->value.ToUint64();
      uint64_t mask =
          (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
      uint64_t new_bits = (rhs_val.ToUint64() & mask) << f.bit_offset;
      uint64_t cleared = old_val & ~(mask << f.bit_offset);
      base_var->value =
          MakeLogic4VecVal(arena, base_var->value.width, cleared | new_bits);
      base_var->NotifyWatchers();
      return true;
    }
  }
  // §8: Class object property write (e.g., obj.a = val).
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (obj) {
    obj->SetProperty(std::string(field_name), rhs_val);
    return true;
  }
  return false;
}

// Write a range of bits [hi:lo] into var.
static void WritePartSelect(Variable* var, uint32_t lo, uint32_t width,
                            const Logic4Vec& rhs_val, Arena& arena) {
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  uint64_t old_val = var->value.ToUint64();
  uint64_t new_bits = (rhs_val.ToUint64() & mask) << lo;
  uint64_t cleared = old_val & ~(mask << lo);
  var->value = MakeLogic4VecVal(arena, var->value.width, cleared | new_bits);
}

// Write rhs_val to var at the bit position(s) indicated by a Select LHS.
static void WriteBitSelect(Variable* var, const Expr* lhs,
                           const Logic4Vec& rhs_val, SimContext& ctx,
                           Arena& arena) {
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  auto idx = static_cast<uint32_t>(idx_val.ToUint64());

  if (lhs->index_end) {
    if (lhs->is_part_select_plus) {
      // §7.4.5: var[base +: width] — write `width` bits starting at `base`.
      auto w = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      WritePartSelect(var, idx, w, rhs_val, arena);
    } else if (lhs->is_part_select_minus) {
      // §7.4.5: var[base -: width] — write `width` bits ending at `base`.
      auto w = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      uint32_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
      WritePartSelect(var, lo, w, rhs_val, arena);
    } else {
      // Part-select: var[hi:lo] = rhs_val.
      auto end_idx = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      auto lo = std::min(idx, end_idx);
      auto hi = std::max(idx, end_idx);
      WritePartSelect(var, lo, hi - lo + 1, rhs_val, arena);
    }
  } else {
    // Single bit select: var[idx] = rhs_val[0].
    uint64_t old_val = var->value.ToUint64();
    uint64_t bit = rhs_val.ToUint64() & 1;
    uint64_t cleared = old_val & ~(uint64_t{1} << idx);
    var->value =
        MakeLogic4VecVal(arena, var->value.width, cleared | (bit << idx));
  }
}

// §11.8.2: Resize value to target width, sign-extending when signed.
static Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width,
                               Arena& arena) {
  if (val.width == target_width || target_width == 0) return val;
  uint64_t v = val.ToUint64();
  if (val.is_signed && target_width > val.width && val.width > 0 &&
      val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (v & sign_bit) v |= ~uint64_t{0} << val.width;
  }
  return MakeLogic4VecVal(arena, target_width, v);
}

// §7.6: Copy elements from one array to another (B = A).
static void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                              std::string_view src_name, const ArrayInfo& src,
                              SimContext& ctx) {
  uint32_t n = std::min(dst.size, src.size);
  for (uint32_t i = 0; i < n; ++i) {
    // Map by logical position: descending arrays count from hi end.
    uint32_t si =
        src.is_descending ? (src.lo + src.size - 1 - i) : (src.lo + i);
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto sn = std::string(src_name) + "[" + std::to_string(si) + "]";
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* sv = ctx.FindVariable(sn);
    auto* dv = ctx.FindVariable(dn);
    if (sv && dv) {
      dv->value = sv->value;
      dv->NotifyWatchers();
    }
  }
}

// §7.4: Distribute assignment pattern elements to array element variables.
static void DistributePatternToArray(std::string_view arr_name,
                                     const ArrayInfo& info, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
  for (uint32_t i = 0; i < info.size; ++i) {
    // §7.4: For descending [hi:lo], element 0 maps to highest index.
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    if (i < rhs->elements.size()) {
      auto val = EvalExpr(rhs->elements[i], ctx, arena);
      elem->value = ResizeToWidth(val, info.elem_width, arena);
    } else {
      elem->value = MakeLogic4VecVal(arena, info.elem_width, 0);
    }
    elem->NotifyWatchers();
  }
}

// §7.4/§7.6: Try array-level blocking assignment (pattern or copy).
static bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  // Assignment pattern: arr = '{1, 2, 3}
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributePatternToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }
  // Whole-array copy: B = A
  if (stmt->rhs->kind == ExprKind::kIdentifier) {
    auto* dst = ctx.FindArrayInfo(stmt->lhs->text);
    auto* src = ctx.FindArrayInfo(stmt->rhs->text);
    if (dst && src) {
      CopyArrayElements(stmt->lhs->text, *dst, stmt->rhs->text, *src, ctx);
      return true;
    }
  }
  return false;
}

// §7.8: Associative array indexed write (aa[key] = val).
static bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                 SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (!aa || !lhs->index) return false;
  if (aa->is_string_key) {
    auto key_vec = EvalExpr(lhs->index, ctx, arena);
    uint32_t nb = key_vec.width / 8;
    std::string s;
    s.reserve(nb);
    for (uint32_t i = nb; i > 0; --i) {
      uint32_t bi = i - 1;
      auto ch = static_cast<char>(
          (key_vec.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
      if (ch != 0) s.push_back(ch);
    }
    aa->str_data[s] = rhs_val;
  } else {
    auto key =
        static_cast<int64_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
    aa->int_data[key] = rhs_val;
  }
  return true;
}

// §7.10: Queue indexed write (q[i] = val).
static bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                 SimContext& ctx, Arena& /*arena*/) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(lhs->base->text);
  if (!q || !lhs->index) return false;
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena()).ToUint64();
  if (idx < q->elements.size()) {
    q->elements[idx] = rhs_val;
    return true;
  }
  return false;
}

// §7.10: Evaluate a queue index expression with $ = last index.
static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  int64_t last =
      q->elements.empty() ? 0 : static_cast<int64_t>(q->elements.size()) - 1;
  dv->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(last));
  auto val = EvalExpr(expr, ctx, arena);
  ctx.PopScope();
  // Sign-extend narrow values so negative indices (e.g. -2) are preserved.
  uint64_t raw = val.ToUint64();
  if (val.width > 0 && val.width < 64) {
    uint64_t sign = uint64_t{1} << (val.width - 1);
    if (raw & sign) raw |= ~uint64_t{0} << val.width;
  }
  return static_cast<int64_t>(raw);
}

// §7.10.1: Collect elements from a queue slice (q[lo:hi]).
static bool CollectFromQueueSlice(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || !expr->index_end)
    return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto lo = EvalQueueIndex(expr->index, q, ctx, arena);
  auto hi = EvalQueueIndex(expr->index_end, q, ctx, arena);
  if (lo < 0) lo = 0;
  auto qsz = static_cast<int64_t>(q->elements.size());
  if (hi >= qsz) hi = qsz - 1;
  for (int64_t i = lo; i <= hi; ++i)
    out.push_back(q->elements[static_cast<size_t>(i)]);
  return true;
}

// §7.10: Collect a single queue element (q[i]) with $ support.
static bool CollectFromQueueElem(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || expr->index_end)
    return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = EvalQueueIndex(expr->index, q, ctx, arena);
  if (idx >= 0 && static_cast<size_t>(idx) < q->elements.size())
    out.push_back(q->elements[static_cast<size_t>(idx)]);
  return true;
}

// §7.10: Collect elements from an expression for queue assignment.
static void CollectQueueElements(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind == ExprKind::kConcatenation) {
    for (auto* elem : expr->elements)
      CollectQueueElements(elem, ctx, arena, out);
    return;
  }
  if (CollectFromQueueSlice(expr, ctx, arena, out)) return;
  if (CollectFromQueueElem(expr, ctx, arena, out)) return;
  // Queue variable: expand all elements.
  if (expr->kind == ExprKind::kIdentifier) {
    auto* q = ctx.FindQueue(expr->text);
    if (q) {
      out.insert(out.end(), q->elements.begin(), q->elements.end());
      return;
    }
  }
  // §7.12.1: Locator method call (e.g., s.find with (item == "sad")).
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

// §7.10.4: Queue assignment from concatenation, slice, or literal.
static bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!q) return false;
  // Empty concat: q = {} -> clear.
  if (stmt->rhs->kind == ExprKind::kConcatenation &&
      stmt->rhs->elements.empty()) {
    q->elements.clear();
    return true;
  }
  // §7.5.1: Dynamic array new[N] — resize queue to N zero-initialized elements.
  if (stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new" &&
      !stmt->rhs->args.empty()) {
    auto sz = EvalExpr(stmt->rhs->args[0], ctx, arena).ToUint64();
    q->elements.resize(static_cast<size_t>(sz),
                       MakeLogic4VecVal(arena, q->elem_width, 0));
    return true;
  }
  std::vector<Logic4Vec> elems;
  CollectQueueElements(stmt->rhs, ctx, arena, elems);
  if (q->max_size > 0 && static_cast<int32_t>(elems.size()) > q->max_size) {
    elems.resize(static_cast<size_t>(q->max_size));
  }
  q->elements = std::move(elems);
  return true;
}

// Write to a variable and notify watchers.
static void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  var->value = ResizeToWidth(val, var->value.width, arena);
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
  return true;  // Select always handled (even if var not found).
}

// §7.8: Associative array whole-array copy assignment (w = words).
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
  auto handle = EvalClassNew(type_name, stmt->rhs, ctx, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) var->value = handle;
  return true;
}

// Execute a blocking assignment with full LHS support.
static StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;

  // §8: Class `new` assignment (test_obj = new).
  if (TryClassNewAssign(stmt, ctx, arena)) return StmtResult::kDone;

  // §7.8: Associative array copy assignment.
  if (TryAssocCopyAssign(stmt, ctx)) return StmtResult::kDone;

  // §7.10.4: Queue assignment must be checked before RHS evaluation.
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;

  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return StmtResult::kDone;
  }

  if (TryArrayBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;

  // Identifier or MemberAccess: whole-variable assign.
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    rhs_val = ResizeToWidth(rhs_val, var->value.width, arena);
    var->value = rhs_val;
    var->NotifyWatchers();
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(stmt->lhs, rhs_val, ctx, arena);
  }
  return StmtResult::kDone;
}

static StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (!stmt->lhs) return StmtResult::kDone;

  // §7.4: Check for unpacked array element first.
  bool is_select = (stmt->lhs->kind == ExprKind::kSelect);
  auto* elem = is_select ? TryResolveArrayElement(stmt->lhs, ctx) : nullptr;
  auto* var = elem ? elem : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  if (is_select && !elem) {
    // Capture select info for deferred bit-write.
    const Expr* lhs_copy = stmt->lhs;
    event->callback = [var, lhs_copy, rhs_val, &ctx, &arena]() {
      WriteBitSelect(var, lhs_copy, rhs_val, ctx, arena);
      var->NotifyWatchers();
    };
  } else {
    var->pending_nba = rhs_val;
    var->has_pending_nba = true;
    event->callback = [var]() {
      if (var->has_pending_nba) {
        var->value = var->pending_nba;
        var->has_pending_nba = false;
        var->NotifyWatchers();
      }
    };
  }
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), nba_region, event);
  return StmtResult::kDone;
}

static StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  EvalExpr(stmt->expr, ctx, arena);
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

// §8: Handle block-level class-typed variable declaration.
static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  auto class_type = stmt->var_decl_type.type_name;
  if (class_type.empty() || !ctx.FindClassType(class_type)) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);
  if (!stmt->var_init) return true;
  if (stmt->var_init->kind != ExprKind::kCall) return true;
  if (stmt->var_init->text != "new") return true;
  auto handle = EvalClassNew(class_type, stmt->var_init, ctx, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  return true;
}

static StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  uint32_t width = EvalTypeWidth(stmt->var_decl_type);
  if (width == 0 && stmt->var_decl_type.kind == DataTypeKind::kString) {
    ctx.CreateVariable(stmt->var_name, 0);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;  // Default to int-sized.
    ctx.CreateVariable(stmt->var_name, width);
    CreateBlockArrayElements(stmt, width, ctx, arena);
  }
  if (stmt->var_init) {
    auto* var = ctx.FindVariable(stmt->var_name);
    if (var) var->value = EvalExpr(stmt->var_init, ctx, arena);
  }
  return StmtResult::kDone;
}

// --- Force / Release (IEEE §10.6.2) ---

// Shared logic for force and procedural assign (IEEE §10.6).
static StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  var->is_forced = true;
  var->forced_value = rhs_val;
  var->value = rhs_val;
  return StmtResult::kDone;
}

// Shared logic for release and deassign (IEEE §10.6).
static StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  return StmtResult::kDone;
}

// --- Randcase (IEEE §18.16) ---

static ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t total_weight = 0;
  for (const auto& item : stmt->randcase_items) {
    total_weight += EvalExpr(item.first, ctx, arena).ToUint64();
  }
  if (total_weight == 0) co_return StmtResult::kDone;

  uint64_t pick = ctx.Urandom32() % total_weight;
  uint64_t cumulative = 0;
  for (const auto& item : stmt->randcase_items) {
    cumulative += EvalExpr(item.first, ctx, arena).ToUint64();
    if (pick < cumulative) {
      co_return co_await ExecStmt(item.second, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

// --- Container coroutines (return ExecTask, support suspension) ---

static ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result != StmtResult::kDone) co_return result;
    if (ctx.StopRequested()) co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

// --- If with unique/priority qualifiers ---

static ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  bool taken = cond.ToUint64() != 0;

  if (taken) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  if (stmt->else_branch) {
    co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
  }
  // priority-if with no match and no else => warning.
  if (stmt->qualifier == CaseQualifier::kPriority) {
    ctx.GetDiag().Warning({}, "priority if: no condition matched");
  }
  co_return StmtResult::kDone;
}

// --- Case matching helpers ---

// Check if a bit position has X or Z in a Logic4Vec.
static bool BitIsZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  bool a = (v.words[wi].aval >> bi) & 1;
  bool b = (v.words[wi].bval >> bi) & 1;
  return a && b;  // Z: aval=1, bval=1
}

static bool BitIsXZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  return (v.words[wi].bval >> bi) & 1;  // bval=1 means X or Z
}

using BitPredicate = bool (*)(const Logic4Vec&, uint32_t);

static bool CaseDontCareMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                              BitPredicate skip_bit) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  for (uint32_t i = 0; i < width; ++i) {
    if (skip_bit(sel, i) || skip_bit(pat, i)) continue;
    uint32_t swi = i / 64, sbi = i % 64;
    uint32_t pwi = i / 64, pbi = i % 64;
    bool sa = (swi < sel.nwords) && ((sel.words[swi].aval >> sbi) & 1);
    bool pa = (pwi < pat.nwords) && ((pat.words[pwi].aval >> pbi) & 1);
    if (sa != pa) return false;
  }
  return true;
}

static bool CasexMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsXZ);
}

static bool CasezMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsZ);
}

// Case-inside uses value matching (exact for known bits).
static bool CaseInsideMatch(uint64_t sel_val, const Logic4Vec& pat) {
  return sel_val == pat.ToUint64();
}

// Check if a case item matches based on case_kind and case_inside.
static bool CaseItemMatches(const Logic4Vec& sel, const Logic4Vec& pat,
                            TokenKind case_kind, bool case_inside) {
  if (case_inside) return CaseInsideMatch(sel.ToUint64(), pat);
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return sel.ToUint64() == pat.ToUint64();
}

// --- Case with casex/casez/inside and qualifiers ---

static ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto sel = EvalExpr(stmt->condition, ctx, arena);

  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    for (auto* pat : item.patterns) {
      auto pat_val = EvalExpr(pat, ctx, arena);
      if (CaseItemMatches(sel, pat_val, stmt->case_kind, stmt->case_inside)) {
        co_return co_await ExecStmt(item.body, ctx, arena);
      }
    }
  }
  // Fall through to default.
  for (const auto& item : stmt->case_items) {
    if (item.is_default) co_return co_await ExecStmt(item.body, ctx, arena);
  }
  // priority case: no match and no default => warning.
  bool is_priority = stmt->qualifier == CaseQualifier::kPriority;
  bool is_unique = stmt->qualifier == CaseQualifier::kUnique;
  if (is_priority || is_unique) {
    ctx.GetDiag().Warning({}, "case: no matching item found");
  }
  co_return StmtResult::kDone;
}

// --- Loops ---

// Create for-init variable when the init declares a type (§12.7.1).
static void CreateForInitVar(const Stmt* stmt, SimContext& ctx) {
  if (stmt->for_init_type.kind == DataTypeKind::kImplicit) return;
  if (!stmt->for_init || !stmt->for_init->lhs) return;
  uint32_t w = EvalTypeWidth(stmt->for_init_type);
  if (w == 0) w = 32;
  ctx.CreateVariable(stmt->for_init->lhs->text, w);
}

static ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  CreateForInitVar(stmt, ctx);
  if (stmt->for_init) co_await ExecStmt(stmt->for_init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (stmt->for_cond) {
      auto cond = EvalExpr(stmt->for_cond, ctx, arena);
      if (cond.ToUint64() == 0) break;
    }
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
    if (stmt->for_step) co_await ExecStmt(stmt->for_step, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  auto count = count_val.ToUint64();
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  do {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
  } while (!ctx.StopRequested());
  co_return StmtResult::kDone;
}

// --- Foreach (IEEE §12.7.3) ---

static uint32_t GetArraySize(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr) return 0;
  if (stmt->expr->kind != ExprKind::kIdentifier) return 0;
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return 0;
  return var->value.width;
}

static ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint32_t size = GetArraySize(stmt, ctx);
  if (size == 0) co_return StmtResult::kDone;

  // Determine loop variable name (first non-empty foreach_vars entry).
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(arena, 32, i);
    }
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      ctx.PopScope();
      co_return result;
    }
  }

  ctx.PopScope();
  co_return StmtResult::kDone;
}

// --- Delay ---

static ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    auto val = EvalExpr(stmt->delay, ctx, arena);
    ticks = val.ToUint64();
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Event control ---

static bool IsNamedEvent(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return false;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return false;
  if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) return false;
  auto* var = ctx.FindVariable(ev.signal->text);
  return var && var->is_event;
}

static ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->events.empty()) {
    if (IsNamedEvent(stmt, ctx)) {
      co_await NamedEventAwaiter{ctx, stmt->events[0].signal->text};
    } else {
      co_await EventAwaiter{ctx, stmt->events};
    }
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Event trigger (->ev) ---

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (var) {
    // §15.5.2: Set sticky triggered state for this timeslot.
    ctx.SetEventTriggered(stmt->expr->text);
    var->NotifyWatchers();
  }
  return StmtResult::kDone;
}

// --- Wait (IEEE §9.4.3) ---

static ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  std::unordered_set<std::string_view> reads;
  CollectExprReads(stmt->condition, reads);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() != 0) break;
    if (read_vars.empty()) co_return StmtResult::kDone;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Fork/join (IEEE §9.3.2) ---

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkJoinState* state) {
  co_await ExecStmt(body, ctx, arena);
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    state->parent.resume();
  }
}

static void SpawnForkChildren(const Stmt* stmt, SimContext& ctx, Arena& arena,
                              ForkJoinState* state) {
  for (auto* s : stmt->fork_stmts) {
    auto* p = arena.Create<Process>();
    p->kind = ProcessKind::kInitial;
    p->coro = ForkChildCoroutine(s, ctx, arena, state).Release();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [p]() { p->Resume(); };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  }
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->fork_stmts.empty()) co_return StmtResult::kDone;

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = static_cast<uint32_t>(stmt->fork_stmts.size());
  state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

  SpawnForkChildren(stmt, ctx, arena, state);

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  co_return StmtResult::kDone;
}

// --- Immediate assertions (§16.3) ---

static ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);
  if (cond.ToUint64() != 0) {
    // Pass action.
    if (stmt->assert_pass_stmt) {
      co_return co_await ExecStmt(stmt->assert_pass_stmt, ctx, arena);
    }
  } else {
    // Fail action.
    if (stmt->assert_fail_stmt) {
      co_return co_await ExecStmt(stmt->assert_fail_stmt, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

// --- Main dispatch ---

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return ExecTask::Immediate(StmtResult::kDone);

  switch (stmt->kind) {
    case StmtKind::kNull:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBlock:
      return ExecBlock(stmt, ctx, arena);
    case StmtKind::kIf:
      return ExecIf(stmt, ctx, arena);
    case StmtKind::kCase:
      return ExecCase(stmt, ctx, arena);
    case StmtKind::kFor:
      return ExecFor(stmt, ctx, arena);
    case StmtKind::kForeach:
      return ExecForeach(stmt, ctx, arena);
    case StmtKind::kWhile:
      return ExecWhile(stmt, ctx, arena);
    case StmtKind::kForever:
      return ExecForever(stmt, ctx, arena);
    case StmtKind::kRepeat:
      return ExecRepeat(stmt, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kBlockingAssign:
      return ExecTask::Immediate(ExecBlockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kNonblockingAssign:
      return ExecTask::Immediate(ExecNonblockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kExprStmt:
      return ExecTask::Immediate(ExecExprStmtImpl(stmt, ctx, arena));
    case StmtKind::kDelay:
      return ExecDelay(stmt, ctx, arena);
    case StmtKind::kEventControl:
      return ExecEventControl(stmt, ctx, arena);
    case StmtKind::kFork:
      return ExecFork(stmt, ctx, arena);
    case StmtKind::kWait:
      return ExecWait(stmt, ctx, arena);
    case StmtKind::kEventTrigger:
      return ExecTask::Immediate(ExecEventTriggerImpl(stmt, ctx));
    case StmtKind::kTimingControl:
    case StmtKind::kDisable:
    case StmtKind::kDisableFork:
    case StmtKind::kWaitFork:
    case StmtKind::kWaitOrder:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBreak:
      return ExecTask::Immediate(StmtResult::kBreak);
    case StmtKind::kContinue:
      return ExecTask::Immediate(StmtResult::kContinue);
    case StmtKind::kReturn:
      return ExecTask::Immediate(StmtResult::kReturn);
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return ExecImmediateAssert(stmt, ctx, arena);
    case StmtKind::kForce:
    case StmtKind::kAssign:
      return ExecTask::Immediate(ExecForceOrAssignImpl(stmt, ctx, arena));
    case StmtKind::kRelease:
    case StmtKind::kDeassign:
      return ExecTask::Immediate(ExecReleaseOrDeassignImpl(stmt, ctx));
    case StmtKind::kRandcase:
      return ExecRandcase(stmt, ctx, arena);
    case StmtKind::kVarDecl:
      return ExecTask::Immediate(ExecVarDeclImpl(stmt, ctx, arena));
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

}  // namespace delta
