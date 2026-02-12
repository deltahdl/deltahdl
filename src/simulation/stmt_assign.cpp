#include "simulation/stmt_assign.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

namespace delta {

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
      auto w = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      WritePartSelect(var, idx, w, rhs_val, arena);
    } else if (lhs->is_part_select_minus) {
      auto w = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      uint32_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
      WritePartSelect(var, lo, w, rhs_val, arena);
    } else {
      auto end_idx = static_cast<uint32_t>(
          EvalExpr(lhs->index_end, ctx, arena).ToUint64());
      auto lo = std::min(idx, end_idx);
      auto hi = std::max(idx, end_idx);
      WritePartSelect(var, lo, hi - lo + 1, rhs_val, arena);
    }
  } else {
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
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributePatternToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }
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
  if (expr->kind == ExprKind::kIdentifier) {
    auto* q = ctx.FindQueue(expr->text);
    if (q) {
      out.insert(out.end(), q->elements.begin(), q->elements.end());
      return;
    }
  }
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

// §7.5.1: Copy source array into new[size](src) target.
static void CopyNewInit(const Expr* rhs, QueueObject* q, SimContext& ctx,
                        Arena& /*arena*/) {
  if (!rhs->lhs || rhs->lhs->kind != ExprKind::kIdentifier) return;
  auto* src = ctx.FindQueue(rhs->lhs->text);
  if (!src) return;
  size_t copy_len = std::min(q->elements.size(), src->elements.size());
  for (size_t i = 0; i < copy_len; ++i) q->elements[i] = src->elements[i];
}

// §7.10.4: Queue assignment from concatenation, slice, or literal.
static bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!q) return false;
  if (stmt->rhs->kind == ExprKind::kConcatenation &&
      stmt->rhs->elements.empty()) {
    q->elements.clear();
    return true;
  }
  if (stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new" &&
      !stmt->rhs->args.empty()) {
    auto sz = EvalExpr(stmt->rhs->args[0], ctx, arena).ToUint64();
    q->elements.resize(static_cast<size_t>(sz),
                       MakeLogic4VecVal(arena, q->elem_width, 0));
    CopyNewInit(stmt->rhs, q, ctx, arena);
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
  return true;
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
// §10.9.2: Evaluate RHS as named struct pattern if applicable.
static Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                          Arena& arena) {
  if (!stmt->rhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalExpr(stmt->rhs, ctx, arena);
  }
  bool named = stmt->rhs->kind == ExprKind::kAssignmentPattern &&
               !stmt->rhs->pattern_keys.empty();
  if (!named) return EvalExpr(stmt->rhs, ctx, arena);
  auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text);
  if (!sinfo) return EvalExpr(stmt->rhs, ctx, arena);
  return EvalStructPattern(stmt->rhs, sinfo, ctx, arena);
}

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;

  if (TryClassNewAssign(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryAssocCopyAssign(stmt, ctx)) return StmtResult::kDone;
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;

  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return StmtResult::kDone;
  }

  if (TryArrayBlockingAssign(stmt, ctx, arena)) return StmtResult::kDone;

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

StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);
  if (!stmt->lhs) return StmtResult::kDone;

  bool is_select = (stmt->lhs->kind == ExprKind::kSelect);
  auto* elem = is_select ? TryResolveArrayElement(stmt->lhs, ctx) : nullptr;
  auto* var = elem ? elem : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  if (is_select && !elem) {
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

StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  uint32_t width = EvalTypeWidth(stmt->var_decl_type);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  if (width == 0 && stmt->var_decl_type.kind == DataTypeKind::kString) {
    ctx.CreateVariable(stmt->var_name, 0);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    ctx.CreateVariable(stmt->var_name, width);
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    CreateBlockArrayElements(stmt, width, ctx, arena);
  }
  if (stmt->var_init) {
    auto* var = ctx.FindVariable(stmt->var_name);
    if (var) var->value = EvalExpr(stmt->var_init, ctx, arena);
  }
  return StmtResult::kDone;
}

// --- Force / Release (IEEE §10.6.2) ---

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
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

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  return StmtResult::kDone;
}

}  // namespace delta
