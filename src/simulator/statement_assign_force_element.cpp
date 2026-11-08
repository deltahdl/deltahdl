#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assoc_index.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_force_internal.h"
#include "simulator/variable.h"

namespace delta {

static void CollectExprVars(const Expr* expr, SimContext& ctx,
                            std::vector<Variable*>& vars) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->text);
    if (var) vars.push_back(var);
    return;
  }
  std::string dotted;
  if (expr->kind == ExprKind::kMemberAccess && DottedNamePath(expr, dotted)) {
    if (auto* var = ctx.FindVariable(dotted)) {
      vars.push_back(var);
      return;
    }
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
  CollectExprVars(expr->stream_range, ctx, vars);
  CollectExprVars(expr->repeat_count, ctx, vars);
  for (auto* e : expr->elements) CollectExprVars(e, ctx, vars);
  for (auto* a : expr->args) CollectExprVars(a, ctx, vars);
}

std::vector<Variable*> CollectDistinctRhsVars(const Expr* rhs, SimContext& ctx,
                                              Variable* self) {
  std::vector<Variable*> rhs_vars;
  CollectExprVars(rhs, ctx, rhs_vars);
  std::sort(rhs_vars.begin(), rhs_vars.end());
  rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()), rhs_vars.end());
  rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), self),
                 rhs_vars.end());
  return rhs_vars;
}

struct ContainerElement {
  QueueObject* queue = nullptr;
  AssocArrayObject* assoc = nullptr;
  uint64_t queue_id = 0;
  bool string_key = false;
  AssocIndex int_key;
  std::string str_key;
  std::string name;
  uint32_t elem_width = 32;
};

static ElementDrive* ElementDriveFor(const ContainerElement& elem,
                                     bool create) {
  if (elem.queue != nullptr) {
    auto& drives = elem.queue->element_drives;
    auto it = drives.find(elem.queue_id);
    if (it != drives.end()) return &it->second;
    return create ? &drives[elem.queue_id] : nullptr;
  }
  if (elem.assoc == nullptr) return nullptr;
  if (elem.string_key) {
    auto& drives = elem.assoc->str_drives;
    auto it = drives.find(elem.str_key);
    if (it != drives.end()) return &it->second;
    return create ? &drives[elem.str_key] : nullptr;
  }
  auto& drives = elem.assoc->int_drives;
  auto it = drives.find(elem.int_key);
  if (it != drives.end()) return &it->second;
  return create ? &drives[elem.int_key] : nullptr;
}

static void ForgetEmptyElementDrive(const ContainerElement& elem) {
  ElementDrive* drive = ElementDriveFor(elem, false);
  if (drive == nullptr || drive->Drives()) return;
  if (elem.queue != nullptr) {
    elem.queue->element_drives.erase(elem.queue_id);
  } else if (elem.string_key) {
    elem.assoc->str_drives.erase(elem.str_key);
  } else {
    elem.assoc->int_drives.erase(elem.int_key);
  }
}

static bool ResolveQueueElement(const Expr* lhs, QueueObject* q,
                                SimContext& ctx, Arena& arena,
                                ContainerElement& out) {
  bool idx_xz = false;
  int64_t idx = QueueElementIndex(lhs->index, q, ctx, arena, &idx_xz);
  if (idx_xz) return false;
  if (idx < 0 || idx >= static_cast<int64_t>(q->elements.size())) return false;
  out.queue = q;
  out.queue_id = q->element_ids[static_cast<size_t>(idx)];
  out.elem_width = q->elem_width;
  return true;
}

static bool ResolveAssocElement(const Expr* lhs, AssocArrayObject* aa,
                                SimContext& ctx, Arena& arena,
                                ContainerElement& out) {
  auto key_val = EvalExpr(lhs->index, ctx, arena);
  if (aa->is_string_key) {
    out.str_key = AssocStringKey(key_val);
    if (aa->str_data.find(out.str_key) == aa->str_data.end()) return false;
    out.string_key = true;
  } else {
    if (HasUnknownBits(key_val)) return false;
    out.int_key = AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                              aa->is_index_signed);
    if (aa->int_data.find(out.int_key) == aa->int_data.end()) return false;
  }
  out.assoc = aa;
  out.elem_width = aa->elem_width;
  return true;
}

static bool ResolveContainerElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena, ContainerElement& out) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return false;
  if (lhs->base == nullptr || lhs->base->kind != ExprKind::kIdentifier)
    return false;
  if (lhs->index == nullptr || lhs->index_end != nullptr) return false;
  out.name = std::string(lhs->base->text);
  if (auto* q = ctx.FindQueue(lhs->base->text)) {
    return ResolveQueueElement(lhs, q, ctx, arena, out);
  }
  if (auto* aa = ctx.FindAssocArray(lhs->base->text)) {
    return ResolveAssocElement(lhs, aa, ctx, arena, out);
  }
  return false;
}

static void StoreContainerElement(const ContainerElement& elem,
                                  const Logic4Vec& val, SimContext& ctx,
                                  Arena& arena) {
  Logic4Vec sized = ResizeToWidth(val, elem.elem_width, arena);
  if (elem.queue != nullptr) {
    const auto& ids = elem.queue->element_ids;
    for (size_t i = 0; i < ids.size() && i < elem.queue->elements.size(); ++i) {
      if (ids[i] != elem.queue_id) continue;
      elem.queue->elements[i] = sized;
      NotifyOwningVar(ctx, elem.name);
      return;
    }
    return;
  }
  if (elem.assoc == nullptr) return;
  if (elem.string_key) {
    auto it = elem.assoc->str_data.find(elem.str_key);
    if (it == elem.assoc->str_data.end()) return;
    it->second = sized;
  } else {
    auto it = elem.assoc->int_data.find(elem.int_key);
    if (it == elem.assoc->int_data.end()) return;
    it->second = sized;
  }
  NotifyOwningVar(ctx, elem.name);
}

static Logic4Vec ElementDriveValue(const ElementDriveSource& src,
                                   SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(src.rhs, ctx, arena, src.rhs_width);
  if (src.width == 0) return val;
  return ExtractBitField(arena, val, src.src_lo, src.width);
}

static void InstallElementDriveWatchers(const ContainerElement& elem,
                                        const ElementDriveSource& src,
                                        bool forced, SimContext& ctx,
                                        Arena& arena) {
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : CollectDistinctRhsVars(src.rhs, ctx, nullptr)) {
    rhs_var->AddWatcher([elem, src, forced, ctx_ptr, arena_ptr]() {
      const ElementDrive* drive = ElementDriveFor(elem, false);
      if (drive == nullptr) return true;
      const ElementDriveSource& standing =
          forced ? drive->forced : drive->assigned;
      if (standing.rhs != src.rhs) return true;
      StoreContainerElement(elem, ElementDriveValue(src, *ctx_ptr, *arena_ptr),
                            *ctx_ptr, *arena_ptr);
      return false;
    });
  }
}

static void DriveContainerElement(const ContainerElement& elem,
                                  const Stmt* stmt,
                                  const ElementDriveSource& src,
                                  SimContext& ctx, Arena& arena) {
  ElementDrive* drive = ElementDriveFor(elem, true);
  bool forced = stmt->kind == StmtKind::kForce;
  if (forced) {
    drive->forced = src;
  } else {
    drive->assigned = src;
  }
  StoreContainerElement(elem, ElementDriveValue(src, ctx, arena), ctx, arena);
  InstallElementDriveWatchers(elem, src, forced, ctx, arena);
}

static void EndContainerElementDrive(const ContainerElement& elem,
                                     const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  ElementDrive* drive = ElementDriveFor(elem, false);
  if (drive == nullptr) return;
  if (stmt->kind == StmtKind::kDeassign) {
    drive->assigned = {};
  } else {
    drive->forced = {};
    if (drive->assigned.rhs != nullptr) {
      StoreContainerElement(
          elem, ElementDriveValue(drive->assigned, ctx, arena), ctx, arena);
    }
  }
  ForgetEmptyElementDrive(elem);
}

bool TryContainerElementDrive(const Expr* lhs, const Stmt* stmt,
                              const ElementDriveSource& slot, SimContext& ctx,
                              Arena& arena) {
  ContainerElement elem;
  if (!ResolveContainerElement(lhs, ctx, arena, elem)) return false;
  if (stmt->kind == StmtKind::kRelease || stmt->kind == StmtKind::kDeassign) {
    EndContainerElementDrive(elem, stmt, ctx, arena);
    return true;
  }
  ElementDriveSource src = slot;
  src.rhs = stmt->rhs;
  DriveContainerElement(elem, stmt, src, ctx, arena);
  return true;
}

}  // namespace delta
