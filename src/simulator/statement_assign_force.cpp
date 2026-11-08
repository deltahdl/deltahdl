#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_force_internal.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

struct RhsWatcherSpec {
  std::function<bool()> still_valid;
  bool forced = false;
  Net* net = nullptr;
  ProcContAssignWindow window;
};

static void WriteOwnedBits(Variable* var, const Logic4Vec& val,
                           const RhsWatcherSpec& spec, Arena& arena) {
  if (spec.window.dst_width == 0) {
    Logic4Vec sized = ResizeToWidth(val, var->value.width, arena);
    if (spec.forced) var->forced_value = sized;
    var->value = sized;
  } else {
    bool whole = spec.window.src_width == 0;
    uint32_t src_lo = whole ? 0 : spec.window.src_lo;
    uint32_t src_width = whole ? spec.window.dst_width : spec.window.src_width;
    Logic4Vec src = val.width < src_lo + src_width
                        ? ResizeToWidth(val, src_lo + src_width, arena)
                        : val;
    Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
    DepositBitField(updated, spec.window.dst_lo,
                    ExtractBitField(arena, src, src_lo, src_width),
                    spec.window.dst_width);
    var->value = updated;
    if (spec.forced) var->forced_value = var->value;
  }
  if (!var->is_4state) CoerceTo2State(var->value);
}

static void RecomputeRhsInto(Variable* var, const Expr* rhs, SimContext& ctx,
                             Arena& arena, const RhsWatcherSpec& spec) {
  auto new_val = EvalExpr(rhs, ctx, arena, spec.window.rhs_width);
  WriteOwnedBits(var, new_val, spec, arena);
  var->NotifyWatchers();
}

static void InstallRhsWatchers(Variable* var, const Expr* rhs, SimContext& ctx,
                               Arena& arena, const RhsWatcherSpec& spec) {
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : CollectDistinctRhsVars(rhs, ctx, var)) {
    rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr, spec]() {
      if (!spec.still_valid()) return true;
      RecomputeRhsInto(var, rhs, *ctx_ptr, *arena_ptr, spec);
      if (spec.net != nullptr) spec.net->Resolve(*arena_ptr);
      return false;
    });
  }
}

static bool WindowsOverlap(const ProcContAssignWindow& a,
                           const ProcContAssignWindow& b) {
  if (a.dst_width == 0 || b.dst_width == 0) return true;
  return a.dst_lo < b.dst_lo + b.dst_width && b.dst_lo < a.dst_lo + a.dst_width;
}

static bool HoldsPart(const Variable& var, const ProcContAssignWindow& window,
                      const Expr* rhs) {
  return std::ranges::any_of(var.held_parts, [&](const Variable::HeldPart& p) {
    return p.rhs == rhs && p.window.dst_lo == window.dst_lo &&
           p.window.dst_width == window.dst_width;
  });
}

static void InstallForcedValueWatcher(Variable* var, const Expr* rhs,
                                      SimContext& ctx, Arena& arena,
                                      RhsWatcherSpec spec) {
  spec.forced = true;
  auto rhs_val = EvalExpr(rhs, ctx, arena, spec.window.rhs_width);
  var->is_forced = true;
  std::erase_if(var->held_parts, [&spec](const Variable::HeldPart& part) {
    return WindowsOverlap(part.window, spec.window);
  });
  var->held_parts.push_back({spec.window, rhs});
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->proc_cont_rhs = rhs;
  var->NotifyWatchers();

  if (spec.net != nullptr) spec.net->Resolve(arena);

  spec.still_valid = [var, rhs, window = spec.window]() {
    return var->is_forced && HoldsPart(*var, window, rhs);
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

static void ReestablishAssign(Variable* var, SimContext& ctx, Arena& arena) {
  RhsWatcherSpec spec;
  spec.window = var->assign_cont_window;
  InstallForcedValueWatcher(var, var->assign_cont_rhs, ctx, arena, spec);
}

static void ScheduleContAssignReevaluation(const Variable* var,
                                           SimContext& ctx) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = var->cont_assign_reevaluate;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
}

static void InstallProcContAssign(Variable* var, const Stmt* stmt,
                                  const RhsWatcherSpec& spec, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->kind == StmtKind::kAssign) {
    var->assign_cont_rhs = stmt->rhs;
    var->assign_cont_window = spec.window;
    if (var->force_active) return;
  } else {
    var->force_active = true;
  }
  InstallForcedValueWatcher(var, stmt->rhs, ctx, arena, spec);
}

static void EndProcContAssign(Variable* var, bool release, SimContext& ctx,
                              Arena& arena) {
  if (!release) {
    var->assign_cont_rhs = nullptr;
    var->assign_cont_window = {};
    if (var->force_active) return;
  }
  var->is_forced = false;
  var->force_active = false;
  var->held_parts.clear();
  var->proc_cont_rhs = nullptr;
  if (!release) return;
  if (var->assign_cont_rhs) {
    ReestablishAssign(var, ctx, arena);
  } else if (var->cont_assign_reevaluate) {
    ScheduleContAssignReevaluation(var, ctx);
  }
}

struct ConcatElemSlot {
  const Expr* el = nullptr;
  Variable* var = nullptr;
  uint32_t src_lo = 0;
  uint32_t width = 0;
  uint32_t rhs_width = 0;
  bool names_whole_element = false;
};

static RhsWatcherSpec SpecForSlot(const ConcatElemSlot& slot, SimContext& ctx,
                                  Arena& arena) {
  PartSelectBits dst{0, slot.width};
  if (!slot.names_whole_element && slot.el->kind == ExprKind::kSelect &&
      slot.el->base != nullptr) {
    dst = SelectStorageBits(*slot.var, slot.el, ctx, arena);
  }
  Net* net = slot.el->kind == ExprKind::kIdentifier ? ctx.FindNet(slot.el->text)
                                                    : nullptr;
  RhsWatcherSpec spec;
  spec.net = net;
  spec.window.rhs_width = slot.rhs_width;
  spec.window.src_lo = slot.src_lo + dst.src_lo;
  spec.window.src_width = slot.width;
  spec.window.dst_lo = dst.lo;
  spec.window.dst_width = dst.width;
  return spec;
}

static void ForceOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                            SimContext& ctx, Arena& arena) {
  InstallProcContAssign(slot.var, stmt, SpecForSlot(slot, ctx, arena), ctx,
                        arena);
}

static Net* ForceTargetNet(const Expr* lhs, SimContext& ctx);
static void ReleaseForcedBits(Variable* var, Net* net,
                              const ProcContAssignWindow& window,
                              SimContext& ctx, Arena& arena);

static void ReleaseOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                              SimContext& ctx, Arena& arena) {
  if (stmt->kind != StmtKind::kRelease) {
    EndProcContAssign(slot.var, false, ctx, arena);
    return;
  }
  ReleaseForcedBits(slot.var, ForceTargetNet(slot.el, ctx),
                    SpecForSlot(slot, ctx, arena).window, ctx, arena);
}

static void ApplyToConcatElement(const ConcatElemSlot& slot, const Stmt* stmt,
                                 SimContext& ctx, Arena& arena) {
  if (!ConcatLhsElemHasWritableBits(slot.el, *slot.var, ctx, arena)) return;
  if (stmt->kind == StmtKind::kRelease || stmt->kind == StmtKind::kDeassign) {
    ReleaseOneElement(slot, stmt, ctx, arena);
    return;
  }
  ForceOneElement(slot, stmt, ctx, arena);
}

static uint32_t WalkConcatLhsElements(const Expr* lhs, const Stmt* stmt,
                                      uint32_t bit_offset, SimContext& ctx,
                                      Arena& arena) {
  uint32_t rhs_width = LhsContextWidth(stmt->lhs, ctx, arena);
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    const Expr* el = *it;
    uint32_t w = ConcatLhsElemWidth(el, ctx, arena);
    if (w == 0) {
      ReportZeroWidthPartSelect(el, ctx, arena);
      continue;
    }
    if (IsConcatLhs(el)) {
      bit_offset = WalkConcatLhsElements(UnwrapTypedPattern(el), stmt,
                                         bit_offset, ctx, arena);
      continue;
    }
    if (TryContainerElementDrive(
            el, stmt, ElementDriveSource{nullptr, bit_offset, w, rhs_width},
            ctx, arena)) {
      bit_offset += w;
      continue;
    }
    Variable* var = TryResolveArrayElement(el, ctx);
    bool whole_element = var != nullptr;
    if (var == nullptr) var = ResolveLhsVariable(el, ctx);
    if (var != nullptr) {
      ApplyToConcatElement({el, var, bit_offset, w, rhs_width, whole_element},
                           stmt, ctx, arena);
    }
    bit_offset += w;
  }
  return bit_offset;
}

static std::string ArrayElementKeyOf(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kSelect || e->base == nullptr ||
      e->index == nullptr || e->index_end != nullptr) {
    return {};
  }
  std::string_view root = ArrayRootKey(e->base, ctx.GetArena());
  if (root.empty() || ctx.FindArrayInfo(root) == nullptr) return {};
  Logic4Vec idx = EvalExpr(e->index, ctx, ctx.GetArena());
  if (HasUnknownBits(idx)) return {};
  return std::string(root) + "[" + std::to_string(idx.ToUint64()) + "]";
}

static std::string ForceElementKey(const Expr* lhs, SimContext& ctx) {
  std::string key = ArrayElementKeyOf(lhs, ctx);
  if (key.empty() && lhs->kind == ExprKind::kSelect && lhs->base != nullptr) {
    key = ArrayElementKeyOf(lhs->base, ctx);
  }
  return key;
}

static Net* ForceTargetNet(const Expr* lhs, SimContext& ctx) {
  if (std::string key = ForceElementKey(lhs, ctx); !key.empty()) {
    return ctx.FindNet(key);
  }
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindNet(lhs->text);
  if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr &&
      lhs->base->kind == ExprKind::kIdentifier) {
    return ctx.FindNet(lhs->base->text);
  }
  return nullptr;
}

static bool ProcContAssignTargetHandled(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena, Variable** var) {
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return true;
  }
  if (TryContainerElementDrive(stmt->lhs, stmt, ElementDriveSource{}, ctx,
                               arena)) {
    return true;
  }
  std::string key = ForceElementKey(stmt->lhs, ctx);
  *var =
      key.empty() ? ResolveLhsVariable(stmt->lhs, ctx) : ctx.FindVariable(key);
  return *var == nullptr;
}

static bool TargetWindow(const Expr* lhs, Variable& var, SimContext& ctx,
                         Arena& arena, ProcContAssignWindow& window) {
  if (lhs->kind != ExprKind::kSelect || !ArrayElementKeyOf(lhs, ctx).empty()) {
    return true;
  }
  PartSelectBits dst = SelectStorageBits(var, lhs, ctx, arena);
  window.src_lo = dst.src_lo;
  window.src_width = dst.width;
  window.dst_lo = dst.lo;
  window.dst_width = dst.width;
  return dst.width != 0;
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  Variable* var = nullptr;
  if (ProcContAssignTargetHandled(stmt, ctx, arena, &var)) {
    return StmtResult::kDone;
  }

  RhsWatcherSpec spec;
  if (!TargetWindow(stmt->lhs, *var, ctx, arena, spec.window)) {
    return StmtResult::kDone;
  }
  spec.window.rhs_width =
      spec.window.dst_width != 0 ? spec.window.dst_width : var->value.width;

  spec.net = ForceTargetNet(stmt->lhs, ctx);
  InstallProcContAssign(var, stmt, spec, ctx, arena);
  GetGlobalVpiContext().NoteForce(
      stmt->kind == StmtKind::kForce ? cbForce : cbAssign, var, stmt,
      ctx.ActiveInstancePrefix());
  return StmtResult::kDone;
}

static void ReleaseUndrivenBits(Net& net, const ProcContAssignWindow& window) {
  if (!net.drivers.empty() || !net.switch_drivers.empty() ||
      net.is_user_nettype || net.type == NetType::kTrireg) {
    return;
  }
  Logic4Vec& value = net.resolved->value;
  uint32_t lo = window.dst_width == 0 ? 0 : window.dst_lo;
  uint32_t width = window.dst_width == 0 ? value.width : window.dst_width;
  for (uint32_t bit = lo; bit < lo + width && bit < value.width; ++bit) {
    uint64_t mask = uint64_t{1} << (bit % 64);
    value.words[bit / 64].aval &= ~mask;
    value.words[bit / 64].bval |= mask;
  }
  net.resolved->NotifyWatchers();
}

static void ReleaseForcedBits(Variable* var, Net* net,
                              const ProcContAssignWindow& window,
                              SimContext& ctx, Arena& arena) {
  auto released_by = [&window](const Variable::HeldPart& part) {
    return WindowsOverlap(part.window, window);
  };
  std::vector<ProcContAssignWindow> released;
  for (const auto& part : var->held_parts) {
    if (released_by(part)) released.push_back(part.window);
  }
  std::erase_if(var->held_parts, released_by);
  if (var->held_parts.empty()) EndProcContAssign(var, true, ctx, arena);
  if (net == nullptr) return;
  for (const auto& bits : released) ReleaseUndrivenBits(*net, bits);
  net->Resolve(arena);
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  Variable* var = nullptr;
  if (ProcContAssignTargetHandled(stmt, ctx, arena, &var)) {
    return StmtResult::kDone;
  }

  if (stmt->kind == StmtKind::kDeassign) {
    EndProcContAssign(var, false, ctx, arena);
    GetGlobalVpiContext().NoteForce(cbDeassign, var, stmt,
                                    ctx.ActiveInstancePrefix());
    return StmtResult::kDone;
  }
  ProcContAssignWindow window;
  if (TargetWindow(stmt->lhs, *var, ctx, arena, window)) {
    ReleaseForcedBits(var, ForceTargetNet(stmt->lhs, ctx), window, ctx, arena);
  }
  GetGlobalVpiContext().NoteForce(cbRelease, var, stmt,
                                  ctx.ActiveInstancePrefix());
  return StmtResult::kDone;
}

void ReleaseForcedTarget(Variable* var, Net* net, SimContext& ctx,
                         Arena& arena) {
  ReleaseForcedBits(var, net, ProcContAssignWindow{}, ctx, arena);
}

}  // namespace delta
