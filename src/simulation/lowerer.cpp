#include "simulation/lowerer.h"

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/net.h"
#include "simulation/process.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag)
    : ctx_(ctx), arena_(arena), diag_(diag) {}

// --- Coroutine factories ---

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
}

static SimCoroutine MakeAlwaysCoroutine(const Stmt* body, SimContext& ctx,
                                        Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysSensCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens};
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body, SimContext& ctx,
                                            Arena& arena) {
  auto read_vars = CollectReadSignals(body);
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

static SimCoroutine MakeContAssignCoroutine(const Expr* lhs, const Expr* rhs,
                                            SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(rhs, ctx, arena);
  if (lhs && lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(lhs->text);
    if (var) {
      var->value = val;
      var->NotifyWatchers();
    }
  }
  co_return;
}

// --- Schedule helper ---

static void ScheduleProcess(Process* proc, Scheduler& sched) {
  auto* event = sched.GetEventPool().Acquire();
  event->callback = [proc]() { proc->Resume(); };
  sched.ScheduleEvent(SimTime{0}, Region::kActive, event);
}

// --- Module lowering ---

// Register struct type metadata for field-level access at runtime.
static void RegisterStructInfo(const RtlirVariable& var, SimContext& ctx) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  StructTypeInfo info;
  info.type_name = var.name;
  info.is_packed = var.dtype->is_packed;
  info.total_width = var.width;
  bool is_union = (var.dtype->kind == DataTypeKind::kUnion);
  // §7.2.1: First struct member is MSB. Union members all at offset 0.
  uint32_t offset = var.width;
  for (const auto& m : var.dtype->struct_members) {
    uint32_t fw = EvalStructMemberWidth(m);
    if (is_union) {
      info.fields.push_back({m.name, 0, fw});
    } else {
      offset -= fw;
      info.fields.push_back({m.name, offset, fw});
    }
  }
  ctx.RegisterStructType(var.name, info);
  ctx.SetVariableStructType(var.name, var.name);
}

// §7.4: Initialize an individual array element, optionally from init pattern.
static void InitArrayElement(const RtlirVariable& var, uint32_t elem_idx,
                             Variable* elem, SimContext& ctx, Arena& arena) {
  if (!var.init_expr) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }
  auto& elements = var.init_expr->elements;
  if (elem_idx < elements.size()) {
    elem->value = EvalExpr(elements[elem_idx], ctx, arena);
    return;
  }
  elem->value = MakeLogic4VecVal(arena, var.width, 0);
}

// §7.4: Create individual element variables for unpacked arrays.
static void CreateArrayElements(const RtlirVariable& var, SimContext& ctx,
                                Arena& arena) {
  if (var.unpacked_size == 0) return;
  ArrayInfo info;
  info.lo = var.unpacked_lo;
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  ctx.RegisterArray(var.name, info);
  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    uint32_t idx = var.unpacked_lo + i;
    auto elem_name = std::string(var.name) + "[" + std::to_string(idx) + "]";
    auto* stored = arena.Create<std::string>(std::move(elem_name));
    auto* elem = ctx.CreateVariable(*stored, var.width);
    // §7.4: For descending [hi:lo], pattern element 0 maps to highest index.
    uint32_t pat_idx = var.is_descending ? (var.unpacked_size - 1 - i) : i;
    InitArrayElement(var, pat_idx, elem, ctx, arena);
  }
}

// §7.8: Set default value for an assoc array from '{default: val} pattern.
void Lowerer::InitAssocDefault(const Expr* init, AssocArrayObject* aa) {
  if (!init || init->kind != ExprKind::kAssignmentPattern) return;
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (init->pattern_keys[i] != "default") continue;
    if (i >= init->elements.size()) break;
    aa->has_default = true;
    aa->default_value = EvalExpr(init->elements[i], ctx_, arena_);
    return;
  }
}

// §7.2.2: Apply struct member default values to a packed struct variable.
static void ApplyStructMemberDefaults(const RtlirVariable& var, Variable* v,
                                      SimContext& ctx, Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  auto* sinfo = ctx.GetVariableStructType(var.name);
  if (!sinfo) return;
  for (const auto& f : sinfo->fields) {
    // Find the matching struct member with an init_expr.
    for (const auto& m : var.dtype->struct_members) {
      if (m.name != f.name || !m.init_expr) continue;
      auto val = EvalExpr(m.init_expr, ctx, arena).ToUint64();
      uint64_t mask =
          (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
      uint64_t old_val = v->value.ToUint64();
      old_val |= (val & mask) << f.bit_offset;
      v->value = MakeLogic4VecVal(arena, v->value.width, old_val);
      break;
    }
  }
}

void Lowerer::LowerVar(const RtlirVariable& var) {
  // §8: Class handles are 64-bit.
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  auto* v = ctx_.CreateVariable(var.name, width);
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.is_string) ctx_.RegisterStringVariable(var.name);
  if (var.is_real) ctx_.RegisterRealVariable(var.name);
  if (var.init_expr) {
    auto val = EvalExpr(var.init_expr, ctx_, arena_);
    if (val.width != var.width)
      val = MakeLogic4VecVal(arena_, var.width, val.ToUint64());
    v->value = val;
  }
  RegisterStructInfo(var, ctx_);
  if (!var.init_expr) ApplyStructMemberDefaults(var, v, ctx_, arena_);
  if (!var.class_type_name.empty()) {
    ctx_.SetVariableClassType(var.name, var.class_type_name);
  }
  if (var.is_queue) {
    ctx_.CreateQueue(var.name, var.width, var.queue_max_size);
  } else if (var.is_assoc) {
    auto* aa = ctx_.CreateAssocArray(var.name, var.width, var.is_string_index);
    InitAssocDefault(var.init_expr, aa);
  } else {
    CreateArrayElements(var, ctx_, arena_);
  }
}

// §8: Create ClassTypeInfo from a ClassDecl AST node.
void Lowerer::LowerClassDecl(const ClassDecl* cls) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      uint32_t w = EvalTypeWidth(member->data_type, {});
      if (w == 0) w = 32;
      info->properties.push_back({member->name, w, member->is_static});
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
  // §8.5: Register class parameters as properties.
  for (const auto& [pname, pexpr] : cls->params) {
    info->properties.push_back({pname, 32, false});
  }
  ctx_.RegisterClassType(cls->name, info);
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  // Create variables for resolved parameters (§6.20).
  for (const auto& p : mod->params) {
    if (!p.is_resolved) continue;
    auto* var = ctx_.CreateVariable(p.name, 32);
    var->value =
        MakeLogic4VecVal(arena_, 32, static_cast<uint64_t>(p.resolved_value));
  }
  // Create Net objects for all declared nets (with resolution support).
  for (const auto& net : mod->nets) {
    ctx_.CreateNet(net.name, net.net_type, net.width, net.charge_strength,
                   net.decay_ticks);
  }
  for (const auto& var : mod->variables) LowerVar(var);
  // Create variables for output ports.
  for (const auto& port : mod->ports) {
    if (!ctx_.FindVariable(port.name)) {
      ctx_.CreateVariable(port.name, port.width);
    }
  }

  // Register function declarations.
  for (auto* func : mod->function_decls) {
    ctx_.RegisterFunction(func->name, func);
  }

  // §8: Register class type declarations.
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }

  // Lower processes.
  for (const auto& proc : mod->processes) {
    LowerProcess(proc);
  }

  // Lower continuous assignments.
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca);
  }
}

// --- Process lowering ---

static void RegisterSensitivity(const RtlirProcess& proc, Process* p,
                                SimContext& ctx) {
  auto signals = CollectReadSignals(proc.body);
  for (auto name : signals) {
    ctx.AddSensitivity(name, p);
  }
}

void Lowerer::LowerProcess(const RtlirProcess& proc) {
  auto* p = arena_.Create<Process>();
  p->id = next_id_++;
  p->home_region = Region::kActive;

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kAlways:
      p->kind = ProcessKind::kAlways;
      if (!proc.sensitivity.empty()) {
        p->coro =
            MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
                .Release();
      } else {
        p->coro = MakeAlwaysCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      RegisterSensitivity(proc, p, ctx_);
      break;
    case RtlirProcessKind::kAlwaysFF:
      p->kind = ProcessKind::kAlwaysFF;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;  // Don't schedule at time 0.
  }

  ScheduleProcess(p, ctx_.GetScheduler());
}

// --- Continuous assignment lowering ---

void Lowerer::LowerContAssign(const RtlirContAssign& ca) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  p->coro = MakeContAssignCoroutine(ca.lhs, ca.rhs, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_.GetScheduler());
}

// --- Design lowering ---

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  for (const auto& [name, width] : design->type_widths) {
    ctx_.RegisterTypeWidth(name, width);
  }
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }
}

}  // namespace delta
