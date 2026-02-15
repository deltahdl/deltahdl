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

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine& /*diag*/)
    : ctx_(ctx), arena_(arena) {}

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
  auto read_strs = CollectReadSignals(body);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

// §10.3.4: Convert parser strength encoding to Strength enum.
static Strength ParserStrToStrength(uint8_t s) {
  switch (s) {
    case 1:
      return Strength::kHighz;
    case 2:
      return Strength::kWeak;
    case 3:
      return Strength::kPull;
    case 4:
      return Strength::kStrong;
    case 5:
      return Strength::kSupply;
    default:
      return Strength::kStrong;
  }
}

static SimCoroutine MakeContAssignCoroutine(const Expr* lhs, const Expr* rhs,
                                            DriverStrength ds, SimContext& ctx,
                                            Arena& arena) {
  auto val = EvalExpr(rhs, ctx, arena);
  if (!lhs || lhs->kind != ExprKind::kIdentifier) co_return;
  // §10.3.4: If target is a net, add as a strength-aware driver.
  auto* net = ctx.FindNet(lhs->text);
  if (net) {
    net->drivers.push_back(val);
    net->driver_strengths.push_back(ds);
    net->Resolve(arena);
    co_return;
  }
  auto* var = ctx.FindVariable(lhs->text);
  if (var) {
    var->value = val;
    var->NotifyWatchers();
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
  info.is_union = (var.dtype->kind == DataTypeKind::kUnion);
  info.is_soft = var.dtype->is_soft;
  info.total_width = var.width;
  // §7.2.1: First struct member is MSB. Union members all at offset 0.
  uint32_t offset = var.width;
  for (const auto& m : var.dtype->struct_members) {
    uint32_t fw = EvalStructMemberWidth(m);
    if (info.is_union) {
      info.fields.push_back({m.name, 0, fw, m.type_kind});
    } else {
      offset -= fw;
      info.fields.push_back({m.name, offset, fw, m.type_kind});
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

// §5.11: Initialize array element from '{count{val}} replication pattern.
static void InitArrayFromReplicate(const RtlirVariable& var, uint32_t elem_idx,
                                   Variable* elem, SimContext& ctx,
                                   Arena& arena) {
  auto* rep = var.init_expr->elements[0];
  auto inner_count = static_cast<uint32_t>(rep->elements.size());
  if (inner_count == 0) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }
  elem->value = EvalExpr(rep->elements[elem_idx % inner_count], ctx, arena);
}

// §5.11: Initialize array element from named pattern (index keys / default).
static void InitArrayFromNamed(const RtlirVariable& var, uint32_t idx,
                               Variable* elem, SimContext& ctx, Arena& arena) {
  auto* init = var.init_expr;
  // Pass 1: explicit index key.
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto& key = init->pattern_keys[i];
    if (key == "default") continue;
    auto key_idx = static_cast<uint32_t>(std::stoul(std::string(key)));
    if (key_idx == idx) {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return;
    }
  }
  // Pass 2: default key.
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    if (init->pattern_keys[i] == "default") {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return;
    }
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
  // §5.11: Detect replication and named array pattern forms.
  bool named = var.init_expr && !var.init_expr->pattern_keys.empty();
  bool replicate = var.init_expr && var.init_expr->elements.size() == 1 &&
                   var.init_expr->elements[0]->kind == ExprKind::kReplicate;
  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    uint32_t idx = var.unpacked_lo + i;
    auto elem_name = std::string(var.name) + "[" + std::to_string(idx) + "]";
    auto* stored = arena.Create<std::string>(std::move(elem_name));
    auto* elem = ctx.CreateVariable(*stored, var.width);
    uint32_t pat_idx = var.is_descending ? (var.unpacked_size - 1 - i) : i;
    if (named) {
      InitArrayFromNamed(var, idx, elem, ctx, arena);
    } else if (replicate) {
      InitArrayFromReplicate(var, pat_idx, elem, ctx, arena);
    } else {
      InitArrayElement(var, pat_idx, elem, ctx, arena);
    }
  }
}

// §7.9.11: Strip surrounding quotes from a string literal key.
static std::string StripQuotes(std::string_view s) {
  if (s.size() >= 2 && s.front() == '"' && s.back() == '"')
    return std::string(s.substr(1, s.size() - 2));
  return std::string(s);
}

// §7.5: Initialize dynamic array from init expression.
void Lowerer::LowerDynArrayInit(const RtlirVariable& var) {
  if (!var.init_expr) return;
  auto* q = ctx_.FindQueue(var.name);
  if (!q) return;
  // Accept both '{...} (assignment pattern) and {...} (concatenation) syntax.
  if (var.init_expr->kind != ExprKind::kAssignmentPattern &&
      var.init_expr->kind != ExprKind::kConcatenation)
    return;
  for (auto* elem : var.init_expr->elements) {
    q->elements.push_back(EvalExpr(elem, ctx_, arena_));
  }
}

// §7.9.11: Initialize assoc array from '{key:val, default:val} literal.
void Lowerer::InitAssocDefault(const Expr* init, AssocArrayObject* aa) {
  if (!init || init->kind != ExprKind::kAssignmentPattern) return;
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto key = init->pattern_keys[i];
    auto val = EvalExpr(init->elements[i], ctx_, arena_);
    if (key == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripQuotes(key)] = val;
    } else {
      auto ikey = static_cast<int64_t>(std::stoll(std::string(key)));
      aa->int_data[ikey] = val;
    }
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

// §7/§8: Lower aggregate (queue/assoc/array) storage for a variable.
void Lowerer::LowerVarAggregate(const RtlirVariable& var) {
  if (var.is_queue) {
    ctx_.CreateQueue(var.name, var.width, var.queue_max_size);
  } else if (var.is_dynamic) {
    // §7.5: Dynamic arrays use queue storage for resize support.
    ctx_.CreateQueue(var.name, var.width);
    LowerDynArrayInit(var);
    // §7.12: Register ArrayInfo so reduction/ordering/locator methods dispatch.
    ArrayInfo info;
    info.is_dynamic = true;
    info.elem_width = var.width;
    ctx_.RegisterArray(var.name, info);
  } else if (var.is_assoc) {
    auto* aa = ctx_.CreateAssocArray(var.name, var.width, var.is_string_index,
                                     var.assoc_index_width);
    InitAssocDefault(var.init_expr, aa);
  } else {
    CreateArrayElements(var, ctx_, arena_);
  }
}

void Lowerer::LowerVar(const RtlirVariable& var) {
  // §8: Class handles are 64-bit. §6.12: Real/shortreal store as 64-bit double.
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  if (var.is_real && width < 64) width = 64;
  auto* v = ctx_.CreateVariable(var.name, width);
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.is_string) ctx_.RegisterStringVariable(var.name);
  if (var.is_real) ctx_.RegisterRealVariable(var.name);
  RegisterStructInfo(var, ctx_);
  if (var.init_expr) {
    LowerVarInit(var, v, width);
  }
  if (!var.init_expr) ApplyStructMemberDefaults(var, v, ctx_, arena_);
  if (!var.class_type_name.empty())
    ctx_.SetVariableClassType(var.name, var.class_type_name);
  // §6.24.2: Register enum type info for $cast validation.
  if (!var.enum_type_name.empty() && var.dtype) {
    RegisterEnumForCast(var);
  }
  LowerVarAggregate(var);
}

// §10.9.2: Evaluate variable initializer with struct pattern awareness.
void Lowerer::LowerVarInit(const RtlirVariable& var, Variable* v,
                           uint32_t width) {
  auto* sinfo = ctx_.GetVariableStructType(var.name);
  bool named = var.init_expr->kind == ExprKind::kAssignmentPattern &&
               !var.init_expr->pattern_keys.empty();
  if (named && sinfo) {
    v->value = EvalStructPattern(var.init_expr, sinfo, ctx_, arena_);
    return;
  }
  auto val = EvalExpr(var.init_expr, ctx_, arena_);
  if (val.width != width && !var.is_real && !var.is_string)
    val = MakeLogic4VecVal(arena_, width, val.ToUint64());
  v->value = val;
}

// §6.24.2: Register enum type info and variable mapping for $cast.
void Lowerer::RegisterEnumForCast(const RtlirVariable& var) {
  ctx_.SetVariableEnumType(var.name, var.enum_type_name);
}

void Lowerer::RegisterEnumTypes(const RtlirModule* mod) {
  for (const auto& [name, members] : mod->enum_types) {
    if (ctx_.FindEnumType(name)) continue;
    EnumTypeInfo info;
    info.type_name = name;
    for (const auto& m : members) {
      info.members.push_back({m.name, static_cast<uint64_t>(m.value)});
    }
    ctx_.RegisterEnumType(name, info);
  }
}

// §8: Create ClassTypeInfo from a ClassDecl AST node.
void Lowerer::LowerClassDecl(const ClassDecl* cls) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  // §8.13: Wire parent linkage from base_class.
  if (!cls->base_class.empty())
    info->parent = ctx_.FindClassType(cls->base_class);
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

void Lowerer::LowerProcesses(const std::vector<RtlirProcess>& procs) {
  for (const auto& proc : procs) {
    if (proc.kind != RtlirProcessKind::kInitial) LowerProcess(proc);
  }
  for (const auto& proc : procs) {
    if (proc.kind == RtlirProcessKind::kInitial) LowerProcess(proc);
  }
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  // Create variables for resolved parameters (§6.20).
  for (const auto& p : mod->params) {
    // §6.20.7: track unbounded parameters for $isunbounded().
    if (p.is_unbounded) {
      ctx_.RegisterUnboundedParam(p.name);
      ctx_.CreateVariable(p.name, 32);
      continue;
    }
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
  // §6.24.2: Register enum types before variables so $cast can look them up.
  RegisterEnumTypes(mod);
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

  // §9.4.2: Always blocks first so they register sensitivity before
  // initial blocks trigger events.
  LowerProcesses(mod->processes);

  // Lower continuous assignments.
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca);
  }
}

// --- Process lowering ---

static void RegisterSensitivity(const RtlirProcess& proc, Process* p,
                                SimContext& ctx) {
  auto signals = CollectReadSignals(proc.body);
  for (const auto& name : signals) {
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
  DriverStrength ds{ParserStrToStrength(ca.drive_strength0),
                    ParserStrToStrength(ca.drive_strength1)};
  p->coro = MakeContAssignCoroutine(ca.lhs, ca.rhs, ds, ctx_, arena_).Release();

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
