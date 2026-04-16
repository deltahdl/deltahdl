#include "simulator/lowerer.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

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
    co_await EventAwaiter{ctx, sens, arena};
    // §12.4.2.1: Flush pending violation reports on process re-trigger.
    ctx.FlushPendingViolations();
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
    // §12.4.2.1: Flush pending violation reports on process re-trigger.
    ctx.FlushPendingViolations();
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

// §10.3.3: Bit-exact comparison of two Logic4Vec values.
static bool Logic4VecEqual(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

// §10.3.3: Check if all bits are high-Z (aval=0, bval=1 for each word).
static bool IsAllHighZ(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0 || v.words[i].bval == 0) return false;
  }
  return v.nwords > 0;
}

// §10.3.3: Evaluated delay values for a continuous assignment.
struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

// §10.3.3: Delay expression AST nodes for a continuous assignment.
struct ContAssignDelayExprs {
  const Expr* rise = nullptr;
  const Expr* fall = nullptr;
  const Expr* decay = nullptr;
};

// §10.3.3: Grouped parameters for a continuous assignment coroutine.
struct ContAssignParams {
  const Expr* lhs;
  const Expr* rhs;
  DriverStrength ds;
  ContAssignDelayExprs delays;
  uint32_t width = 0;
};

// §10.3.3: Select the appropriate delay for a continuous assignment based on
// the transition from old_val to new_val.
static uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                                      const Logic4Vec& new_val,
                                      const ContAssignDelays& d,
                                      uint32_t width) {
  if (!d.has_fall) return d.rise;  // Single delay for all transitions.

  bool new_is_z = IsAllHighZ(new_val);
  if (new_is_z) {
    if (d.has_decay) return d.decay;
    return std::min(d.rise, d.fall);
  }

  if (width <= 1) {
    // Scalar net: gate delay rules (§28.16).
    bool new_has_x = HasUnknownBits(new_val);
    if (new_has_x) {
      uint64_t m = std::min(d.rise, d.fall);
      if (d.has_decay) m = std::min(m, d.decay);
      return m;
    }
    if (HasUnknownBits(old_val) || IsAllHighZ(old_val)) {
      return std::min(d.rise, d.fall);
    }
    uint64_t nv = new_val.ToUint64();
    uint64_t ov = old_val.ToUint64();
    if (nv > ov) return d.rise;
    if (nv < ov) return d.fall;
    return d.rise;
  }

  // Vector net: §10.3.3 rules.
  // Nonzero-to-zero uses fall; all other transitions use rise.
  if (!HasUnknownBits(new_val) && new_val.ToUint64() == 0 &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      old_val.ToUint64() != 0) {
    return d.fall;
  }
  return d.rise;
}

static SimCoroutine MakeContAssignCoroutine(ContAssignParams params,
                                            SimContext& ctx, Arena& arena) {
  if (!params.lhs || params.lhs->kind != ExprKind::kIdentifier) co_return;

  // §10.3: Collect RHS read signals for re-evaluation sensitivity.
  std::unordered_set<std::string> read_strs;
  CollectExprReads(params.rhs, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());

  // Track the net driver index so updates replace rather than append.
  auto* net = ctx.FindNet(params.lhs->text);
  size_t driver_idx = net ? net->drivers.size() : 0;
  bool first = true;

  while (!ctx.StopRequested()) {
    auto val = EvalExpr(params.rhs, ctx, arena, params.width);

    // §10.3.3: Apply continuous assignment delay with inertial semantics.
    if (params.delays.rise) {
      ContAssignDelays d;
      d.rise = EvalExpr(params.delays.rise, ctx, arena).ToUint64();
      d.fall = params.delays.fall
                   ? EvalExpr(params.delays.fall, ctx, arena).ToUint64()
                   : 0;
      d.decay = params.delays.decay
                    ? EvalExpr(params.delays.decay, ctx, arena).ToUint64()
                    : 0;
      d.has_fall = params.delays.fall != nullptr;
      d.has_decay = params.delays.decay != nullptr;

      Logic4Vec old_val = MakeLogic4VecVal(arena, 1, 0);
      auto* var = ctx.FindVariable(params.lhs->text);
      if (var)
        old_val = var->value;
      else if (net && net->resolved)
        old_val = net->resolved->value;

      uint64_t ticks = SelectContAssignDelay(old_val, val, d, params.width);
      if (ticks > 0 && !read_vars.empty()) {
        // §10.3.3: Inertial delay — if the RHS changes before the delay
        // expires, cancel the pending assignment and reschedule.
        SimTime target = ctx.CurrentTime() + SimTime{ticks};
        while (true) {
          uint64_t remaining = (target.ticks > ctx.CurrentTime().ticks)
                                   ? (target.ticks - ctx.CurrentTime().ticks)
                                   : 0;
          if (remaining == 0) break;
          bool expired =
              co_await InertialDelayAwaiter{ctx, remaining, read_vars};
          if (expired) break;
          auto new_val = EvalExpr(params.rhs, ctx, arena, params.width);
          if (!Logic4VecEqual(new_val, val)) {
            val = new_val;
            ticks = SelectContAssignDelay(old_val, val, d, params.width);
            target = ctx.CurrentTime() + SimTime{ticks};
          }
        }
      } else if (ticks > 0) {
        co_await DelayAwaiter{ctx, ticks};
      }
    }

    // §10.3.4: If target is a net, add/update as a strength-aware driver.
    if (net) {
      if (first) {
        net->drivers.push_back(val);
        net->driver_strengths.push_back(params.ds);
      } else {
        net->drivers[driver_idx] = val;
        net->driver_strengths[driver_idx] = params.ds;
      }
      net->Resolve(arena);
    } else {
      auto* var = ctx.FindVariable(params.lhs->text);
      if (var) {
        var->value = ResizeToWidth(val, var->value.width, arena);
        var->NotifyWatchers();
      }
    }

    first = false;

    // §10.3: Re-evaluate whenever the RHS changes.
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

// --- Schedule helper ---

static void ScheduleProcess(Process* proc, SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* event = sched.GetEventPool().Acquire();
  event->callback = [proc, &ctx]() {
    ctx.SetCurrentProcess(proc);
    proc->Resume();
  };
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

// §10.9.1: Check if a pattern key is a type keyword (int, logic, etc.).
static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" ||
         key == "time" || key == "realtime" || key == "string";
}

// §10.9.1: Check if a type keyword string matches a DataTypeKind.
static bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kInt: return key == "int";
    case DataTypeKind::kInteger: return key == "integer";
    case DataTypeKind::kLogic: return key == "logic";
    case DataTypeKind::kReg: return key == "reg";
    case DataTypeKind::kByte: return key == "byte";
    case DataTypeKind::kShortint: return key == "shortint";
    case DataTypeKind::kLongint: return key == "longint";
    case DataTypeKind::kBit: return key == "bit";
    case DataTypeKind::kReal: return key == "real";
    case DataTypeKind::kShortreal: return key == "shortreal";
    case DataTypeKind::kTime: return key == "time";
    case DataTypeKind::kRealtime: return key == "realtime";
    case DataTypeKind::kString: return key == "string";
    default: return false;
  }
}

// §10.9.1: Initialize array element from named pattern (index/type/default keys).
static void InitArrayFromNamed(const RtlirVariable& var, uint32_t idx,
                               Variable* elem, SimContext& ctx, Arena& arena) {
  auto* init = var.init_expr;
  // Pass 1: explicit index key.
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto& key = init->pattern_keys[i];
    if (key == "default" || IsTypeKeyword(key)) continue;
    auto key_idx = static_cast<uint32_t>(std::stoul(std::string(key)));
    if (key_idx == idx) {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return;
    }
  }
  // Pass 2: type key — matches if element type matches the keyword.
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto& key = init->pattern_keys[i];
    if (IsTypeKeyword(key) &&
        TypeKeyMatchesKind(key, var.elem_type_kind)) {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return;
    }
  }
  // Pass 3: default key.
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
  info.is_4state = var.is_4state;
  info.elem_type_kind = var.elem_type_kind;
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
                                     var.assoc_index_width,
                                     var.is_wildcard_index,
                                     var.is_4state);
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
  // §6.8 Table 6-7: 2-state types default to 0, real/shortreal to 0.0.
  if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle) {
    v->value = MakeLogic4VecVal(arena_, width, 0);
  }
  // §6.14: chandle defaults to null (0), not X.
  if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
  v->is_4state = var.is_4state;
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
  // §15.5.5.2: Event initialized to null breaks the synchronization queue.
  if (var.is_event && var.init_expr->kind == ExprKind::kIdentifier &&
      var.init_expr->text == "null") {
    v->is_null_event = true;
    return;
  }
  // §15.5.5: Event initialization from another event shares the handle.
  if (var.is_event && var.init_expr->kind == ExprKind::kIdentifier) {
    auto* target = ctx_.FindVariable(var.init_expr->text);
    if (target && target->is_event) {
      ctx_.AliasVariable(var.name, var.init_expr->text);
      return;
    }
  }
  auto* sinfo = ctx_.GetVariableStructType(var.name);
  // §A.6.7.1: Unwrap typed assignment pattern expression (kCast wrapping
  // pattern).
  auto* init = var.init_expr;
  if (init->kind == ExprKind::kCast && init->lhs &&
      init->lhs->kind == ExprKind::kAssignmentPattern)
    init = init->lhs;
  bool named =
      init->kind == ExprKind::kAssignmentPattern && !init->pattern_keys.empty();
  if (named && sinfo) {
    v->value = EvalStructPattern(init, sinfo, ctx_, arena_);
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

// §8.22: Add or update a single vtable entry for a virtual method.
static void AddOrUpdateVTableEntry(ClassTypeInfo* info,
                                   const ClassMember* member) {
  int idx = info->FindVTableIndex(member->method->name);
  auto* method_ptr = member->is_pure_virtual ? nullptr : member->method;
  if (idx >= 0) {
    info->vtable[static_cast<size_t>(idx)].method = method_ptr;
    info->vtable[static_cast<size_t>(idx)].owner = info;
  } else {
    info->vtable.push_back({member->method->name, method_ptr, info});
  }
}

// §8.22: Build vtable for polymorphic dispatch from class members.
static void BuildVTable(ClassTypeInfo* info, const ClassDecl* cls) {
  if (info->parent) info->vtable = info->parent->vtable;
  for (const auto* iface : info->extended_interfaces) {
    if (!iface) continue;
    for (const auto& entry : iface->vtable) {
      bool found = false;
      for (const auto& existing : info->vtable) {
        if (existing.method_name == entry.method_name) { found = true; break; }
      }
      if (!found) info->vtable.push_back(entry);
    }
  }
  for (auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kMethod || !member->method) continue;
    // §8.20: A virtual method may override a non-virtual method, making it
    // virtual from that point in the hierarchy. Also include pure_virtual
    // and methods with ':extends' (which implies virtuality per §8.20).
    if (!member->is_virtual && !member->is_pure_virtual &&
        !(member->method && member->method->is_method_extends))
      continue;
    AddOrUpdateVTableEntry(info, member);
  }
}

// §8.9: Initialize static properties on the class type.
static void InitStaticProperties(ClassTypeInfo* info, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& p : info->properties) {
    if (p.is_static) {
      if (p.init_expr) {
        info->static_properties[std::string(p.name)] =
            EvalExpr(p.init_expr, ctx, arena);
      } else {
        info->static_properties[std::string(p.name)] =
            MakeLogic4VecVal(arena, p.width, 0);
      }
    }
  }
}

// §8: Create ClassTypeInfo from a ClassDecl AST node.
void Lowerer::LowerClassDecl(const ClassDecl* cls) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  info->is_interface = cls->is_interface;
  // §8.13: Wire parent linkage from base_class.
  if (!cls->base_class.empty())
    info->parent = ctx_.FindClassType(cls->base_class);
  for (const auto& ref : cls->extends_interfaces) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (const auto& ref : cls->implements_types) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      uint32_t w = EvalTypeWidth(member->data_type, {});
      if (w == 0) w = 32;
      info->properties.push_back({member->name, w, member->is_static,
                                  member->is_local, member->is_protected,
                                  member->is_const, member->init_expr});
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
  BuildVTable(info, cls);
  InitStaticProperties(info, ctx_, arena_);
  // §8.23: Register class parameters as static properties so they are
  // accessible via the scope resolution operator (ClassName::PARAM).
  for (const auto& [pname, pexpr] : cls->params) {
    info->properties.push_back({pname, 32, false});
    if (pexpr) {
      info->static_properties[std::string(pname)] =
          EvalExpr(pexpr, ctx_, arena_);
    } else {
      info->static_properties[std::string(pname)] =
          MakeLogic4VecVal(arena_, 32, 0);
    }
  }
  // §8.5: Collect enum members declared inside the class.
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kTypedef || !member->typedef_item)
      continue;
    const auto& enum_members = member->typedef_item->typedef_type.enum_members;
    int64_t next_val = 0;
    for (const auto& em : enum_members) {
      if (em.value) next_val = static_cast<int64_t>(em.value->int_val);
      info->enum_members[std::string(em.name)] = static_cast<uint64_t>(next_val);
      ++next_val;
    }
  }
  // §8.26.3: Interface class params and typedefs are inherited through extends.
  if (cls->is_interface) {
    auto inherit_from = [&](const ClassTypeInfo* src) {
      for (const auto& [k, v] : src->static_properties) {
        if (info->static_properties.find(k) == info->static_properties.end())
          info->static_properties[k] = v;
      }
      for (const auto& [k, v] : src->enum_members) {
        if (info->enum_members.find(k) == info->enum_members.end())
          info->enum_members[k] = v;
      }
    };
    if (info->parent && info->parent->is_interface)
      inherit_from(info->parent);
    for (const auto* iface : info->extended_interfaces)
      inherit_from(iface);
  }
  ctx_.RegisterClassType(cls->name, info);
  // §8.23: Register nested class declarations with scope-qualified names
  // (e.g., Outer::Inner) so they can be accessed via the :: operator.
  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class) {
      auto qualified =
          std::string(cls->name) + "::" + std::string(member->nested_class->name);
      auto* nested_info = arena_.Create<ClassTypeInfo>();
      nested_info->name =
          *arena_.Create<std::string>(std::move(qualified));
      nested_info->decl = member->nested_class;
      nested_info->is_abstract = member->nested_class->is_virtual;
      nested_info->is_interface = member->nested_class->is_interface;
      if (!member->nested_class->base_class.empty())
        nested_info->parent = ctx_.FindClassType(member->nested_class->base_class);
      for (auto* m : member->nested_class->members) {
        if (m->kind == ClassMemberKind::kProperty) {
          uint32_t w = EvalTypeWidth(m->data_type, {});
          if (w == 0) w = 32;
          nested_info->properties.push_back({m->name, w, m->is_static,
                                             m->is_local, m->is_protected,
                                             m->is_const, m->init_expr});
        } else if (m->kind == ClassMemberKind::kMethod && m->method) {
          nested_info->methods[std::string(m->method->name)] = m->method;
        }
      }
      InitStaticProperties(nested_info, ctx_, arena_);
      ctx_.RegisterClassType(nested_info->name, nested_info);
    }
  }
}

void Lowerer::LowerProcesses(const std::vector<RtlirProcess>& procs) {
  for (const auto& proc : procs) {
    if (proc.kind != RtlirProcessKind::kInitial) LowerProcess(proc);
  }
  for (const auto& proc : procs) {
    if (proc.kind == RtlirProcessKind::kInitial) LowerProcess(proc);
  }
}

// §6.20: Create variables for resolved parameters.
void Lowerer::LowerParams(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
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
}

// §10.11: Lower net aliases.
void Lowerer::LowerAliases(const RtlirModule* mod) {
  for (const auto& alias : mod->aliases) {
    if (alias.nets.size() < 2) continue;
    std::string_view primary;
    for (auto* net : alias.nets) {
      if (net->kind != ExprKind::kIdentifier) continue;
      if (primary.empty()) {
        primary = net->text;
      } else {
        ctx_.AliasVariable(net->text, primary);
      }
    }
  }
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  LowerParams(mod);
  for (const auto& net : mod->nets) {
    ctx_.CreateNet(net.name, net.net_type, net.width, net.charge_strength,
                   net.decay_ticks, net.is_user_nettype, net.resolve_func);
  }
  RegisterEnumTypes(mod);
  for (const auto& var : mod->variables) LowerVar(var);
  for (const auto& port : mod->ports) {
    if (!ctx_.FindVariable(port.name)) {
      auto* v = ctx_.CreateVariable(port.name, port.width);
      if (port.is_signed) v->is_signed = true;
    }
  }
  for (auto* func : mod->function_decls) {
    ctx_.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }
  for (auto* seq_decl : mod->sequence_decls) {
    ctx_.RegisterSequenceDecl(seq_decl->name, seq_decl);
    // §9.4.4: Create the __seq_ endpoint event variable so that
    // wait(seq.triggered) and @(seq) can reference it immediately.
    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx_.FindVariable(ep_name)) {
      auto* ep_var = ctx_.CreateVariable(ep_name, 1);
      ep_var->is_event = true;
    }
  }
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }
  {
    // §9.7: Register synthetic ClassTypeInfo for the built-in process class.
    auto* proc_type = arena_.Create<ClassTypeInfo>();
    proc_type->name = "process";
    proc_type->enum_members["FINISHED"] = 0;
    proc_type->enum_members["RUNNING"] = 1;
    proc_type->enum_members["WAITING"] = 2;
    proc_type->enum_members["SUSPENDED"] = 3;
    proc_type->enum_members["KILLED"] = 4;
    ctx_.RegisterClassType("process", proc_type);
  }
  LowerAliases(mod);
  LowerProcesses(mod->processes);
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca);
  }
  // §23.6: Recursively lower child module instances for hierarchical access.
  LowerChildModules(mod);
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
  p->inst_prefix = inst_prefix_;

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kAlways:
      p->kind = ProcessKind::kAlways;
      if (!proc.sensitivity.empty() || proc.is_star_sensitivity) {
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

  ScheduleProcess(p, ctx_);
}

// --- Continuous assignment lowering ---

void Lowerer::LowerContAssign(const RtlirContAssign& ca) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  ContAssignParams cap;
  cap.lhs = ca.lhs;
  cap.rhs = ca.rhs;
  cap.ds = {ParserStrToStrength(ca.drive_strength0),
            ParserStrToStrength(ca.drive_strength1)};
  cap.delays = {ca.delay, ca.delay_fall, ca.delay_decay};
  cap.width = ca.width;
  p->coro = MakeContAssignCoroutine(cap, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}

// --- §23.6: Recursive child module lowering for hierarchical access ---

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto saved_prefix = inst_prefix_;
    inst_prefix_ = inst_prefix_ + std::string(child.inst_name) + ".";

    // Create child variables with hierarchical prefix.
    for (const auto& var : child.resolved->variables) {
      auto* name =
          arena_.Create<std::string>(inst_prefix_ + std::string(var.name));
      uint32_t width = var.class_type_name.empty() ? var.width : 64;
      if (var.is_real && width < 64) width = 64;
      auto* v = ctx_.CreateVariable(*name, width);
      if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle)
        v->value = MakeLogic4VecVal(arena_, width, 0);
      if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
      v->is_4state = var.is_4state;
      if (var.is_event) v->is_event = true;
      if (var.is_signed) v->is_signed = true;
    }

    // Create child ports with hierarchical prefix.
    for (const auto& port : child.resolved->ports) {
      auto* name =
          arena_.Create<std::string>(inst_prefix_ + std::string(port.name));
      if (!ctx_.FindVariable(*name)) {
        auto* v = ctx_.CreateVariable(*name, port.width);
        if (port.is_signed) v->is_signed = true;
      }
    }

    // Lower child processes (inst_prefix_ is set on each Process).
    LowerProcesses(child.resolved->processes);

    // Recurse into grandchildren.
    LowerChildModules(child.resolved);

    inst_prefix_ = saved_prefix;
  }
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
  // §11.12: Register CU-scope let declarations.
  for (auto* let_decl : design->cu_let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }
  // §8.24: Link out-of-block method bodies to their class types.
  for (auto* item : design->cu_function_decls) {
    if (item->method_class.empty()) continue;
    auto* cls = ctx_.FindClassType(item->method_class);
    if (!cls) continue;
    std::string name(item->name);
    cls->methods[name] = item;
  }
}

}  // namespace delta
