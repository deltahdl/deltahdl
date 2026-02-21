#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/dpi.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include "simulation/vcd_writer.h"

namespace delta {

// --- PRNG system calls ---

static Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string_view name) {
  if (name == "$random") {
    return MakeLogic4VecVal(arena, 32, ctx.Random32());
  }
  if (name == "$urandom") {
    return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
  }
  if (name == "$urandom_range") {
    uint32_t max_val = 0;
    uint32_t min_val = 0;
    if (!expr->args.empty()) {
      max_val =
          static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    if (expr->args.size() > 1) {
      min_val =
          static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
    }
    return MakeLogic4VecVal(arena, 32, ctx.UrandomRange(min_val, max_val));
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// --- System call evaluation ---

// §21.2.1.6: Build %p format string for a tagged union variable.
static std::string BuildFormatP(const Expr* arg, SimContext& ctx) {
  if (arg->kind != ExprKind::kIdentifier) return "";
  auto tag = ctx.GetVariableTag(arg->text);
  if (tag.empty()) return "";
  auto* var = ctx.FindVariable(arg->text);
  uint64_t val = var ? var->value.ToUint64() : 0;
  return "'{" + std::string(tag) + ":" + std::to_string(val) + "}";
}

static void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  std::vector<std::string> p_fmts;
  for (size_t i = 0; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == 0 && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
      p_fmts.push_back(BuildFormatP(expr->args[i], ctx));
    }
  }
  std::string output = fmt.empty() ? "" : FormatDisplay(fmt, arg_vals, p_fmts);
  std::cout << output;
  if (expr->callee == "$display") std::cout << "\n";
}

static void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                             const char* prefix, std::ostream& os) {
  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  size_t start_idx = 0;

  if (std::string_view(prefix) == "FATAL" && !expr->args.empty()) {
    if (expr->args[0]->kind != ExprKind::kStringLiteral) {
      EvalExpr(expr->args[0], ctx, arena);
      start_idx = 1;
    }
  }

  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == start_idx && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string msg = fmt.empty() ? "" : FormatDisplay(fmt, arg_vals);
  os << prefix << ": " << msg << "\n";
}

static Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [expr, &ctx, &arena]() {
    ExecDisplayWrite(expr, ctx, arena);
    std::cout << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalVcdSysCall(SimContext& ctx, Arena& arena,
                                std::string_view name) {
  auto* vcd = ctx.GetVcdWriter();
  if (name == "$dumpvars" || name == "$dumpall") {
    if (vcd) vcd->DumpAllValues();
  } else if (name == "$dumpoff") {
    if (vcd) vcd->SetEnabled(false);
  } else if (name == "$dumpon") {
    if (vcd) vcd->SetEnabled(true);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool IsMathSysCall(std::string_view n) {
  return n == "$ln" || n == "$log10" || n == "$exp" || n == "$sqrt" ||
         n == "$pow" || n == "$floor" || n == "$ceil" || n == "$sin" ||
         n == "$cos" || n == "$tan" || n == "$asin" || n == "$acos" ||
         n == "$atan" || n == "$atan2" || n == "$hypot" || n == "$sinh" ||
         n == "$cosh" || n == "$tanh" || n == "$asinh" || n == "$acosh" ||
         n == "$atanh" || n == "$dist_uniform" || n == "$dist_normal" ||
         n == "$dist_exponential" || n == "$dist_poisson" ||
         n == "$dist_chi_square" || n == "$dist_t" || n == "$dist_erlang";
}

static bool IsExtFileIOSysCall(std::string_view n) {
  return n == "$fgets" || n == "$fgetc" || n == "$fflush" || n == "$feof" ||
         n == "$ferror" || n == "$fseek" || n == "$ftell" || n == "$rewind" ||
         n == "$ungetc" || n == "$fscanf" || n == "$fread";
}

static Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
                                 std::string_view name) {
  if (name == "$stime") {
    auto ticks = ctx.CurrentTime().ticks & 0xFFFFFFFF;
    return MakeLogic4VecVal(arena, 32, ticks);
  }
  return MakeLogic4VecVal(arena, 64, ctx.CurrentTime().ticks);
}

static Logic4Vec EvalSystemCommand(const Expr* expr, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto text = expr->args[0]->text;
  std::string cmd;
  if (text.size() >= 2 && text.front() == '"') {
    cmd = std::string(text.substr(1, text.size() - 2));
  } else {
    cmd = std::string(text);
  }
  int ret = std::system(cmd.c_str());
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ret));
}

static bool IsUtilitySysCall(std::string_view n) {
  return n == "$clog2" || n == "$bits" || n == "$unsigned" || n == "$signed" ||
         n == "$countones" || n == "$onehot" || n == "$onehot0" ||
         n == "$isunknown" || n == "$isunbounded" || n == "$cast" ||
         n == "$test$plusargs" || n == "$value$plusargs" || n == "$typename" ||
         n == "$sformatf" || n == "$itor" || n == "$rtoi" ||
         n == "$bitstoreal" || n == "$realtobits" || n == "$countbits" ||
         n == "$shortrealtobits" || n == "$bitstoshortreal";
}

static bool IsArrayQuerySysCall(std::string_view n) {
  return n == "$dimensions" || n == "$unpacked_dimensions" || n == "$left" ||
         n == "$right" || n == "$low" || n == "$high" || n == "$increment" ||
         n == "$size";
}

static bool IsVerifSysCall(std::string_view n) {
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" || n.starts_with("$assert") ||
         n.starts_with("$coverage") || n.starts_with("$q_") ||
         n.starts_with("$async$") || n.starts_with("$sync$");
}

static bool IsIOSysCall(std::string_view n) {
  return n == "$fopen" || n == "$fclose" || n == "$fwrite" ||
         n == "$fdisplay" || n == "$readmemh" || n == "$readmemb" ||
         n == "$writememh" || n == "$writememb" || n == "$sscanf";
}

static bool IsNoOpSysCall(std::string_view n) {
  return n == "$monitoron" || n == "$monitoroff" || n == "$printtimescale" ||
         n == "$timeformat";
}

static Logic4Vec EvalMiscSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$time" || name == "$stime" || name == "$realtime") {
    return EvalTimeSysCall(ctx, arena, name);
  }
  if (name == "$strobe" || name == "$monitor") {
    return EvalDeferredPrint(expr, ctx, arena);
  }
  if (IsNoOpSysCall(name)) return MakeLogic4VecVal(arena, 1, 0);
  if (name == "$system") return EvalSystemCommand(expr, arena);
  if (name == "$stacktrace") {
    std::cerr << "stacktrace not available\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name.starts_with("$dump")) return EvalVcdSysCall(ctx, arena, name);
  if (IsMathSysCall(name)) return EvalMathSysCall(expr, ctx, arena, name);
  if (IsUtilitySysCall(name)) return EvalUtilitySysCall(expr, ctx, arena, name);
  if (IsIOSysCall(name)) return EvalIOSysCall(expr, ctx, arena, name);
  if (IsExtFileIOSysCall(name))
    return EvalFileIOSysCall(expr, ctx, arena, name);
  if (IsArrayQuerySysCall(name))
    return EvalArrayQuerySysCall(expr, ctx, arena, name);
  if (IsVerifSysCall(name)) return EvalVerifSysCall(expr, ctx, arena, name);
  return EvalPrngCall(expr, ctx, arena, name);
}

static Logic4Vec EvalSeveritySysCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    ctx.RequestStop();
  } else if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
  } else if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", std::cout);
  } else if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", std::cout);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto name = expr->callee;

  if (name == "$display" || name == "$write") {
    ExecDisplayWrite(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$finish" || name == "$stop") {
    ctx.RequestStop();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$fatal" || name == "$error" || name == "$warning" ||
      name == "$info") {
    return EvalSeveritySysCall(expr, ctx, arena, name);
  }
  return EvalMiscSysCall(expr, ctx, arena, name);
}

// --- Function call evaluation ---

// §13.5.4: Resolve the call-site arg index for a given parameter index.
static int ResolveArgIndex(const ModuleItem* func, const Expr* expr,
                           size_t param_idx) {
  if (expr->arg_names.empty()) {
    return (param_idx < expr->args.size()) ? static_cast<int>(param_idx) : -1;
  }
  // §A.6.9: list_of_arguments allows positional args followed by named args.
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (param_idx < positional_count) {
    return static_cast<int>(param_idx);
  }
  auto param_name = func->func_args[param_idx].name;
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == param_name)
      return static_cast<int>(positional_count + j);
  }
  return -1;
}

// §13.5.2: Try to pass by reference. Returns true if aliased successfully.
static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  auto* target = ctx.FindVariable(call_arg->text);
  if (!target) return false;
  ctx.AliasLocalVariable(param_name, target);
  return true;
}

// §7.10.3: Try to bind a queue element (q[i]) by reference.
// Creates a local variable with the current value; records a QueueRefBinding
// for writeback on function return.
static bool TryBindQueueElementRef(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  auto* q = ctx.FindQueue(call_arg->base->text);
  if (!q || !call_arg->index) return false;
  auto idx = EvalExpr(call_arg->index, ctx, arena).ToUint64();
  if (idx >= q->elements.size()) return false;
  // §6.22.2: Width must match for ref binding (skip for implicit types).
  if (param.data_type.kind != DataTypeKind::kImplicit) {
    uint32_t param_width = EvalTypeWidth(param.data_type);
    if (param_width != q->elem_width) return false;
  }
  // Create a local variable initialized with the current element value.
  auto* var = ctx.CreateLocalVariable(param.name, q->elem_width);
  var->value = q->elements[idx];
  // Record binding for writeback: capture the element's unique ID.
  if (idx < q->element_ids.size()) {
    ctx.RecordQueueRef({q, q->element_ids[idx], var});
  }
  return true;
}

// §7.10.3: Write back queue ref bindings. For each binding, search for the
// captured element ID in the queue. If found, write back; otherwise the ref
// is outdated (§13.5.2) and the write is suppressed.
static void WritebackQueueRefs(SimContext& ctx) {
  auto bindings = ctx.PopQueueRefFrame();
  for (const auto& b : bindings) {
    auto& ids = b.queue->element_ids;
    auto it = std::find(ids.begin(), ids.end(), b.element_id);
    if (it == ids.end()) continue;
    auto pos = static_cast<size_t>(it - ids.begin());
    if (pos < b.queue->elements.size()) {
      b.queue->elements[pos] = b.local_var->value;
    }
  }
}

// §13.5.3: Evaluate call-site arg, use default value, or X.
static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0) {
    return EvalExpr(expr->args[static_cast<size_t>(arg_index)], ctx, arena);
  }
  if (param.default_value) return EvalExpr(param.default_value, ctx, arena);
  return MakeLogic4Vec(arena, 32);
}

// §7.8: Copy associative array data when passing to a subroutine.
static bool TryBindAssocArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  auto* src = ctx.FindAssocArray(call_arg->text);
  if (!src) return false;
  auto* dst =
      ctx.CreateAssocArray(param_name, src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;
  return true;
}

// §13.4: Copy array elements when passing an unpacked array to a subroutine.
static bool TryBindArrayArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, param_name, ctx)) return true;
  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;
  ctx.RegisterArray(param_name, *info);
  for (uint32_t j = 0; j < info->size; ++j) {
    uint32_t idx = info->lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(param_name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info->elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = val;
  }
  return true;
}

// §13.5: Bind function arguments with named, default, and ref support.
static void BindFunctionArgs(const ModuleItem* func, const Expr* expr,
                             SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    auto dir = func->func_args[i].direction;
    if (dir == Direction::kRef) {
      if (TryBindRefArg(expr, ai, func->func_args[i].name, ctx)) continue;
      if (TryBindQueueElementRef(expr, ai, func->func_args[i], ctx, arena))
        continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)],
                                   func->func_args[i].name, ctx, arena)) {
      continue;
    }
    auto val = ResolveArgValue(func->func_args[i], expr, ai, ctx, arena);
    auto* var = ctx.CreateLocalVariable(func->func_args[i].name, val.width);
    var->value = val;
  }
}

// Write back output/inout args, respecting named binding (§13.5.4).
static void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                                SimContext& ctx) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    auto* local = ctx.FindLocalVariable(func->func_args[i].name);
    if (!local) continue;
    int ai = ResolveArgIndex(func, expr, i);
    if (ai < 0) continue;
    auto* call_arg = expr->args[static_cast<size_t>(ai)];
    if (call_arg->kind != ExprKind::kIdentifier) continue;
    auto* target = ctx.FindVariable(call_arg->text);
    if (target) target->value = local->value;
  }
}

// §13: Handle blocking assignment inside function/task body.
// Write to an indexed LHS inside a function body (array/assoc element).
static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (aa && lhs->index) {
    if (aa->is_string_key) {
      aa->str_data[FormatValueAsString(EvalExpr(lhs->index, ctx, arena))] = val;
    } else {
      auto key =
          static_cast<int64_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
      aa->int_data[key] = val;
    }
    return;
  }
  auto idx = EvalExpr(lhs->index, ctx, arena).ToUint64();
  auto name = std::string(lhs->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(name);
  if (elem) elem->value = val;
}

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) {
      var->value = val;
      return;
    }
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->text), val);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(stmt->lhs, val, ctx, arena);
  }
}

// Forward declarations for mutually recursive function body execution.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                         Arena& arena);
static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                          Arena& arena);

static bool ExecFuncIf(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                       Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  bool taken = cond.ToUint64() != 0;
  if (taken) return ExecFuncStmt(stmt->then_branch, ret_var, ctx, arena);
  if (stmt->else_branch) {
    return ExecFuncStmt(stmt->else_branch, ret_var, ctx, arena);
  }
  return false;
}

static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                          Arena& arena) {
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, ret_var, ctx, arena)) return true;
  }
  return false;
}

// §13.8: For-loop execution inside function bodies.
static bool ExecFuncFor(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                        Arena& arena) {
  if (stmt->for_init_type.kind != DataTypeKind::kImplicit && stmt->for_init &&
      stmt->for_init->lhs &&
      stmt->for_init->lhs->kind == ExprKind::kIdentifier) {
    uint32_t w = EvalTypeWidth(stmt->for_init_type);
    if (w == 0) w = 32;
    auto* v = ctx.CreateLocalVariable(stmt->for_init->lhs->text, w);
    if (stmt->for_init->rhs)
      v->value = EvalExpr(stmt->for_init->rhs, ctx, arena);
  } else if (stmt->for_init) {
    ExecFuncStmt(stmt->for_init, ret_var, ctx, arena);
  }
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, ctx, arena).ToUint64() != 0) {
    if (stmt->for_body && ExecFuncStmt(stmt->for_body, ret_var, ctx, arena))
      return true;
    if (stmt->for_step) ExecFuncStmt(stmt->for_step, ret_var, ctx, arena);
  }
  return false;
}

// Execute a single statement in a function body; returns true on 'return'.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                         Arena& arena) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ret_var->value = EvalExpr(stmt->expr, ctx, arena);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, ctx, arena);
      return false;
    case StmtKind::kExprStmt:
      EvalExpr(stmt->expr, ctx, arena);
      return false;
    case StmtKind::kVarDecl: {
      // §13.3.1: Static variables persist across calls — skip re-init.
      if (ctx.FindLocalVariable(stmt->var_name)) return false;
      uint32_t w = EvalTypeWidth(stmt->var_decl_type);
      if (w == 0) w = 32;
      auto* v = ctx.CreateLocalVariable(stmt->var_name, w);
      if (stmt->var_init) v->value = EvalExpr(stmt->var_init, ctx, arena);
      return false;
    }
    case StmtKind::kIf:
      return ExecFuncIf(stmt, ret_var, ctx, arena);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, ret_var, ctx, arena);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, ret_var, ctx, arena);
    default:
      return false;
  }
}

static void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                             SimContext& ctx, Arena& arena) {
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, ret_var, ctx, arena)) return;
  }
}

// §8.7: Allocate a new class object, execute constructor, return handle.
Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;
  for (const auto& prop : info->properties) {
    obj->properties[std::string(prop.name)] =
        MakeLogic4VecVal(arena, prop.width, 0);
  }
  auto handle = ctx.AllocateClassObject(obj);
  auto it = info->methods.find("new");
  if (it != info->methods.end() && it->second) {
    ctx.PushScope();
    ctx.PushThis(obj);
    if (new_expr) BindFunctionArgs(it->second, new_expr, ctx, arena);
    Variable dummy;
    ExecFunctionBody(it->second, &dummy, ctx, arena);
    ctx.PopThis();
    ctx.PopScope();
  }
  return MakeLogic4VecVal(arena, 64, handle);
}

static Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiContext();
  if (!dpi || !dpi->HasImport(expr->callee)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::vector<uint64_t> args;
  args.reserve(expr->args.size());
  for (auto* arg : expr->args) {
    args.push_back(EvalExpr(arg, ctx, arena).ToUint64());
  }
  uint64_t result = dpi->Call(expr->callee, args);
  return MakeLogic4VecVal(arena, 32, result);
}

// §8: Dispatch a method call on a class object instance.
static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return false;
  auto* obj = ctx.GetClassObject(handle);
  if (!obj) return false;
  auto* method = obj->ResolveMethod(parts.method_name);
  if (!method) return false;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  ctx.PushScope();
  ctx.PushThis(obj);
  ctx.PushQueueRefFrame();
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) ret_var = ctx.CreateLocalVariable(method->name, 32);
  ExecFunctionBody(method, ret_var, ctx, arena);
  WritebackOutputArgs(method, expr, ctx);
  WritebackQueueRefs(ctx);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
  ctx.PopThis();
  ctx.PopScope();
  return true;
}

// §13.8: Bind class parameters from specialization values into the scope.
static void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                            SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  for (size_t i = 0; i < params.size(); ++i) {
    Logic4Vec val;
    if (i < values.size()) {
      val = EvalExpr(values[i], ctx, arena);
    } else if (params[i].second) {
      val = EvalExpr(params[i].second, ctx, arena);
    } else {
      val = MakeLogic4VecVal(arena, 32, 0);
    }
    auto* v = ctx.CreateLocalVariable(params[i].first, val.width);
    v->value = val;
  }
}

// §13.8: Dispatch a parameterized class scope call — C#(N)::method(args).
static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->elements.empty()) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;

  auto* cls = ctx.FindClassType(access->lhs->text);
  if (!cls) return false;
  auto it = cls->methods.find(std::string(access->rhs->text));
  if (it == cls->methods.end()) return false;
  auto* method = it->second;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);

  ctx.PushScope();
  BindClassParams(cls, access->lhs, ctx, arena);
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) ret_var = ctx.CreateLocalVariable(method->name, 32);
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
  ctx.PopScope();
  return true;
}

// Try dispatching to built-in type methods (enum, string, array, queue).
static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

// §11.12: Guard against recursive let expansion.
static thread_local std::unordered_set<std::string_view> expanding_lets;

// §11.12/§F.4: Bind let formal arguments to actual values in a new scope.
static void BindLetArgs(ModuleItem* decl, const Expr* call, SimContext& ctx,
                        Arena& arena) {
  auto& formals = decl->func_args;
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val;
    if (i < call->args.size()) {
      val = EvalExpr(call->args[i], ctx, arena);
    } else if (formals[i].default_value) {
      val = EvalExpr(formals[i].default_value, ctx, arena);
    } else {
      val = MakeLogic4Vec(arena, 32);
    }
    auto* var = ctx.CreateLocalVariable(formals[i].name, val.width);
    var->value = val;
  }
}

// §11.12/§F.4: Expand a let declaration by binding args and evaluating body.
static Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call,
                                  SimContext& ctx, Arena& arena) {
  // §11.12: Recursive let instantiation is not permitted.
  if (expanding_lets.count(decl->name)) return MakeAllX(arena, 32);
  expanding_lets.insert(decl->name);
  ctx.PushScope();
  BindLetArgs(decl, call, ctx, arena);
  auto result = EvalExpr(decl->init_expr, ctx, arena);
  ctx.PopScope();
  expanding_lets.erase(decl->name);
  return result;
}

// Try dispatching to method calls (builtin, class, parameterized scope)
// or let expansion. Returns true if the call was handled.
static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  auto* let_decl = ctx.FindLetDecl(expr->callee);
  if (let_decl) {
    out = EvalLetExpansion(let_decl, expr, ctx, arena);
    return true;
  }
  return false;
}

// §13: Dispatch function calls with lifetime and void support.
Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryDispatchMethodOrLet(expr, ctx, arena, result)) return result;

  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  // §13.3.1: Static functions reuse their variable frame across calls.
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }

  ctx.PushQueueRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);

  // §13.4.1: Void functions have no implicit return variable.
  // For static functions, reuse the existing return variable if present.
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    ret_var = existing ? existing : ctx.CreateLocalVariable(func->name, 32);
  }

  ExecFunctionBody(func, ret_var, ctx, arena);
  WritebackOutputArgs(func, expr, ctx);
  WritebackQueueRefs(ctx);
  result = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  return result;
}

// §13: Set up task call scope for coroutine-based execution.
const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;
  // §A.6.9 footnote 42: tf_call without parentheses (bare identifier).
  if (expr->kind == ExprKind::kIdentifier) {
    auto* func = ctx.FindFunction(expr->text);
    if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;
    ctx.PushScope();
    ctx.PushQueueRefFrame();
    return func;
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  auto* func = ctx.FindFunction(expr->callee);
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;
  ctx.PushScope();
  ctx.PushQueueRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr,
                      SimContext& ctx) {
  WritebackOutputArgs(func, expr, ctx);
  WritebackQueueRefs(ctx);
  ctx.PopScope();
}

// §6.21: Reject ref arguments in static subroutines.
void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  bool is_static = func->is_static && !func->is_automatic;
  if (!is_static) return;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error({}, "ref argument '" + std::string(arg.name) +
                         "' not allowed in static subroutine '" +
                         std::string(func->name) + "'");
    }
  }
}

}  // namespace delta
