#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/dpi.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

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
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  return true;
}

// §13.4: Copy array elements when passing an unpacked array to a subroutine.
// §7.7: Runtime size check when fixed-size formal receives dynamic/queue actual.
static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx)) return true;
  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;

  // §7.7: Fixed-size formal receiving dynamic/queue actual requires runtime
  // size check.
  if (!formal.unpacked_dims.empty() && formal.unpacked_dims[0] != nullptr &&
      (info->is_dynamic || info->is_queue)) {
    auto formal_size = EvalExpr(formal.unpacked_dims[0], ctx, arena).ToUint64();
    if (info->size != formal_size) {
      ctx.GetDiag().Error(
          {}, "array size mismatch: formal expects " +
                  std::to_string(formal_size) + " elements, actual has " +
                  std::to_string(info->size));
      return true;
    }
  }

  ctx.RegisterArray(formal.name, *info);
  for (uint32_t j = 0; j < info->size; ++j) {
    uint32_t idx = info->lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
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
                                   func->func_args[i], ctx, arena)) {
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
    return;
  }
  // §8.11: this.property = val
  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "this" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->rhs->text), val);
    return;
  }
  // §8.15: super.property = val
  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "super" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(stmt->lhs->rhs->text),
                               self->type->parent, val);
    }
  }
}

// Forward declarations for mutually recursive function body execution.
// func_name is passed through for §13.4.2 mixed-lifetime local variable
// support.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
                         Arena& arena);
static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena);

static bool ExecFuncIf(const Stmt* stmt, Variable* ret_var,
                       std::string_view func_name, SimContext& ctx,
                       Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  bool taken = cond.ToUint64() != 0;
  if (taken)
    return ExecFuncStmt(stmt->then_branch, ret_var, func_name, ctx, arena);
  if (stmt->else_branch) {
    return ExecFuncStmt(stmt->else_branch, ret_var, func_name, ctx, arena);
  }
  return false;
}

static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena) {
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, ret_var, func_name, ctx, arena)) return true;
  }
  return false;
}

// §13.8: For-loop execution inside function bodies.
static bool ExecFuncFor(const Stmt* stmt, Variable* ret_var,
                        std::string_view func_name, SimContext& ctx,
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
    ExecFuncStmt(stmt->for_init, ret_var, func_name, ctx, arena);
  }
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, ctx, arena).ToUint64() != 0) {
    if (stmt->for_body &&
        ExecFuncStmt(stmt->for_body, ret_var, func_name, ctx, arena))
      return true;
    if (stmt->for_step)
      ExecFuncStmt(stmt->for_step, ret_var, func_name, ctx, arena);
  }
  return false;
}

// §13.4.2: Create or reinitialize a local variable with given width and init.
static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  uint32_t w = EvalTypeWidth(type);
  if (w == 0) w = 32;
  auto* v = ctx.CreateLocalVariable(name, w);
  if (init) v->value = EvalExpr(init, ctx, arena);
  return v;
}

// §13.4.2: Handle automatic var in static function.
static void ExecFuncVarDeclAutomatic(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

// §13.4.2: Handle static var in automatic function.
static void ExecFuncVarDeclStatic(const Stmt* stmt, std::string_view func_name,
                                  SimContext& ctx, Arena& arena) {
  auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
  if (existing) {
    ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, ctx, arena);
  ctx.SaveStaticFuncVar(func_name, stmt->var_name, v);
}

// §13.3.1/§13.4.2: Handle var declaration inside function body.
static void ExecFuncVarDecl(const Stmt* stmt, std::string_view func_name,
                            SimContext& ctx, Arena& arena) {
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, ctx, arena);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, func_name, ctx, arena);
    return;
  }
  if (ctx.FindLocalVariable(stmt->var_name)) return;
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

static bool ExecFuncForeach(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  if (!stmt->expr) return false;
  uint32_t size = 0;
  if (stmt->expr->kind == ExprKind::kIdentifier) {
    auto* info = ctx.FindArrayInfo(stmt->expr->text);
    if (info) {
      size = info->size;
    } else {
      auto* var = ctx.FindVariable(stmt->expr->text);
      if (var) size = var->value.width;
    }
  }
  if (size == 0) return false;

  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size; ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(arena, 32, i);
    }
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      ctx.PopScope();
      return true;
    }
  }

  ctx.PopScope();
  return false;
}

// Execute a single statement in a function body; returns true on 'return'.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
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
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, func_name, ctx, arena);
      return false;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, ret_var, func_name, ctx, arena);
    default:
      return false;
  }
}

static void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                             SimContext& ctx, Arena& arena) {
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, ret_var, func->name, ctx, arena)) return;
  }
}

// §8.7: Initialize properties for a single class level to their explicit
// defaults or zero if no default is provided.
static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      ClassObject* obj, SimContext& ctx,
                                      Arena& arena) {
  for (const auto& prop : info->properties) {
    Logic4Vec val = prop.init_expr ? EvalExpr(prop.init_expr, ctx, arena)
                                  : MakeLogic4VecVal(arena, prop.width, 0);
    obj->properties[std::string(prop.name)] = val;
    std::string scoped = std::string(info->name) + "::" + std::string(prop.name);
    obj->properties[scoped] = val;
  }
  // §8.5/§8.15: Populate parameter properties with default values.
  // Store with scoped names so super.PARAM resolves to the base class value.
  if (info->decl) {
    for (const auto& [pname, pexpr] : info->decl->params) {
      if (pexpr) {
        auto val = EvalExpr(pexpr, ctx, arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped = std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
  }
}

// §8.7: Run the constructor for a single class level. If the class has no
// explicit constructor, this is a no-op (implicit constructor).
static void RunConstructorForLevel(const ClassTypeInfo* info, ClassObject* obj,
                                   const Expr* args_expr, SimContext& ctx,
                                   Arena& arena) {
  auto it = info->methods.find("new");
  if (it == info->methods.end() || !it->second) return;
  ctx.PushScope();
  if (args_expr) BindFunctionArgs(it->second, args_expr, ctx, arena);
  Variable dummy;
  ExecFunctionBody(it->second, &dummy, ctx, arena);
  ctx.PopScope();
}

// §8.7: Allocate a new class object, execute constructor, return handle.
//
// Construction order per §8.7:
//  1. Call base class constructor (super.new).
//  2. Initialize each property to its explicit default value or its
//     uninitialized value if no default is provided.
//  3. Execute the remaining code in the user-defined constructor.
//
// For implicit constructors (no user-defined new), steps 2-3 still apply;
// the base class constructor is called automatically for derived classes.
Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error(
        {}, "cannot construct object of abstract class '" +
                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error(
        {}, "cannot construct object of interface class '" +
                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;

  // Collect the inheritance chain from base to most-derived.
  std::vector<const ClassTypeInfo*> chain;
  for (auto* cur = info; cur; cur = cur->parent) chain.push_back(cur);
  std::reverse(chain.begin(), chain.end());

  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);

  // Walk base-to-derived: for each level, initialize property defaults then
  // run its constructor. The most-derived constructor receives new_expr args;
  // base constructors run with no args (explicit super.new args are handled
  // when the constructor body executes a super.new() call).
  for (size_t i = 0; i < chain.size(); ++i) {
    InitClassPropertyDefaults(chain[i], obj, ctx, arena);
    const Expr* args = (i == chain.size() - 1) ? new_expr : nullptr;
    // §8.17: Forward extends specifier args to base constructor.
    if (!args && i + 1 < chain.size() && chain[i + 1]->decl) {
      const auto* child_decl = chain[i + 1]->decl;
      if (!child_decl->extends_args.empty()) {
        auto* synth = arena.Create<Expr>();
        synth->kind = ExprKind::kCall;
        synth->args = child_decl->extends_args;
        args = synth;
      } else if (child_decl->extends_has_default && new_expr) {
        // Find the position of 'default' in the child constructor's arg list.
        size_t default_pos = 0;
        for (const auto* m : child_decl->members) {
          if (m->kind == ClassMemberKind::kMethod && m->method &&
              m->method->name == "new") {
            for (size_t j = 0; j < m->method->func_args.size(); ++j) {
              if (m->method->func_args[j].is_default) {
                default_pos = j;
                break;
              }
            }
            break;
          }
        }
        // Determine base constructor arg count.
        size_t base_argc = 0;
        auto base_it = chain[i]->methods.find("new");
        if (base_it != chain[i]->methods.end() && base_it->second) {
          base_argc = base_it->second->func_args.size();
        }
        auto* synth = arena.Create<Expr>();
        synth->kind = ExprKind::kCall;
        for (size_t j = 0; j < base_argc &&
                           default_pos + j < new_expr->args.size();
             ++j) {
          synth->args.push_back(new_expr->args[default_pos + j]);
        }
        args = synth;
      }
    }
    RunConstructorForLevel(chain[i], obj, args, ctx, arena);
  }

  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

// §8.5: Override parameter properties on a class object with specialization
// values stored for the given variable.
void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const auto& param_exprs = ctx.GetVariableClassParamExprs(var_name);
  if (param_exprs.empty()) return;
  const auto& params = obj->type->decl->params;
  for (size_t i = 0; i < params.size() && i < param_exprs.size(); ++i) {
    if (param_exprs[i]) {
      auto val = EvalExpr(param_exprs[i], ctx, arena);
      obj->properties[std::string(params[i].first)] = val;
      std::string scoped =
          std::string(obj->type->name) + "::" + std::string(params[i].first);
      obj->properties[scoped] = val;
    }
  }
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

// Forward declaration for use in ExecInstanceMethodCall.
static void ExecClassMethod(ModuleItem* method, const Expr* expr,
                            SimContext& ctx, Arena& arena, Logic4Vec& out);

struct InstanceMethodInfo {
  ClassObject* obj = nullptr;
  ModuleItem* method = nullptr;
};

// §8.22: Resolve a class instance and its method by name.
static bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                                  InstanceMethodInfo& info) {
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return false;
  info.obj = ctx.GetClassObject(handle);
  if (!info.obj) return false;
  info.method = info.obj->ResolveVirtualMethod(parts.method_name);
  if (!info.method) {
    // §8.14: Non-virtual methods resolve from the declared type, not the
    // runtime type, so overridden members are hidden through base handles.
    auto* declared_type = ctx.FindClassType(class_type);
    if (declared_type) {
      info.method =
          info.obj->ResolveMethodForType(parts.method_name, declared_type);
    } else {
      info.method = info.obj->ResolveMethod(parts.method_name);
    }
  }
  return info.method != nullptr;
}

// §8: Execute a resolved instance method call.
static Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  Logic4Vec out;
  ctx.PushScope();
  ctx.PushThis(obj);
  ctx.PushQueueRefFrame();
  ExecClassMethod(method, expr, ctx, arena, out);
  WritebackOutputArgs(method, expr, ctx);
  WritebackQueueRefs(ctx);
  ctx.PopThis();
  ctx.PopScope();
  return out;
}

// §8.15: Dispatch a super.method() call from within a derived class.
static bool TryEvalSuperMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.var_name != "super") return false;
  auto* self = ctx.CurrentThis();
  if (!self || !self->type || !self->type->parent) return false;
  auto* method =
      self->ResolveMethodForType(parts.method_name, self->type->parent);
  if (!method) return false;
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  return true;
}

// §8: Dispatch a method call on a class object instance.
static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
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

struct ClassScopeInfo {
  const Expr* access;
  ClassTypeInfo* cls;
  ModuleItem* method;
  bool is_void;
};

static bool ResolveClassScope(const Expr* expr, SimContext& ctx,
                              ClassScopeInfo& info) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  info.access = expr->lhs;
  if (!info.access->lhs || info.access->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!info.access->rhs || info.access->rhs->kind != ExprKind::kIdentifier)
    return false;
  info.cls = ctx.FindClassType(info.access->lhs->text);
  if (!info.cls) return false;
  auto it = info.cls->methods.find(std::string(info.access->rhs->text));
  if (it == info.cls->methods.end()) return false;
  info.method = it->second;
  info.is_void = (info.method->return_type.kind == DataTypeKind::kVoid);
  return true;
}

static void ExecClassMethod(ModuleItem* method, const Expr* expr,
                            SimContext& ctx, Arena& arena, Logic4Vec& out) {
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) ret_var = ctx.CreateLocalVariable(method->name, 32);
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
}

// §8.23: Dispatch a non-parameterized class scope call — Class::method(args).
static bool TryEvalClassScopeCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (!info.access->lhs->elements.empty()) return false;
  // §8.8: Typed constructor call — Class::new(args).
  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    return true;
  }
  ctx.PushScope();
  ExecClassMethod(info.method, expr, ctx, arena, out);
  ctx.PopScope();
  return true;
}

// §13.8: Dispatch a parameterized class scope call — C#(N)::method(args).
static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (info.access->lhs->elements.empty()) return false;
  ctx.PushScope();
  BindClassParams(info.cls, info.access->lhs, ctx, arena);
  // §8.8: Parameterized typed constructor call — C#(N)::new(args).
  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    ctx.PopScope();
    return true;
  }
  ExecClassMethod(info.method, expr, ctx, arena, out);
  ctx.PopScope();
  return true;
}

// §8.30.3/§8.30.4: Dispatch weak_reference get()/clear() method calls.
static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "weak_reference") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto wr_handle = var->value.ToUint64();
  auto* wr = ctx.FindWeakReferenceByHandle(wr_handle);
  if (parts.method_name == "get") {
    uint64_t referent = (wr != nullptr) ? wr->Get() : kNullClassHandle;
    out = MakeLogic4VecVal(arena, 64, referent);
    return true;
  }
  if (parts.method_name == "clear") {
    if (wr != nullptr) wr->Clear();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

// §8.30.5: Dispatch weak_reference#(T)::get_id(obj) static call.
static bool TryEvalWeakRefStaticCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "weak_reference") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "get_id") return false;
  if (expr->args.empty()) return false;
  uint64_t obj_handle = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  int64_t id = WeakReference::GetId(obj_handle);
  out = MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(id));
  return true;
}

// Try dispatching to built-in type methods (enum, string, array, queue).
static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalWeakRefMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

// §11.12: Guard against recursive let expansion.
static thread_local std::unordered_set<std::string_view> expanding_lets;

// §11.12: Evaluate let actual arguments in the caller's scope.
// Returns a vector of evaluated values, one per formal.
static std::vector<Logic4Vec> EvalLetActuals(ModuleItem* decl, const Expr* call,
                                             SimContext& ctx, Arena& arena) {
  auto& formals = decl->func_args;
  size_t positional_count = call->args.size() - call->arg_names.size();
  std::vector<Logic4Vec> vals;
  vals.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val;
    if (i < positional_count) {
      val = EvalExpr(call->args[i], ctx, arena);
    } else {
      int found = -1;
      for (size_t j = 0; j < call->arg_names.size(); ++j) {
        if (call->arg_names[j] == formals[i].name) {
          found = static_cast<int>(positional_count + j);
          break;
        }
      }
      if (found >= 0 && call->args[static_cast<size_t>(found)]) {
        val = EvalExpr(call->args[static_cast<size_t>(found)], ctx, arena);
      } else if (formals[i].default_value) {
        val = EvalExpr(formals[i].default_value, ctx, arena);
      } else {
        val = MakeLogic4Vec(arena, 32);
      }
    }
    // §11.12: Typed formal — cast actual to formal's declared width.
    const auto& dt = formals[i].data_type;
    if (dt.kind != DataTypeKind::kImplicit && dt.packed_dim_left &&
        dt.packed_dim_right) {
      uint32_t formal_width = EvalTypeWidth(dt);
      if (formal_width > 0 && formal_width != val.width) {
        val = ResizeToWidth(val, formal_width, arena);
      }
    }
    vals.push_back(val);
  }
  return vals;
}

// §11.12: Bind pre-evaluated actual values to let formals in the current scope.
static void BindLetArgs(ModuleItem* decl, const std::vector<Logic4Vec>& vals,
                        SimContext& ctx) {
  auto& formals = decl->func_args;
  for (size_t i = 0; i < formals.size(); ++i) {
    auto* var = ctx.CreateLocalVariable(formals[i].name, vals[i].width);
    var->value = vals[i];
  }
}

// §11.12/§F.4: Expand a let declaration by binding args and evaluating body.
// §11.12: Free variables in the let body resolve from the declaration scope
// (module-level), not the instantiation scope.
static Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call,
                                  SimContext& ctx, Arena& arena) {
  // §11.12: Recursive let instantiation is not permitted.
  if (expanding_lets.count(decl->name)) return MakeAllX(arena, 32);
  expanding_lets.insert(decl->name);
  // §11.12: Evaluate actuals in the caller's scope before isolating.
  auto vals = EvalLetActuals(decl, call, ctx, arena);
  // §11.12: Clear the scope stack so free variables in the let body
  // resolve from the declaration (module-level) scope, not the caller's.
  auto saved_scopes = ctx.SwapScopeStack({});
  ctx.PushScope();
  BindLetArgs(decl, vals, ctx);
  auto result = EvalExpr(decl->init_expr, ctx, arena);
  ctx.PopScope();
  ctx.SwapScopeStack(std::move(saved_scopes));
  expanding_lets.erase(decl->name);
  return result;
}

// Try dispatching to method calls (builtin, class, parameterized scope)
// or let expansion. Returns true if the call was handled.
static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalSuperMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
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
    // §13.3.1: Static tasks reuse their variable frame across calls.
    bool is_static = func->is_static && !func->is_automatic;
    if (is_static) {
      ctx.PushStaticScope(func->name);
    } else {
      ctx.PushScope();
    }
    ctx.PushQueueRefFrame();
    return func;
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  auto* func = ctx.FindFunction(expr->callee);
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;
  // §13.3.1: Static tasks reuse their variable frame across calls.
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  ctx.PushQueueRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr,
                      SimContext& ctx) {
  WritebackOutputArgs(func, expr, ctx);
  WritebackQueueRefs(ctx);
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
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
