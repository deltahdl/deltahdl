#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_select_indexes.h"
#include "simulator/vpi_stmt_objects.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int RunTimeArgumentKind(const Expr& actual) {
  switch (actual.kind) {
    case ExprKind::kCall:
      return vpiFuncCall;
    case ExprKind::kSystemCall:
      return vpiSysFuncCall;
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
      return vpiConstant;
    default:
      return vpiOperation;
  }
}

int RunTimeConstType(const Expr& actual) {
  if (actual.kind == ExprKind::kRealLiteral) return vpiRealConst;
  if (actual.kind == ExprKind::kStringLiteral) return vpiStringConst;
  return vpiIntConst;
}

VpiObject* SystfCallArgument(VpiObject* arg, const Expr* actual,
                             SimContext& ctx, Arena& arena, bool evaluate) {
  if (actual == nullptr) {
    VpiMakeEmptyArgument(arg);
    return arg;
  }
  if (actual->kind == ExprKind::kIdentifier && actual->text == "null") {
    VpiMakeNullArgument(arg);
    return arg;
  }
  Variable* named = actual->kind == ExprKind::kIdentifier
                        ? ctx.FindVariable(actual->text)
                        : nullptr;
  if (named != nullptr) {
    arg->type = vpiRefObj;
    arg->name = std::string_view(
        arena.AllocString(actual->text.data(), actual->text.size()),
        actual->text.size());
    arg->var = named;
  } else {
    arg->type = RunTimeArgumentKind(*actual);
    if (arg->type == vpiConstant) arg->const_type = RunTimeConstType(*actual);
    auto* holder = arena.Create<Variable>();
    if (evaluate) holder->value = EvalExpr(actual, ctx, arena);
    arg->var = holder;
  }
  arg->has_side_effects = VpiSourceExprHasSideEffects(actual);
  arg->size = static_cast<int>(arg->var->value.width);
  return arg;
}

Variable* DynamicPrefixBaseVar(const Expr* actual, SimContext& ctx) {
  if (actual == nullptr || actual->kind != ExprKind::kMemberAccess) {
    return nullptr;
  }
  if (actual->lhs->kind != ExprKind::kIdentifier) return nullptr;
  Variable* base = ctx.FindVariable(actual->lhs->text);
  return ctx.IsVirtualInterfaceVar(base) ? base : nullptr;
}

std::string_view DynamicPrefixFieldName(const Expr* actual) {
  return actual->rhs->text;
}

struct DynamicPrefix {
  Variable* base = nullptr;
  Variable* member = nullptr;
  VpiHandle actual = nullptr;
};

DynamicPrefix ResolveDynamicPrefix(const Expr* actual, Variable* base,
                                   SimContext& ctx, VpiContext& vpi) {
  DynamicPrefix prefix;
  prefix.base = base;
  if (!ctx.VirtualInterfaceIsBound(base)) return prefix;
  std::string scope(ctx.VirtualInterfaceBinding(base));
  prefix.member = ctx.FindVariable(scope + "." +
                                   std::string(DynamicPrefixFieldName(actual)));
  prefix.actual = vpi.HandleByName(scope.c_str(), nullptr);
  return prefix;
}

std::string_view ArenaName(Arena& arena, const std::string& name) {
  return std::string_view(arena.AllocString(name.data(), name.size()),
                          name.size());
}

void FillPrefixedArgument(VpiObject* arg, VpiObject* prefix, const Expr* actual,
                          const DynamicPrefix& resolved, Arena& arena) {
  prefix->type = vpiVirtualInterfaceVar;
  prefix->name = ArenaName(arena, std::string(actual->lhs->text));
  prefix->var = resolved.base;
  prefix->actual = resolved.actual;

  arg->type = vpiRefObj;
  arg->name = ArenaName(arena, std::string(actual->lhs->text) + "." +
                                   std::string(DynamicPrefixFieldName(actual)));
  arg->prefix = prefix;
  arg->var =
      resolved.member != nullptr ? resolved.member : arena.Create<Variable>();
  arg->size = static_cast<int>(arg->var->value.width);
}

struct SystfArgumentBuild {
  VpiContext& vpi;
  SimContext& ctx;
  Arena& arena;
  bool evaluate;
  std::function<VpiObject*()> alloc;
};

void AppendSystfCallArguments(VpiObject* call, const Expr& call_site,
                              const SystfArgumentBuild& build) {
  const std::vector<VpiObject*>& written = call->written_arguments;
  for (std::size_t i = 0; i < call_site.args.size(); ++i) {
    const Expr* actual = call_site.args[i];
    Variable* base = DynamicPrefixBaseVar(actual, build.ctx);
    VpiObject* model = i < written.size() ? written[i] : nullptr;
    if (base == nullptr && model != nullptr) {
      if (VpiSourceExprHasSideEffects(actual)) model->has_side_effects = true;
      call->arguments.push_back(model);
      continue;
    }
    VpiObject* arg = build.alloc();
    if (base != nullptr) {
      FillPrefixedArgument(
          arg, build.alloc(), actual,
          ResolveDynamicPrefix(actual, base, build.ctx, build.vpi),
          build.arena);
    } else {
      SystfCallArgument(arg, actual, build.ctx, build.arena, build.evaluate);
      if (actual != nullptr) VpiNoteSelectIndexes(arg, actual, build.alloc);
    }
    call->arguments.push_back(arg);
  }
}

}  // namespace

VpiHandle VpiContext::MakeSystfCallObject(const s_vpi_systf_data& data,
                                          const Expr* call_site,
                                          SimContext& ctx, Arena& arena,
                                          bool evaluate_args) {
  VpiObject* call = VpiCallSiteObjectFor(call_site_objects_, call_site,
                                         ctx.ActiveInstancePrefix());
  if (call == nullptr) {
    VpiObject*& made =
        invoked_call_objects_[{call_site, ctx.ActiveInstancePrefix()}];
    if (made == nullptr) {
      made = AllocObject();
      if (data.type == vpiSysFunc) made->name = std::string_view(data.tfname);
      VpiRecordWrittenLocation(made, call_site->range.start, ctx);
    }
    call = made;
  }
  call->type = (data.type == vpiSysFunc) ? vpiSysFuncCall : vpiSysTaskCall;
  call->func_type = data.type == vpiSysFunc ? data.sysfunctype : 0;
  call->decompile = VpiExprDecompile(call_site);
  call->user_defined = true;
  call->user_systf =
      systf_objects_[static_cast<std::size_t>(&data - systfs_.data())];
  call->arguments.clear();

  auto* value_holder = arena.Create<Variable>();
  int result_bits = SystfResultSizeBits(data);
  auto width = static_cast<uint32_t>(
      result_bits > 0 ? result_bits : kVpiDefaultSizedFuncBits);
  value_holder->value = MakeLogic4VecVal(arena, width, 0);
  if (data.type == vpiSysFunc && data.sysfunctype == vpiRealFunc) {
    value_holder->is_real = true;
    value_holder->value.is_real = true;
  }
  call->var = value_holder;
  call->size = static_cast<int>(width);

  AppendSystfCallArguments(
      call, *call_site,
      SystfArgumentBuild{*this, ctx, arena, evaluate_args,
                         [this] { return AllocObject(); }});
  return call;
}

void VpiContext::NoteTimeFormatCall(const Expr* call_site, SimContext& ctx) {
  VpiObject* call = VpiCallSiteObjectFor(call_site_objects_, call_site,
                                         ctx.ActiveInstancePrefix());
  if (call == nullptr) {
    call = AllocObject();
    call->type = vpiSysTaskCall;
    VpiRecordWrittenLocation(call, call_site->range.start, ctx);
    call->decompile = VpiExprDecompile(call_site);
  }
  active_time_format_call_ = call;
}

}  // namespace delta
