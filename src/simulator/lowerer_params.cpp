#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"
#include "simulator/vcd_dump_state.h"

namespace delta {

void Lowerer::LowerParams(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    auto* full = arena_.Create<std::string>(
        inst_prefix_ + std::string(p.gen_block_prefix) + std::string(p.name));
    ctx_.Vcd().MarkVcdParameter(*full);
    LowerParam(*mod, p, *full);
  }
  for (const auto& redefined : mod->block_param_overrides) {
    ctx_.RegisterBlockParamOverride(inst_prefix_, redefined.decl,
                                    redefined.init);
  }
}

static void BindParamLayout(const RtlirParamDecl& p, std::string_view full,
                            uint32_t width, SimContext& ctx, Arena& arena) {
  const DataType* type = ParamValueType(p);
  if (type == nullptr) return;
  if (type->kind == DataTypeKind::kNamed) {
    BindNamedLayout(full, *type, ctx);
    return;
  }
  RegisterAggregateLayout(full, type, width, ctx, arena);
}

static void FillParamArray(std::string_view full, RtlirVariable& var,
                           const Expr* value, SimContext& ctx, Arena& arena) {
  const ArrayInfo* source = value->kind == ExprKind::kIdentifier
                                ? ctx.FindArrayInfo(value->text)
                                : nullptr;
  if (source != nullptr) {
    CopyArrayElements(full, *ctx.FindArrayInfo(full), value->text, *source,
                      ctx);
    return;
  }
  var.init_expr = UnwrapTypedPattern(value);
  InitArrayElements(full, var, ctx, arena);
}

static RtlirVariable CreateParamArray(const RtlirParamDecl& p,
                                      std::string_view full, SimContext& ctx,
                                      Arena& arena) {
  ParamStorageShape shape = ParamStorageShapeOf(p);
  BindParamLayout(p, full, shape.width, ctx, arena);
  const DataType& type = *p.decl_type;
  RtlirVariable var;
  var.name = p.name;
  var.width = shape.width;
  var.is_signed = shape.is_signed;
  const DataType& value_type = *ParamValueType(p);
  var.is_4state = DeclaredTypeIs4State(value_type, ctx);
  var.is_real = DeclaredTypeIsReal(value_type, ctx);
  var.dtype = &type;
  var.elem_type_kind = type.kind;
  var.unpacked_dims = p.unpacked_bounds;
  for (const auto& dim : p.unpacked_bounds) {
    var.unpacked_dim_sizes.push_back(dim.Size());
  }
  const RtlirUnpackedDim& outer = p.unpacked_bounds.front();
  var.unpacked_lo = outer.Low();
  var.unpacked_size = outer.Size();
  var.is_descending = outer.left > outer.right;
  var.num_unpacked_dims = static_cast<uint32_t>(p.unpacked_bounds.size());
  CreateArrayElements(full, var, ctx, arena);
  return var;
}

static const Expr* ParamValueExpr(const RtlirParamDecl& p) {
  return p.override_expr != nullptr ? p.override_expr : p.default_value;
}

static bool NamesOwnEnumConstant(const Expr* expr, const RtlirModule& mod) {
  bool found = false;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind != ExprKind::kIdentifier) return;
    for (const auto& entry : mod.enum_types) {
      for (const auto& m : entry.second) found = found || m.name == e->text;
    }
  });
  return found;
}

static bool HoldStructParamValue(const RtlirParamDecl& p, std::string_view full,
                                 Variable* var, SimContext& ctx, Arena& arena) {
  const StructTypeInfo* layout = ctx.GetVariableStructType(full);
  if (layout == nullptr || (p.from_override && p.override_expr == nullptr))
    return false;
  const Expr* value = ParamValueExpr(p);
  const Expr* pattern = UnwrapTypedPattern(value);
  bool is_pattern = pattern->kind == ExprKind::kAssignmentPattern;
  if (!is_pattern && layout->is_packed) return false;
  uint32_t width = var->value.width;
  var->value =
      is_pattern ? EvalStructPatternValue(pattern, layout, ctx, arena)
                 : OwnRhsWords(ResizeToWidth(EvalExpr(value, ctx, arena, width),
                                             width, arena),
                               arena);
  return true;
}

void Lowerer::FillInValueScope(const RtlirParamDecl& p,
                               const std::function<void()>& fill) {
  if (p.defparam_module != nullptr) {
    Process writer;
    writer.stand_in = true;
    writer.inst_prefix = instance_prefixes_[p.defparam_module];
    writer.gen_prefixes.assign(p.defparam_value_scopes.begin(),
                               p.defparam_value_scopes.end());
    InstallGenBlockConsts(p.defparam_value_consts, &writer);
    CallerStandIn in_writer(&writer, ctx_);
    fill();
    return;
  }
  std::string own = ctx_.ActiveInstancePrefix();
  if (p.override_expr != nullptr)
    ctx_.SetLoweringInstancePrefix(ctx_.InstantiatingPrefix(own));
  fill();
  ctx_.SetLoweringInstancePrefix(own);
}

void Lowerer::FillParamValue(const RtlirParamDecl& p,
                             std::function<void()> fill) {
  if (p.defparam_module != nullptr &&
      !instance_prefixes_.contains(p.defparam_module)) {
    deferred_param_fills_.emplace_back(
        [this, &p, fill = std::move(fill)] { FillInValueScope(p, fill); });
    return;
  }
  FillInValueScope(p, fill);
}

void Lowerer::LowerParam(const RtlirModule& mod, const RtlirParamDecl& p,
                         std::string_view full) {
  if (p.is_unbounded) {
    ctx_.RegisterUnboundedParam(full);
    ctx_.CreateVariable(full, 32);
    return;
  }
  if (!p.unpacked_bounds.empty()) {
    RtlirVariable var = CreateParamArray(p, full, ctx_, arena_);
    FillParamValue(p, [this, &p, full, var]() mutable {
      FillParamArray(full, var, ParamValueExpr(p), ctx_, arena_);
    });
    return;
  }
  if (!p.is_resolved && !UnfoldedParamEvaluable(p, ctx_)) return;
  if (p.is_real_value) {
    Logic4Vec real = ToDeclaredReal(MakeRealVec(arena_, p.resolved_real, 64),
                                    ParamValueType(p), ctx_, arena_);
    auto* rvar = ctx_.CreateVariable(full, real.width);
    rvar->value = real;
    rvar->is_real = true;
    ctx_.RegisterRealVariable(full);
    return;
  }
  if (p.is_string_value) {
    auto chars =
        StripStringZeros(StringToLogic4Vec(arena_, p.resolved_string), arena_);
    auto* svar = ctx_.CreateVariable(full, chars.width);
    svar->value = chars;
    ctx_.RegisterStringVariable(full);
    ctx_.Vcd().SetVcdVarKind(full, DataTypeKind::kString);
    return;
  }
  ParamStorageShape shape = ParamStorageShapeOf(p);
  uint32_t width = shape.width;
  auto* var = ctx_.CreateVariable(full, width);
  BindParamLayout(p, full, width, ctx_, arena_);
  RecordPackedRange(ParamValueType(p), var, ctx_, arena_);
  var->value =
      MakeLogic4VecVal(arena_, width, static_cast<uint64_t>(p.resolved_value));
  var->is_signed = shape.is_signed;
  FillParamValue(p, [this, &mod, &p, full, var, shape] {
    if (!HoldStructParamValue(p, full, var, ctx_, arena_) &&
        (p.override_expr != nullptr ||
         !NamesOwnEnumConstant(p.default_value, mod)))
      ReevaluateParamValue(p, var, ctx_, arena_);
    var->value.is_signed = shape.is_signed;
  });
}

}  // namespace delta
