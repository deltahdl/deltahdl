#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
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

static void CreateParamArray(const RtlirParamDecl& p, std::string_view full,
                             SimContext& ctx, Arena& arena) {
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
  var.init_expr = p.override_expr == nullptr ? p.default_value : nullptr;
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
  if (p.override_expr == nullptr) return;
  var.init_expr = p.override_expr;
  std::string own = ctx.ActiveInstancePrefix();
  ctx.SetLoweringInstancePrefix(ctx.InstantiatingPrefix(own));
  InitArrayElements(full, var, ctx, arena);
  ctx.SetLoweringInstancePrefix(own);
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

static bool HoldStructParamPattern(const RtlirParamDecl& p,
                                   std::string_view full, Variable* var,
                                   SimContext& ctx, Arena& arena) {
  const StructTypeInfo* layout = ctx.GetVariableStructType(full);
  if (layout == nullptr || (p.from_override && p.override_expr == nullptr))
    return false;
  const Expr* pattern = UnwrapTypedPattern(
      p.override_expr != nullptr ? p.override_expr : p.default_value);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string own = ctx.ActiveInstancePrefix();
  if (p.override_expr != nullptr)
    ctx.SetLoweringInstancePrefix(ctx.InstantiatingPrefix(own));
  var->value = EvalStructPatternValue(pattern, layout, ctx, arena);
  ctx.SetLoweringInstancePrefix(own);
  return true;
}

void Lowerer::LowerParam(const RtlirModule& mod, const RtlirParamDecl& p,
                         std::string_view full) {
  if (p.is_unbounded) {
    ctx_.RegisterUnboundedParam(full);
    ctx_.CreateVariable(full, 32);
    return;
  }
  if (!p.unpacked_bounds.empty()) {
    CreateParamArray(p, full, ctx_, arena_);
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
  var->value =
      MakeLogic4VecVal(arena_, width, static_cast<uint64_t>(p.resolved_value));
  if (!HoldStructParamPattern(p, full, var, ctx_, arena_) &&
      (p.override_expr != nullptr ||
       !NamesOwnEnumConstant(p.default_value, mod)))
    ReevaluateParamValue(p, var, ctx_, arena_);
  var->is_signed = shape.is_signed;
  var->value.is_signed = shape.is_signed;
}

}  // namespace delta
