#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

static uint32_t BoundTypeParamWidth(std::string_view name, SimContext& ctx) {
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return ScopedTypeParamWidth(name, ctx);
  if (self->type == nullptr || self->type->decl == nullptr) return 0;
  const ClassDecl* decl = self->type->decl;
  std::string_view pname = TypeParamNamedBy(decl, name);
  if (pname.empty()) return 0;
  const DataType* actual = TypeParamActual(self, decl, pname);
  return actual != nullptr ? DeclaredTypeWidth(*actual, ctx) : 0;
}

static uint64_t FixedArrayBits(const Expr* arg, SimContext& ctx, Arena& arena) {
  size_t depth = 0;
  while (arg->kind == ExprKind::kSelect && arg->base != nullptr &&
         arg->index_end == nullptr) {
    arg = arg->base;
    ++depth;
  }
  std::string name = ArrayArgPath(arg, ctx, arena);
  if (name.empty()) return 0;
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue ||
      info->elem_type_kind == DataTypeKind::kString) {
    return 0;
  }
  std::vector<uint32_t> dims = info->dim_sizes;
  if (dims.empty()) dims.push_back(info->size);
  if (depth >= dims.size()) return 0;
  uint64_t count = 1;
  for (size_t d = depth; d < dims.size(); ++d) count *= dims[d];
  return count * info->elem_width;
}

static std::string ScopedTypeName(const Expr* arg) {
  if (arg->kind == ExprKind::kIdentifier) return std::string(arg->text);
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution ||
      arg->lhs == nullptr || arg->rhs == nullptr ||
      arg->rhs->kind != ExprKind::kIdentifier)
    return {};
  std::string scope = ScopedTypeName(arg->lhs);
  if (scope.empty()) return {};
  return scope + "::" + std::string(arg->rhs->text);
}

static uint64_t NamedTypeBits(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind == ExprKind::kIdentifier) {
    uint32_t tw = BoundTypeParamWidth(arg->text, ctx);
    return tw > 0 ? tw : TypedefBits(arg->text, ctx, arena);
  }
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution)
    return 0;
  if (uint32_t tw = SpecializationTypeParamWidth(arg, ctx, arena); tw > 0)
    return tw;
  std::string name = ScopedTypeName(arg);
  return name.empty() ? 0 : ctx.FindTypeWidth(name);
}

static uint64_t UserSystemFunctionBits(const Expr* arg) {
  if (arg->kind != ExprKind::kSystemCall) return 0;
  VpiContext& vpi = GetGlobalVpiContext();
  const s_vpi_systf_data* data =
      vpi.ResolveSystf(std::string(arg->callee).c_str());
  if (data == nullptr || data->type != vpiSysFunc) return 0;
  const int kBits = vpi.SystfResultSizeBits(*data);
  return static_cast<uint64_t>(kBits > 0 ? kBits : kVpiDefaultSizedFuncBits);
}

Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);

  auto* arg = expr->args[0];
  if (arg->type_value != nullptr) {
    return MakeLogic4VecVal(arena, 32,
                            DeclaredTypeWidth(*arg->type_value, ctx));
  }
  if (uint64_t bits = FixedArrayBits(arg, ctx, arena); bits > 0) {
    return MakeLogic4VecVal(arena, 32, bits);
  }
  if (uint64_t tw = NamedTypeBits(arg, ctx, arena); tw > 0) {
    return MakeLogic4VecVal(arena, 32, tw);
  }
  if (arg->kind == ExprKind::kCall) {
    SubroutineTarget target = FindSubroutineTarget(arg, ctx, arena);
    if (target.func != nullptr) {
      return MakeLogic4VecVal(arena, 32,
                              DeclaredTypeWidth(target.func->return_type, ctx));
    }
  }
  if (uint64_t bits = UserSystemFunctionBits(arg); bits > 0) {
    return MakeLogic4VecVal(arena, 32, bits);
  }
  if (std::string name = ArrayArgPath(arg, ctx, arena); !name.empty()) {
    if (auto* q = ctx.FindQueue(name)) {
      uint64_t bits = static_cast<uint64_t>(q->elements.size()) * q->elem_width;
      return MakeLogic4VecVal(arena, 32, bits);
    }
  }
  ClassArrayRef ref;
  if (ResolveClassArray(arg, ctx, arena, ref)) {
    return MakeLogic4VecVal(arena, 32,
                            static_cast<uint64_t>(ref.size) * ref.prop->width);
  }
  auto val = EvalExpr(arg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
}

}  // namespace delta
