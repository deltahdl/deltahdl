#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_struct_property.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto* dst = FindAssocArrayOfBase(stmt->lhs, ctx, arena);
  if (!dst) return false;
  auto* src = FindAssocArrayOfBase(stmt->rhs, ctx, arena);
  if (!src) return false;
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  if (!dst) return false;
  AssocArrayObject mapped;
  if (!TryCollectAssocMapResult(stmt->rhs, ctx, arena, mapped)) return false;
  dst->int_data = mapped.int_data;
  dst->str_data = mapped.str_data;
  return true;
}

static std::string StripAssocKeyQuotes(std::string_view key) {
  if (key.size() >= 2 && key.front() == '"' && key.back() == '"')
    return std::string(key.substr(1, key.size() - 2));
  return std::string(key);
}

bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kAssignmentPattern)
    return false;
  if (stmt->rhs->pattern_keys.empty()) return false;
  auto* aa = ctx.FindAssocArray(stmt->lhs->text);
  if (!aa) return false;
  aa->int_data.clear();
  aa->str_data.clear();
  const Expr* rhs = stmt->rhs;
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    const auto* key = rhs->pattern_keys[i];
    auto val = EvalExpr(rhs->elements[i], ctx, arena);
    if (key->text == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripAssocKeyQuotes(key->text)] = val;
    } else {
      auto key_val = EvalExpr(key, ctx, arena);
      aa->int_data[AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                               aa->is_index_signed)] = val;
    }
  }
  return true;
}

static bool TryClassCopyNewAssign(const Stmt* stmt, std::string_view target,
                                  SimContext& ctx, Arena& arena) {
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto src_val = EvalExpr(stmt->rhs->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, copy_handle);
    var->NotifyWatchers();
  }
  return true;
}

Logic4Vec EvalWeakReferenceNew(const Expr* call, SimContext& ctx,
                               Arena& arena) {
  uint64_t referent = kNullClassHandle;
  if (!call->args.empty())
    referent = EvalExpr(call->args[0], ctx, arena).ToUint64();
  return MakeLogic4VecVal(arena, 64,
                          ctx.AllocateWeakReference(referent, arena));
}

static void AssignWeakReferenceNew(const Stmt* stmt, std::string_view target,
                                   SimContext& ctx, Arena& arena) {
  Logic4Vec wr_handle = EvalWeakReferenceNew(stmt->rhs, ctx, arena);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = wr_handle;
    var->NotifyWatchers();
  }
}

static std::string_view ClassNewTargetKey(const Expr* lhs, Arena& arena) {
  if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
  if (lhs->kind != ExprKind::kMemberAccess) return {};
  if (!lhs->is_scope_resolution) {
    return *arena.Create<std::string>(HierarchicalReferenceName(lhs));
  }
  if (!lhs->lhs || lhs->lhs->kind != ExprKind::kIdentifier || !lhs->rhs ||
      lhs->rhs->kind != ExprKind::kIdentifier)
    return {};
  return *arena.Create<std::string>(std::string(lhs->lhs->text) + "." +
                                    std::string(lhs->rhs->text));
}

static bool NameHoldsAnArray(std::string_view name, SimContext& ctx) {
  return ctx.FindArrayInfo(name) != nullptr || ctx.FindQueue(name) != nullptr ||
         ctx.FindAssocArray(name) != nullptr;
}

bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs) return false;
  std::string_view target = ClassNewTargetKey(stmt->lhs, arena);
  if (target.empty()) return false;
  auto type_name = ctx.GetVariableClassType(target);
  if (type_name.empty()) return false;
  if (NameHoldsAnArray(target, ctx)) return false;

  if (TryClassCopyNewAssign(stmt, target, ctx, arena)) return true;

  if (type_name == "weak_reference") {
    AssignWeakReferenceNew(stmt, target, ctx, arena);
    return true;
  }

  auto handle =
      EvalClassNew(type_name, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  ApplyClassParamOverrides(target, handle.ToUint64(), ctx, arena);
  return true;
}

bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->rhs->rhs || stmt->rhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (stmt->rhs->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(stmt->rhs->lhs->text);
  if (!cls) return false;
  bool parameterized = !stmt->rhs->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, stmt->rhs->lhs, ctx, arena);
  }
  auto handle = EvalClassNew(stmt->rhs->lhs->text, nullptr, ctx, arena,
                             stmt->rhs->range.start);
  if (parameterized) ctx.PopScope();
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  return true;
}

struct MemberNewBase {
  const ClassTypeInfo* cls = nullptr;
  const ClassObject* obj = nullptr;
};

static MemberNewBase MemberNewBaseClass(const Expr* base_expr,
                                        std::string_view field, SimContext& ctx,
                                        Arena& arena) {
  std::string_view base = base_expr->text;
  auto base_type = ctx.GetVariableClassType(base);
  if (!base_type.empty()) {
    const Variable* var = ctx.FindVariable(base);
    const ClassObject* obj =
        var != nullptr ? ctx.GetClassObject(var->value.ToUint64()) : nullptr;
    return {ctx.FindClassType(base_type), obj};
  }
  const auto* cls = ctx.FindClassType(base);
  if (cls == nullptr) {
    const ClassObject* obj =
        ctx.GetClassObject(EvalExpr(base_expr, ctx, arena).ToUint64());
    return obj != nullptr ? MemberNewBase{obj->type, obj} : MemberNewBase{};
  }
  const ClassTypeInfo* declarer = cls->StaticPropertyDeclarer(field);
  if (declarer == nullptr) return {};
  return {declarer, nullptr};
}

bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kMemberAccess) return false;
  const Expr* holder = stmt->lhs->lhs;
  if (!holder || (holder->kind != ExprKind::kIdentifier &&
                  holder->kind != ExprKind::kSelect)) {
    return false;
  }
  if (!stmt->lhs->rhs || stmt->lhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  MemberNewBase base =
      MemberNewBaseClass(stmt->lhs->lhs, stmt->lhs->rhs->text, ctx, arena);
  if (base.cls == nullptr) return false;
  auto field_type =
      PropertyClassName(base.obj, base.cls, stmt->lhs->rhs->text, ctx);
  if (field_type.empty()) return false;
  auto handle =
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  WriteStructField(stmt->lhs, handle, ctx);
  return true;
}

static std::string_view StructMemberClassName(const Expr* lhs,
                                              SimContext& ctx) {
  const std::string kPath = HierarchicalReferenceName(lhs);
  const std::string_view kView = kPath;
  const size_t kDot = kView.find('.');
  uint32_t offset = 0;
  const StructFieldInfo* field =
      StructMemberOfClassType(ctx.GetVariableStructType(kView.substr(0, kDot)),
                              kView.substr(kDot + 1), ctx, &offset);
  return field == nullptr ? std::string_view{} : field->type_name;
}

bool TryStructMemberClassNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (stmt->rhs->kind != ExprKind::kCall || stmt->rhs->text != "new" ||
      stmt->lhs->kind != ExprKind::kMemberAccess ||
      stmt->lhs->is_scope_resolution) {
    return false;
  }
  std::string_view type_name = StructMemberClassName(stmt->lhs, ctx);
  if (type_name.empty()) return false;
  auto handle =
      EvalClassNew(type_name, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  WriteStructField(stmt->lhs, handle, ctx);
  return true;
}

}  // namespace delta
