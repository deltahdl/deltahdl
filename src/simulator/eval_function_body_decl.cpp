#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/covergroup_instance.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/static_aggregate.h"
#include "simulator/sync_variable.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

static std::string_view NamedLayoutKey(const DataType& type, SimContext& ctx) {
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  auto key_in = [&](std::string_view scope) -> std::string_view {
    auto* key = ctx.GetArena().Create<std::string>(std::string(scope) +
                                                   "::" + std::string(name));
    return ctx.FindStructType(*key) != nullptr ? std::string_view(*key)
                                               : std::string_view{};
  };
  if (!type.scope_name.empty())
    return type.type_params.empty() ? key_in(type.scope_name)
                                    : std::string_view{};
  if (ctx.FindStructType(name) != nullptr) return name;
  std::string_view specialized;
  if (MethodClassTypedefLayout(name, ctx, &specialized) != nullptr)
    return specialized;
  for (const ClassTypeInfo* c = ctx.CurrentMethodClass(); c != nullptr;
       c = c->parent) {
    if (c->param_actuals != nullptr) return {};
    if (std::string_view key = key_in(c->name); !key.empty()) return key;
  }
  return {};
}

bool BindNamedLayout(std::string_view var_name, const DataType& type,
                     SimContext& ctx) {
  std::string_view type_name = NamedLayoutKey(type, ctx);
  if (type_name.empty()) return false;
  ctx.SetVariableStructType(var_name, type_name);
  return true;
}

const StructTypeInfo* NamedLayout(const DataType& type, SimContext& ctx) {
  std::string_view type_name = NamedLayoutKey(type, ctx);
  return type_name.empty() ? nullptr : ctx.FindStructType(type_name);
}

const StructTypeInfo* DeclaredTypeLayout(const DataType& type,
                                         SimContext& ctx) {
  if (type.struct_members.empty()) return NamedLayout(type, ctx);
  return InlineAggregateLayout(type, ctx);
}

static void BindLocalAggregateLayout(std::string_view name,
                                     const DataType& type, const Expr* init,
                                     SimContext& ctx) {
  if (!BindNamedLayout(name, type, ctx)) return;
  if (init != nullptr && init->kind == ExprKind::kTagged &&
      init->rhs != nullptr) {
    ctx.SetVariableTag(name, init->rhs->text);
  }
}

static const StructTypeInfo* TaggedPatternMemberLayout(const DataType& type,
                                                       const Expr* init,
                                                       SimContext& ctx) {
  if (init->kind != ExprKind::kTagged || init->rhs == nullptr ||
      init->lhs == nullptr ||
      UnwrapTypedPattern(init->lhs)->kind != ExprKind::kAssignmentPattern)
    return nullptr;
  const StructTypeInfo* layout = ctx.FindStructType(type.type_name);
  return layout != nullptr ? TaggedMemberLayout(*layout, init->rhs->text)
                           : nullptr;
}

static Logic4Vec EvalLocalInitializer(const DataType& type, const Expr* init,
                                      SimContext& ctx, Arena& arena) {
  if (const StructTypeInfo* member =
          TaggedPatternMemberLayout(type, init, ctx)) {
    return EvalStructPatternValue(UnwrapTypedPattern(init->lhs), member, ctx,
                                  arena);
  }
  return EvalTaggedOrPlain(init, ctx.FindStructType(type.type_name), ctx,
                           arena);
}

static void FillLocalDefault(Variable* v, bool has_initializer,
                             bool holds_a_handle, Arena& arena) {
  if (has_initializer || !v->is_4state || holds_a_handle || v->is_string)
    return;
  v->value = MakeAllX(arena, v->value.width);
  v->value.is_signed = v->is_signed;
}

static Logic4Vec SizeLocalInitializer(const Logic4Vec& val, const Variable& v,
                                      uint32_t declared, Arena& arena) {
  if (v.is_real) return ConvertRealForKnownLhs(val, true, declared, arena);
  return ResizeToWidth(val, declared, arena);
}

Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                             const Expr* init, SimContext& ctx, Arena& arena) {
  std::string_view class_key = DeclaredClassKey(type, ctx, arena);
  bool is_class = !class_key.empty();
  bool is_virtual_interface = DeclaresAVirtualInterface(type, ctx);
  bool holds_a_handle = is_class || is_virtual_interface;
  uint32_t declared = holds_a_handle ? 64 : DeclaredTypeWidth(type, ctx);
  bool is_string = !is_class && DeclaredTypeIsString(type, ctx);
  uint32_t w = declared ? declared : (is_string ? 0 : 32);
  auto* v = ctx.CreateLocalVariable(name, w, DeclaredTypeIsSigned(type, ctx));
  v->declared_type = &type;
  if (TryCreateCovergroupLocal(type, init, v, ctx, arena)) return v;
  v->is_4state = DeclaredTypeIs4State(type, ctx);
  v->is_virtual_interface = is_virtual_interface;
  if (is_string) v->is_string = true;
  v->is_real = !holds_a_handle && DeclaredTypeIsReal(type, ctx);
  v->is_event = type.kind == DataTypeKind::kEvent;
  FillLocalDefault(v, init != nullptr, holds_a_handle, arena);
  if (is_class) {
    ctx.SetVariableClassType(name, class_key);
    RecordClassParamActuals(name, class_key, type.type_params, ctx);
  }
  RecordVariableEnumType(name, type, ctx);
  if (!holds_a_handle) {
    RecordDeclaredRange(type, v, ctx, arena);
    BindLocalAggregateLayout(name, type, init, ctx);
  }
  if (init == nullptr) {
    ApplyVariableLayoutDefaults(name, v, ctx, arena);
    return v;
  }
  if (is_class && init->kind == ExprKind::kCall && init->text == "new") {
    v->value = EvalClassNew(ctx.GetVariableClassType(name), init, ctx, arena,
                            init->range.start);
    ApplyClassParamOverrides(name, v->value.ToUint64(), ctx, arena);
    return v;
  }
  v->value = OwnRhsWords(
      SizeLocalInitializer(EvalLocalInitializer(type, init, ctx, arena), *v,
                           declared, arena),
      arena);
  if (!v->is_4state) CoerceTo2State(v->value);
  return v;
}

static void CreateFuncLocalAggregate(const Stmt* stmt, Variable* var,
                                     SimContext& ctx, Arena& arena) {
  if (var == nullptr) return;
  CreateDeclAggregate(stmt, var->value.width, ctx, arena);
  AssignDeclAggregateInit(stmt, ctx, arena);
  CreateSyncObjectForLocal(stmt, var, ctx, arena);
}

static const Expr* CarrierInit(const Stmt* stmt) {
  return stmt->var_unpacked_dims.empty() ? stmt->var_init : nullptr;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, std::string_view func_name,
                                  SimContext& ctx, Arena& arena) {
  std::string_view block = ctx.InnermostStmtFrame();
  std::string_view frame = block.empty() ? func_name : block;
  auto* existing = ctx.FindStaticFuncVar(frame, stmt->var_name);
  if (existing == nullptr && frame != func_name) {
    existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
    if (existing != nullptr) frame = func_name;
  }
  if (existing) {
    ctx.AliasLocalVariable(stmt->var_name, existing);
    RestoreStaticAggregate(frame, stmt->var_name, ctx);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
  ctx.SaveStaticFuncVar(frame, stmt->var_name, v);
  RetainStaticAggregate(frame, stmt->var_name, ctx, arena);
}

static const Stmt* DeclOfThisTypeRef(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  const DataType* type =
      TypeOfThisNamed(&stmt->var_decl_type, ctx.CurrentMethodClass(), ctx);
  if (type == &stmt->var_decl_type) return stmt;
  auto* copy = arena.Create<Stmt>(*stmt);
  copy->var_decl_type = *type;
  return copy;
}

static const Stmt* DeclOfTypeParam(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const DataType& type = stmt->var_decl_type;
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      type.packed_dim_left != nullptr || !type.type_params.empty()) {
    return stmt;
  }
  const DataType* actual = RunningTypeActual(type.type_name, ctx);
  if (actual == nullptr || actual->kind == DataTypeKind::kImplicit) return stmt;
  auto* copy = arena.Create<Stmt>(*stmt);
  copy->var_decl_type = *actual;
  copy->var_decl_type.param_arg_name = {};
  return copy;
}

static Expr* BoundLiteral(Arena& arena, uint32_t bound) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = bound;
  return lit;
}

const Stmt* DeclParameterTypedByValue(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  Expr* redefined = stmt->var_is_param ? ctx.BlockParamOverride(
                                             ctx.ActiveInstancePrefix(), stmt)
                                       : nullptr;
  if (redefined != nullptr) {
    auto* copy = arena.Create<Stmt>(*stmt);
    copy->var_init = redefined;
    stmt = copy;
  }
  const DataType& type = stmt->var_decl_type;
  if (!stmt->var_is_param || stmt->var_init == nullptr ||
      type.kind != DataTypeKind::kImplicit || type.packed_dim_left != nullptr) {
    return stmt;
  }
  Logic4Vec value = EvalExpr(stmt->var_init, ctx, arena);
  auto* typed = arena.Create<Stmt>(*stmt);
  DataType& as_value = typed->var_decl_type;
  as_value.is_signed = type.signing_written ? type.is_signed : value.is_signed;
  if (value.is_real) {
    as_value.kind = DataTypeKind::kReal;
    return typed;
  }
  as_value.kind = DataTypeKind::kLogic;
  as_value.packed_dim_left = BoundLiteral(arena, value.width - 1);
  as_value.packed_dim_right = BoundLiteral(arena, 0);
  return typed;
}

void ExecFuncVarDecl(const Stmt* stmt, StaticFrame frame, SimContext& ctx,
                     Arena& arena) {
  stmt = DeclareInlineEnumOf(stmt, ctx, arena);
  stmt = DeclOfThisTypeRef(stmt, ctx, arena);
  stmt = DeclOfTypeParam(stmt, ctx, arena);
  stmt = DeclShapedByTypedef(stmt, ctx, arena);
  stmt = DeclParameterTypedByValue(stmt, ctx, arena);
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, ctx, arena);
    return;
  }
  if (stmt->var_is_static || frame.is_static_sub) {
    ExecFuncVarDeclStatic(stmt, frame.name, ctx, arena);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
}

}  // namespace delta
