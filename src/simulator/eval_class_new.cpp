#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

static void StoreClassPropertyDefault(const ClassTypeInfo* info,
                                      const ClassTypeInfo::PropertyInfo& prop,
                                      const Logic4Vec& val, ClassObject* obj,
                                      Arena& arena) {
  if (prop.is_dynamic) {
    obj->properties[ClassArraySizeKey(prop.name)] =
        MakeLogic4VecVal(arena, 32, 0);
    return;
  }
  if (prop.dim_sizes.size() >= 2) {
    ArrayInfo shape;
    shape.dim_los = prop.dim_los;
    shape.dim_sizes = prop.dim_sizes;
    for (const std::string& leaf : MultiDimLeafSuffixes(shape))
      obj->properties[std::string(prop.name) + leaf] = OwnRhsWords(val, arena);
    return;
  }
  if (prop.array_size > 0) {
    for (uint32_t i = 0; i < prop.array_size; ++i) {
      obj->properties[ClassArrayElementKey(prop.name, prop.array_lo + i)] =
          OwnRhsWords(val, arena);
    }
    return;
  }
  obj->properties[std::string(prop.name)] = val;
  std::string scoped = std::string(info->name) + "::" + std::string(prop.name);
  obj->properties[scoped] = val;
}

static ClassObject* ShallowCopyOfNewSource(const Expr* init, SimContext& ctx,
                                           Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return nullptr;
  auto* src = ctx.GetClassObject(EvalExpr(init->lhs, ctx, arena).ToUint64());
  return src ? src->ShallowCopy(arena) : nullptr;
}

static bool TryInitClassPropertyNew(const ClassTypeInfo* info,
                                    const ClassTypeInfo::PropertyInfo& prop,
                                    SimContext& ctx, Arena& arena,
                                    Logic4Vec& out) {
  const Expr* init = prop.init_expr;
  if (init->kind != ExprKind::kCall || init->text != "new") return false;
  if (auto handle = CovergroupPropertyNew(info, prop.name, init, ctx, arena)) {
    out = *handle;
    return true;
  }
  std::string_view class_name =
      PropertyClassName(ctx.CurrentThis(), info, prop.name, ctx);
  if (class_name.empty()) return false;
  if (ClassObject* copy = ShallowCopyOfNewSource(init, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 64, ctx.AllocateClassObject(copy));
    return true;
  }
  out = EvalClassNew(class_name, init, ctx, arena, init->range.start);
  return true;
}

using TypeBindings = std::unordered_map<std::string_view, const DataType*>;

struct Construction {
  ClassObject* obj;
  const Expr* new_expr;
  SimContext& ctx;
  Arena& arena;
  TypeBindings types;
};

static TypeBindings OwnTypeBindings(const ClassObject* obj) {
  TypeBindings bindings;
  const ClassDecl* decl = obj->type->decl;
  if (decl == nullptr) return bindings;
  for (const auto& [pname, pexpr] : decl->params) {
    if (decl->type_param_names.count(pname) == 0) continue;
    if (const DataType* actual = TypeParamActual(obj, decl, pname))
      bindings[pname] = actual;
  }
  return bindings;
}

static const std::vector<DataType>* BaseTypeActuals(
    const ClassDecl* child, const TypeBindings& child_types) {
  if (child->type_param_names.count(child->base_class) == 0)
    return &child->base_class_type_params;
  auto bound = child_types.find(child->base_class);
  return bound == child_types.end() ? nullptr : &bound->second->type_params;
}

static TypeBindings BaseTypeBindings(const ClassDecl* child,
                                     const TypeBindings& child_types,
                                     const ClassTypeInfo* base) {
  TypeBindings bindings;
  const ClassDecl* decl = base->decl;
  if (decl == nullptr || child == nullptr) return bindings;
  const std::vector<DataType>* actuals = BaseTypeActuals(child, child_types);
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual =
        actuals == nullptr ? nullptr : ActualForParam(*actuals, i, pname);
    if (actual == nullptr) {
      actual = TypeParamActual(nullptr, decl, pname);
    } else if (actual->kind == DataTypeKind::kNamed) {
      auto bound = child_types.find(actual->type_name);
      if (bound != child_types.end()) actual = bound->second;
    }
    if (actual != nullptr) bindings[pname] = actual;
  }
  return bindings;
}

static uint32_t BoundPropertyWidth(const ClassTypeInfo::PropertyInfo& prop,
                                   const Construction& c) {
  if (prop.width_is_declared || prop.type_name.empty()) return prop.width;
  auto bound = c.types.find(prop.type_name);
  if (bound == c.types.end()) return prop.width;
  uint32_t width = DeclaredTypeWidth(*bound->second, c.ctx);
  return width != 0 ? width : prop.width;
}

static bool TryStructPropertyDefault(const ClassTypeInfo::PropertyInfo& prop,
                                     SimContext& ctx, Arena& arena,
                                     Logic4Vec& val) {
  if (prop.type_name.empty()) return false;
  const StructTypeInfo* layout = ctx.FindStructType(prop.type_name);
  if (layout == nullptr) return false;
  val = MakeLogic4VecVal(arena, layout->total_width, 0);
  ApplyLayoutDefaults(val, *layout, 0, ctx, arena);
  return true;
}

static bool TryInitClassArrayPattern(const ClassTypeInfo::PropertyInfo& prop,
                                     Construction& c) {
  if (prop.init_expr == nullptr ||
      prop.init_expr->kind != ExprKind::kAssignmentPattern ||
      (!prop.IsArray() && prop.dim_sizes.size() < 2)) {
    return false;
  }
  uint32_t width = BoundPropertyWidth(prop, c);
  Logic4Vec fill = prop.is_4state ? MakeAllX(c.arena, width)
                                  : MakeLogic4VecVal(c.arena, width, 0);
  StoreClassPropertyDefault(c.obj->type, prop, fill, c.obj, c.arena);
  ClassArrayRef ref;
  ref.obj = c.obj;
  ref.prop = &prop;
  const bool kMulti = prop.dim_sizes.size() >= 2;
  ref.size = kMulti ? prop.dim_sizes[0] : prop.array_size;
  ref.lo = kMulti ? prop.dim_los[0] : prop.array_lo;
  return StoreClassArrayPattern(ref, prop.init_expr, c.ctx, c.arena);
}

static void InitClassPropertyDefault(const ClassTypeInfo* info,
                                     const ClassTypeInfo::PropertyInfo& prop,
                                     Construction& c) {
  ClassObject* obj = c.obj;
  SimContext& ctx = c.ctx;
  Arena& arena = c.arena;
  if (prop.init_expr != nullptr &&
      InitClassQueueProperty(obj, info, prop.name, prop.init_expr, ctx)) {
    return;
  }
  if (TryInitClassSyncProperty(obj, info, prop.name, prop.init_expr, ctx))
    return;
  Logic4Vec val;
  if (prop.init_expr && TryInitClassPropertyNew(info, prop, ctx, arena, val)) {
    StoreClassPropertyDefault(info, prop, val, obj, arena);
    return;
  }
  if (TryInitClassArrayPattern(prop, c)) return;
  if (prop.init_expr) {
    uint32_t context_width = prop.width_is_declared && !prop.is_real
                                 ? BoundPropertyWidth(prop, c)
                                 : 0;
    val = CoerceToPropertyType(
        info, prop.name, EvalExpr(prop.init_expr, ctx, arena, context_width),
        arena);
  } else if (!TryStructPropertyDefault(prop, ctx, arena, val)) {
    val = prop.is_4state
              ? MakeAllX(arena, BoundPropertyWidth(prop, c))
              : MakeLogic4VecVal(arena, BoundPropertyWidth(prop, c), 0);
  }
  StoreClassPropertyDefault(info, prop, val, obj, arena);
}

static bool StoreSpecializationParam(const ClassTypeInfo* info, size_t i,
                                     ClassParamSizer& sizer, ClassObject* obj,
                                     Arena& arena) {
  if (info->param_actuals == nullptr) return false;
  std::string_view pname = info->decl->params[i].first;
  if (info->decl->type_param_names.count(pname) != 0) return false;
  auto bound = info->static_properties.find(std::string(pname));
  if (bound == info->static_properties.end()) return false;
  Logic4Vec val = OwnRhsWords(bound->second, arena);
  sizer.Record(i, val);
  obj->properties[std::string(pname)] = val;
  obj->properties[std::string(info->name) + "::" + std::string(pname)] = val;
  return true;
}

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      Construction& c) {
  ClassObject* obj = c.obj;
  SimContext& ctx = c.ctx;
  Arena& arena = c.arena;
  for (const auto& prop : info->properties) {
    if (prop.is_static) continue;
    InitClassPropertyDefault(info, prop, c);
  }

  if (info->decl) {
    ClassParamSizer sizer(info->decl);
    sizer.UseTypeActuals(info->param_actuals);
    const auto& params = info->decl->params;
    for (size_t i = 0; i < params.size(); ++i) {
      const auto& [pname, pexpr] = params[i];
      if (StoreSpecializationParam(info, i, sizer, obj, arena)) continue;
      if (pexpr) {
        auto val = OwnRhsWords(sizer.Value(i, pexpr, ctx, arena), arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped =
            std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
    MarkUnboundedClassParams(obj, info->decl);
  }
}

static void BindCallerConstructorArgs(const ModuleItem* ctor,
                                      const Expr* args_expr, SimContext& ctx,
                                      Arena& arena) {
  ClassObject* constructed = ctx.CurrentThis();
  ctx.PopThis();
  BindFunctionArgs(ctor, args_expr, ctx, arena);
  ctx.PushThis(constructed);
}

struct ConstructorActuals {
  const Expr* args = nullptr;
  bool are_callers = false;
};

static const ModuleItem* ClassConstructor(const ClassTypeInfo* info) {
  auto it = info->methods.find("new");
  return it == info->methods.end() ? nullptr : it->second;
}

static const Expr* LeadingSuperNewCall(const ModuleItem* ctor) {
  if (!ctor) return nullptr;
  const Stmt* first = nullptr;
  for (const Stmt* s : ctor->func_body_stmts) {
    if (s && s->kind == StmtKind::kVarDecl) continue;
    first = s;
    break;
  }
  if (!first || first->kind != StmtKind::kExprStmt || !first->expr)
    return nullptr;
  const Expr* call = first->expr;
  if (call->kind != ExprKind::kCall) return nullptr;
  MethodCallParts parts;
  if (!ExtractMethodCallParts(call, parts)) return nullptr;
  if (parts.var_name != "super" || parts.method_name != "new") return nullptr;
  return call;
}

static bool IsSuperNewDefault(const Expr* call) {
  return call->args.size() == 1 && call->args[0] &&
         call->args[0]->kind == ExprKind::kIdentifier &&
         call->args[0]->text == "default";
}

bool IsSuperNewRunByConstruction(const Expr* call, SimContext& ctx) {
  if (IsSuperNewDefault(call)) return true;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) return false;
  return call == LeadingSuperNewCall(ClassConstructor(enclosing));
}

static size_t FindFirstDefaultArgPos(const ModuleItem* method) {
  for (size_t j = 0; j < method->func_args.size(); ++j) {
    if (method->func_args[j].is_default) {
      return j;
    }
  }
  return 0;
}

static size_t FindChildNewDefaultPos(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return FindFirstDefaultArgPos(m->method);
    }
  }
  return 0;
}

static const Expr* SynthDefaultExtendsArgs(const ClassTypeInfo* base,
                                           const ClassDecl* child_decl,
                                           const Expr* new_expr, Arena& arena) {
  size_t default_pos = FindChildNewDefaultPos(child_decl);

  size_t base_argc = 0;
  const ModuleItem* base_ctor = ClassConstructor(base);
  if (base_ctor) base_argc = base_ctor->func_args.size();
  auto* synth = arena.Create<Expr>();
  synth->kind = ExprKind::kCall;
  for (size_t j = 0; j < base_argc && default_pos + j < new_expr->args.size();
       ++j) {
    synth->args.push_back(new_expr->args[default_pos + j]);
  }
  return synth;
}

static bool ChildNewUsesDefaultArg(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      for (const auto& a : m->method->func_args) {
        if (a.is_default) return true;
      }
      return false;
    }
  }
  return false;
}

static ConstructorActuals BaseConstructorActuals(const ClassTypeInfo* info,
                                                 const ModuleItem* ctor,
                                                 const Expr* new_expr,
                                                 Arena& arena) {
  const Expr* leading = LeadingSuperNewCall(ctor);
  if (leading && !IsSuperNewDefault(leading)) return {leading, false};
  const ClassDecl* decl = info->decl;
  if (!decl) return {};
  if (!decl->extends_args.empty()) {
    auto* synth = arena.Create<Expr>();
    synth->kind = ExprKind::kCall;
    synth->args = decl->extends_args;
    return {synth, false};
  }
  if ((decl->extends_has_default || ChildNewUsesDefaultArg(decl)) && new_expr) {
    return {SynthDefaultExtendsArgs(info->parent, decl, new_expr, arena), true};
  }
  return {};
}

static void BindLevelFormals(const ModuleItem* ctor, ConstructorActuals actuals,
                             SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  if (!actuals.args) return;
  if (actuals.are_callers) {
    BindCallerConstructorArgs(ctor, actuals.args, ctx, arena);
  } else {
    BindFunctionArgs(ctor, actuals.args, ctx, arena);
  }
}

static void WritebackLevelFormals(const ModuleItem* ctor,
                                  ConstructorActuals actuals, SimContext& ctx,
                                  Arena& arena) {
  if (!actuals.args) return;
  if (!actuals.are_callers) {
    WritebackOutputArgs(ctor, actuals.args, ctx, arena);
    return;
  }
  ClassObject* constructed = ctx.CurrentThis();
  ctx.PopThis();
  WritebackOutputArgs(ctor, actuals.args, ctx, arena);
  ctx.PushThis(constructed);
}

static void ConstructLevel(const ClassTypeInfo* info,
                           ConstructorActuals actuals, Construction& c);

static void ConstructBaseThenDefaults(const ClassTypeInfo* info,
                                      const ModuleItem* ctor, Construction& c) {
  if (info->parent) {
    TypeBindings own = std::move(c.types);
    c.types = BaseTypeBindings(info->decl, own, info->parent);
    ConstructLevel(info->parent,
                   BaseConstructorActuals(info, ctor, c.new_expr, c.arena), c);
    c.types = std::move(own);
  } else if (info->decl != nullptr) {
    BuildBuiltinSyncBase(
        c.obj, info->decl->base_class,
        BaseConstructorActuals(info, ctor, c.new_expr, c.arena).args, c.ctx,
        c.arena);
  }
  auto params = CollectClassParamBindings(info, c.ctx);
  c.ctx.PushScope();
  RebindClassParamBindings(params, c.ctx);
  c.ctx.EnterSubroutineScope(info->package);
  InitClassPropertyDefaults(info, c);
  c.ctx.PopScope();
}

static void ConstructLevel(const ClassTypeInfo* info,
                           ConstructorActuals actuals, Construction& c) {
  const ModuleItem* ctor = ClassConstructor(info);
  auto params = CollectClassParamBindings(info, c.ctx);
  if (ctor) {
    BindLevelFormals(ctor, actuals, c.ctx, c.arena);
    RebindClassParamBindings(params, c.ctx);
  }
  c.ctx.PushMethodClass(info);
  ConstructBaseThenDefaults(info, ctor, c);
  if (ctor) {
    c.ctx.EnterSubroutineScope(info->package);
    Variable dummy;
    ExecFunctionBody(ctor, nullptr, &dummy, c.ctx, c.arena);
    WritebackLevelFormals(ctor, actuals, c.ctx, c.arena);
  }
  c.ctx.PopMethodClass();
  if (ctor) c.ctx.PopScope();
}

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena, SourceLoc loc) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of abstract class '" +
                            std::string(class_type) + "'",
                        Subclause("8.21"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of interface class '" +
                            std::string(class_type) + "'",
                        Subclause("8.26.5"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;
  const ClassObject* running = ctx.CurrentThis();
  obj->instance =
      running != nullptr ? running->instance : ctx.ActiveInstancePrefix();
  BindSpecializationTypeParams(obj);
  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);
  Construction construction{obj, new_expr, ctx, arena, OwnTypeBindings(obj)};
  ConstructLevel(info, {new_expr, true}, construction);
  ctx.PopThis();
  GetGlobalVpiContext().NoteObjectCreated(*obj);
  return MakeLogic4VecVal(arena, 64, handle);
}

}  // namespace delta
