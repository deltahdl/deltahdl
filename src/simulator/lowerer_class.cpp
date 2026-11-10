#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_enum_members.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_class_sync.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/unit_scope_items.h"

namespace delta {

static ModuleItem* VTableMethodOf(const ClassTypeInfo* info,
                                  const ClassMember* member) {
  if (member->is_pure_virtual) return nullptr;
  auto it = info->methods.find(std::string(member->method->name));
  return it == info->methods.end() ? member->method : it->second;
}

static void AddOrUpdateVTableEntry(ClassTypeInfo* info,
                                   const ClassMember* member) {
  int idx = info->FindVTableIndex(member->method->name);
  auto* method_ptr = VTableMethodOf(info, member);
  if (idx >= 0) {
    info->vtable[static_cast<size_t>(idx)].method = method_ptr;
    info->vtable[static_cast<size_t>(idx)].owner = info;
  } else {
    info->vtable.push_back({member->method->name, method_ptr, info});
  }
}

static bool VTableHasMethodName(const ClassTypeInfo* info,
                                std::string_view method_name) {
  for (const auto& existing : info->vtable) {
    if (existing.method_name == method_name) return true;
  }
  return false;
}

static void MergeInterfaceVTableEntries(ClassTypeInfo* info,
                                        const ClassTypeInfo* iface) {
  for (const auto& entry : iface->vtable) {
    if (!VTableHasMethodName(info, entry.method_name))
      info->vtable.push_back(entry);
  }
}

static void MergeInterfaceVTables(ClassTypeInfo* info) {
  for (const auto* iface : info->extended_interfaces) {
    if (!iface) continue;
    MergeInterfaceVTableEntries(info, iface);
  }
}

static bool MemberContributesToVTable(ClassTypeInfo* info,
                                      const ClassMember* member) {
  bool overrides_inherited_virtual =
      !member->method->is_method_initial &&
      info->FindVTableIndex(member->method->name) >= 0;
  return member->is_virtual || member->is_pure_virtual ||
         member->method->is_method_extends || overrides_inherited_virtual;
}

static void BuildVTable(ClassTypeInfo* info, const ClassDecl* cls) {
  if (info->parent) info->vtable = info->parent->vtable;
  MergeInterfaceVTables(info);
  for (auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kMethod || !member->method) continue;
    if (!MemberContributesToVTable(info, member)) continue;
    AddOrUpdateVTableEntry(info, member);
  }
}

static void ClearStaticArrayElements(ClassTypeInfo* info,
                                     std::string_view name) {
  std::string element_prefix = std::string(name) + "[";
  std::string size_key = ClassArraySizeKey(name);
  std::erase_if(info->static_properties, [&](const auto& entry) {
    return entry.first == size_key || entry.first.starts_with(element_prefix);
  });
}

static void CreateStaticProperties(ClassTypeInfo* info, Arena& arena) {
  for (const auto& p : info->properties) {
    if (!p.is_static) continue;
    info->static_properties[std::string(p.name)] =
        p.is_4state ? MakeAllX(arena, p.width)
                    : MakeLogic4VecVal(arena, p.width, 0);
    if (p.IsArray() || !p.dim_sizes.empty())
      ClearStaticArrayElements(info, p.name);
  }
}

static bool TryInitStaticArrayPattern(ClassTypeInfo* info,
                                      const ClassTypeInfo::PropertyInfo& p,
                                      SimContext& ctx, Arena& arena) {
  if (p.init_expr->kind != ExprKind::kAssignmentPattern ||
      (!p.IsArray() && p.dim_sizes.size() < 2)) {
    return false;
  }
  ClassArrayRef ref;
  ref.prop = &p;
  ref.static_owner = info;
  const bool kMulti = p.dim_sizes.size() >= 2;
  ref.size = kMulti ? p.dim_sizes[0] : p.array_size;
  ref.lo = kMulti ? p.dim_los[0] : (p.is_dynamic ? 0 : p.array_lo);
  return StoreClassArrayPattern(ref, p.init_expr, ctx, arena);
}

static void InitStaticProperty(ClassTypeInfo* info,
                               const ClassTypeInfo::PropertyInfo& p,
                               SimContext& ctx, Arena& arena) {
  if (TryInitStaticSyncProperty(info, p.name, p.init_expr, ctx)) return;
  if (p.init_expr == nullptr) return;
  if (TryInitStaticArrayPattern(info, p, ctx, arena)) return;
  if (p.init_expr->kind == ExprKind::kCall && p.init_expr->text == "new") {
    std::string_view cls = PropertyClassName(nullptr, info, p.name, ctx);
    if (!cls.empty()) {
      info->static_properties[std::string(p.name)] =
          EvalClassNew(cls, p.init_expr, ctx, arena, p.init_expr->range.start);
      return;
    }
  }
  info->static_properties[std::string(p.name)] = CoerceToPropertyType(
      info, p.name, EvalExpr(p.init_expr, ctx, arena), arena);
}

static void InitStaticProperties(ClassTypeInfo* info, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& p : info->properties) {
    if (p.is_static) InitStaticProperty(info, p, ctx, arena);
  }
  for (const auto* member : info->decl->members) {
    if (member->kind != ClassMemberKind::kClassDecl || !member->nested_class)
      continue;
    std::string key = std::string(info->name) +
                      "::" + std::string(member->nested_class->name);
    if (ClassTypeInfo* nested = ctx.FindClassType(key))
      InitStaticProperties(nested, ctx, arena);
  }
}

static void BindStaticInitValueParams(const ClassTypeInfo* info,
                                      SimContext& ctx) {
  const ClassDecl* decl = info->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) != 0 ||
        decl->param_port_unpacked_dims.count(pname) != 0)
      continue;
    auto entry = info->static_properties.find(std::string(pname));
    if (entry == info->static_properties.end()) continue;
    auto* v = ctx.CreateLocalVariable(pname, entry->second.width);
    v->value = entry->second;
    ShapeClassParamLocal(decl, i, v, ctx, ctx.GetArena());
  }
}

void InitSpecializationStaticProperties(ClassTypeInfo* spec, SimContext& ctx,
                                        Arena& arena) {
  if (spec == nullptr || spec->decl == nullptr) return;
  CreateStaticProperties(spec, arena);
  if (!spec->package.empty()) ctx.PushScope(spec->package);
  ctx.PushScope();
  BindStaticInitTypeActuals(spec, ctx);
  BindStaticInitValueParams(spec, ctx);
  InitStaticProperties(spec, ctx, arena);
  ctx.PopScope();
  if (!spec->package.empty()) ctx.PopScope();
}

static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

static void CarryPrototypeDefaults(const ModuleItem* proto, ModuleItem* body) {
  if (proto->func_args.size() != body->func_args.size()) return;
  for (size_t i = 0; i < body->func_args.size(); ++i) {
    if (body->func_args[i].default_value == nullptr)
      body->func_args[i].default_value = proto->func_args[i].default_value;
  }
}

static void AttachMethodBody(ClassTypeInfo* cls, ModuleItem* body) {
  std::string name(body->name);
  auto existing = cls->methods.find(name);
  if (existing != cls->methods.end()) {
    if (existing->second->is_static_method) body->is_static_method = true;
    CarryPrototypeDefaults(existing->second, body);
  }
  cls->methods[name] = body;
}

static void AttachScopeMethodBodies(
    ClassTypeInfo* info, const ClassDecl* cls,
    const std::vector<ModuleItem*>& scope_items) {
  for (auto* item : scope_items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl)
      continue;
    if (item->method_class != cls->name) continue;
    AttachMethodBody(info, item);
  }
}

struct ClassDeclScope {
  const std::vector<ModuleItem*>& items;
  const ScopeMap& constants;
};

static ScopeMap ClassParamScope(const ClassDecl* cls,
                                const ScopeMap& constants) {
  ScopeMap scope = constants;
  for (const auto& [pname, pexpr] : cls->params) {
    if (pexpr == nullptr || cls->type_param_names.count(pname) != 0) continue;
    if (auto v = ConstEvalInt(pexpr, scope)) scope[pname] = *v;
  }
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param ||
        member->init_expr == nullptr) {
      continue;
    }
    if (auto v = ConstEvalInt(member->init_expr, scope))
      scope[member->name] = *v;
  }
  return scope;
}

static const StructTypeInfo* StructPropertyLayout(const DataType& type,
                                                  std::string_view key,
                                                  SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      type.packed_dim_left != nullptr)
    return nullptr;
  return ctx.FindStructType(key);
}

static std::string_view PropertyTypeKey(const DataType& type,
                                        const ClassTypeInfo& info,
                                        const ClassDecl& cls,
                                        const ScopeMap& params,
                                        SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return type.type_name;
  const ClassDecl* decl = nullptr;
  const ClassTypeInfo* owner =
      ClassTypedefDeclarer(type.type_name, info, cls, decl);
  const DataType* aggregate =
      owner != nullptr ? ClassAggregateTypedef(*decl, type.type_name) : nullptr;
  if (aggregate == nullptr) return type.type_name;
  if (ClassHasValueParams(*decl)) {
    if (owner != &info)
      return ClassTypedefLayoutKey(*owner, type.type_name, ctx);
    return RegisterSpecializationTypedefLayout(
        std::string(info.name) + "#()", info, type.type_name, params, ctx);
  }
  Arena& arena = ctx.GetArena();
  const auto* key = arena.Create<std::string>(
      std::string(owner->name) + "::" + std::string(type.type_name));
  if (ctx.FindStructType(*key) == nullptr)
    RegisterTypeLayout(*key, aggregate, ctx, arena);
  return *key;
}

static bool LayoutHas4StateMember(const StructTypeInfo& layout) {
  for (const auto& field : layout.fields) {
    if (field.nested != nullptr ? LayoutHas4StateMember(*field.nested)
                                : Is4stateType(field.type_kind))
      return true;
  }
  return false;
}

struct PropertyScope {
  const ClassDecl& cls;
  const ScopeMap& params;
};

static ClassTypeInfo::PropertyInfo PropertyRecord(const ClassMember* member,
                                                  const DataType& type,
                                                  const PropertyScope& scope,
                                                  std::string_view type_key,
                                                  SimContext& ctx) {
  uint32_t w = OuterParamPartsWidth(type, scope.cls, ctx);
  if (w == 0) w = EvalTypeWidth(type, {}, scope.params);
  const StructTypeInfo* layout =
      w == 0 ? StructPropertyLayout(type, type_key, ctx) : nullptr;
  if (w == 0) w = layout ? layout->total_width : DeclaredTypeWidth(type, ctx);
  bool sized = w != 0;
  bool four_state = layout != nullptr ? LayoutHas4StateMember(*layout)
                                      : Is4stateType(type, {});
  return {member->name,
          sized ? w : 32,
          member->is_static,
          member->is_local,
          member->is_protected,
          member->is_const,
          member->init_expr,
          four_state,
          sized,
          IsRealKind(type.kind),
          type.kind == DataTypeKind::kString,
          IsSignedType(type, {}),
          type_key,
          type.kind == DataTypeKind::kVirtualInterface};
}

static void CollectClassMembers(ClassTypeInfo* info, const ClassDecl* cls,
                                const ScopeMap& constants, SimContext& ctx) {
  ScopeMap params = ClassParamScope(cls, constants);
  TypedefMap type_params = TypeParamTypes(cls, {}, ctx);
  TypedefRegistryGuard type_param_guard(&type_params, nullptr);
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      const DataType& type = *TypeOfThisNamed(&member->data_type, info, ctx);
      std::string_view key =
          member->is_param
              ? InPlaceAggregateLayoutKey(cls->name, member->name, type, ctx)
              : std::string_view{};
      if (key.empty()) key = PropertyTypeKey(type, *info, *cls, params, ctx);
      info->properties.push_back(
          PropertyRecord(member, ClassPropertyType(type, cls, type_params),
                         {*cls, params}, key, ctx));
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
}

static void FoldMultiDimExtents(const std::vector<Expr*>& dims,
                                const ScopeMap& scope, SimContext& ctx,
                                Arena& arena,
                                ClassTypeInfo::PropertyInfo* prop) {
  if (prop == nullptr) return;
  std::vector<uint32_t> los;
  std::vector<uint32_t> sizes;
  std::vector<bool> descending;
  for (const Expr* dim : dims) {
    PropertyArrayDim folded = FoldPropertyDimension(dim, scope, ctx, arena);
    if (folded.size == 0) return;
    los.push_back(static_cast<uint32_t>(folded.lo));
    sizes.push_back(folded.size);
    descending.push_back(folded.descending);
  }
  prop->dim_los = std::move(los);
  prop->dim_sizes = std::move(sizes);
  prop->dim_descending = std::move(descending);
}

static ClassTypeInfo::PropertyInfo* OwnProperty(ClassTypeInfo* info,
                                                std::string_view name) {
  for (auto& prop : info->properties) {
    if (prop.name == name) return &prop;
  }
  return nullptr;
}

static void ShapeArrayProperty(ClassTypeInfo::PropertyInfo* prop,
                               const std::vector<Expr*>& dims,
                               const ScopeMap& scope, SimContext& ctx,
                               Arena& arena) {
  if (dims.size() > 1) FoldMultiDimExtents(dims, scope, ctx, arena, prop);
  if (dims.size() != 1) return;
  const bool kDynamic = dims[0] == nullptr;
  PropertyArrayDim dim =
      kDynamic ? PropertyArrayDim{}
               : FoldPropertyDimension(dims[0], scope, ctx, arena);
  if (dim.size == 0 && !kDynamic) return;
  prop->array_size = dim.size;
  prop->array_lo = dim.lo;
  prop->array_descending = dim.descending;
  prop->is_dynamic = kDynamic;
}

static void RecordArrayProperties(ClassTypeInfo* info, const ClassDecl* cls,
                                  const ScopeMap& constants, SimContext& ctx,
                                  Arena& arena) {
  ScopeMap scope = ClassParamScope(cls, constants);
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty) continue;
    const ModuleItem* item = PropertyTypedefItem(member, info, ctx);
    ShapeArrayProperty(
        OwnProperty(info, member->name),
        item != nullptr ? item->unpacked_dims : member->unpacked_dims, scope,
        ctx, arena);
  }
}

static void MakeParamArraysStatic(ClassTypeInfo* info, const ClassDecl* cls,
                                  const ScopeMap& constants, SimContext& ctx,
                                  Arena& arena) {
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param)
      continue;
    ClassTypeInfo::PropertyInfo* prop = OwnProperty(info, member->name);
    if (prop->IsArray() || prop->dim_sizes.size() >= 2) prop->is_static = true;
  }
  ScopeMap scope = ClassParamScope(cls, constants);
  for (size_t i = 0; i < cls->params.size(); ++i) {
    const auto& [pname, pexpr] = cls->params[i];
    auto dims = cls->param_port_unpacked_dims.find(pname);
    if (dims == cls->param_port_unpacked_dims.end()) continue;
    auto* port = arena.Create<ClassMember>();
    port->kind = ClassMemberKind::kProperty;
    port->name = pname;
    port->data_type = cls->param_types[i];
    port->init_expr = pexpr;
    port->is_static = true;
    info->properties.push_back(PropertyRecord(
        port, port->data_type, {*cls, scope},
        PropertyTypeKey(port->data_type, *info, *cls, scope, ctx), ctx));
    ShapeArrayProperty(&info->properties.back(), dims->second, scope, ctx,
                       arena);
  }
}

static void StoreClassParam(ClassTypeInfo* info, std::string_view pname,
                            const Logic4Vec& value) {
  info->static_properties[std::string(pname)] = value;
}

static void InitClassParams(ClassTypeInfo* info, const ClassDecl* cls,
                            SimContext& ctx, Arena& arena) {
  ClassParamSizer sizer(cls, info->name);
  for (size_t i = 0; i < cls->params.size(); ++i) {
    const auto& [pname, pexpr] = cls->params[i];
    if (OwnProperty(info, pname) == nullptr)
      info->properties.push_back({pname, 32, false});
    StoreClassParam(info, pname,
                    pexpr ? sizer.Value(i, pexpr, ctx, arena)
                          : MakeLogic4VecVal(arena, 32, 0));
  }
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param)
      continue;
    uint32_t w = EvalTypeWidth(member->data_type, {});
    if (w == 0) w = 32;
    StoreClassParam(info, member->name,
                    member->init_expr
                        ? sizer.Value(member->name, &member->data_type,
                                      member->init_expr, ctx, arena)
                        : MakeLogic4VecVal(arena, w, 0));
  }
  FoldClassBodyParams(ClassParamSizer(cls, info->name),
                      ClassStaticStorage(info), ctx, arena);
}

static void InheritInterfaceStaticsAndEnums(ClassTypeInfo* info,
                                            const ClassTypeInfo* src) {
  for (const auto& [k, v] : src->static_properties) {
    if (info->static_properties.find(k) == info->static_properties.end())
      info->static_properties[k] = v;
  }
  for (const auto& [k, v] : src->enum_members) {
    if (info->enum_members.find(k) == info->enum_members.end()) {
      info->enum_members[k] = v;
      auto shape = src->enum_literal_shapes.find(k);
      if (shape != src->enum_literal_shapes.end())
        info->enum_literal_shapes[k] = shape->second;
    }
  }
}

static void InheritInterfaceMembers(ClassTypeInfo* info) {
  if (info->parent && info->parent->is_interface)
    InheritInterfaceStaticsAndEnums(info, info->parent);
  for (const auto* iface : info->extended_interfaces)
    InheritInterfaceStaticsAndEnums(info, iface);
}

static ClassTypeInfo* PackageClassType(std::string_view scope,
                                       std::string_view name, SimContext& ctx) {
  if (scope.empty()) return nullptr;
  return ctx.FindClassType(std::string(scope) + "::" + std::string(name));
}

static ClassTypeInfo* InterfaceClassType(const InterfaceRef& ref,
                                         SimContext& ctx) {
  ClassTypeInfo* in_package = PackageClassType(ref.scope, ref.name, ctx);
  return in_package != nullptr ? in_package : ctx.FindClassType(ref.name);
}

static ClassTypeInfo* BaseClassOf(const ClassDecl* cls, SimContext& ctx) {
  ClassTypeInfo* in_package =
      PackageClassType(cls->base_class_scope, cls->base_class, ctx);
  if (in_package != nullptr) return in_package;
  if (cls->type_param_names.count(cls->base_class) == 0)
    return ctx.FindClassType(cls->base_class);
  const DataType* def = TypeParamActual(nullptr, cls, cls->base_class);
  if (def == nullptr || def->kind != DataTypeKind::kNamed) return nullptr;
  return ctx.FindClassType(def->type_name);
}

static void PopulateClassType(ClassTypeInfo* info, const ClassDecl* cls,
                              const ClassDeclScope& scope, SimContext& ctx,
                              Arena& arena) {
  if (!cls->base_class.empty()) info->parent = BaseClassOf(cls, ctx);
  info->unit_constants = &scope.constants;
  for (const auto& ref : cls->extends_interfaces) {
    auto* iface = InterfaceClassType(ref, ctx);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (const auto& ref : cls->implements_types) {
    auto* iface = InterfaceClassType(ref, ctx);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  CollectClassMembers(info, cls, scope.constants, ctx);
  AttachScopeMethodBodies(info, cls, scope.items);
  RecordArrayProperties(info, cls, scope.constants, ctx, arena);
  MakeParamArraysStatic(info, cls, scope.constants, ctx, arena);
  BuildVTable(info, cls);
  CreateStaticProperties(info, arena);
  InitClassParams(info, cls, ctx, arena);
  CollectClassEnumMembers(info, cls, ctx, arena);
  if (cls->is_interface) InheritInterfaceMembers(info);
}

static void LowerNestedClasses(ClassTypeInfo* outer, const ClassDecl* cls,
                               const ScopeMap& constants, SimContext& ctx,
                               Arena& arena);

static void RecordClassPackage(ClassTypeInfo* info, std::string_view package,
                               SimContext& ctx) {
  if (package.empty()) return;
  info->package = package;
  for (const auto& entry : info->methods) {
    ctx.RegisterSubroutinePackage(entry.second, package);
  }
}

static void LowerNestedClass(ClassTypeInfo* outer, const ClassDecl* nested,
                             const ScopeMap& constants, SimContext& ctx,
                             Arena& arena) {
  auto qualified = std::string(outer->name) + "::" + std::string(nested->name);
  auto* info = arena.Create<ClassTypeInfo>();
  info->name = *arena.Create<std::string>(std::move(qualified));
  info->decl = nested;
  info->is_abstract = nested->is_virtual;
  info->is_interface = nested->is_interface;
  info->enclosing = outer;
  info->instance_scope = outer->instance_scope;
  const std::vector<ModuleItem*> kNoItems;
  PopulateClassType(info, nested, {kNoItems, constants}, ctx, arena);
  RecordClassPackage(info, outer->package, ctx);
  ctx.RegisterClassType(info->name, info);
  BindDeclarationBase(info, ctx, arena);
  LowerNestedClasses(info, nested, constants, ctx, arena);
}

static void LowerNestedClasses(ClassTypeInfo* outer, const ClassDecl* cls,
                               const ScopeMap& constants, SimContext& ctx,
                               Arena& arena) {
  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class)
      LowerNestedClass(outer, member->nested_class, constants, ctx, arena);
  }
}

std::string_view Lowerer::DeclaringPackage(const ClassDecl* cls) const {
  if (design_ == nullptr) return {};
  for (const auto* pkg : design_->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl == cls)
        return pkg->name;
    }
  }
  return {};
}

void Lowerer::RegisterClassDecl(const ClassDecl* cls,
                                const std::vector<ModuleItem*>& scope_items) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->instance_scope = *arena_.Create<std::string>(ctx_.ClassInstanceScope());
  info->is_abstract = cls->is_virtual;
  info->is_interface = cls->is_interface;
  static const ScopeMap kNoConstants;
  const ScopeMap& constants =
      design_ != nullptr ? design_->unit_constants : kNoConstants;
  std::string_view scope = DeclaringPackage(cls);
  if (scope.empty()) scope = UnitScopeOfClass(design_, cls, arena_);
  if (!scope.empty()) ctx_.PushScope(scope);
  PopulateClassType(info, cls, {scope_items, constants}, ctx_, arena_);
  if (!scope.empty()) ctx_.PopScope();
  RecordClassPackage(info, scope, ctx_);
  ctx_.RegisterClassType(cls->name, info);
  RegisterClassScopeTypedefAliases(info, ctx_, arena_);
  BindDeclarationBase(info, ctx_, arena_);
  LowerNestedClasses(info, cls, constants, ctx_, arena_);
}

void Lowerer::InitClassStaticProperties(const ClassDecl* cls) {
  ClassTypeInfo* info = ctx_.FindClassType(cls->name);
  if (info == nullptr || info->decl != cls) return;
  if (!info->package.empty()) ctx_.PushScope(info->package);
  ctx_.PushScope();
  BindStaticInitTypeActuals(info, ctx_);
  BindStaticInitValueParams(info, ctx_);
  InitStaticProperties(info, ctx_, arena_);
  ctx_.PopScope();
  if (!info->package.empty()) ctx_.PopScope();
}

void Lowerer::LowerClassDecl(const ClassDecl* cls,
                             const std::vector<ModuleItem*>& scope_items) {
  RegisterClassDecl(cls, scope_items);
  InitClassStaticProperties(cls);
}

}  // namespace delta
