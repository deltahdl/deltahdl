#include <algorithm>
#include <cstddef>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/system_functions.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_procedures_internal.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_named_type_kinds.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int CallKindOf(const ModuleItem& decl, int task, int function) {
  return decl.kind == ModuleItemKind::kTaskDecl || decl.dpi_is_task ? task
                                                                    : function;
}

CallShape SubroutineCallShape(const VpiCalledSubroutine& sub,
                              std::string_view name) {
  if (sub.decl == nullptr) return {vpiFuncCall, name};
  CallShape shape{CallKindOf(*sub.decl, vpiTaskCall, vpiFuncCall), name};
  shape.called = sub.object;
  return shape;
}

struct MethodCall {
  int type = 0;
  bool declared = false;
  VpiScopedClass owner = {};
};

MethodCall ClassMethodCall(const BodyWalk& walk, std::string_view cls,
                           std::string_view method,
                           std::string_view package = {},
                           std::span<const DataType> args = {}) {
  const bool kNamesClass = !cls.empty();
  while (!cls.empty()) {
    VpiScopedClass found = VpiFindClassDecl(walk, cls, package);
    if (found.decl == nullptr) {
      return {VpiBuiltInClassCallKind(VpiClassNameOf(walk, cls), method),
              false};
    }
    const ModuleItem* item = VpiMethodNamed(*found.decl, method);
    if (item != nullptr) {
      return {CallKindOf(*item, vpiMethodTaskCall, vpiMethodFuncCall), true,
              std::move(found)};
    }
    const VpiHeldClass kBase = VpiBaseOf(*found.decl, args);
    cls = kBase.name;
    args = kBase.args;
  }
  const bool kBuiltIn = kNamesClass && VpiIsClassBuiltInMethod(method);
  return {kBuiltIn ? vpiMethodFuncCall : 0, false};
}

CallShape SystemCallShape(const Expr& call, const BodyWalk& walk) {
  const VpiRegisteredSystf kSystf = walk.calls.systf(call.callee);
  const bool kFunction =
      kSystf.type == vpiSysFunc ||
      (kSystf.type == 0 && IsStandardSystemFunction(call.callee));
  CallShape shape{kFunction ? vpiSysFuncCall : vpiSysTaskCall, call.callee};
  shape.user_defined = kSystf.type == vpiSysTask || kSystf.type == vpiSysFunc;
  shape.systf = kSystf.object;
  shape.sysfunctype = kSystf.sysfunctype;
  return shape;
}

bool IsAssocDim(const Expr& dim, const BodyWalk& walk) {
  static constexpr std::string_view kIndexTypes[] = {
      "string", "int",   "integer", "byte", "shortint", "longint",
      "bit",    "logic", "reg",     "time", "*"};
  if (dim.kind != ExprKind::kIdentifier) return false;
  return std::ranges::any_of(
             kIndexTypes, [&](std::string_view t) { return t == dim.text; }) ||
         walk.design.type_kinds.contains(dim.text) ||
         VpiFindClassDecl(walk, dim.text).decl != nullptr;
}

VpiBuiltInHolder DeclaredHolder(const std::vector<Expr*>& dims, int kind,
                                const BodyWalk& walk) {
  if (!dims.empty()) {
    const Expr* dim = dims.front();
    if (dim == nullptr) return VpiBuiltInHolder::kDynamicArray;
    if (IsQueueDim(dim)) return VpiBuiltInHolder::kQueue;
    return IsAssocDim(*dim, walk) ? VpiBuiltInHolder::kAssocArray
                                  : VpiBuiltInHolder::kFixedArray;
  }
  if (kind == vpiStringVar) return VpiBuiltInHolder::kString;
  if (kind == vpiNamedEvent) return VpiBuiltInHolder::kEvent;
  return kind == vpiEnumVar ? VpiBuiltInHolder::kEnum : VpiBuiltInHolder::kNone;
}

VpiBuiltInHolder TypedHolder(const std::vector<Expr*>& dims,
                             const DataType& type, const BodyWalk& walk) {
  if (dims.empty() && type.kind == DataTypeKind::kNamed &&
      VisibleCovergroup(type.type_name, &walk.mod,
                        walk.design.compilation_unit) != nullptr) {
    return VpiBuiltInHolder::kCovergroup;
  }
  return DeclaredHolder(dims, TypeVariableKind(type, walk), walk);
}

VpiBuiltInHolder BlockHolder(const Stmt& decl, const BodyWalk& walk) {
  return TypedHolder(decl.var_unpacked_dims, decl.var_decl_type, walk);
}

VpiBuiltInHolder ModuleHolder(const RtlirVariable& var) {
  if (var.is_queue) return VpiBuiltInHolder::kQueue;
  if (var.is_dynamic) return VpiBuiltInHolder::kDynamicArray;
  if (var.is_assoc) return VpiBuiltInHolder::kAssocArray;
  if (var.num_unpacked_dims > 0) return VpiBuiltInHolder::kFixedArray;
  if (var.is_string) return VpiBuiltInHolder::kString;
  if (var.covergroup != nullptr) return VpiBuiltInHolder::kCovergroup;
  if (var.is_event) return VpiBuiltInHolder::kEvent;
  return var.enum_type_name.empty() && !var.is_enum_constant
             ? VpiBuiltInHolder::kNone
             : VpiBuiltInHolder::kEnum;
}

std::string_view VifInterface(const DataType* type) {
  return type != nullptr && type->kind == DataTypeKind::kVirtualInterface
             ? type->type_name
             : std::string_view();
}

struct PrefixVar {
  std::string_view cls;
  VpiBuiltInHolder holder = VpiBuiltInHolder::kNone;
  VpiObject* object = nullptr;
  std::string_view vif;
  const DataType* type = nullptr;
  std::span<const DataType> args = {};
};

PrefixVar ModulePrefixVar(const RtlirModule& mod, const std::string& prefix,
                          std::string_view name, const BodyWalk& walk) {
  PrefixVar var;
  var.object = FindObjectForFlatName(walk.objects, VpiFlatName(prefix, name));
  for (const RtlirVariable& decl : mod.variables) {
    if (decl.name != name) continue;
    var.cls = decl.class_type_name;
    var.holder = ModuleHolder(decl);
    var.vif = VifInterface(decl.written_type);
    var.type = decl.written_type;
    if (decl.class_data_type != nullptr) {
      var.args = decl.class_data_type->type_params;
    }
    break;
  }
  return var;
}

PrefixVar BlockPrefixVar(const Stmt& item, VpiObject* object,
                         const BodyWalk& walk) {
  const DataType& type = item.var_decl_type;
  return {
      type.kind == DataTypeKind::kNamed ? type.type_name : std::string_view(),
      BlockHolder(item, walk),
      object,
      VifInterface(&type),
      &type,
      type.type_params};
}

PrefixVar FindPrefixVar(const BlockParent& parent, std::string_view name,
                        const BodyWalk& walk) {
  const BlockParent* where = nullptr;
  if (const Stmt* item = BlockVarDecl(parent, name, where)) {
    return BlockPrefixVar(*item, ChildNamed(where->scope, name), walk);
  }
  return ModulePrefixVar(walk.mod, walk.prefix, name, walk);
}

const RtlirModule* ChildModule(const RtlirModule& mod, std::string_view name) {
  for (const RtlirModuleInst& child : mod.children) {
    if (child.inst_name == name) return child.resolved;
  }
  return nullptr;
}

struct ChainHead {
  PrefixVar var;
  const RtlirModule* mod = nullptr;
  std::string path;
  std::size_t used = 1;
  const Stmt* block_decl = nullptr;

  BodyWalk WalkAt(const BodyWalk& walk) const {
    return {walk.design, *mod, walk.objects, path, walk.calls, walk.build};
  }
};

ChainHead ChainHeadVar(const std::vector<std::string_view>& names,
                       const BlockParent& parent, const BodyWalk& walk) {
  const RtlirModule* mod = &walk.mod;
  std::string path = walk.prefix;
  std::size_t i = 0;
  for (; i + 1 < names.size(); ++i) {
    const RtlirModule* child = ChildModule(*mod, names[i]);
    if (child == nullptr) break;
    mod = child;
    path = VpiFlatName(path, names[i]);
  }
  if (i + 1 < names.size()) {
    if (const Stmt* decl = VpiNamedBlockVarDecl(*mod, names[i], names[i + 1])) {
      const std::string kFlat =
          VpiFlatName(VpiFlatName(path, names[i]), names[i + 1]);
      return {BlockPrefixVar(*decl, FindObjectForFlatName(walk.objects, kFlat),
                             walk),
              mod, path, i + 2, decl};
    }
  }
  if (i == 0) return {FindPrefixVar(parent, names.front(), walk), mod, path, 1};
  return {ModulePrefixVar(*mod, path, names[i], walk), mod, path, i + 1};
}

int IndexTypeKind(std::string_view name, const BodyWalk& walk) {
  static constexpr struct {
    std::string_view keyword;
    int kind;
  } kKeywords[] = {
      {"string", vpiStringVar},     {"int", vpiIntVar},
      {"integer", vpiIntegerVar},   {"byte", vpiByteVar},
      {"shortint", vpiShortIntVar}, {"longint", vpiLongIntVar},
      {"bit", vpiBitVar},           {"logic", vpiLogicVar},
      {"reg", vpiLogicVar},         {"time", vpiTimeVar},
  };
  for (const auto& entry : kKeywords) {
    if (entry.keyword == name) return entry.kind;
  }
  return VpiNamedTypeVariableKind(walk.design, walk.mod, name);
}

int ModuleIndexKind(const RtlirModule& mod, std::string_view name,
                    const BodyWalk& walk) {
  for (const RtlirVariable& var : mod.variables) {
    if (var.name != name || !var.is_assoc) continue;
    if (var.is_class_index) return vpiClassVar;
    return IndexTypeKind(var.assoc_index_keyword.empty()
                             ? var.assoc_index_type_name
                             : var.assoc_index_keyword,
                         walk);
  }
  return vpiIntVar;
}

int FirstDimIndexKind(const std::vector<Expr*>& dims, const BodyWalk& walk) {
  const Expr* dim = dims.empty() ? nullptr : dims.front();
  const bool kAssoc = dim != nullptr && IsAssocDim(*dim, walk);
  return kAssoc ? IndexTypeKind(dim->text, walk) : vpiIntVar;
}

VpiObject* MethodObject(const BodyWalk& walk, const VpiScopedClass& owner,
                        std::string_view name, const VpiObject* around) {
  if (owner.decl == nullptr) return nullptr;
  const VpiObject* defn =
      VpiClassDefnOf(walk.calls.classes, owner.decl, owner.scope, around);
  return *std::ranges::find_if(defn->children, [name](const VpiObject* child) {
    return VpiIsClassMethodType(child->type) && child->name == name;
  });
}

CallShape MethodShape(const MethodCall& call, std::string_view name,
                      VpiObject* prefix, const VpiObject* around,
                      const BodyWalk& walk) {
  if (call.type == 0) return {};
  CallShape shape{call.type, name};
  shape.prefix = prefix;
  shape.user_defined = call.declared;
  shape.called = MethodObject(walk, call.owner, name, around);
  return shape;
}

CallShape InterfaceCallShape(const BodyWalk& walk, std::string_view iface,
                             std::string_view name) {
  return SubroutineCallShape({VpiInterfaceItem(walk.design, iface, name,
                                               {ModuleItemKind::kTaskDecl,
                                                ModuleItemKind::kFunctionDecl}),
                              nullptr},
                             name);
}

CallShape MethodCallShape(const Expr& access, const BlockParent& parent,
                          const BodyWalk& walk) {
  const PrefixVar kVar = FindPrefixVar(parent, access.lhs->text, walk);
  if (!kVar.vif.empty()) {
    return InterfaceCallShape(walk, kVar.vif, access.rhs->text);
  }
  MethodCall call;
  if (kVar.holder == VpiBuiltInHolder::kNone) {
    call = ClassMethodCall(walk, kVar.cls, access.rhs->text, {}, kVar.args);
  } else {
    call.type = vpiMethodFuncCall;
  }
  return MethodShape(call, access.rhs->text, kVar.object, parent.scope, walk);
}

struct HandleType {
  std::string_view cls;
  std::string_view vif;
  std::span<const DataType> args = {};
  VpiBuiltInHolder holder = VpiBuiltInHolder::kNone;
  std::string_view scope = {};
};

HandleType PropertyType(const BodyWalk& walk, std::string_view cls,
                        std::string_view name, std::string_view package = {},
                        std::span<const DataType> args = {}) {
  const VpiDeclaredMember kFound = VpiMemberNamed(
      walk, ClassMemberKind::kProperty, {cls, args}, name, package);
  if (kFound.member == nullptr) {
    const bool kEmbedded = VpiMemberNamed(walk, ClassMemberKind::kCovergroup,
                                          {cls, args}, name, package)
                               .member != nullptr;
    return kEmbedded ? HandleType{{}, {}, {}, VpiBuiltInHolder::kCovergroup}
                     : HandleType{};
  }
  const VpiPropertyType kOf = VpiPropertyTypeOf(kFound);
  const DataType& type = *kOf.type;
  return {
      type.kind == DataTypeKind::kNamed ? type.type_name : std::string_view(),
      VifInterface(&type), type.type_params,
      TypedHolder(kFound.member->unpacked_dims, type, walk), kOf.scope};
}

HandleType StructMemberType(const DataType& aggregate, std::string_view name,
                            const BodyWalk& walk) {
  HandleType type;
  for (const StructMember& member : aggregate.struct_members) {
    if (member.name != name) continue;
    const int kKind =
        member.type_kind == DataTypeKind::kNamed
            ? VpiNamedTypeVariableKind(walk.design, walk.mod, member.type_name)
            : VpiDataTypeVariableKind(member.type_kind);
    type = {member.type_name,
            {},
            member.type_params,
            DeclaredHolder(member.unpacked_dims, kKind, walk)};
  }
  return type;
}

int HeadIndexKind(const ChainHead& head, std::string_view name,
                  const BodyWalk& at) {
  return head.block_decl != nullptr
             ? FirstDimIndexKind(head.block_decl->var_unpacked_dims, at)
             : ModuleIndexKind(*head.mod, name, at);
}

int MemberIndexKind(const Expr& array, const BlockParent& parent,
                    const BodyWalk& walk) {
  std::vector<std::string_view> names;
  if (!ChainNames(array, names)) return vpiIntVar;
  const ChainHead kHead = ChainHeadVar(names, parent, walk);
  const BodyWalk kAt = kHead.WalkAt(walk);
  if (kHead.used == names.size())
    return HeadIndexKind(kHead, names.back(), kAt);
  HandleType held{kHead.var.cls, {}, kHead.var.args};
  std::size_t first = kHead.used;
  const ModuleItem* iface_var = VpiInterfaceItem(
      walk.design, kHead.var.vif, names[first], {ModuleItemKind::kVarDecl});
  if (iface_var != nullptr && first + 1 == names.size()) {
    return FirstDimIndexKind(iface_var->unpacked_dims, kAt);
  }
  const DataType* aggregate = VpiStructTypeOf(kAt, kHead.var.type);
  while (aggregate != nullptr) {
    const DataType* inner = nullptr;
    for (const StructMember& member : aggregate->struct_members) {
      if (member.name != names[first]) continue;
      if (first + 1 == names.size()) {
        return FirstDimIndexKind(member.unpacked_dims, kAt);
      }
      held = HandleType{member.type_name, {}, member.type_params};
      inner = VpiMemberStructType(kAt, member);
    }
    ++first;
    aggregate = inner;
  }
  for (std::size_t i = first; i + 1 < names.size(); ++i) {
    held = PropertyType(kAt, held.cls, names[i], held.scope, held.args);
  }
  const ClassMember* member =
      VpiMemberNamed(kAt, ClassMemberKind::kProperty, {held.cls, held.args},
                     names.back(), held.scope)
          .member;
  return member == nullptr ? vpiIntVar
                           : FirstDimIndexKind(member->unpacked_dims, kAt);
}

struct ExprClassName {
  std::string_view cls;
  std::string_view package;
  std::span<const DataType> args = {};
  bool built_in = false;
};

ExprClassName PackageVarClass(const BodyWalk& walk, std::string_view package,
                              std::string_view name) {
  ExprClassName cls{{}, package};
  for (const PackageDecl* decl : walk.design.packages) {
    if (decl->name != package) continue;
    for (const ModuleItem* item : decl->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name) {
        continue;
      }
      const DataType& type = item->data_type;
      const int kKind = type.kind == DataTypeKind::kNamed
                            ? VpiPackageNamedTypeVariableKind(walk.design, decl,
                                                              type.type_name)
                            : VpiDataTypeVariableKind(type.kind);
      cls = {type.type_name, package, type.type_params,
             DeclaredHolder(item->unpacked_dims, kKind, walk) !=
                 VpiBuiltInHolder::kNone};
    }
  }
  return cls;
}

ExprClassName BuiltInResult(const ExprClassName& owner,
                            std::string_view method) {
  if (method == "self") return {owner.cls, owner.package};
  return {{}, {}, {}, true};
}

ExprClassName ReturnedValue(const DataType& returned, std::string_view package,
                            const BodyWalk& walk) {
  return {returned.type_name, package, returned.type_params,
          DeclaredHolder({}, TypeVariableKind(returned, walk), walk) !=
              VpiBuiltInHolder::kNone};
}

ExprClassName ExprClass(const Expr& expr, const BlockParent& parent,
                        const BodyWalk& walk);

ExprClassName LetResultClass(std::string_view name, const BlockParent& parent,
                             const BodyWalk& walk) {
  ExprClassName cls;
  for (const ModuleItem* item : walk.mod.let_decls) {
    if (item->name == name) cls = ExprClass(*item->init_expr, parent, walk);
  }
  return cls;
}

ExprClassName CallResultClass(const Expr& callee, const BlockParent& parent,
                              const BodyWalk& walk) {
  const ModuleItem* function =
      VpiCalleeSubroutine(CallSiteOf(parent, walk), callee).decl;
  if (function != nullptr) {
    return ReturnedValue(
        function->return_type,
        callee.is_scope_resolution ? callee.lhs->text : std::string_view(),
        walk);
  }
  if (callee.kind != ExprKind::kMemberAccess) {
    return LetResultClass(callee.text, parent, walk);
  }
  const ExprClassName kOwner = callee.is_scope_resolution
                                   ? ExprClassName{callee.lhs->text, {}}
                                   : ExprClass(*callee.lhs, parent, walk);
  const std::string_view kMethod = callee.rhs->text;
  const ClassDecl* decl =
      ClassMethodCall(walk, kOwner.cls, kMethod, kOwner.package, kOwner.args)
          .owner.decl;
  if (decl == nullptr) return BuiltInResult(kOwner, kMethod);
  return ReturnedValue(VpiMethodNamed(*decl, kMethod)->return_type,
                       kOwner.package, walk);
}

ExprClassName ExprClass(const Expr& expr, const BlockParent& parent,
                        const BodyWalk& walk) {
  if (expr.kind == ExprKind::kIdentifier) {
    const PrefixVar kVar = FindPrefixVar(parent, expr.text, walk);
    return {kVar.cls, {}, kVar.args, kVar.holder != VpiBuiltInHolder::kNone};
  }
  if (expr.kind == ExprKind::kSelect) {
    ExprClassName element = ExprClass(*expr.base, parent, walk);
    element.built_in = element.cls.empty();
    return element;
  }
  if (expr.kind == ExprKind::kCall) {
    return CallResultClass(*expr.lhs, parent, walk);
  }
  if (expr.kind == ExprKind::kTernary) {
    return ExprClass(*expr.true_expr, parent, walk);
  }
  if (expr.kind == ExprKind::kBinary) {
    return ExprClass(*expr.lhs, parent, walk);
  }
  if (expr.kind == ExprKind::kCast) {
    return {
        expr.text, {}, {}, VpiFindClassDecl(walk, expr.text).decl == nullptr};
  }
  if (expr.kind != ExprKind::kMemberAccess) return {{}, {}, {}, true};
  if (expr.is_scope_resolution) {
    return PackageVarClass(walk, expr.lhs->text, expr.rhs->text);
  }
  const ExprClassName kOuter = ExprClass(*expr.lhs, parent, walk);
  const HandleType kHeld = PropertyType(walk, kOuter.cls, expr.rhs->text,
                                        kOuter.package, kOuter.args);
  return {kHeld.cls, kOuter.package, kHeld.args,
          kHeld.holder != VpiBuiltInHolder::kNone};
}

CallShape ExprCallShape(const Expr& access, const BlockParent& parent,
                        const BodyWalk& walk) {
  const std::string_view kName = access.rhs->text;
  const ExprClassName kClass = ExprClass(*access.lhs, parent, walk);
  std::vector<std::string_view> members;
  const Expr* base = access.lhs;
  while (base->kind == ExprKind::kMemberAccess && !base->is_scope_resolution) {
    members.insert(members.begin(), base->rhs->text);
    base = base->lhs;
  }
  MethodCall call;
  if (kClass.built_in) {
    call.type = vpiMethodFuncCall;
  } else {
    call =
        ClassMethodCall(walk, kClass.cls, kName, kClass.package, kClass.args);
  }
  CallShape shape = MethodShape(
      call, kName,
      VpiCallSiteExpression(base, walk.objects, CallSiteOf(parent, walk),
                            walk.calls.ctx, walk.build),
      parent.scope, walk);
  shape.prefix_members = std::move(members);
  return shape;
}

CallShape MemberChainCallShape(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk) {
  std::vector<std::string_view> names;
  if (!ChainNames(*access.lhs, names)) {
    return ExprCallShape(access, parent, walk);
  }
  const ChainHead kHead = ChainHeadVar(names, parent, walk);
  const BodyWalk kAt = kHead.WalkAt(walk);
  HandleType type{kHead.var.cls, kHead.var.vif, kHead.var.args};
  VpiObject* prefix = kHead.var.object;
  std::size_t first = kHead.used;
  const DataType* aggregate =
      first < names.size() ? VpiStructTypeOf(kAt, kHead.var.type) : nullptr;
  while (aggregate != nullptr) {
    const std::string_view kMember = names[first];
    type = StructMemberType(*aggregate, kMember, kAt);
    prefix = ChildNamed(prefix, kMember);
    ++first;
    aggregate = first < names.size()
                    ? VpiMemberStructNamed(kAt, *aggregate, kMember)
                    : nullptr;
  }
  for (std::size_t i = first; i < names.size(); ++i) {
    type = PropertyType(kAt, type.cls, names[i], type.scope, type.args);
  }
  if (!type.vif.empty()) {
    return InterfaceCallShape(kAt, type.vif, access.rhs->text);
  }
  MethodCall call;
  if (type.holder != VpiBuiltInHolder::kNone) {
    call.type = vpiMethodFuncCall;
  } else {
    call =
        ClassMethodCall(kAt, type.cls, access.rhs->text, type.scope, type.args);
    if (call.type == 0) call.type = VpiMemberBuiltInCallKind(access.rhs->text);
  }
  CallShape shape =
      MethodShape(call, access.rhs->text, prefix, parent.scope, kAt);
  if (shape.type != 0) {
    shape.prefix_members.assign(
        names.begin() + static_cast<std::ptrdiff_t>(first), names.end());
  }
  return shape;
}

std::vector<DataType> ScopeArguments(const Expr& scope) {
  std::vector<DataType> args;
  for (std::size_t i = 0; i < scope.elements.size(); ++i) {
    if (scope.elements[i] == nullptr) continue;
    DataType& arg = args.emplace_back();
    arg.kind = DataTypeKind::kNamed;
    arg.type_name = scope.elements[i]->text;
    arg.param_arg_name = scope.arg_names[i];
  }
  return args;
}

CallShape ScopedCallShape(const Expr& callee, const BlockParent& parent,
                          const BodyWalk& walk) {
  const std::string_view kName = callee.rhs->text;
  const Expr& scope = *callee.lhs;
  if (scope.kind == ExprKind::kIdentifier) {
    const VpiCalledSubroutine kSub =
        VpiCalleeSubroutine(CallSiteOf(parent, walk), callee);
    if (kSub.decl != nullptr || scope.text == "std") {
      return SubroutineCallShape(kSub, kName);
    }
    const std::vector<DataType> kArgs = ScopeArguments(scope);
    return MethodShape(ClassMethodCall(walk, scope.text, kName, {}, kArgs),
                       kName, nullptr, parent.scope, walk);
  }
  return MethodShape(
      ClassMethodCall(walk, scope.rhs->text, kName, scope.lhs->text), kName,
      nullptr, parent.scope, walk);
}

CallShape OwnMethodCallShape(const Expr& callee, const BlockParent& parent,
                             const BodyWalk& walk) {
  const VpiObject& scope = *parent.scope;
  const bool kInObject = scope.type == vpiClassObj;
  if (!kInObject && scope.type != vpiClassDefn) return {};
  const MethodCall kCall = ClassMethodCall(
      walk, kInObject ? scope.children.front()->name : scope.name, callee.text,
      walk.package);
  if (!kCall.declared) return {};
  return MethodShape(kCall, callee.text, kInObject ? parent.scope : nullptr,
                     parent.scope, walk);
}

}  // namespace

VpiCallSite CallSiteOf(const BlockParent& parent, const BodyWalk& walk) {
  return {walk.design,
          walk.mod,
          walk.prefix,
          parent.scope,
          walk.calls.subroutines,
          walk.gen_prefixes,
          [&parent, &walk](const Expr& call, VpiObject* made) {
            return ShapeExprCall(call, made, parent, walk);
          },
          walk.package,
          parent.formals};
}

int TypeVariableKind(const DataType& type, const BodyWalk& walk) {
  if (type.kind != DataTypeKind::kNamed) {
    return VpiDataTypeVariableKind(type.kind);
  }
  if (walk.package.empty() && type.scope_name.empty()) {
    return VpiNamedTypeVariableKind(walk.design, walk.mod, type.type_name);
  }
  return VpiScopedTypeVariableKind(walk.design, walk.package, type);
}

int ForeachIndexKind(const Expr* array, const BlockParent& parent,
                     const BodyWalk& walk) {
  if (array->kind != ExprKind::kIdentifier) {
    return MemberIndexKind(*array, parent, walk);
  }
  const BlockParent* where = nullptr;
  if (const Stmt* item = BlockVarDecl(parent, array->text, where)) {
    return FirstDimIndexKind(item->var_unpacked_dims, walk);
  }
  return ModuleIndexKind(walk.mod, array->text, walk);
}

VpiObject* MethodCallClassDefn(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk) {
  const ExprClassName kClass = ExprClass(*access.lhs, parent, walk);
  const VpiScopedClass kFound =
      VpiFindClassDecl(walk, kClass.cls, kClass.package);
  return VpiClassDefnOf(walk.calls.classes, kFound.decl, kFound.scope,
                        parent.scope);
}

CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk) {
  if (expr.kind == ExprKind::kSystemCall) {
    return SystemCallShape(expr, walk);
  }
  const Expr* callee = expr.kind == ExprKind::kCall ? expr.lhs : &expr;
  if (callee == nullptr) return {};
  if (callee->kind == ExprKind::kIdentifier) {
    CallShape own = OwnMethodCallShape(*callee, parent, walk);
    if (own.type != 0) return own;
    return SubroutineCallShape(
        VpiCalleeSubroutine(CallSiteOf(parent, walk), *callee), callee->text);
  }
  if (callee->kind != ExprKind::kMemberAccess) return {};
  if (callee->is_scope_resolution) {
    return ScopedCallShape(*callee, parent, walk);
  }
  if (callee->lhs->kind != ExprKind::kIdentifier) {
    return MemberChainCallShape(*callee, parent, walk);
  }
  return MethodCallShape(*callee, parent, walk);
}

}  // namespace delta
