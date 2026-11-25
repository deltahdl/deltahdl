#include "elaborator/value_scopes.h"

#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <optional>
#include <string_view>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kDeepestChain = 64;

ValueSymbol DataSymbol(const DataType& type, std::size_t dims,
                       const NameScope& scope) {
  ValueSymbol symbol;
  symbol.kind = SymbolKind::kData;
  symbol.type = &type;
  symbol.dims = dims;
  symbol.where = &scope;
  return symbol;
}

void DeclareFunction(const ModuleItem& function, NameScope& scope) {
  ValueSymbol symbol = DataSymbol(function.return_type, 0, scope);
  symbol.kind = SymbolKind::kFunction;
  scope.names.insert_or_assign(function.name, symbol);
}

void DeclareTypedef(const ModuleItem& def, NameScope& scope) {
  if (def.forward_type_kind != DataTypeKind::kImplicit) return;
  ValueSymbol symbol =
      DataSymbol(def.typedef_type, def.unpacked_dims.size(), scope);
  symbol.kind = SymbolKind::kType;
  scope.names.insert_or_assign(def.name, symbol);
}

void DeclareEnumConstants(const DataType& type, NameScope& scope) {
  for (const EnumMember& constant : type.enum_members) {
    scope.names.emplace(constant.name, DataSymbol(type, 0, scope));
  }
}

void DeclareSpecparam(std::string_view name, NameScope& scope) {
  scope.names.try_emplace(name).first->second.constant =
      ConstantKind::kSpecparam;
}

template <typename Decl>
void DeclareParamPorts(const Decl& decl, NameScope& scope) {
  for (std::size_t i = 0; i < decl.params.size(); ++i) {
    const std::string_view kName = decl.params[i].first;
    if (decl.type_param_names.contains(kName)) {
      DeclareOther(kName, scope);
    } else {
      const auto kDims = decl.param_port_unpacked_dims.find(kName);
      DeclareData(kName, decl.param_types[i],
                  kDims == decl.param_port_unpacked_dims.end()
                      ? 0
                      : kDims->second.size(),
                  scope);
    }
    scope.names[kName].constant = ConstantKind::kParameter;
  }
}

}  // namespace

void DeclareOther(std::string_view name, NameScope& scope) {
  scope.names.insert_or_assign(name, ValueSymbol{});
}

void DeclareData(std::string_view name, const DataType& type, std::size_t dims,
                 NameScope& scope) {
  scope.names.insert_or_assign(name, DataSymbol(type, dims, scope));
}

void DeclareFormals(const std::vector<FunctionArg>& formals, NameScope& scope) {
  for (const FunctionArg& formal : formals) {
    DeclareData(formal.name, formal.data_type, formal.unpacked_dims.size(),
                scope);
  }
}

void DeclareResult(const ModuleItem& function, NameScope& scope) {
  if (function.kind == ModuleItemKind::kFunctionDecl) {
    scope.names.insert_or_assign(function.name,
                                 DataSymbol(function.return_type, 0, scope));
  }
}

ValueScopes::ValueScopes(const CompilationUnit& unit) {
  for (const PackageDecl* package : unit.packages) {
    DeclareItems(package->items, packages_[package->name]);
  }
  for (const ClassDecl* cls : unit.classes) DeclareClass(*cls, unit_scope_);
  DeclareItems(unit.cu_items, unit_scope_);
  for (const auto* decls :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *decls) {
      module_names_.emplace(decl->name, decl);
      DeclareModule(*decl, unit_scope_);
    }
  }
}

void ValueScopes::DeclareModule(const ModuleDecl& decl,
                                const NameScope& outer) {
  NameScope& scope = modules_[&decl];
  scope.outer = &outer;
  DeclareParamPorts(decl, scope);
  for (const auto* ports : {&decl.ports, &decl.port_expr_objects}) {
    for (const PortDecl& port : *ports) {
      DeclareData(port.name, port.data_type, port.unpacked_dims.size(), scope);
      DeclareEnumConstants(port.data_type, scope);
    }
  }
  DeclareItems(decl.items, scope);
}

void ValueScopes::DeclareClassMember(const ClassMember& member,
                                     NameScope& scope) {
  switch (member.kind) {
    case ClassMemberKind::kProperty:
      DeclareEnumConstants(member.data_type, scope);
      DeclareData(member.name, member.data_type, member.unpacked_dims.size(),
                  scope);
      scope.names[member.name].mode =
          member.is_rand || member.is_randc ? "rand_mode" : "";
      scope.names[member.name].constant =
          member.is_param ? ConstantKind::kParameter : ConstantKind::kNone;
      break;
    case ClassMemberKind::kMethod:
      DeclareFunction(*member.method, scope);
      break;
    case ClassMemberKind::kTypedef:
      DeclareEnumConstants(member.typedef_item->typedef_type, scope);
      DeclareTypedef(*member.typedef_item, scope);
      break;
    case ClassMemberKind::kClassDecl:
      DeclareClass(*member.nested_class, scope);
      break;
    case ClassMemberKind::kConstraint:
      DeclareOther(member.name, scope);
      scope.names[member.name].mode = "constraint_mode";
      break;
    default:
      DeclareOther(member.name, scope);
      break;
  }
}

void ValueScopes::DeclareClass(const ClassDecl& cls, NameScope& scope) {
  ValueSymbol symbol;
  symbol.kind = SymbolKind::kClass;
  symbol.cls = &cls;
  scope.names.insert_or_assign(cls.name, symbol);
  NameScope& members = classes_[&cls];
  members.outer = &scope;
  members.cls = &cls;
  DeclareParamPorts(cls, members);
  for (const ClassMember* member : cls.members) {
    DeclareClassMember(*member, members);
  }
}

void ValueScopes::DeclareImport(const ImportItem& import,
                                NameScope& scope) const {
  if (import.is_wildcard) {
    scope.wildcards.push_back(import.package_name);
    return;
  }
  const ValueSymbol* imported =
      FindHere(import.item_name, PackageScope(import.package_name));
  scope.names.insert_or_assign(import.item_name,
                               imported == nullptr ? ValueSymbol{} : *imported);
}

void ValueScopes::DeclareItem(const ModuleItem& item, NameScope& scope) {
  DeclareEnumConstants(item.data_type, scope);
  DeclareEnumConstants(item.typedef_type, scope);
  switch (item.kind) {
    case ModuleItemKind::kParamDecl:
      DeclareData(item.name, item.data_type, item.unpacked_dims.size(), scope);
      scope.names[item.name].constant = ConstantKind::kParameter;
      break;
    case ModuleItemKind::kSpecparam:
      DeclareSpecparam(item.name, scope);
      scope.names[item.name].module_specparam = item.init_expr;
      break;
    case ModuleItemKind::kSpecifyBlock:
      for (const SpecifyItem* specify : item.specify_items) {
        if (specify->kind == SpecifyItemKind::kSpecparam) {
          DeclareSpecparam(specify->param_name, scope);
        }
      }
      break;
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kNetDecl:
      DeclareData(item.name, item.data_type, item.unpacked_dims.size(), scope);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kDpiImport:
      if (item.method_class.empty()) DeclareFunction(item, scope);
      break;
    case ModuleItemKind::kTypedef:
      DeclareTypedef(item, scope);
      break;
    case ModuleItemKind::kClassDecl:
      DeclareClass(*item.class_decl, scope);
      break;
    case ModuleItemKind::kImportDecl:
      DeclareImport(item.import_item, scope);
      break;
    case ModuleItemKind::kNestedModuleDecl:
      DeclareModule(*item.nested_module_decl, scope);
      break;
    case ModuleItemKind::kModuleInst:
      scope.names[item.inst_name] = {SymbolKind::kInstance,
                                     nullptr,
                                     item.inst_dims.size(),
                                     nullptr,
                                     nullptr,
                                     item.inst_module};
      break;
    default:
      if (!item.name.empty() && item.method_class.empty()) {
        scope.names.try_emplace(item.name);
      }
      break;
  }
}

void ValueScopes::DeclareItems(const std::vector<ModuleItem*>& items,
                               NameScope& scope) {
  for (const ModuleItem* item : items) DeclareItem(*item, scope);
}

void ValueScopes::DeclareStmts(const std::vector<Stmt*>& stmts,
                               NameScope& scope) {
  for (const Stmt* stmt : stmts) {
    if (stmt->kind == StmtKind::kVarDecl) {
      DeclareEnumConstants(stmt->var_decl_type, scope);
      DeclareData(stmt->var_name, stmt->var_decl_type,
                  stmt->var_unpacked_dims.size(), scope);
    } else if (stmt->kind == StmtKind::kBlockItemDecl) {
      DeclareItem(*stmt->decl_item, scope);
    }
  }
}

const NameScope& ValueScopes::PackageScope(std::string_view name) const {
  static const NameScope kNone;
  const auto kFound = packages_.find(name);
  return kFound == packages_.end() ? kNone : kFound->second;
}

const NameScope& ValueScopes::ModuleScope(const ModuleDecl& decl) const {
  return modules_.at(&decl);
}

const NameScope& ValueScopes::ClassScope(const ClassDecl& cls) const {
  return classes_.at(&cls);
}

const NameScope* ValueScopes::ModuleNamed(std::string_view name) const {
  const auto kFound = module_names_.find(name);
  return kFound == module_names_.end() ? nullptr
                                       : &ModuleScope(*kFound->second);
}

const ClassDecl* ValueScopes::ClassOfSymbol(const ValueSymbol& symbol) const {
  if (symbol.kind == SymbolKind::kClass) return symbol.cls;
  return symbol.kind == SymbolKind::kType
             ? Resolve(*symbol.type, symbol.dims, *symbol.where).cls
             : nullptr;
}

const ClassDecl* ValueScopes::ClassNamed(std::string_view name,
                                         const NameScope& scope) const {
  return ClassOfSymbol(Find(name, scope));
}

const ClassDecl* ValueScopes::ClassDeclaredAs(const DataType& named,
                                              const NameScope& scope) const {
  return FindQualified(named, scope).cls;
}

const ClassDecl* ValueScopes::BaseOf(const ClassDecl& cls) const {
  DataType base;
  base.kind = DataTypeKind::kNamed;
  base.type_name = cls.base_class;
  base.scope_name = cls.base_class_scope;
  return Resolve(base, 0, *ClassScope(cls).outer).cls;
}

const ValueSymbol* ValueScopes::FindInClass(std::string_view name,
                                            const ClassDecl& cls) const {
  static const ValueSymbol kUnknown;
  const ClassDecl* walked = &cls;
  for (int depth = 0; walked != nullptr && depth < kDeepestChain; ++depth) {
    const NameScope& members = ClassScope(*walked);
    const auto kFound = members.names.find(name);
    if (kFound != members.names.end()) return &kFound->second;
    if (walked->base_class.empty()) return nullptr;
    walked = BaseOf(*walked);
  }
  return &kUnknown;
}

const ValueSymbol* ValueScopes::FindHere(std::string_view name,
                                         const NameScope& scope) const {
  const auto kFound = scope.names.find(name);
  if (kFound != scope.names.end()) return &kFound->second;
  if (scope.cls != nullptr) {
    const ValueSymbol* member = FindInClass(name, *scope.cls);
    if (member != nullptr) return member;
  }
  for (const std::string_view kPackage : scope.wildcards) {
    const NameScope& package = PackageScope(kPackage);
    const auto kImported = package.names.find(name);
    if (kImported != package.names.end()) return &kImported->second;
  }
  return nullptr;
}

ValueSymbol ValueScopes::Find(std::string_view name,
                              const NameScope& scope) const {
  for (const NameScope* at = &scope; at != nullptr; at = at->outer) {
    if (const ValueSymbol* found = FindHere(name, *at)) return *found;
  }
  return {};
}

ValueSymbol ValueScopes::FindScoped(std::string_view prefix,
                                    std::string_view name,
                                    const NameScope& scope) const {
  const ClassDecl* cls = ClassNamed(prefix, scope);
  const ValueSymbol* found = cls != nullptr ? FindInClass(name, *cls)
                             : prefix == "$unit"
                                 ? FindHere(name, unit_scope_)
                                 : FindHere(name, PackageScope(prefix));
  return found == nullptr ? ValueSymbol{} : *found;
}

ValueSymbol ValueScopes::SymbolNamedBy(const Expr& e,
                                       const NameScope& scope) const {
  if (e.kind == ExprKind::kIdentifier) {
    return e.scope_prefix.empty() ? Find(e.text, scope)
                                  : FindScoped(e.scope_prefix, e.text, scope);
  }
  if (e.lhs->kind == ExprKind::kIdentifier && e.lhs->scope_prefix.empty()) {
    return FindScoped(e.lhs->text, e.rhs->text, scope);
  }
  return MemberOfClass(ClassOfSymbol(SymbolNamedBy(*e.lhs, scope)),
                       e.rhs->text);
}

ConstantKind ValueScopes::ConstantNamedBy(const Expr& name,
                                          const NameScope& scope) const {
  return SymbolNamedBy(name, scope).constant;
}

ConstantKind ValueScopes::ConstantNamed(std::string_view name,
                                        const NameScope& scope) const {
  return Find(name, scope).constant;
}

const Expr* ValueScopes::ModuleSpecparamValue(std::string_view name,
                                              const NameScope& scope) const {
  return Find(name, scope).module_specparam;
}

bool ValueScopes::Declares(std::string_view name,
                           const NameScope& scope) const {
  const NameScope* at = &scope;
  while (at != nullptr && FindHere(name, *at) == nullptr) at = at->outer;
  return at != nullptr;
}

ValueSymbol ValueScopes::MemberOfClass(const ClassDecl* cls,
                                       std::string_view name) const {
  const ValueSymbol* found = cls == nullptr ? nullptr : FindInClass(name, *cls);
  return found == nullptr ? ValueSymbol{} : *found;
}

ScopedValue ValueScopes::Resolve(const DataType& type, std::size_t dims,
                                 const NameScope& where) const {
  if (resolving_ == kDeepestChain) return {};
  ++resolving_;
  ScopedValue value = ResolveNames(type, dims, where);
  --resolving_;
  return value;
}

ScopedValue ValueScopes::ResolveNames(const DataType& type, std::size_t dims,
                                      const NameScope& where) const {
  ScopedValue value;
  value.where = &where;
  if (type.type_ref_expr != nullptr) {
    value = ValueOf(*type.type_ref_expr, where);
  } else if (type.kind != DataTypeKind::kNamed) {
    value.kind = type.kind;
    value.members = &type.struct_members;
    value.inside = ModuleNamed(type.type_name);
  } else {
    value = ResolveName(type, where);
  }
  value.dims += dims;
  return value;
}

ValueSymbol ValueScopes::FindQualified(const DataType& type,
                                       const NameScope& where) const {
  std::vector<std::string_view> names = type.outer_scope_names;
  if (!type.scope_name.empty()) names.push_back(type.scope_name);
  names.push_back(type.type_name);
  if (names.size() == 1) return Find(names[0], where);
  ValueSymbol found = FindScoped(names[0], names[1], where);
  for (std::size_t i = 2; i < names.size(); ++i) {
    found = MemberOfClass(ClassOfSymbol(found), names[i]);
  }
  return found;
}

ScopedValue ValueScopes::ResolveName(const DataType& type,
                                     const NameScope& where) const {
  const ValueSymbol kNamed = FindQualified(type, where);
  ScopedValue value;
  if (kNamed.kind == SymbolKind::kType) {
    value = Resolve(*kNamed.type, kNamed.dims, *kNamed.where);
  } else {
    value.cls = kNamed.cls;
    value.inside = ModuleNamed(type.type_name);
    value.std_class = type.type_name;
  }
  if (type.packed_dim_left != nullptr) {
    value.packed += 1 + type.extra_packed_dims.size();
  }
  return value;
}

ScopedValue ValueScopes::ValueOfSymbol(const ValueSymbol& symbol) const {
  if (symbol.kind == SymbolKind::kValue) return symbol.value;
  ScopedValue value;
  if (symbol.type != nullptr) {
    value = Resolve(*symbol.type, symbol.dims, *symbol.where);
  } else {
    value.dims = symbol.dims;
    value.inside = ModuleNamed(symbol.module);
  }
  value.mode = symbol.mode;
  return value;
}

std::optional<ScopedValue> ValueScopes::StructMemberOf(
    const ScopedValue& holder, std::string_view name) const {
  const auto kFound =
      std::ranges::find(*holder.members, name, &StructMember::name);
  if (kFound == holder.members->end()) return std::nullopt;
  const std::size_t kDims = kFound->unpacked_dims.size();
  if (kFound->nested_type != nullptr) {
    return Resolve(*kFound->nested_type, kDims, *holder.where);
  }
  DataType written;
  written.kind = kFound->type_kind;
  written.type_name = kFound->type_name;
  written.scope_name = kFound->scope_name;
  written.outer_scope_names = kFound->outer_scope_names;
  written.packed_dim_left = kFound->packed_dim_left;
  written.extra_packed_dims = kFound->extra_packed_dims;
  ScopedValue value = Resolve(written, kDims, *holder.where);
  if (value.members == &written.struct_members) value.members = nullptr;
  return value;
}

std::optional<ScopedValue> ValueScopes::MemberOf(const ScopedValue& holder,
                                                 std::string_view name) const {
  if (holder.dims != 0) return std::nullopt;
  const ValueSymbol* found = nullptr;
  if (holder.cls != nullptr) {
    found = FindInClass(name, *holder.cls);
  } else if (holder.inside != nullptr) {
    found = FindHere(name, *holder.inside);
  } else if (holder.members != nullptr) {
    return StructMemberOf(holder, name);
  }
  if (found == nullptr) return std::nullopt;
  return ValueOfSymbol(*found);
}

namespace {

ScopedValue PlainValue(DataTypeKind kind) {
  ScopedValue value;
  value.kind = kind;
  return value;
}

using Names = std::initializer_list<std::string_view>;

bool Among(std::string_view name, Names names) {
  return std::ranges::find(names, name) != names.end();
}

MethodResult ArrayMethod(const ScopedValue& array, std::string_view name,
                         bool has_with) {
  ScopedValue element = array;
  --element.dims;
  if (Among(name, {"sum", "product", "and", "or", "xor"})) {
    return {true, has_with ? ScopedValue{} : element};
  }
  ScopedValue queue = element;
  if (Among(name,
            {"min", "max", "unique", "find", "find_first", "find_last"})) {
    queue.dims = element.dims + 1;
    return {true, queue};
  }
  if (Among(name, {"unique_index", "find_index", "find_first_index",
                   "find_last_index", "map"})) {
    queue = PlainValue(name == "map" ? DataTypeKind::kImplicit
                                     : DataTypeKind::kInt);
    queue.dims = 1;
    return {true, queue};
  }
  if (Among(name, {"size", "num"}))
    return {true, PlainValue(DataTypeKind::kInt)};
  return {Among(name, {"pop_front", "pop_back"}), element};
}

MethodResult StringMethod(std::string_view name) {
  if (Among(name, {"toupper", "tolower"})) {
    return {true, PlainValue(DataTypeKind::kString)};
  }
  return {Among(name, {"len", "atoi", "atohex", "atooct", "atobin", "atoreal"}),
          PlainValue(DataTypeKind::kInt)};
}

MethodResult HandleMethod(const ScopedValue& handle, std::string_view name) {
  const bool kProcess = handle.std_class == "process";
  if (kProcess && name == "status") {
    return {true, PlainValue(DataTypeKind::kEnum)};
  }
  if (name == "get_randstate") {
    return {kProcess || handle.cls != nullptr,
            PlainValue(DataTypeKind::kString)};
  }
  return {(handle.cls != nullptr && name == "randomize") ||
              (handle.std_class == "mailbox" && name == "num") ||
              (handle.std_class == "semaphore" && name == "try_get"),
          PlainValue(DataTypeKind::kInt)};
}

MethodResult EnumMethod(const ScopedValue& receiver, std::string_view name) {
  if (Among(name, {"first", "last", "next", "prev"})) return {true, receiver};
  const bool kName = name == "name";
  return {kName || name == "num",
          PlainValue(kName ? DataTypeKind::kString : DataTypeKind::kInt)};
}

}  // namespace

bool IsBuiltinMethodNameWithoutArguments(std::string_view name) {
  ScopedValue array;
  array.dims = 1;
  return Among(name, {"index", "triggered", "randomize", "get_randstate",
                      "rand_mode", "constraint_mode", "status", "try_get"}) ||
         ArrayMethod(array, name, false).is_method ||
         StringMethod(name).is_method || EnumMethod(array, name).is_method;
}

MethodResult ValueScopes::MethodOn(const ScopedValue& receiver,
                                   std::string_view name, bool has_with) const {
  if (MemberOf(receiver, name).has_value()) return {};
  if (receiver.iterator && name == "index") {
    return {true, PlainValue(DataTypeKind::kInt)};
  }
  if (!receiver.mode.empty() && receiver.mode == name) {
    return {true, PlainValue(DataTypeKind::kInt)};
  }
  if (receiver.dims != 0) return ArrayMethod(receiver, name, has_with);
  if (receiver.packed != 0) return {};
  switch (receiver.kind) {
    case DataTypeKind::kString:
      return StringMethod(name);
    case DataTypeKind::kEnum:
      return EnumMethod(receiver, name);
    case DataTypeKind::kEvent:
      return {name == "triggered", PlainValue(DataTypeKind::kBit)};
    default:
      return HandleMethod(receiver, name);
  }
}

ScopedValue ValueScopes::ValueOfIdentifier(const Expr& e,
                                           const NameScope& scope) const {
  if (e.text != "this" && e.text != "super") {
    return ValueOfSymbol(SymbolNamedBy(e, scope));
  }
  const NameScope* at = &scope;
  while (at != nullptr && at->cls == nullptr) at = at->outer;
  ScopedValue value;
  if (at != nullptr) value.cls = e.text == "this" ? at->cls : BaseOf(*at->cls);
  return value;
}

ScopedValue ValueScopes::ValueOfSelect(const Expr& e,
                                       const NameScope& scope) const {
  ScopedValue value = ValueOf(*e.base, scope);
  std::size_t& levels = value.dims != 0 ? value.dims : value.packed;
  if (levels == 0) return {};
  if (e.index_end == nullptr) --levels;
  return value;
}

ScopedValue ValueScopes::ValueOfAccess(const Expr& access, bool has_with,
                                       const NameScope& scope) const {
  const ScopedValue kHolder = ValueOf(*access.lhs, scope);
  const std::optional<ScopedValue> kMember =
      MemberOf(kHolder, access.rhs->text);
  return kMember ? *kMember
                 : MethodOn(kHolder, access.rhs->text, has_with).value;
}

ScopedValue ValueScopes::ValueOfCast(const Expr& cast,
                                     const NameScope& scope) const {
  if (cast.text == "string") return PlainValue(DataTypeKind::kString);
  return cast.rhs == nullptr ? ScopedValue{} : ValueOf(*cast.rhs, scope);
}

ScopedValue ValueScopes::ValueOfConcatenation(const Expr& e,
                                              const NameScope& scope) const {
  for (const Expr* element : e.elements) {
    ScopedValue value = ValueOf(*element, scope);
    if (value.kind == DataTypeKind::kString && value.dims == 0) return value;
  }
  return {};
}

ScopedValue ValueScopes::ValueOfName(const Expr& name, const Expr& written,
                                     const NameScope& scope) const {
  switch (name.kind) {
    case ExprKind::kIdentifier:
      return ValueOfIdentifier(name, scope);
    case ExprKind::kSelect:
      return ValueOfSelect(name, scope);
    case ExprKind::kMemberAccess:
      return name.is_scope_resolution
                 ? ValueOfSymbol(SymbolNamedBy(name, scope))
                 : ValueOfAccess(name, written.with_expr != nullptr, scope);
    default:
      return {};
  }
}

ScopedValue ValueScopes::ValueOf(const Expr& e, const NameScope& scope) const {
  switch (e.kind) {
    case ExprKind::kCast:
      return ValueOfCast(e, scope);
    case ExprKind::kTernary:
      return ValueOf(*e.true_expr, scope);
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return ValueOfConcatenation(e, scope);
    case ExprKind::kSystemCall:
      return e.callee == "$sformatf" ? PlainValue(DataTypeKind::kString)
                                     : ScopedValue{};
    case ExprKind::kCall:
      return ValueOfName(*e.lhs, e, scope);
    default:
      return ValueOfName(e, e, scope);
  }
}

void ValueScopes::DeclareIterator(const Expr& call, const NameScope& scope,
                                  NameScope& with) const {
  const Expr* access = call.kind == ExprKind::kCall ? call.lhs : &call;
  for (const Expr* arg : call.args) DeclareOther(arg->text, with);
  if (access->kind != ExprKind::kMemberAccess) return;
  ValueSymbol symbol;
  symbol.kind = SymbolKind::kValue;
  symbol.value = ValueOf(*access->lhs, scope);
  if (symbol.value.dims == 0) return;
  --symbol.value.dims;
  symbol.value.iterator = true;
  const std::string_view kName =
      call.args.empty() ? std::string_view("item") : call.args[0]->text;
  with.names.insert_or_assign(kName, symbol);
}

}  // namespace delta
