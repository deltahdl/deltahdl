#include "elaborator/elaborator_call_targets.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <initializer_list>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_member_names.h"
#include "elaborator/elaborator_enclosing_subroutines.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/operator_result_members.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// A variable's declaration: the type it was declared with and the number of
// unpacked dimensions it writes after its name (§7.4).
struct DeclaredVar {
  const DataType* type = nullptr;
  std::size_t dims = 0;
};

// The names a walk of one module's procedures sees as variables or nets: the
// module's own, and those each block around the statement walked declares,
// the innermost last (§23.9); the other names the module itself declares, or
// imports as data, which a call statement cannot call; the tasks and
// functions the module declares; and, first, whether the scope or a module
// enclosing it sees a name at all.
struct DataScope {
  const std::function<bool(std::string_view)>& visible;
  const CompilationUnit& unit;
  const std::vector<ModuleItem*>& items;
  // The declaration of each variable of the module and of a block around the
  // statement walked.
  std::unordered_map<std::string_view, DeclaredVar> module_vars = {};
  // In a method of a class, the declaration of each property the class
  // declares or inherits (§8.13), which hides a variable of the scope around
  // the class of its name and is what `this` reaches (§8.11).
  std::unordered_map<std::string_view, DeclaredVar> properties = {};
  std::unordered_set<std::string_view> module = {};
  std::vector<std::pair<std::string_view, DeclaredVar>> blocks = {};
  std::unordered_set<std::string_view> uncallable = {};
  std::unordered_set<std::string_view> subroutines = {};
  // The kind of scope `items` belong to, which the types of the scope's
  // variables are looked up from.
  SiteKind site = SiteKind::kModule;
  // The names a type of the scope may be written as without naming a class of
  // the scope around it: a type parameter of the module, and in a method a
  // type parameter, typedef or nested class of its class or a class it
  // extends.
  std::unordered_set<std::string_view> local_types = {};
  // The classes of the unit known by their name alone, shared by every scope
  // copied from the one that made them.
  std::shared_ptr<const SoleClassIndex> classes = nullptr;
  // In a method of a class, the class, whose methods a call by a name alone
  // calls first (§8.13).
  const ClassDecl* cls = nullptr;

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::any_of(blocks, [name](const auto& declared) {
             return declared.first == name;
           });
  }

  // The declaration of the variable `name` names in the scope, the innermost
  // block's first, then a property of the class a method's scope is in, then
  // the module's (§23.9); null for a name no variable bears.
  const DeclaredVar* Declared(std::string_view name) const {
    for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
      if (it->first == name) return &it->second;
    }
    for (const auto* vars : {&properties, &module_vars}) {
      const auto kFound = vars->find(name);
      if (kFound != vars->end()) return &kFound->second;
    }
    return nullptr;
  }

  // §8.11: the declaration of the property `name` names through `this`; null
  // for a name no property of the class bears, and outside a method.
  const DeclaredVar* Property(std::string_view name) const {
    const auto kFound = properties.find(name);
    return kFound == properties.end() ? nullptr : &kFound->second;
  }
};

// Reports a call of `name` written at `loc` where the scope sees the name as
// a variable or a net.
void ReportIfData(std::string_view name, SourceLoc loc, const DataScope& scope,
                  DiagEngine& diag) {
  if (!scope.Names(name)) return;
  diag.Error(loc,
             std::format("'{}' names a variable or a net, and a call names a "
                         "task or a function",
                         name),
             Subclause("A.8.2"));
}

// The plain name the call `expr` calls, null where `expr` is no call by a
// plain name. A constructor call is none: its `lhs` is the object a shallow
// copy copies, `new src` (§8.12).
const Expr* NamedCallee(const Expr& expr) {
  const bool kNamed = expr.kind == ExprKind::kCall && expr.lhs != nullptr &&
                      expr.text != "new" &&
                      expr.lhs->kind == ExprKind::kIdentifier;
  return kNamed ? expr.lhs : nullptr;
}

// A.6.9: a call statement, `x;` or `x(...);`, whose name the scope declares
// as no task or function: a variable or a net (A.8.2), or anything else the
// module declares or imports as data, such as a parameter, a let or a
// sequence. A call with an argument list naming nothing the scope, the
// compilation unit or a module enclosing an instance of the module sees
// (§23.8) is an undeclared identifier (§23.9); a bare one is the scope rules'
// report.
void ReportStatementCall(const Stmt& stmt, const DataScope& scope,
                         DiagEngine& diag) {
  const bool kBare = stmt.expr->kind == ExprKind::kIdentifier;
  const Expr* callee = kBare ? stmt.expr : NamedCallee(*stmt.expr);
  if (callee == nullptr) return;
  const std::string_view kName = callee->text;
  if (scope.Names(kName)) {
    // A call with an argument list naming data is the expression walk's.
    if (kBare) ReportIfData(kName, stmt.range.start, scope, diag);
    return;
  }
  if (scope.uncallable.contains(kName)) {
    diag.Error(stmt.range.start,
               std::format("'{}' names no task or function, and a call "
                           "statement calls one",
                           kName),
               Subclause("A.6.9"));
    return;
  }
  if (kBare || scope.subroutines.contains(kName) || scope.visible(kName)) {
    return;
  }
  diag.Error(stmt.range.start, std::format("undeclared identifier '{}'", kName),
             Subclause("23.9"));
}

// Whether the interface `unit` declares under `iface` declares a task or a
// function `name`.
bool InterfaceDeclaresSubroutine(const CompilationUnit& unit,
                                 std::string_view iface,
                                 std::string_view name) {
  bool declares = false;
  for (const ModuleDecl* decl : unit.interfaces) {
    if (decl->name != iface) continue;
    for (const ModuleItem* item : decl->items) {
      if (IsSubroutineItem(*item) && item->name == name) declares = true;
    }
  }
  return declares;
}

// The interface a value declared with `type` refers to an instance of, where
// it is a virtual interface (§25.9); empty for any other type.
std::string_view VifInterface(const DataType& type) {
  return type.kind == DataTypeKind::kVirtualInterface ? type.type_name
                                                      : std::string_view();
}

// A type written in a scope, the site it is written at, and the unpacked
// dimensions the typedefs it was reached through write after their names
// (§6.18, §7.4).
struct SitedType {
  const DataType* type = nullptr;
  TypeSite site = {};
  std::size_t dims = 0;
};

// §6.18 with §26.3: the type the type `type` of a variable of the module
// stands for, through each typedef it is written as, each typedef's own type
// looked up as the scope declaring that typedef sees it before the typedef.
// Each step reaches a declaration before the last in its scope, or a scope
// around it or a package, which leads to no module; a package reaches only
// one declared before it, a typedef naming no type the parser has not yet
// read, so the walk ends.
SitedType ThroughTypedefs(const DataScope& scope, const DataType& type) {
  SitedType named{&type, {&scope.items, scope.items.size(), scope.site}};
  for (FoundItem def = TypedefOf(scope.unit, named.site, *named.type);
       def.item != nullptr;
       def = TypedefOf(scope.unit, named.site, *named.type)) {
    named = {&def.item->typedef_type, def.site,
             named.dims + def.item->unpacked_dims.size()};
  }
  return named;
}

// §8.3 with §7.4: the class declaration whose handle the element of the
// variable `var` that `selects` selects reach holds, through the typedefs its
// type is written as, their unpacked dimensions counted with the variable's
// own (§6.18); null where none is, and where the selects reach no element.
const ClassDecl* ClassNamed(const DataScope& scope, const DeclaredVar& var,
                            std::size_t selects) {
  const auto [named, site, dims] = ThroughTypedefs(scope, *var.type);
  if (var.dims + dims != selects) return nullptr;
  if (!named->scope_name.empty()) {
    return ScopedClass(scope.unit, site, named->scope_name, named->type_name);
  }
  return ClassIn(scope.unit, site, named->type_name);
}

// The expression the selects in front of `e` select from, the number of them
// counted into `selects`: `va` of va[0][1], two.
const Expr& SelectRoot(const Expr& e, std::size_t& selects) {
  const Expr* root = &e;
  while (root->kind == ExprKind::kSelect && root->base != nullptr) {
    ++selects;
    root = root->base;
  }
  return *root;
}

// §8.4: the property of the class a variable of the scope holds a handle of
// that the member access `access`, h.vif, names; null for any other
// expression and for a name the class declares no property under.
const ClassMember* HandleProperty(const Expr& access, const DataScope& scope) {
  if (access.kind != ExprKind::kMemberAccess || access.is_scope_resolution ||
      access.lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  const DeclaredVar* holder = scope.Declared(access.lhs->text);
  const ClassDecl* cls =
      holder == nullptr ? nullptr : ClassNamed(scope, *holder, 0);
  if (cls == nullptr) return nullptr;
  const ClassMember* found = nullptr;
  for (const ClassMember* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty &&
        member->name == access.rhs->text) {
      found = member;
    }
  }
  return found;
}

// The variable the root `root` of a prefix names: the innermost declaration
// of a plain name, v, or a property of the class whose method writes the
// prefix, reached through `this`, this.vif (§8.11); null for anything else.
const DeclaredVar* RootVar(const Expr& root, const DataScope& scope) {
  if (root.kind == ExprKind::kIdentifier) return scope.Declared(root.text);
  const bool kThis =
      root.kind == ExprKind::kMemberAccess && !root.is_scope_resolution &&
      root.lhs->kind == ExprKind::kIdentifier && root.lhs->text == "this";
  return kThis ? scope.Property(root.rhs->text) : nullptr;
}

// §25.9: the interface the virtual interface `prefix` names refers to an
// instance of: a variable of the module or of a block around the call, v, a
// property of the class whose method writes the call, vif or this.vif, or a
// property of the class a variable holds a handle of, h.vif, or an element of
// an array of any of them, one select per unpacked dimension (§7.4), va[0] or
// h.vifs[0]; empty for anything else.
std::string_view VifOf(const Expr& prefix, const DataScope& scope) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(prefix, selects);
  if (const DeclaredVar* var = RootVar(root, scope)) {
    return var->dims == selects ? VifInterface(*var->type) : std::string_view();
  }
  const ClassMember* property = HandleProperty(root, scope);
  return property != nullptr && property->unpacked_dims.size() == selects
             ? VifInterface(property->data_type)
             : std::string_view();
}

// §8.11: the property of the class whose method writes `root` that `root`
// names, vif where no local variable of the method hides it, or this.vif;
// null for anything else.
const DeclaredVar* OwnProperty(const Expr& root, const DataScope& scope) {
  if (root.kind != ExprKind::kIdentifier) return RootVar(root, scope);
  const DeclaredVar* property = scope.Property(root.text);
  return property != nullptr && scope.Declared(root.text) == property ? property
                                                                      : nullptr;
}

// The declaration of the class property `root` names: one of the class whose
// method writes it, vif or this.vif, or one of the class a variable holds a
// handle of, h.vif; one with no type for anything else.
DeclaredVar SelectedProperty(const Expr& root, const DataScope& scope) {
  if (const DeclaredVar* own = OwnProperty(root, scope)) return *own;
  const ClassMember* held = HandleProperty(root, scope);
  return held == nullptr
             ? DeclaredVar{}
             : DeclaredVar{&held->data_type, held->unpacked_dims.size()};
}

// §8.4: the class whose handle `e` holds, where the scope tells it for
// certain: a variable of the scope, or an element of one, one select per
// unpacked dimension (§7.4), whose type names a class, or a property of such a
// class (§8.5), h.p or h.p[0]; null for anything else.
const ClassDecl* HandleClass(const Expr& e, const DataScope& scope) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(e, selects);
  if (root.kind == ExprKind::kIdentifier) {
    const DeclaredVar* var = scope.Declared(root.text);
    const bool kClassType = var != nullptr &&
                            var->type->kind == DataTypeKind::kNamed &&
                            !scope.local_types.contains(var->type->type_name);
    return kClassType ? ClassNamed(scope, *var, selects) : nullptr;
  }
  if (root.kind != ExprKind::kMemberAccess) return nullptr;
  const ClassDecl* holder = HandleClass(*root.lhs, scope);
  return holder == nullptr
             ? nullptr
             : scope.classes->PropertyClass(*holder, root.rhs->text, selects);
}

// §8.5 and §8.6: a member access `access`, h.m, applied to a handle of a class
// that, with the classes it extends or implements, declares nothing `m`
// names; reported under `rule`, §8.6 where the access is what a call calls and
// §8.5 otherwise.
void ReportUndeclaredMember(const Expr& access, std::string_view rule,
                            const DataScope& scope, DiagEngine& diag) {
  const ClassDecl* cls = HandleClass(*access.lhs, scope);
  std::unordered_set<std::string_view> names;
  if (cls == nullptr || !scope.classes->SelectableNames(*cls, names) ||
      names.contains(access.rhs->text)) {
    return;
  }
  diag.Error(access.rhs->range.start,
             std::format("class '{}' has no member named '{}'", cls->name,
                         access.rhs->text),
             Subclause(rule));
}

// §6.16 and §6.19.5: the built-in methods of a string and of an enumeration.
constexpr std::string_view kStringMethods[] = {
    "len",      "putc",   "getc",   "toupper", "tolower", "compare",
    "icompare", "substr", "atoi",   "atohex",  "atooct",  "atobin",
    "atoreal",  "itoa",   "hextoa", "octtoa",  "bintoa",  "realtoa"};
constexpr std::string_view kEnumMethods[] = {"first", "last", "next",
                                             "prev",  "num",  "name"};

// §8.13: the member of kind `kind` named `name` the class `cls` or the nearest
// class it extends declares; null where none does. Each base is looked up from
// the scope's site; no class is its own ancestor (§8.13), so the walk ends.
const ClassMember* ChainMember(const ClassDecl& cls, ClassMemberKind kind,
                               std::string_view name, const DataScope& scope) {
  const TypeSite kSite{&scope.items, scope.items.size(), scope.site};
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = ClassIn(scope.unit, kSite, walked->base_class)) {
    for (const ClassMember* member : walked->members) {
      if (member->kind == kind && member->name == name) return member;
    }
  }
  return nullptr;
}

// §6.18: the kind of the type `type` stands for, through the typedefs the
// scope sees it written as, where it is a single value; kImplicit where those
// typedefs make it an array (§7.4).
DataTypeKind ScalarKind(const DataScope& scope, const DataType& type) {
  const SitedType kNamed = ThroughTypedefs(scope, type);
  return kNamed.dims == 0 ? kNamed.type->kind : DataTypeKind::kImplicit;
}

// §13.4.1 with §8.13: the kind of type the method `method` of the class `cls`
// returns as a single value: a name, written without a scope, that the class
// or a class it extends declares as a type is its typedef there, and any other
// type as the scope sees it; kImplicit where the class's name is a type
// parameter or a nested class, or its typedef writes unpacked dimensions.
DataTypeKind MethodResultKind(const ModuleItem& method, const ClassDecl& cls,
                              const DataScope& scope) {
  const DataType* type = &method.return_type;
  std::unordered_set<std::string_view> local;
  scope.classes->AddLocalTypes(cls, local);
  if (type->kind == DataTypeKind::kNamed && type->scope_name.empty() &&
      local.contains(type->type_name)) {
    const ClassMember* def =
        ChainMember(cls, ClassMemberKind::kTypedef, type->type_name, scope);
    if (def == nullptr || !def->typedef_item->unpacked_dims.empty()) {
      return DataTypeKind::kImplicit;
    }
    type = &def->typedef_item->typedef_type;
  }
  return ScalarKind(scope, *type);
}

// §G.1: the class of the std package whose handle `e` holds, where the scope
// tells it for certain: a variable of the scope declared as one, process p,
// where no class of the design takes the name, or a call of a method of one
// returning one, process::self() or p.self(); none for anything else.
std::optional<StdPackageMember> StdClassOf(const Expr& e,
                                           const DataScope& scope) {
  const Expr* callee = e.kind == ExprKind::kCall ? e.lhs : nullptr;
  if (callee != nullptr && callee->kind == ExprKind::kMemberAccess) {
    const std::optional<StdPackageMember> kOwner =
        callee->is_scope_resolution ? StdPackageMemberNamed(callee->lhs->text)
                                    : StdClassOf(*callee->lhs, scope);
    const StdMethodPrototype* prototype =
        kOwner ? StdMethodNamed(*kOwner, callee->rhs->text) : nullptr;
    return prototype == nullptr ? std::nullopt
                                : StdPackageMemberNamed(prototype->return_type);
  }
  const DeclaredVar* var =
      e.kind == ExprKind::kIdentifier ? scope.Declared(e.text) : nullptr;
  if (var == nullptr || var->type->kind != DataTypeKind::kNamed ||
      ClassNamed(scope, *var, 0) != nullptr) {
    return std::nullopt;
  }
  return StdPackageMemberNamed(var->type->type_name);
}

// §G.3 to §G.7: the kind of type the method `method` of the std class `owner`
// returns: a string, get_randstate()'s, or process's enumeration state,
// status()'s (§9.7); kImplicit for any other.
DataTypeKind StdResultKind(StdPackageMember owner, std::string_view method) {
  const StdMethodPrototype* prototype = StdMethodNamed(owner, method);
  const std::string_view kReturns =
      prototype == nullptr ? std::string_view() : prototype->return_type;
  if (kReturns == "string") return DataTypeKind::kString;
  return kReturns == "state" ? DataTypeKind::kEnum : DataTypeKind::kImplicit;
}

// §13.4.1 with §23.9: the kind of type the call of `name`, written alone,
// returns: in a method of a class, a method the class or a class it extends
// declares (§8.13), else a function the items of the scope declare; kImplicit
// where neither does.
DataTypeKind PlainCallKind(std::string_view name, const DataScope& scope) {
  const ClassMember* method =
      scope.cls == nullptr
          ? nullptr
          : ChainMember(*scope.cls, ClassMemberKind::kMethod, name, scope);
  if (method != nullptr) {
    return MethodResultKind(*method->method, *scope.cls, scope);
  }
  for (const ModuleItem* item : scope.items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name) {
      return ScalarKind(scope, item->return_type);
    }
  }
  return DataTypeKind::kImplicit;
}

// §13.4.1: the kind of type the call whose callee is `callee` returns as a
// single value, where the scope tells it for certain: a function or method
// called by its name alone, f(); a method of a std class (§G.3 to §G.7),
// p.status(); and a method of the class a handle holds, h.get(); kImplicit
// for any other call.
DataTypeKind CallResultKind(const Expr& callee, const DataScope& scope) {
  if (callee.kind != ExprKind::kMemberAccess) {
    return PlainCallKind(callee.text, scope);
  }
  if (callee.is_scope_resolution) return DataTypeKind::kImplicit;
  const std::string_view kMethod = callee.rhs->text;
  if (const auto kStd = StdClassOf(*callee.lhs, scope)) {
    return StdResultKind(*kStd, kMethod);
  }
  const ClassDecl* cls = HandleClass(*callee.lhs, scope);
  const ClassMember* method =
      cls == nullptr
          ? nullptr
          : ChainMember(*cls, ClassMemberKind::kMethod, kMethod, scope);
  return method == nullptr ? DataTypeKind::kImplicit
                           : MethodResultKind(*method->method, *cls, scope);
}

// The value a member access is applied to, as far as the scope tells it: the
// kind of its type, how a report names it, and whether it is a property of
// the class whose method writes it, which may be random (§18.8).
struct AppliedValue {
  DataTypeKind kind = DataTypeKind::kImplicit;
  std::string named;
  bool property = false;
};

// The value `root`, written `selects` selects in front of a member access,
// stands for: a variable of the scope or an element of one, one select per
// unpacked dimension its declaration and its typedefs write (§6.18, §7.4), or
// the result of a call (§13.4.1).
AppliedValue ValueOf(const Expr& root, std::size_t selects,
                     const DataScope& scope) {
  AppliedValue value;
  const DeclaredVar* var =
      root.kind == ExprKind::kIdentifier ? scope.Declared(root.text) : nullptr;
  const Expr* callee =
      root.kind == ExprKind::kCall && selects == 0 ? root.lhs : nullptr;
  if (var != nullptr) {
    const SitedType kNamed = ThroughTypedefs(scope, *var->type);
    if (var->dims + kNamed.dims == selects) value.kind = kNamed.type->kind;
    value.named = std::format("'{}'", root.text);
    value.property = scope.Property(root.text) == var;
  } else if (callee != nullptr) {
    value.kind = CallResultKind(*callee, scope);
    const std::string_view kCalled = callee->kind == ExprKind::kMemberAccess
                                         ? callee->rhs->text
                                         : callee->text;
    value.named = std::format("that '{}()' returns", kCalled);
  }
  return value;
}

// §6.16 and §6.19.5: a member access `access`, s.m or e.m, applied to a string
// or an enumeration (ValueOf), naming none of its type's built-in methods, and
// §23.7 a): one applied to an integral or real value, which has none. A random
// property of a class, but a string, also has rand_mode (§18.8).
void ReportNoBuiltInMethod(const Expr& access, const DataScope& scope,
                           DiagEngine& diag) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(*access.lhs, selects);
  const AppliedValue kValue = ValueOf(root, selects, scope);
  const bool kString = kValue.kind == DataTypeKind::kString;
  const bool kBare = IsMemberlessKind(kValue.kind);
  if (!kString && !kBare && kValue.kind != DataTypeKind::kEnum) return;
  const std::string_view kName = access.rhs->text;
  using Methods = std::span<const std::string_view>;
  const Methods kMethods = kString ? Methods(kStringMethods)
                           : kBare ? Methods()
                                   : Methods(kEnumMethods);
  if (std::ranges::find(kMethods, kName) != kMethods.end() ||
      (!kString && kName == "rand_mode" && kValue.property))
    return;
  constexpr const char* kNouns[] = {"string", "integral or real value",
                                    "enumeration"};
  constexpr const char* kRules[] = {"6.16", "23.7", "6.19.5"};
  const int kWhich = kString ? 0 : (kBare ? 1 : 2);
  diag.Error(access.rhs->range.start,
             std::format("'{}' is not a built-in method of the {} {}", kName,
                         kNouns[kWhich], kValue.named),
             Subclause(kRules[kWhich]));
}

// §25.9 with §7.4: a select `select` into a class property that is a virtual
// interface, past the property's unpacked dimensions, vif[0], this.vif[0] or
// h.vif[0], which selects into a virtual interface; reported once, at the
// first select past them.
void ReportPropertyVifSelect(const Expr& select, const DataScope& scope,
                             DiagEngine& diag) {
  std::size_t selects = 0;
  const DeclaredVar kProperty =
      SelectedProperty(SelectRoot(select, selects), scope);
  if (kProperty.type == nullptr ||
      kProperty.type->kind != DataTypeKind::kVirtualInterface ||
      kProperty.dims + 1 != selects) {
    return;
  }
  diag.Error(select.range.start, "bit-select on virtual interface is illegal",
             Subclause("25.9"));
}

// §25.9: a call `call` through a virtual interface, v.t(), naming no task or
// function the interface declares.
void ReportVifCall(const Expr& call, const DataScope& scope, DiagEngine& diag) {
  const Expr& callee = *call.lhs;
  if (callee.kind != ExprKind::kMemberAccess || callee.is_scope_resolution) {
    return;
  }
  const std::string_view kIface = VifOf(*callee.lhs, scope);
  if (kIface.empty() ||
      InterfaceDeclaresSubroutine(scope.unit, kIface, callee.rhs->text)) {
    return;
  }
  diag.Error(call.range.start,
             std::format("'{}' names no task or function of interface '{}'",
                         callee.rhs->text, kIface),
             Subclause("25.9"));
}

// Each call by a plain name `expr` holds, itself included, each call through a
// virtual interface, each select into a class property that is one, and each
// member access naming nothing its class, its string or enumeration type or
// the operator result it is applied to has, `rule` being the subclause one
// `expr` itself makes on a class is reported under. A scope resolution, C::m or
// p::m, selects from no value.
void CheckExprCalls(const Expr* expr, const DataScope& scope, DiagEngine& diag,
                    std::string_view rule = "8.5") {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution) {
    ReportUndeclaredMember(*expr, rule, scope, diag);
    ReportNoBuiltInMethod(*expr, scope, diag);
    ReportOperatorResultMember(
        *expr, [&scope](const Expr& e) { return ValueOf(e, 0, scope).kind; },
        kStringMethods, diag);
  }
  if (const Expr* callee = NamedCallee(*expr)) {
    ReportIfData(callee->text, expr->range.start, scope, diag);
  }
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr) {
    ReportVifCall(*expr, scope, diag);
  }
  if (expr->kind == ExprKind::kSelect)
    ReportPropertyVifSelect(*expr, scope, diag);
  const Expr* called = expr->kind == ExprKind::kCall ? expr->lhs : nullptr;
  ForEachExprChild(expr, [&](const Expr* child) {
    CheckExprCalls(child, scope, diag, child == called ? "8.6" : "8.5");
  });
}

// The calls `stmt` and the statements it holds make by a plain name: a bare
// call statement, `x;`, and each call an expression of theirs holds, with the
// variables a block declares in scope over the statements the block holds.
void CheckStmtCalls(const Stmt* stmt, DataScope& scope, DiagEngine& diag) {
  if (stmt == nullptr) return;
  const std::size_t kOuter = scope.blocks.size();
  if (stmt->kind == StmtKind::kBlock || stmt->kind == StmtKind::kFork) {
    const std::vector<Stmt*>& items =
        stmt->kind == StmtKind::kFork ? stmt->fork_stmts : stmt->stmts;
    for (const Stmt* item : items) {
      if (item->kind == StmtKind::kVarDecl) {
        scope.blocks.emplace_back(
            item->var_name,
            DeclaredVar{&item->var_decl_type, item->var_unpacked_dims.size()});
      }
    }
  }
  if (stmt->kind == StmtKind::kExprStmt) {
    ReportStatementCall(*stmt, scope, diag);
  }
  ForEachChildExpr(
      stmt, [&](const Expr* expr) { CheckExprCalls(expr, scope, diag); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CheckStmtCalls(sub, scope, diag); });
  scope.blocks.resize(kOuter);
}

// §13.3: each call the body of the task or function `item` writes, the
// subroutine's formal arguments and the variables its body declares in scope
// over its statements as a block's are (§23.9).
void CheckSubroutineCalls(const ModuleItem& item, DataScope& scope,
                          DiagEngine& diag) {
  const std::size_t kOuter = scope.blocks.size();
  for (const FunctionArg& arg : item.func_args) {
    scope.blocks.emplace_back(
        arg.name, DeclaredVar{&arg.data_type, arg.unpacked_dims.size()});
  }
  for (const Stmt* stmt : item.func_body_stmts) {
    if (stmt->kind == StmtKind::kVarDecl) {
      scope.blocks.emplace_back(
          stmt->var_name,
          DeclaredVar{&stmt->var_decl_type, stmt->var_unpacked_dims.size()});
    }
  }
  for (const Stmt* stmt : item.func_body_stmts) {
    CheckStmtCalls(stmt, scope, diag);
  }
  scope.blocks.resize(kOuter);
}

// §26.3: the variables and nets the package `import` names brings in, by its
// item name or with a wildcard, added to `names`.
void AddImportedData(const CompilationUnit& unit, const ImportItem& import,
                     std::unordered_set<std::string_view>& names) {
  for (const PackageDecl* package : unit.packages) {
    if (package->name != import.package_name) continue;
    for (const ModuleItem* item : package->items) {
      const bool kData = item->kind == ModuleItemKind::kVarDecl ||
                         item->kind == ModuleItemKind::kNetDecl;
      if (kData && (import.is_wildcard || item->name == import.item_name)) {
        names.insert(item->name);
      }
    }
  }
}

// §6.19.3: each named constant the enumeration `type` writes, as a value of
// `scope` of that enumeration; one a range names, R[2], goes by the numbered
// names §6.19.2 gives it, not by its own, and is left out. A variable of the
// constant's name keeps its own declaration.
void DeclareEnumConstants(const DataType& type, DataScope& scope) {
  for (const EnumMember& member : type.enum_members) {
    if (member.range_start == nullptr) {
      scope.module_vars.emplace(member.name, DeclaredVar{&type, 0});
    }
  }
}

// The declaration of each variable the module `decl` declares, as a variable
// of `scope`: each of its ports (§23.2.2), each object an explicitly named
// port of it stands for (§23.2.2.1), and each variable its items declare, a
// body declaration of a port's name giving the port its type; and each named
// constant of an enumeration a port or an item writes.
void DeclareModuleVars(const ModuleDecl& decl, DataScope& scope) {
  for (const auto* ports : {&decl.ports, &decl.port_expr_objects}) {
    for (const PortDecl& port : *ports) {
      scope.module_vars[port.name] =
          DeclaredVar{&port.data_type, port.unpacked_dims.size()};
      DeclareEnumConstants(port.data_type, scope);
    }
  }
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      scope.module_vars[item->name] =
          DeclaredVar{&item->data_type, item->unpacked_dims.size()};
    }
    DeclareEnumConstants(item->data_type, scope);
    DeclareEnumConstants(item->typedef_type, scope);
  }
}

// §3.12.1: each variable and net the compilation unit `unit` declares, as data
// of `scope`, but for a name the module declares as something else, which
// hides it (§23.9).
void DeclareUnitData(const CompilationUnit& unit, DataScope& scope) {
  for (const ModuleItem* item : unit.cu_items) {
    const bool kData = item->kind == ModuleItemKind::kVarDecl ||
                       item->kind == ModuleItemKind::kNetDecl;
    if (kData && !scope.subroutines.contains(item->name) &&
        !scope.uncallable.contains(item->name)) {
      scope.module.insert(item->name);
    }
  }
}

// The names the items of module `decl` declare, each in the set of `scope`
// its kind puts it in: data, subroutines and the rest, which no call names.
void DeclareModuleItems(const ModuleDecl& decl, const CompilationUnit& unit,
                        DataScope& scope) {
  DeclareModuleVars(decl, scope);
  std::unordered_set<std::string_view>& subroutines = scope.subroutines;
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.module.insert(item->name);
    } else if (IsSubroutineItem(*item)) {
      subroutines.insert(item->name);
    } else if (!item->name.empty()) {
      scope.uncallable.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kImportDecl) {
      AddImportedData(unit, item->import_item, scope.uncallable);
    }
  }
  // A name a DPI export gives a function the module also declares stays
  // callable whichever item the walk met first.
  for (std::string_view name : subroutines) scope.uncallable.erase(name);
  // §18.12: a scope randomize call may be written without its std:: prefix.
  subroutines.insert("randomize");
}

// §8.13: the properties the class `cls` declares and those it inherits, as
// the properties of `scope`, a derived class's shadowing a base's of its name.
// Each base is looked up from the scope's site; no class is its own ancestor
// (§8.13), so the walk ends at a class that extends none.
void DeclareClassProperties(const ClassDecl& cls, DataScope& scope) {
  const TypeSite kSite{&scope.items, scope.items.size(), scope.site};
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = ClassIn(scope.unit, kSite, walked->base_class)) {
    for (const ClassMember* member : walked->members) {
      if (member->kind == ClassMemberKind::kProperty) {
        scope.properties.emplace(
            member->name,
            DeclaredVar{&member->data_type, member->unpacked_dims.size()});
      }
    }
  }
}

// The scope a method of the class `cls`, declared in the scope `site` sees,
// is walked in: the site's, its variables among them (§23.9), with the
// class's properties hiding those of their names.
DataScope ClassScope(const ClassDecl& cls, const DataScope& site) {
  DataScope scope{site.visible, site.unit, site.items};
  scope.site = site.site;
  scope.module_vars = site.module_vars;
  scope.local_types = site.local_types;
  scope.classes = site.classes;
  scope.classes->AddLocalTypes(cls, scope.local_types);
  scope.cls = &cls;
  DeclareClassProperties(cls, scope);
  return scope;
}

// §8.3: each call the methods of the class `cls`, declared in the scope
// `site`, write, and those of each class nested in it (§8.23).
void CheckClassCalls(const ClassDecl& cls, const DataScope& site,
                     DiagEngine& diag) {
  DataScope scope = ClassScope(cls, site);
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kMethod) {
      CheckSubroutineCalls(*member->method, scope, diag);
    }
    if (member->nested_class != nullptr) {
      CheckClassCalls(*member->nested_class, site, diag);
    }
  }
}

// Each call the classes the scope `site` declares write in their methods,
// `classes` among them where the site's items do not hold its classes, and
// each a method defined out of its class's body there writes (§8.24), in the
// scope of the class the site sees under the name the method is written
// behind.
void CheckSiteClasses(const DataScope& site,
                      const std::vector<ClassDecl*>& classes,
                      DiagEngine& diag) {
  for (const ClassDecl* cls : classes) CheckClassCalls(*cls, site, diag);
  const TypeSite kSite{&site.items, site.items.size(), site.site};
  for (const ModuleItem* item : site.items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      CheckClassCalls(*item->class_decl, site, diag);
      continue;
    }
    const bool kOutOfBody = (item->kind == ModuleItemKind::kTaskDecl ||
                             item->kind == ModuleItemKind::kFunctionDecl) &&
                            !item->method_class.empty();
    const ClassDecl* cls =
        kOutOfBody ? ClassIn(site.unit, kSite, item->method_class) : nullptr;
    if (cls == nullptr) continue;
    DataScope scope = ClassScope(*cls, site);
    CheckSubroutineCalls(*item, scope, diag);
  }
}

void CheckItemCalls(const std::vector<ModuleItem*>& items, DataScope& scope,
                    DiagEngine& diag);

// §27: each call the generate block whose items are `items` writes, the
// variables and nets it declares in scope over its items as a block's are,
// and the tasks and functions it declares callable there (§23.9).
void CheckGenerateBlockCalls(const std::vector<ModuleItem*>& items,
                             DataScope& scope, DiagEngine& diag) {
  const std::size_t kOuter = scope.blocks.size();
  const std::unordered_set<std::string_view> kOuterSubroutines =
      scope.subroutines;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.blocks.emplace_back(
          item->name,
          DeclaredVar{&item->data_type, item->unpacked_dims.size()});
    } else if (IsSubroutineItem(*item)) {
      scope.subroutines.insert(item->name);
    }
  }
  CheckItemCalls(items, scope, diag);
  scope.blocks.resize(kOuter);
  scope.subroutines = kOuterSubroutines;
}

// §27.4 and §27.5: each call the blocks of the generate construct `construct`
// write: a loop's one block, each block of a conditional construct and of the
// else chain after it, and each case item's block.
void CheckGenerateCalls(const ModuleItem& construct, DataScope& scope,
                        DiagEngine& diag) {
  for (const ModuleItem* branch = &construct; branch != nullptr;
       branch = branch->gen_else) {
    CheckGenerateBlockCalls(branch->gen_body, scope, diag);
    for (const GenerateCaseItem& item : branch->gen_case_items) {
      CheckGenerateBlockCalls(item.body, scope, diag);
    }
  }
}

// Each call the items `items` of a module or of a generate block write: in
// their procedures, in the tasks and functions they declare, a method defined
// out of its class's body (§8.24) excepted, and in the generate constructs
// among them.
void CheckItemCalls(const std::vector<ModuleItem*>& items, DataScope& scope,
                    DiagEngine& diag) {
  for (const ModuleItem* item : items) {
    if (IsProceduralItemKind(item->kind)) {
      CheckStmtCalls(item->body, scope, diag);
    } else if ((item->kind == ModuleItemKind::kTaskDecl ||
                item->kind == ModuleItemKind::kFunctionDecl) &&
               item->method_class.empty()) {
      CheckSubroutineCalls(*item, scope, diag);
    } else if (item->kind == ModuleItemKind::kGenerateFor ||
               item->kind == ModuleItemKind::kGenerateIf ||
               item->kind == ModuleItemKind::kGenerateCase) {
      CheckGenerateCalls(*item, scope, diag);
    }
  }
}

}  // namespace

void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag) {
  DataScope scope{visible, unit, decl.items};
  scope.local_types = decl.type_param_names;
  scope.classes = std::make_shared<const SoleClassIndex>(unit);
  DeclareModuleItems(decl, unit, scope);
  DeclareUnitData(unit, scope);
  CheckItemCalls(decl.items, scope, diag);
}

void ReportClassMethodCalls(const CompilationUnit& unit, DiagEngine& diag) {
  const std::function<bool(std::string_view)> kSeesAll = [](std::string_view) {
    return true;
  };
  const auto kClasses = std::make_shared<const SoleClassIndex>(unit);
  DataScope at_unit{kSeesAll, unit, unit.cu_items};
  at_unit.site = SiteKind::kUnit;
  at_unit.classes = kClasses;
  CheckSiteClasses(at_unit, unit.classes, diag);
  for (const PackageDecl* package : unit.packages) {
    DataScope at_package{kSeesAll, unit, package->items};
    at_package.site = SiteKind::kPackage;
    at_package.classes = kClasses;
    CheckSiteClasses(at_package, {}, diag);
  }
  for (const std::vector<ModuleDecl*>* decls :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *decls) {
      DataScope at_module{kSeesAll, unit, decl->items};
      at_module.local_types = decl->type_param_names;
      at_module.classes = kClasses;
      DeclareModuleVars(*decl, at_module);
      CheckSiteClasses(at_module, {}, diag);
    }
  }
}

}  // namespace delta
