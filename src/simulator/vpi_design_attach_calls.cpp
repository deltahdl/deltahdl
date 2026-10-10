#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_procedures_internal.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §13.3 and §13.4: the kind of tf call a call of the subroutine `decl` is,
// `task` for a task, one a DPI import declares among them (§35.5), and
// `function` for a function.
int CallKindOf(const ModuleItem& decl, int task, int function) {
  return decl.kind == ModuleItemKind::kTaskDecl || decl.dpi_is_task ? task
                                                                    : function;
}

// §37.42: a task or function call named `name` of the subroutine `sub`
// resolves to, reaching the task or function object made for it. A call the
// elaborator accepts naming no declared subroutine calls the scope randomize
// function the language builds in, randomize(a) or std::randomize(a) (§18.12):
// a func call reaching no function object, as detail 11 has a built-in
// method's call reach none.
CallShape SubroutineCallShape(const VpiCalledSubroutine& sub,
                              std::string_view name) {
  if (sub.decl == nullptr) return {vpiFuncCall, name};
  CallShape shape{CallKindOf(*sub.decl, vpiTaskCall, vpiFuncCall), name};
  shape.called = sub.object;
  return shape;
}

// The class among `decls` named `name`, null for none.
const ClassDecl* ClassNamed(const std::vector<ClassDecl*>& decls,
                            std::string_view name) {
  for (const ClassDecl* decl : decls) {
    if (decl->name == name) return decl;
  }
  return nullptr;
}

// A class declaration with the flat name of the scope its class defn was made
// under, the key VpiClassDefnObjects files the defn by: the instance's prefix,
// a package's name or "$unit".
struct ScopedClass {
  const ClassDecl* decl = nullptr;
  std::string scope;
};

// The classes the package named `package` declares; none for a name no
// package of the design has.
std::vector<ClassDecl*> PackageClasses(const RtlirDesign& design,
                                       std::string_view package) {
  std::vector<ClassDecl*> classes;
  for (const PackageDecl* decl : design.packages) {
    if (decl->name == package) classes = VpiPackageClasses(*decl);
  }
  return classes;
}

// §6.18 with §8.3: the class name `name` stands for, the class at the end of
// a typedef's chain of names where it is a typedef name, `typedef B B_t;`.
std::string_view ClassNameOf(const BodyWalk& walk, std::string_view name) {
  const auto kTarget = walk.design.type_targets.find(name);
  return kTarget == walk.design.type_targets.end() ? name : kTarget->second;
}

// The class the design declares under `name`: in the package `package` where
// one is named (§26.3), and otherwise in the instance's module, the
// compilation unit or a package the module imports the name from, by name or
// with a wildcard (§26.3), a typedef name standing for the class it names. No
// declaration for a name the design declares no class under, a built-in class
// among them.
ScopedClass FindClassDecl(const BodyWalk& walk, std::string_view name,
                          std::string_view package = {}) {
  name = ClassNameOf(walk, name);
  if (!package.empty()) {
    return {ClassNamed(PackageClasses(walk.design, package), name),
            std::string(package)};
  }
  const ClassDecl* decl = ClassNamed(walk.mod.class_decls, name);
  if (decl != nullptr) return {decl, walk.prefix};
  decl = ClassNamed(walk.design.cu_class_decls, name);
  if (decl != nullptr) return {decl, "$unit"};
  for (const RtlirImport& entry : walk.mod.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    decl = ClassNamed(PackageClasses(walk.design, entry.package_name), name);
    if (decl != nullptr) return {decl, std::string(entry.package_name)};
  }
  return {};
}

// §8.3: the method `cls` declares under `name`, null for none.
const ModuleItem* MethodNamed(const ClassDecl& cls, std::string_view name) {
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kMethod &&
        member->method->name == name) {
      return member->method;
    }
  }
  return nullptr;
}

// §37.42: what a method call calls - the kind of tf call it is, zero for a
// method the walk resolves to nothing, whether the design declares it, and if
// it does the class declaring it with the scope its class defn was made in.
struct MethodCall {
  int type = 0;
  bool declared = false;
  ScopedClass owner = {};
};

// The method `method` of the class `cls`, of the package `package` where one is
// named, found in the class or, by §8.13, in the classes it extends. A class
// the design declares answers ahead of a built-in one of its name, which §15.2
// lets user code redefine. A method none of them declares is one of the
// built-in methods every class has (§18), a function, or else nothing.
MethodCall ClassMethodCall(const BodyWalk& walk, std::string_view cls,
                           std::string_view method,
                           std::string_view package = {}) {
  const bool kNamesClass = !cls.empty();
  while (!cls.empty()) {
    ScopedClass found = FindClassDecl(walk, cls, package);
    if (found.decl == nullptr) {
      return {VpiBuiltInClassCallKind(ClassNameOf(walk, cls), method), false};
    }
    const ModuleItem* item = MethodNamed(*found.decl, method);
    if (item != nullptr) {
      return {CallKindOf(*item, vpiMethodTaskCall, vpiMethodFuncCall), true,
              std::move(found)};
    }
    cls = found.decl->base_class;
  }
  const bool kBuiltIn = kNamesClass && VpiIsClassBuiltInMethod(method);
  return {kBuiltIn ? vpiMethodFuncCall : 0, false};
}

// §37.42: a system task or system function call, named after what it calls. A
// system function stays a function where a statement calls it, and the
// evaluator runs it as one (§36.5). A name an application registered is what
// the registration made it, which the run calls it as; every other name is a
// system task.
CallShape SystemCallShape(const Expr& call, const BodyWalk& walk) {
  const VpiRegisteredSystf kSystf = walk.calls.systf(call.callee);
  const bool kFunction =
      kSystf.type == vpiSysFunc ||
      (kSystf.type == 0 && VpiIsBuiltInSystemFunction(call.callee));
  CallShape shape{kFunction ? vpiSysFuncCall : vpiSysTaskCall, call.callee};
  shape.user_defined = kSystf.type == vpiSysTask || kSystf.type == vpiSysFunc;
  shape.systf = kSystf.object;
  return shape;
}

// §7.8: whether the unpacked dimension `dim` gives an associative array its
// index type: a data type keyword, the wildcard, or a name standing for a type
// or a class.
bool IsAssocDim(const Expr& dim, const BodyWalk& walk) {
  static constexpr std::string_view kIndexTypes[] = {
      "string", "int",   "integer", "byte", "shortint", "longint",
      "bit",    "logic", "reg",     "time", "*"};
  if (dim.kind != ExprKind::kIdentifier) return false;
  return std::ranges::any_of(
             kIndexTypes, [&](std::string_view t) { return t == dim.text; }) ||
         walk.design.type_kinds.contains(dim.text) ||
         FindClassDecl(walk, dim.text).decl != nullptr;
}

// The kind of built-in value a block declares with `decl`: an array of the kind
// its first unpacked dimension makes, a dynamic array's `[]` being recorded as
// no dimension and a queue's as `[$]`; else a string or an enum, written as
// one or through a typedef.
VpiBuiltInHolder BlockHolder(const Stmt& decl, const BodyWalk& walk) {
  if (!decl.var_unpacked_dims.empty()) {
    const Expr* dim = decl.var_unpacked_dims.front();
    if (dim == nullptr) return VpiBuiltInHolder::kDynamicArray;
    if (IsQueueDim(dim)) return VpiBuiltInHolder::kQueue;
    return IsAssocDim(*dim, walk) ? VpiBuiltInHolder::kAssocArray
                                  : VpiBuiltInHolder::kFixedArray;
  }
  const int kKind = TypeVariableKind(decl.var_decl_type, walk);
  if (kKind == vpiStringVar) return VpiBuiltInHolder::kString;
  return kKind == vpiEnumVar ? VpiBuiltInHolder::kEnum
                             : VpiBuiltInHolder::kNone;
}

// The same, of a variable of the instance's module.
VpiBuiltInHolder ModuleHolder(const RtlirVariable& var) {
  if (var.is_queue) return VpiBuiltInHolder::kQueue;
  if (var.is_dynamic) return VpiBuiltInHolder::kDynamicArray;
  if (var.is_assoc) return VpiBuiltInHolder::kAssocArray;
  if (var.num_unpacked_dims > 0) return VpiBuiltInHolder::kFixedArray;
  if (var.is_string) return VpiBuiltInHolder::kString;
  // An enum declared without a typedef is keyed by its declaration's name
  // (SetEnumTypeInfo), so every enum variable names an enumeration.
  return var.enum_type_name.empty() ? VpiBuiltInHolder::kNone
                                    : VpiBuiltInHolder::kEnum;
}

// §25.9: the interface a value declared with `type` refers to an instance of,
// where it is a virtual interface; empty for any other type and for none.
std::string_view VifInterface(const DataType* type) {
  return type != nullptr && type->kind == DataTypeKind::kVirtualInterface
             ? type->type_name
             : std::string_view();
}

// §8.4: the variable a call's prefix names, as the class it holds a handle of
// (empty for a variable of no class type and for no variable), the kind of
// built-in value it is, the object standing for it, the interface it refers
// to an instance of where it is a virtual interface, and the type its
// declaration wrote, null where the elaborator recorded none.
struct PrefixVar {
  std::string_view cls;
  VpiBuiltInHolder holder = VpiBuiltInHolder::kNone;
  VpiObject* object = nullptr;
  std::string_view vif;
  const DataType* type = nullptr;
};

// The variable `name` of the module `mod`, whose instance's objects are keyed
// under `prefix`.
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
    break;
  }
  return var;
}

// §23.9: the variable `name` names in the scope `parent` stands for: one a
// block declares, the innermost around the statement first, or else one of the
// instance's module.
PrefixVar FindPrefixVar(const BlockParent& parent, std::string_view name,
                        const BodyWalk& walk) {
  const BlockParent* where = nullptr;
  if (const Stmt* item = BlockVarDecl(parent, name, where)) {
    const DataType& type = item->var_decl_type;
    return {
        type.kind == DataTypeKind::kNamed ? type.type_name : std::string_view(),
        BlockHolder(*item, walk), ChildNamed(where->scope, name),
        VifInterface(&type), &type};
  }
  return ModulePrefixVar(walk.mod, walk.prefix, name, walk);
}

// The module an instance named `name` of `mod` is of; null where `mod` holds
// no instance of that name.
const RtlirModule* ChildModule(const RtlirModule& mod, std::string_view name) {
  for (const RtlirModuleInst& child : mod.children) {
    if (child.inst_name == name) return child.resolved;
  }
  return nullptr;
}

// The variable a chain of names, a.b.c, starts from: one of the scope the
// first name names (FindPrefixVar), or, by §23.6, one of the module of an
// instance below the walked one the leading names reach downward, u.h; with
// that instance's module and path, the walked instance's for a variable of the
// scope, and the number of names the variable took.
struct ChainHead {
  PrefixVar var;
  const RtlirModule* mod = nullptr;
  std::string path;
  std::size_t used = 1;

  // What the rest of the chain is resolved with: the classes and variables of
  // the instance the head belongs to.
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
  if (i == 0) return {FindPrefixVar(parent, names.front(), walk), mod, path, 1};
  return {ModulePrefixVar(*mod, path, names[i], walk), mod, path, i + 1};
}

// §12.7.3 with §7.8: the kind of variable an associative array's index type
// written as `name` declares, which a foreach loop variable over the array is
// of: a built-in keyword's, or the kind a class or typedef name gives (§6.18).
// §7.8.1 bars a foreach over a wildcard index.
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

// §12.7.3: the kind of the first index variable of a foreach loop over the
// variable `name` of the instance's module: its index type's where the array
// is associative, an int var otherwise.
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

// §12.7.3: the kind of the first index variable of a foreach loop over an
// array declared with the unpacked dimensions `dims`: the index type's where
// the first is associative, an int var otherwise.
int FirstDimIndexKind(const std::vector<Expr*>& dims, const BodyWalk& walk) {
  const Expr* dim = dims.empty() ? nullptr : dims.front();
  const bool kAssoc = dim != nullptr && IsAssocDim(*dim, walk);
  return kAssoc ? IndexTypeKind(dim->text, walk) : vpiIntVar;
}

// §37.42 with §37.31: the task or function the class defn made for `owner`
// holds under `name`; null for no owner. A defn is made for each class of an
// instance, a package or the compilation unit, under the scope FindClassDecl
// reports, holding a method for each method the class declares.
VpiObject* MethodObject(const BodyWalk& walk, const ScopedClass& owner,
                        std::string_view name) {
  if (owner.decl == nullptr) return nullptr;
  const VpiObject* defn = walk.calls.classes.at({owner.decl, owner.scope});
  return *std::ranges::find_if(defn->children, [name](const VpiObject* child) {
    return VpiIsClassMethodType(child->type) && child->name == name;
  });
}

// §37.42: a call of the method `name` that `call` resolves it to, applied to
// `prefix`; nothing where it resolves to none.
CallShape MethodShape(const MethodCall& call, std::string_view name,
                      VpiObject* prefix, const BodyWalk& walk) {
  if (call.type == 0) return {};
  CallShape shape{call.type, name};
  shape.prefix = prefix;
  // Detail 11 tells a built-in method call apart from the rest, and the
  // figure's vpiUserDefn is what says which a method call is.
  shape.user_defined = call.declared;
  shape.called = MethodObject(walk, call.owner, name);
  return shape;
}

// §25.9 with §37.42: a call, through a virtual interface, of the task or
// function `name` the interface `iface` declares: a task or func call named
// after it. Which instance of the interface the virtual interface refers to is
// known only when the call runs, so the call reaches no one instance's task or
// function object. The interface's declaration says which the subroutine is,
// whether or not anything instantiates the interface.
CallShape InterfaceCallShape(const BodyWalk& walk, std::string_view iface,
                             std::string_view name) {
  const ModuleItem* called = nullptr;
  for (const ModuleDecl* decl : walk.design.compilation_unit->interfaces) {
    if (decl->name != iface) continue;
    for (const ModuleItem* item : decl->items) {
      const bool kSubroutine = item->kind == ModuleItemKind::kTaskDecl ||
                               item->kind == ModuleItemKind::kFunctionDecl;
      if (kSubroutine && item->name == name) called = item;
    }
  }
  return SubroutineCallShape({called, nullptr}, name);
}

// §37.42: a method task or method function call, applied through `access`,
// which joins two names, to a variable of the scope the call stands in: a
// class var, whose class says what the method is, or a string, an enum or an
// unpacked array, whose built-in methods are functions no design declares.
CallShape MethodCallShape(const Expr& access, const BlockParent& parent,
                          const BodyWalk& walk) {
  const PrefixVar kVar = FindPrefixVar(parent, access.lhs->text, walk);
  if (!kVar.vif.empty()) {
    return InterfaceCallShape(walk, kVar.vif, access.rhs->text);
  }
  MethodCall call;
  if (kVar.holder == VpiBuiltInHolder::kNone) {
    call = ClassMethodCall(walk, kVar.cls, access.rhs->text);
  } else if (VpiIsBuiltInMethod(kVar.holder, access.rhs->text)) {
    call.type = vpiMethodFuncCall;
  }
  return MethodShape(call, access.rhs->text, kVar.object, walk);
}

// §8.4 with §8.13: the property `name` the class `cls`, of the package
// `package` where one is named, or a class it extends, declares; null where
// neither does.
const ClassMember* PropertyNamed(const BodyWalk& walk, std::string_view cls,
                                 std::string_view name,
                                 std::string_view package = {}) {
  for (const ClassDecl* decl = FindClassDecl(walk, cls, package).decl;
       decl != nullptr;
       decl = FindClassDecl(walk, decl->base_class, package).decl) {
    for (const ClassMember* member : decl->members) {
      if (member->kind == ClassMemberKind::kProperty && member->name == name) {
        return member;
      }
    }
  }
  return nullptr;
}

// What a value a call is applied through holds: the class it holds a handle
// of, or the interface it refers to an instance of as a virtual interface
// (§25.9); both empty for any other value.
struct HandleType {
  std::string_view cls;
  std::string_view vif;
};

// The same for the property `name` of the class `cls`, or of a class it
// extends; empty where neither declares it with a named type or as a virtual
// interface.
HandleType PropertyType(const BodyWalk& walk, std::string_view cls,
                        std::string_view name, std::string_view package = {}) {
  const ClassMember* member = PropertyNamed(walk, cls, name, package);
  if (member == nullptr) return {};
  const DataType& type = member->data_type;
  return {
      type.kind == DataTypeKind::kNamed ? type.type_name : std::string_view(),
      VifInterface(&type)};
}

// §6.18: the type the typedef `name` the walked module declares stands for;
// null where the module declares no typedef of that name.
const DataType* ModuleTypedef(const BodyWalk& walk, std::string_view name) {
  const DataType* found = nullptr;
  for (const ModuleDecl* decl : walk.design.compilation_unit->modules) {
    if (decl->name != walk.mod.name) continue;
    for (const ModuleItem* item : decl->items) {
      if (item->kind == ModuleItemKind::kTypedef && item->name == name) {
        found = &item->typedef_type;
      }
    }
  }
  return found;
}

// §7.2: the unpacked or packed structure `type` declares, written as one or
// through a typedef the walked module declares; null for any other type.
const DataType* StructTypeOf(const BodyWalk& walk, const DataType* type) {
  if (type != nullptr && type->kind == DataTypeKind::kNamed) {
    type = ModuleTypedef(walk, type->type_name);
  }
  return type != nullptr && type->kind == DataTypeKind::kStruct ? type
                                                                : nullptr;
}

// §7.2 with §8.4: the class the member `name` of the structure `aggregate`
// holds a handle of, named as its declaration wrote it.
HandleType StructMemberType(const DataType& aggregate, std::string_view name) {
  HandleType type;
  for (const StructMember& member : aggregate.struct_members) {
    if (member.name == name) type.cls = member.type_name;
  }
  return type;
}

// §12.7.3 with §8.4, §7.2 and §23.6: the same for an array named through
// members: a variable of the module of an instance the leading names reach,
// u.m; a member of a structure variable, s.aa, or of a class the member holds
// a handle of, s.h.m; or else the first unpacked dimension of the property
// the chain's last name is, of the class the rest of the chain holds a handle
// of, o.m or o.h.m. An int var where the chain names none of these, such as
// one through an element select.
int MemberIndexKind(const Expr& array, const BlockParent& parent,
                    const BodyWalk& walk) {
  std::vector<std::string_view> names;
  if (!ChainNames(array, names)) return vpiIntVar;
  const ChainHead kHead = ChainHeadVar(names, parent, walk);
  const BodyWalk kAt = kHead.WalkAt(walk);
  if (kHead.used == names.size()) {
    return ModuleIndexKind(*kHead.mod, names.back(), kAt);
  }
  std::string_view cls = kHead.var.cls;
  std::size_t first = kHead.used;
  if (const DataType* aggregate = StructTypeOf(kAt, kHead.var.type)) {
    for (const StructMember& member : aggregate->struct_members) {
      if (member.name != names[first]) continue;
      if (first + 1 == names.size()) {
        return FirstDimIndexKind(member.unpacked_dims, kAt);
      }
      cls = member.type_name;
    }
    ++first;
  }
  for (std::size_t i = first; i + 1 < names.size(); ++i) {
    cls = PropertyType(kAt, cls, names[i]).cls;
  }
  const ClassMember* member = PropertyNamed(kAt, cls, names.back());
  return member == nullptr ? vpiIntVar
                           : FirstDimIndexKind(member->unpacked_dims, kAt);
}

// The class a value of an expression is a handle of, named as written, with
// the package declaring it where it is a package's; empty for an expression
// this walk reads no class from.
struct ExprClassName {
  std::string_view cls;
  std::string_view package;
};

// §26.3: the class the variable `name` the package `package` declares holds a
// handle of; empty where the package declares no such variable of a named
// type.
std::string_view PackageVarClass(const RtlirDesign& design,
                                 std::string_view package,
                                 std::string_view name) {
  std::string_view cls;
  for (const PackageDecl* decl : design.packages) {
    if (decl->name != package) continue;
    for (const ModuleItem* item : decl->items) {
      if (item->kind == ModuleItemKind::kVarDecl && item->name == name) {
        cls = item->data_type.type_name;
      }
    }
  }
  return cls;
}

// §9.7: the built-in class a method of the built-in class `cls` returns a
// handle of: process::self(), the process it is called in. Empty for any
// other method, which returns no handle.
std::string_view BuiltInResultClass(std::string_view cls,
                                    std::string_view method) {
  return cls == "process" && method == "self" ? cls : std::string_view();
}

ExprClassName ExprClass(const Expr& expr, const BlockParent& parent,
                        const BodyWalk& walk);

// §11.12: the class the expression the let `name` the instance's module
// declares stands for is a handle of, cur() as the class of b where
// `let cur() = b;`; empty where the module declares no let of the name.
ExprClassName LetResultClass(std::string_view name, const BlockParent& parent,
                             const BodyWalk& walk) {
  ExprClassName cls;
  for (const ModuleItem* item : walk.mod.let_decls) {
    if (item->name == name) cls = ExprClass(*item->init_expr, parent, walk);
  }
  return cls;
}

// §13.4 with §8.6 and §8.10: the class the subroutine `callee` names returns
// a handle of: a function's, f() or a package's p::f(), the class looked up in
// that package; a static method's of the class a scope names, C::make(); or a
// method's of the class of the value it is applied through, a.self().
ExprClassName CallResultClass(const Expr& callee, const BlockParent& parent,
                              const BodyWalk& walk) {
  const ModuleItem* function =
      VpiCalleeSubroutine(CallSiteOf(parent, walk), callee).decl;
  if (function != nullptr) {
    return {function->return_type.type_name,
            callee.is_scope_resolution ? callee.lhs->text : std::string_view()};
  }
  if (callee.kind != ExprKind::kMemberAccess) {
    return LetResultClass(callee.text, parent, walk);
  }
  const ExprClassName kOwner = callee.is_scope_resolution
                                   ? ExprClassName{callee.lhs->text, {}}
                                   : ExprClass(*callee.lhs, parent, walk);
  const std::string_view kMethod = callee.rhs->text;
  const ClassDecl* decl =
      ClassMethodCall(walk, kOwner.cls, kMethod, kOwner.package).owner.decl;
  return {decl == nullptr ? BuiltInResultClass(kOwner.cls, kMethod)
                          : MethodNamed(*decl, kMethod)->return_type.type_name,
          kOwner.package};
}

// §8.4: the class the value `expr` writes is a handle of: a variable's of the
// scope; an element's of an array of handles, objs[0]; a property's of the
// class of what it is selected from, a.h; a package's variable's, p::obj; the
// return type of what a call calls, f() or a.self(); and a conditional's, of
// the operand it may answer with first (§11.4.11, which has both operands
// share a class or one extend the other). Empty for any other expression.
ExprClassName ExprClass(const Expr& expr, const BlockParent& parent,
                        const BodyWalk& walk) {
  if (expr.kind == ExprKind::kIdentifier) {
    return {FindPrefixVar(parent, expr.text, walk).cls, {}};
  }
  if (expr.kind == ExprKind::kSelect) {
    return ExprClass(*expr.base, parent, walk);
  }
  if (expr.kind == ExprKind::kCall) {
    return CallResultClass(*expr.lhs, parent, walk);
  }
  if (expr.kind == ExprKind::kTernary) {
    return ExprClass(*expr.true_expr, parent, walk);
  }
  if (expr.kind != ExprKind::kMemberAccess) return {};
  if (expr.is_scope_resolution) {
    return {PackageVarClass(walk.design, expr.lhs->text, expr.rhs->text),
            expr.lhs->text};
  }
  const ExprClassName kOuter = ExprClass(*expr.lhs, parent, walk);
  return {PropertyType(walk, kOuter.cls, expr.rhs->text, kOuter.package).cls,
          kOuter.package};
}

// §37.42 detail 2: a method call applied to the value of an expression other
// than a chain of names, objs[0].run() or objs[0].h.run(), whose class says
// what the method is. The call is applied to the expression object the
// expression's base stands as (§37.58, §37.59), objs[0], and through the
// members a chain of plain names selects after it, h, which are read in the
// objects the base references when the prefix is asked for.
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
  CallShape shape = MethodShape(
      ClassMethodCall(walk, kClass.cls, kName, kClass.package), kName,
      VpiCallSiteExpression(base, walk.objects, CallSiteOf(parent, walk),
                            walk.calls.ctx, walk.build),
      walk);
  shape.prefix_members = std::move(members);
  return shape;
}

// §37.42 detail 2 with §8.4: a method call applied through a chain of members
// to a class var, a.b.run(): one of the scope, or, by §23.6, one of an
// instance below it the leading names reach, u.h.run(). The class of the
// chain's last member says what the method is, and the call is applied to
// that member in the object the var references, which is read when the
// prefix is asked for. A method that class does not declare may be one of the
// built-in methods of the member itself, h.x.rand_mode(0) or
// h.c.constraint_mode(0) (§18.8, §18.9).
CallShape MemberChainCallShape(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk) {
  std::vector<std::string_view> names;
  if (!ChainNames(*access.lhs, names)) {
    return ExprCallShape(access, parent, walk);
  }
  const ChainHead kHead = ChainHeadVar(names, parent, walk);
  if (kHead.var.holder != VpiBuiltInHolder::kNone) return {};
  const BodyWalk kAt = kHead.WalkAt(walk);
  HandleType type{kHead.var.cls, kHead.var.vif};
  VpiObject* prefix = kHead.var.object;
  std::size_t first = kHead.used;
  // §7.2: a structure's member is selected in the structure variable itself,
  // whose member object stands for it, so the chain's class vars start there.
  const DataType* aggregate =
      first < names.size() ? StructTypeOf(kAt, kHead.var.type) : nullptr;
  if (aggregate != nullptr) {
    type = StructMemberType(*aggregate, names[first]);
    prefix = ChildNamed(prefix, names[first]);
    ++first;
  }
  for (std::size_t i = first; i < names.size(); ++i) {
    type = PropertyType(kAt, type.cls, names[i]);
  }
  if (!type.vif.empty()) {
    return InterfaceCallShape(kAt, type.vif, access.rhs->text);
  }
  MethodCall call = ClassMethodCall(kAt, type.cls, access.rhs->text);
  if (call.type == 0) call.type = VpiMemberBuiltInCallKind(access.rhs->text);
  CallShape shape = MethodShape(call, access.rhs->text, prefix, kAt);
  if (shape.type != 0) {
    shape.prefix_members.assign(
        names.begin() + static_cast<std::ptrdiff_t>(first), names.end());
  }
  return shape;
}

// §37.42: a call written behind a scope: a package's subroutine, p::t (§26.3);
// the scope randomize function of the built-in package std, std::randomize
// (§18.12, §26.7); else a static method of the class the scope names, C::f
// (§8.10, §8.23), or of a class a package declares, p::C::f. A static method is
// called through no object, so the call has no prefix.
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
    return MethodShape(ClassMethodCall(walk, scope.text, kName), kName, nullptr,
                       walk);
  }
  return MethodShape(
      ClassMethodCall(walk, scope.rhs->text, kName, scope.lhs->text), kName,
      nullptr, walk);
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
          }};
}

int TypeVariableKind(const DataType& type, const BodyWalk& walk) {
  if (type.kind == DataTypeKind::kNamed) {
    return VpiNamedTypeVariableKind(walk.design, walk.mod, type.type_name);
  }
  return VpiDataTypeVariableKind(type.kind);
}

const Stmt* BlockVarDecl(const BlockParent& parent, std::string_view name,
                         const BlockParent*& where) {
  for (const BlockParent* at = &parent; at != nullptr; at = at->outer) {
    if (at->block == nullptr) continue;
    for (const Stmt* item : BlockItems(*at->block)) {
      if (item->kind == StmtKind::kVarDecl && item->var_name == name) {
        where = at;
        return item;
      }
    }
  }
  return nullptr;
}

bool ChainNames(const Expr& expr, std::vector<std::string_view>& names) {
  if (expr.kind == ExprKind::kIdentifier) {
    names.push_back(expr.text);
    return true;
  }
  if (expr.kind != ExprKind::kMemberAccess || expr.is_scope_resolution) {
    return false;
  }
  // The right-hand side of a member access is always the member's name.
  if (!ChainNames(*expr.lhs, names)) return false;
  names.push_back(expr.rhs->text);
  return true;
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
  const ScopedClass kFound = FindClassDecl(walk, kClass.cls, kClass.package);
  const auto kMade = walk.calls.classes.find({kFound.decl, kFound.scope});
  return kMade == walk.calls.classes.end() ? nullptr : kMade->second;
}

CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk) {
  if (expr.kind == ExprKind::kSystemCall) {
    return SystemCallShape(expr, walk);
  }
  const Expr* callee = expr.kind == ExprKind::kCall ? expr.lhs : &expr;
  if (callee == nullptr) return {};
  if (callee->kind == ExprKind::kIdentifier) {
    return SubroutineCallShape(
        VpiCalleeSubroutine(CallSiteOf(parent, walk), *callee), callee->text);
  }
  if (callee->kind != ExprKind::kMemberAccess) return {};
  if (callee->is_scope_resolution) {
    return ScopedCallShape(*callee, parent, walk);
  }
  // The right-hand side is always the name called. A left-hand side other than
  // a plain name is a chain of members, a.b.run(), resolved as one.
  if (callee->lhs->kind != ExprKind::kIdentifier) {
    return MemberChainCallShape(*callee, parent, walk);
  }
  return MethodCallShape(*callee, parent, walk);
}

}  // namespace delta
