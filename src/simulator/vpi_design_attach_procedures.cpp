#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.12 detail 6: the vpiJoinType of a fork closed by `keyword`.
int JoinTypeOf(TokenKind keyword) {
  if (keyword == TokenKind::kKwJoinAny) return vpiJoinAny;
  if (keyword == TokenKind::kKwJoinNone) return vpiJoinNone;
  return vpiJoin;
}

// The items a begin or fork block holds, its declarations among them.
const std::vector<Stmt*>& BlockItems(const Stmt& block) {
  return block.kind == StmtKind::kFork ? block.fork_stmts : block.stmts;
}

// §37.12: the kind of block `stmt` is, 0 where it is none: a named begin or
// fork where it has a label, and a begin or fork where it has none. Detail 1
// makes the first always a scope and the second one only where it directly
// declares a block item; a block that is no scope is a statement all the same
// (§37.60), standing between the statements it holds and the scope around it.
int BlockKind(const Stmt& stmt) {
  if (stmt.kind != StmtKind::kBlock && stmt.kind != StmtKind::kFork) return 0;
  bool is_fork = stmt.kind == StmtKind::kFork;
  if (!stmt.label.empty()) return is_fork ? vpiNamedFork : vpiNamedBegin;
  return is_fork ? vpiFork : vpiBegin;
}

// Where the objects a statement holds hang: the scope object around it, and
// the path a named one among them is named under, which an unnamed scope
// between them leaves as it was. A scope a block stands as also carries the
// block, whose declarations a name the statement writes resolves to first
// (§9.3, §23.9), and every scope carries the one around it, null at a
// procedure's own scope.
struct BlockParent {
  VpiObject* scope;
  const std::string& path;
  const Stmt* block = nullptr;
  const BlockParent* outer = nullptr;
};

// What a walk of one procedure body builds with: the design and the instance's
// module, which a call's subroutine is found among; the objects the instance's
// declarations stand as, keyed under its prefix; what a call statement is
// built with; the build; and the process the body runs in (null for an
// assertion the elaborator carries as a process).
struct BodyWalk {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const VpiObjectMap& objects;
  const std::string& prefix;
  const VpiCallBuild& calls;
  const VpiAttachBuild& build;
  VpiObject* process = nullptr;
  // §27.4: the prefixes of the generate block instances the procedure stands
  // in, innermost last, null for one of the instance itself.
  const GenBlockPrefixes* gen_prefixes = nullptr;
};

// §9.7: the name the trigger names its event by, which is an identifier in the
// scope the statement stands in. A trigger written through anything else names
// no declaration this walk can resolve against the design.
std::string_view EventTriggerTargetName(const Stmt& stmt) {
  const Expr* target = stmt.expr;
  if (target == nullptr || target->kind != ExprKind::kIdentifier) return {};
  return target->text;
}

// §37.60: the object an atomic statement of `type` stands as, hung from the
// block or statement it is written in, whose nearest scope is what its
// vpiScope reads (§37.12 with §37.63) and below which §38.36.1.3 reads a
// module's statements off, its label its vpiName.
VpiObject* MakeAtomicStatement(const Stmt& stmt, int type,
                               const BlockParent& parent,
                               const BodyWalk& walk) {
  VpiObject* obj = walk.build.alloc();
  obj->type = type;
  obj->parent = parent.scope;
  obj->process = walk.process;
  if (!stmt.label.empty()) obj->name = walk.build.keep(std::string(stmt.label));
  VpiRecordWrittenLocation(obj, stmt.range.start, walk.calls.ctx);
  walk.calls.stmts[{&stmt, walk.prefix}] = obj;
  parent.scope->children.push_back(obj);
  return obj;
}

// §37.62: the event statement a trigger stands as.
VpiObject* MakeEventStatement(const Stmt& stmt, const BlockParent& parent,
                              const BodyWalk& walk) {
  VpiObject* obj = MakeAtomicStatement(stmt, vpiEventStmt, parent, walk);
  // §9.7.2: "->" is the blocking event trigger and "->>" the nonblocking one,
  // which is the whole of what the property distinguishes.
  obj->blocking = stmt.kind == StmtKind::kEventTrigger;
  // The figure's single arrow, which the generic one-to-one traversal walks by
  // the kind of the child: the named event object the design already carries
  // for the declaration, not a second one standing for the same event.
  const std::string_view kTarget = EventTriggerTargetName(stmt);
  if (kTarget.empty()) return obj;
  VpiObject* event =
      FindObjectForFlatName(walk.objects, VpiFlatName(walk.prefix, kTarget));
  if (event != nullptr) obj->children.push_back(event);
  return obj;
}

// §37.60: the kind of an atomic statement that carries nothing but its label,
// 0 for a statement of another kind.
int BareAtomicKind(StmtKind kind) {
  switch (kind) {
    case StmtKind::kBreak:
      return vpiBreak;
    case StmtKind::kContinue:
      return vpiContinue;
    case StmtKind::kNull:
      return vpiNullStmt;
    default:
      return 0;
  }
}

// §37.42: what a call statement stands as. `type` is the kind of tf call, zero
// for a statement that calls nothing the walk resolves; `name` is the
// subroutine it calls; `prefix` is the object a method is applied to (detail
// 2), or the class var a chain of `prefix_members` starts from;
// `user_defined` is the figure's vpiUserDefn; `systf` is the systf object
// a call of a registered system task reaches; and `called` is the task or
// function object of the declaration a task, function or method call calls.
struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
  std::vector<std::string_view> prefix_members = {};
  bool user_defined = false;
  VpiObject* systf = nullptr;
  VpiObject* called = nullptr;
};

// §13.3 and §13.4: the kind of tf call a call of `decl` is, `task` for a task
// and `function` for a function, zero for an item that is neither.
int CallKindOf(const ModuleItem& decl, int task, int function) {
  if (decl.kind == ModuleItemKind::kTaskDecl) return task;
  return decl.kind == ModuleItemKind::kFunctionDecl ? function : 0;
}

// §37.42: a task or function call named `name` of the subroutine `sub`
// resolves to, reaching the task or function object made for it.
CallShape SubroutineCallShape(const VpiCalledSubroutine& sub,
                              std::string_view name) {
  if (sub.decl == nullptr) return {};
  CallShape shape{CallKindOf(*sub.decl, vpiTaskCall, vpiFuncCall), name};
  shape.called = sub.object;
  return shape;
}

// Where a statement standing in `parent` is written, as a call it holds
// resolves the subroutine it calls.
VpiCallSite CallSiteOf(const BlockParent& parent, const BodyWalk& walk) {
  return {walk.design,
          walk.mod,
          walk.prefix,
          parent.scope,
          walk.calls.subroutines,
          walk.gen_prefixes};
}

// The class among `decls` named `name`, null for none.
const ClassDecl* ClassNamed(const std::vector<ClassDecl*>& decls,
                            std::string_view name) {
  for (const ClassDecl* decl : decls) {
    if (decl != nullptr && decl->name == name) return decl;
  }
  return nullptr;
}

// The class the design declares under `name`, in the instance's module or the
// compilation unit; null for one it does not, a built-in class among them.
const ClassDecl* FindClassDecl(const BodyWalk& walk, std::string_view name) {
  const ClassDecl* decl = ClassNamed(walk.mod.class_decls, name);
  return decl != nullptr ? decl : ClassNamed(walk.design.cu_class_decls, name);
}

// §37.17: the object kind of a variable declared with `type` in the instance,
// leaving its unpacked dimensions aside.
int TypeVariableKind(const DataType& type, const BodyWalk& walk) {
  if (type.kind == DataTypeKind::kNamed) {
    return VpiNamedTypeVariableKind(walk.design, walk.mod, type.type_name);
  }
  return VpiDataTypeVariableKind(type.kind);
}

// §37.17: the object kind of a variable a block declares, as a module's of its
// type is. An unpacked array of events is a named event array (§37.27), and
// one of any other element one array var (§37.17 detail 1).
int BlockVariableKind(const Stmt& decl, const BodyWalk& walk) {
  const int kKind = TypeVariableKind(decl.var_decl_type, walk);
  if (decl.var_unpacked_dims.empty()) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiRegArray;
}

// §37.12: the key the run makes the storage of the variable `name` the block
// `stmt` declares under, as BindNamedBlockVariable (stmt_exec_control.cpp)
// enters it when the block runs: the instance's prefix, the generate block
// instance the procedure stands in, and the named blocks from the outermost
// in; empty where no named block encloses the variable, which the run keys
// under no such path.
std::string BlockVariableRunKey(std::string_view name, const Stmt& stmt,
                                const BlockParent& parent,
                                const BodyWalk& walk) {
  std::string scopes = stmt.label.empty() ? "" : std::string(stmt.label) + ".";
  for (const BlockParent* outer = &parent; outer != nullptr;
       outer = outer->outer) {
    if (outer->block != nullptr && !outer->block->label.empty()) {
      scopes.insert(0, std::string(outer->block->label) + ".");
    }
  }
  if (scopes.empty()) return {};
  const bool kInGenBlock =
      walk.gen_prefixes != nullptr && !walk.gen_prefixes->empty();
  const std::string kGen =
      kInGenBlock ? std::string(walk.gen_prefixes->back()) : "";
  return VpiFlatName(walk.prefix, kGen + scopes + std::string(name));
}

// §37.12 (figure): the variables a block declares hang from it, each named
// under the block's path and keyed as the run keys its storage. A block
// parameter is a block item declaration but no variable.
void MakeBlockVariables(VpiObject* block, const Stmt& stmt,
                        const std::string& path, const BlockParent& parent,
                        const BodyWalk& walk) {
  for (const Stmt* item : BlockItems(stmt)) {
    if (item == nullptr || item->kind != StmtKind::kVarDecl ||
        item->var_is_param) {
      continue;
    }
    VpiObject* var = walk.build.alloc();
    var->type = BlockVariableKind(*item, walk);
    var->parent = block;
    var->name = walk.build.keep(std::string(item->var_name));
    var->full_name = path + "." + std::string(item->var_name);
    var->run_key = BlockVariableRunKey(item->var_name, stmt, parent, walk);
    block->children.push_back(var);
  }
}

// §8.3: the method `cls` declares under `name`, null for none.
const ModuleItem* MethodNamed(const ClassDecl& cls, std::string_view name) {
  for (const ClassMember* member : cls.members) {
    if (member != nullptr && member->kind == ClassMemberKind::kMethod &&
        member->method != nullptr && member->method->name == name) {
      return member->method;
    }
  }
  return nullptr;
}

// §37.42: what a method call calls - the kind of tf call it is, zero for a
// method the walk resolves to nothing, whether the design declares it, and if
// it does the class declaring it.
struct MethodCall {
  int type = 0;
  bool declared = false;
  const ClassDecl* owner = nullptr;
};

// The method `method` of the class `cls`, found in the class or, by §8.13, in
// the classes it extends. A class the design declares answers ahead of a
// built-in one of its name, which §15.2 lets user code redefine. The bound
// stops a chain of extensions that loops.
MethodCall ClassMethodCall(const BodyWalk& walk, std::string_view cls,
                           std::string_view method) {
  constexpr int kMaxDepth = 64;
  for (int depth = 0; depth < kMaxDepth && !cls.empty(); ++depth) {
    const ClassDecl* decl = FindClassDecl(walk, cls);
    if (decl == nullptr) return {VpiBuiltInClassCallKind(cls, method), false};
    const ModuleItem* found = MethodNamed(*decl, method);
    if (found != nullptr) {
      return {CallKindOf(*found, vpiMethodTaskCall, vpiMethodFuncCall), true,
              decl};
    }
    cls = decl->base_class;
  }
  return {};
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
         FindClassDecl(walk, dim.text) != nullptr;
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
  const bool kEnum =
      !var.enum_type_name.empty() || var.decl_kind == DataTypeKind::kEnum;
  return kEnum ? VpiBuiltInHolder::kEnum : VpiBuiltInHolder::kNone;
}

// §8.4: the variable a call's prefix names, as the class it holds a handle of
// (empty for a variable of no class type and for no variable), the kind of
// built-in value it is, and the object standing for it.
struct PrefixVar {
  std::string_view cls;
  VpiBuiltInHolder holder = VpiBuiltInHolder::kNone;
  VpiObject* object = nullptr;
};

// §23.9: the declaration of the variable `name` a block around the statement
// `parent` stands for declares, the innermost first, with `where` set to the
// block's; null where no block declares one.
const Stmt* BlockVarDecl(const BlockParent& parent, std::string_view name,
                         const BlockParent*& where) {
  for (const BlockParent* at = &parent; at != nullptr; at = at->outer) {
    if (at->block == nullptr) continue;
    for (const Stmt* item : BlockItems(*at->block)) {
      if (item != nullptr && item->kind == StmtKind::kVarDecl &&
          item->var_name == name) {
        where = at;
        return item;
      }
    }
  }
  return nullptr;
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
        BlockHolder(*item, walk), ChildNamed(where->scope, name)};
  }
  PrefixVar var;
  var.object =
      FindObjectForFlatName(walk.objects, VpiFlatName(walk.prefix, name));
  for (const RtlirVariable& decl : walk.mod.variables) {
    if (decl.name != name) continue;
    var.cls = decl.class_type_name;
    var.holder = ModuleHolder(decl);
    break;
  }
  return var;
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
int ModuleIndexKind(std::string_view name, const BodyWalk& walk) {
  for (const RtlirVariable& var : walk.mod.variables) {
    if (var.name != name || !var.is_assoc) continue;
    if (var.is_class_index) return vpiClassVar;
    return IndexTypeKind(var.assoc_index_keyword.empty()
                             ? var.assoc_index_type_name
                             : var.assoc_index_keyword,
                         walk);
  }
  return vpiIntVar;
}

// §12.7.3: the kind of the first index variable of a foreach loop over the
// array `array` names, the index type's where the array's first dimension is
// associative and an int var otherwise; an array a block around the
// statement declares is found first (§23.9).
int ForeachIndexKind(const Expr* array, const BlockParent& parent,
                     const BodyWalk& walk) {
  if (array == nullptr || array->kind != ExprKind::kIdentifier) {
    return vpiIntVar;
  }
  const BlockParent* where = nullptr;
  if (const Stmt* item = BlockVarDecl(parent, array->text, where)) {
    const Expr* dim = item->var_unpacked_dims.empty()
                          ? nullptr
                          : item->var_unpacked_dims.front();
    const bool kAssoc = dim != nullptr && IsAssocDim(*dim, walk);
    return kAssoc ? IndexTypeKind(dim->text, walk) : vpiIntVar;
  }
  return ModuleIndexKind(array->text, walk);
}

// §37.42 with §37.31: the task or function the class defn made for `owner`
// holds under `name`, the defn of the instance walked or else of the
// compilation unit; null where none was made.
VpiObject* MethodObject(const BodyWalk& walk, const ClassDecl* owner,
                        std::string_view name) {
  if (owner == nullptr) return nullptr;
  for (const std::string& scope : {walk.prefix, std::string("$unit")}) {
    auto found = walk.calls.classes.find({owner, scope});
    if (found == walk.calls.classes.end()) continue;
    for (VpiObject* child : found->second->children) {
      if (VpiIsClassMethodType(child->type) && child->name == name) {
        return child;
      }
    }
  }
  return nullptr;
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

// §37.42: a method task or method function call, applied through `access`,
// which joins two names, to a variable of the scope the call stands in: a
// class var, whose class says what the method is, or a string, an enum or an
// unpacked array, whose built-in methods are functions no design declares.
CallShape MethodCallShape(const Expr& access, const BlockParent& parent,
                          const BodyWalk& walk) {
  const PrefixVar kVar = FindPrefixVar(parent, access.lhs->text, walk);
  MethodCall call;
  if (kVar.holder == VpiBuiltInHolder::kNone) {
    call = ClassMethodCall(walk, kVar.cls, access.rhs->text);
  } else if (VpiIsBuiltInMethod(kVar.holder, access.rhs->text)) {
    call.type = vpiMethodFuncCall;
  }
  return MethodShape(call, access.rhs->text, kVar.object, walk);
}

// §8.4 with §8.13: the class the property `name` of the class `cls`, or of a
// class it extends, holds a handle of; empty where neither declares it with a
// named type. The bound stops a chain of extensions that loops.
std::string_view PropertyClass(const BodyWalk& walk, std::string_view cls,
                               std::string_view name) {
  constexpr int kMaxDepth = 64;
  for (int depth = 0; depth < kMaxDepth && !cls.empty(); ++depth) {
    const ClassDecl* decl = FindClassDecl(walk, cls);
    if (decl == nullptr) return {};
    for (const ClassMember* member : decl->members) {
      if (member == nullptr || member->kind != ClassMemberKind::kProperty ||
          member->name != name) {
        continue;
      }
      const DataType& type = member->data_type;
      return type.kind == DataTypeKind::kNamed ? type.type_name
                                               : std::string_view();
    }
    cls = decl->base_class;
  }
  return {};
}

// The plain names a chain of member accesses joins, `a.b.c` as a, b and c,
// appended to `names`; false where a link is anything else.
bool ChainNames(const Expr& expr, std::vector<std::string_view>& names) {
  if (expr.kind == ExprKind::kIdentifier) {
    names.push_back(expr.text);
    return true;
  }
  if (expr.kind != ExprKind::kMemberAccess || expr.is_scope_resolution ||
      expr.lhs == nullptr || expr.rhs == nullptr) {
    return false;
  }
  return ChainNames(*expr.lhs, names) && ChainNames(*expr.rhs, names);
}

// §37.42 detail 2 with §8.4: a method call applied through a chain of members
// to a class var of the scope, a.b.run(). The class of the chain's last member
// says what the method is, and the call is applied to that member in the
// object the var references, which is read when the prefix is asked for.
CallShape MemberChainCallShape(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk) {
  std::vector<std::string_view> names;
  if (access.rhs->kind != ExprKind::kIdentifier ||
      !ChainNames(*access.lhs, names) || names.size() < 2) {
    return {};
  }
  const PrefixVar kVar = FindPrefixVar(parent, names.front(), walk);
  if (kVar.holder != VpiBuiltInHolder::kNone) return {};
  std::string_view cls = kVar.cls;
  for (std::size_t i = 1; i < names.size(); ++i) {
    cls = PropertyClass(walk, cls, names[i]);
  }
  CallShape shape = MethodShape(ClassMethodCall(walk, cls, access.rhs->text),
                                access.rhs->text, kVar.object, walk);
  if (shape.type != 0) {
    shape.prefix_members.assign(names.begin() + 1, names.end());
  }
  return shape;
}

// Whether the member access or scope resolution `access` joins two plain
// names, `obj.run` or `p::t`, the one form of either this walk resolves.
bool JoinsTwoNames(const Expr& access) {
  return access.lhs != nullptr && access.rhs != nullptr &&
         access.lhs->kind == ExprKind::kIdentifier &&
         access.rhs->kind == ExprKind::kIdentifier;
}

// §37.42 with §37.60: what the expression statement `expr`, standing in the
// scope `parent` stands for, calls. A task is enabled with or without an
// argument list (§13.3), so the callee is the expression itself where no list
// follows it.
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
  if (callee->kind != ExprKind::kMemberAccess || callee->lhs == nullptr ||
      callee->rhs == nullptr) {
    return {};
  }
  if (!JoinsTwoNames(*callee)) {
    return callee->is_scope_resolution
               ? CallShape{}
               : MemberChainCallShape(*callee, parent, walk);
  }
  // §26.3: a package's subroutine behind the package's name, `p::t`.
  if (callee->is_scope_resolution) {
    return SubroutineCallShape(
        VpiCalleeSubroutine(CallSiteOf(parent, walk), *callee),
        callee->rhs->text);
  }
  return MethodCallShape(*callee, parent, walk);
}

// §37.42: the arguments `expr`, standing in `parent`, was written with, in
// order, each the expression object the instance's names resolve it to
// (§37.58, §37.59), an empty position being detail 8's empty argument. An
// expression of a kind the model builds no object for is passed over.
void MakeCallArguments(VpiObject* call, const Expr& expr,
                       const BlockParent& parent, const BodyWalk& walk) {
  if (expr.kind != ExprKind::kCall && expr.kind != ExprKind::kSystemCall) {
    return;
  }
  const VpiCallSite kSite = CallSiteOf(parent, walk);
  for (const Expr* actual : expr.args) {
    VpiObject* arg = nullptr;
    if (actual == nullptr) {
      arg = walk.build.alloc();
      VpiMakeEmptyArgument(arg);
    } else {
      arg = VpiCallSiteExpression(actual, walk.objects, kSite, walk.calls.ctx,
                                  walk.build);
    }
    if (arg != nullptr) call->arguments.push_back(arg);
  }
}

// §37.42 with §37.60: the call statement `stmt` stands as, null for a
// statement that calls nothing the walk resolves. A call is named after what
// it calls; a label written on it names the begin §9.3.5 makes around it
// instead. It is marked as written as a statement, which tells a function call
// standing as one from a function call standing as an expression. A system
// task or function call decompiles to the call written (detail 9), and is
// recorded as the call statement it is, which a run's invocation of a
// registered system task or function stands as (detail 3).
VpiObject* MakeCallStatement(const Stmt& stmt, const BlockParent& parent,
                             const BodyWalk& walk) {
  if (stmt.kind != StmtKind::kExprStmt || stmt.expr == nullptr) return nullptr;
  const CallShape kShape = CallShapeOf(*stmt.expr, parent, walk);
  if (kShape.type == 0) return nullptr;
  VpiObject* call = MakeAtomicStatement(stmt, kShape.type, parent, walk);
  call->name = walk.build.keep(std::string(kShape.name));
  call->tf_prefix = kShape.prefix;
  call->prefix_members = kShape.prefix_members;
  call->tf_decl = kShape.called;
  call->user_defined = kShape.user_defined;
  call->user_systf = kShape.systf;
  call->written_as_stmt = true;
  MakeCallArguments(call, *stmt.expr, parent, walk);
  if (kShape.type == vpiSysTaskCall || kShape.type == vpiSysFuncCall) {
    call->decompile = VpiExprDecompile(stmt.expr);
    walk.calls.sites[{stmt.expr, walk.prefix}] = call;
  }
  return call;
}

// §9.3.5: whether the label on `stmt` creates a named begin around it. A label
// on a begin or fork is the block's name, and one on a foreach loop, or on a
// for loop declaring its variables, names the block the loop creates; on any
// other statement it creates a named begin-end block of its own.
bool LabelCreatesNamedBegin(const Stmt& stmt) {
  if (stmt.label.empty() || stmt.kind == StmtKind::kBlock ||
      stmt.kind == StmtKind::kFork || stmt.kind == StmtKind::kForeach) {
    return false;
  }
  return stmt.kind != StmtKind::kFor || stmt.for_init_types.empty() ||
         stmt.for_init_types.front().kind == DataTypeKind::kImplicit;
}

// A block or scope object of `kind` hung from the block, statement or scope
// around it, named `label` under the path the scope extends, which `path` is
// set to; an unnamed block leaves the path as it was.
VpiObject* MakeScopeObject(int kind, std::string_view label,
                           const BlockParent& parent, const BodyWalk& walk,
                           std::string& path) {
  VpiObject* scope = walk.build.alloc();
  scope->type = kind;
  scope->parent = parent.scope;
  scope->process = walk.process;
  path = parent.path;
  if (!label.empty()) {
    scope->name = walk.build.keep(std::string(label));
    path += "." + std::string(label);
    scope->full_name = path;
  }
  parent.scope->children.push_back(scope);
  return scope;
}

VpiObject* WalkStmt(const Stmt* stmt, const BlockParent& parent,
                    const BodyWalk& walk);

// The statements `stmt` holds, each walked for the objects it writes.
void WalkSubStmts(const Stmt& stmt, const BlockParent& parent,
                  const BodyWalk& walk) {
  ForEachChildStmt(&stmt,
                   [&](const Stmt* sub) { WalkStmt(sub, parent, walk); });
}

// What a statement written at `parent` builds the objects it reaches with,
// used while `parent` and `walk` live.
VpiStmtBuild StmtBuildAt(const BlockParent& parent, const BodyWalk& walk) {
  return {walk.build,
          [site = CallSiteOf(parent, walk), &walk](const Expr* expr) {
            return VpiCallSiteExpression(expr, walk.objects, site,
                                         walk.calls.ctx, walk.build);
          },
          [&parent, &walk](const Stmt* held, VpiObject* holder) {
            return WalkStmt(
                held, BlockParent{holder, parent.path, nullptr, &parent}, walk);
          },
          [&parent, &walk](const Expr* array) {
            return ForeachIndexKind(array, parent, walk);
          }};
}

// The object a statement the builder of vpi_design_attach_statements.cpp
// knows stands as, with the expressions it writes and the statements it holds,
// each hung from it; null for a statement of another kind.
VpiObject* MakeBuiltStmt(const Stmt& stmt, const BlockParent& parent,
                         const BodyWalk& walk) {
  const int kKind = VpiBuiltStmtKind(stmt);
  if (kKind == 0) return nullptr;
  VpiObject* obj = MakeAtomicStatement(stmt, kKind, parent, walk);
  // §37.49: an assertion reports where its text stands.
  if (VpiIsAssertionType(kKind)) {
    VpiRecordAssertionLocation(obj, stmt.range, walk.calls.ctx);
  }
  VpiFillStmt(obj, stmt, StmtBuildAt(parent, walk));
  return obj;
}

// §37.12: the object a block stands as, nested in the scope or statement around
// it, with the variables it declares and the statements it holds.
VpiObject* MakeBlock(const Stmt& stmt, int kind, const BlockParent& parent,
                     const BodyWalk& walk) {
  std::string path;
  VpiObject* block = MakeScopeObject(kind, stmt.label, parent, walk, path);
  VpiRecordWrittenLocation(block, stmt.range.start, walk.calls.ctx);
  walk.calls.stmts[{&stmt, walk.prefix}] = block;
  if (stmt.kind == StmtKind::kFork) {
    block->join_type = JoinTypeOf(stmt.join_kind);
  }
  MakeBlockVariables(block, stmt, path, parent, walk);
  WalkSubStmts(stmt, BlockParent{block, path, &stmt, &parent}, walk);
  return block;
}

// The object `stmt` itself stands as, made with the objects it holds; null for
// a statement of a kind the run builds no object for, whose contents are
// walked all the same.
VpiObject* WalkStmtItself(const Stmt& stmt, const BlockParent& parent,
                          const BodyWalk& walk) {
  if (stmt.kind == StmtKind::kEventTrigger ||
      stmt.kind == StmtKind::kNbEventTrigger) {
    return MakeEventStatement(stmt, parent, walk);
  }
  const int kAtomic = BareAtomicKind(stmt.kind);
  if (kAtomic != 0) return MakeAtomicStatement(stmt, kAtomic, parent, walk);
  VpiObject* call = MakeCallStatement(stmt, parent, walk);
  if (call != nullptr) return call;
  VpiObject* made = MakeBuiltStmt(stmt, parent, walk);
  if (made != nullptr) return made;
  const int kBlock = BlockKind(stmt);
  if (kBlock != 0) return MakeBlock(stmt, kBlock, parent, walk);
  WalkSubStmts(stmt, parent, walk);
  return nullptr;
}

// The object `stmt` stands as: the named begin its label creates around it
// (§9.3.5), holding what the statement itself stands as, or that object alone.
VpiObject* WalkStmt(const Stmt* stmt, const BlockParent& parent,
                    const BodyWalk& walk) {
  if (stmt == nullptr) return nullptr;
  if (!LabelCreatesNamedBegin(*stmt)) {
    return WalkStmtItself(*stmt, parent, walk);
  }
  std::string path;
  VpiObject* begin =
      MakeScopeObject(vpiNamedBegin, stmt->label, parent, walk, path);
  WalkStmtItself(*stmt, BlockParent{begin, path, nullptr, &parent}, walk);
  return begin;
}

// §37.63 with §37.65: the statement a procedure runs. The parser lifts the
// event control an always or always_ff procedure opens with into the
// procedure's sensitivity, keeping the statement it guards as the body, so
// that control is built here from the events, @* writing none, guarding the
// body; an always_comb or always_latch procedure's sensitivity is inferred
// (§9.2.2.2, §9.2.2.3) rather than written, and so stands for no control.
VpiObject* WalkProcessBody(const RtlirProcess& proc, const BlockParent& parent,
                           const BodyWalk& walk) {
  const bool kAlways = proc.kind == RtlirProcessKind::kAlways ||
                       proc.kind == RtlirProcessKind::kAlwaysFF;
  if (!kAlways || (proc.sensitivity.empty() && !proc.is_star_sensitivity)) {
    return WalkStmt(proc.body, parent, walk);
  }
  Stmt control{};
  control.kind = StmtKind::kEventControl;
  control.events = proc.sensitivity;
  control.is_star_event = proc.is_star_sensitivity;
  control.body = proc.body;
  return MakeBuiltStmt(control, parent, walk);
}

// §37.63: the object a procedure stands as, one of the three kinds the
// `process` class groups, with detail 1's always type for an always procedure.
VpiObject* MakeProcess(const RtlirProcess& proc, VpiObject* scope,
                       const VpiAttachBuild& build) {
  VpiObject* process = build.alloc();
  process->type = vpiAlways;
  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      process->type = vpiInitial;
      break;
    case RtlirProcessKind::kFinal:
      process->type = vpiFinal;
      break;
    case RtlirProcessKind::kAlways:
      process->always_type = vpiAlways;
      break;
    case RtlirProcessKind::kAlwaysComb:
      process->always_type = vpiAlwaysComb;
      break;
    case RtlirProcessKind::kAlwaysFF:
      process->always_type = vpiAlwaysFF;
      break;
    case RtlirProcessKind::kAlwaysLatch:
      process->always_type = vpiAlwaysLatch;
      break;
  }
  process->parent = scope;
  scope->children.push_back(process);
  return process;
}

// `make` called for each entry of `items`, an item `instance` writes, with
// the generate block instance writing it and what a statement written there
// builds the objects it reaches with, a name resolving in that block first
// (§27.4).
template <typename Scoped, typename Make>
void AttachScopedItems(VpiObject* instance, const BodyWalk& instance_walk,
                       const std::vector<Scoped>& items, const Make& make) {
  for (const Scoped& entry : items) {
    VpiObject* scope = VpiGenScopeOf(instance, entry.gen_block_path);
    if (scope == nullptr || entry.item == nullptr) continue;
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &entry.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    make(entry, scope, StmtBuildAt(kParent, walk));
  }
}

// The properties one instance declares and the assertions it writes as
// items, each in the generate block instance writing it, and the procedures
// it declares with the objects their bodies hold, walked with
// `instance_walk`, whose process each procedure's own replaces. A property
// is built ahead of the assertions instantiating it (§37.51). An assertion
// the elaborator carries as a process is no procedure the source wrote, a
// concurrent one being the item's (§37.50).
void AttachInstanceProcedures(VpiObject* instance,
                              const BodyWalk& instance_walk) {
  AttachScopedItems(
      instance, instance_walk, instance_walk.mod.declared_properties,
      [&instance_walk](const RtlirPropertyDecl& declared, VpiObject* scope,
                       const VpiStmtBuild& with) {
        const VpiCallBuild& calls = instance_walk.calls;
        VpiMakePropertyDecl(
            declared,
            {scope, calls.unit_typespecs, calls.ctx, instance_walk.mod.imports},
            with);
      });
  AttachScopedItems(
      instance, instance_walk, instance_walk.mod.assertions,
      [&instance_walk](const RtlirAssertion& assertion, VpiObject* scope,
                       const VpiStmtBuild& with) {
        VpiMakeItemAssertion(assertion, scope, instance_walk.calls.ctx, with);
      });
  for (const RtlirProcess& proc : instance_walk.mod.processes) {
    // A process stands in the generate block instance its path names.
    VpiObject* scope = VpiGenScopeOf(instance, proc.gen_block_path);
    if (scope == nullptr) continue;
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &proc.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    if (!proc.is_static_assertion && !proc.is_concurrent_clocked) {
      walk.process = MakeProcess(proc, scope, instance_walk.build);
      walk.process->body = WalkProcessBody(proc, kParent, walk);
    } else if (proc.body != nullptr && proc.body->is_deferred) {
      // §16.4.3: a deferred assertion item is the statement it runs (§37.55).
      MakeBuiltStmt(*proc.body, kParent, walk);
    }
  }
}

}  // namespace

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build) {
  // §37.63: each procedure an instance declares is a process of it, reaching
  // the statement it runs; §37.12: each begin or fork is a block of the
  // instance whose procedure writes it, and detail 1 makes a named one, and an
  // unnamed one declaring a block item, a scope; §37.62: each event trigger
  // is an event statement, §37.42: each call of a task, a method task or a
  // system task a call statement, and each statement VpiBuiltStmtKind names
  // an object of its kind, each hung from the block or statement it stands in.
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  // The first top carries the empty prefix and is keyed under its own name.
  const std::string kFirstTop(design->top_modules.front()->name);
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* instance =
            FindObjectForFlatName(objects, prefix.empty() ? kFirstTop : prefix);
        if (instance != nullptr) {
          AttachInstanceProcedures(
              instance, BodyWalk{*design, *mod, objects, prefix, calls, build});
        }
      });
}

}  // namespace delta
