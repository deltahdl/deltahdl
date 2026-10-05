#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/string_methods.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
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

bool IsBlockItemDeclaration(const Stmt* item) {
  return item != nullptr && (item->kind == StmtKind::kVarDecl ||
                             item->kind == StmtKind::kBlockItemDecl);
}

// §37.12 detail 1: the scope kind `stmt` is, 0 where it is none. A named begin
// or fork always is one, and an unnamed one only where it directly declares a
// block item; a declaration inside a block nested in it does not count.
int BlockScopeKind(const Stmt& stmt) {
  if (stmt.kind != StmtKind::kBlock && stmt.kind != StmtKind::kFork) return 0;
  bool is_fork = stmt.kind == StmtKind::kFork;
  if (!stmt.label.empty()) return is_fork ? vpiNamedFork : vpiNamedBegin;
  if (std::ranges::any_of(BlockItems(stmt), IsBlockItemDeclaration)) {
    return is_fork ? vpiFork : vpiBegin;
  }
  return 0;
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
// scope it is written in (§37.12 with §37.63), which is what its vpiScope reads
// and what §38.36.1.3 reads a module's statements off, its label its vpiName.
VpiObject* MakeAtomicStatement(const Stmt& stmt, int type,
                               const BlockParent& parent,
                               const BodyWalk& walk) {
  VpiObject* obj = walk.build.alloc();
  obj->type = type;
  obj->parent = parent.scope;
  obj->process = walk.process;
  if (!stmt.label.empty()) obj->name = walk.build.keep(std::string(stmt.label));
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
// 2); `user_defined` is the figure's vpiUserDefn; `systf` is the systf object
// a call of a registered system task reaches; and `called` is the task or
// function object of the declaration a task, function or method call calls.
struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
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
  return {walk.design, walk.mod, walk.prefix, parent.scope,
          walk.calls.subroutines};
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

// §37.12 (figure): the variables a block declares hang from it, each named
// under the block's path. A block parameter is a block item declaration but no
// variable.
void MakeBlockVariables(VpiObject* block, const Stmt& stmt,
                        const std::string& path, const BodyWalk& walk) {
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

// §9.7, §15.3 and §15.4: the kind of tf call a call of the method `method` of
// the built-in class `cls` is, zero for none. Every method the three classes
// declare is listed but new, which no statement calls through a variable.
int BuiltInClassCallKind(std::string_view cls, std::string_view method) {
  using Method = std::pair<std::string_view, std::string_view>;
  static constexpr Method kTasks[] = {
      {"process", "await"}, {"semaphore", "get"}, {"mailbox", "put"},
      {"mailbox", "get"},   {"mailbox", "peek"},
  };
  static constexpr Method kFunctions[] = {
      {"process", "self"},          {"process", "status"},
      {"process", "kill"},          {"process", "suspend"},
      {"process", "resume"},        {"process", "srandom"},
      {"process", "get_randstate"}, {"process", "set_randstate"},
      {"semaphore", "put"},         {"semaphore", "try_get"},
      {"mailbox", "num"},           {"mailbox", "try_put"},
      {"mailbox", "try_get"},       {"mailbox", "try_peek"},
  };
  const auto kIsCalled = [&](const Method& entry) {
    return entry.first == cls && entry.second == method;
  };
  if (std::ranges::any_of(kTasks, kIsCalled)) return vpiMethodTaskCall;
  return std::ranges::any_of(kFunctions, kIsCalled) ? vpiMethodFuncCall : 0;
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
    if (decl == nullptr) return {BuiltInClassCallKind(cls, method), false};
    const ModuleItem* found = MethodNamed(*decl, method);
    if (found != nullptr) {
      return {CallKindOf(*found, vpiMethodTaskCall, vpiMethodFuncCall), true,
              decl};
    }
    cls = decl->base_class;
  }
  return {};
}

// Whether `name` is a built-in system function, every one the standard defines
// listed by the clause defining it: §14.14, §16.14.7, §18.13, §19.9, and the
// functions of §20.3 to §20.15, §21.3 and §21.6. $cast (§8.16), $system
// (§20.17.1) and $stacktrace (§20.17.2) may each be called as a task or a
// function, and a statement calling one calls the task.
bool IsBuiltInSystemFunction(std::string_view name) {
  static constexpr std::string_view kFunctions[] = {
      // §14.14, §16.14.7, §18.13 and §19.9.
      "$global_clock", "$inferred_clock", "$inferred_disable", "$urandom",
      "$urandom_range", "$get_coverage",
      // §20.3 and §20.4.
      "$realtime", "$stime", "$time", "$timeunit", "$timeprecision",
      // §20.5 and §20.6.
      "$bitstoreal", "$realtobits", "$bitstoshortreal", "$shortrealtobits",
      "$itor", "$rtoi", "$signed", "$unsigned", "$bits", "$isunbounded",
      "$typename",
      // §20.7.
      "$unpacked_dimensions", "$dimensions", "$left", "$right", "$low", "$high",
      "$increment", "$size",
      // §20.8.
      "$clog2", "$ln", "$log10", "$exp", "$sqrt", "$pow", "$floor", "$ceil",
      "$sin", "$cos", "$tan", "$asin", "$acos", "$atan", "$atan2", "$hypot",
      "$sinh", "$cosh", "$tanh", "$asinh", "$acosh", "$atanh",
      // §20.9.
      "$countbits", "$countones", "$onehot", "$onehot0", "$isunknown",
      // §20.12.
      "$sampled", "$rose", "$fell", "$stable", "$changed", "$past",
      "$past_gclk", "$rose_gclk", "$fell_gclk", "$stable_gclk", "$changed_gclk",
      "$future_gclk", "$rising_gclk", "$falling_gclk", "$steady_gclk",
      "$changing_gclk",
      // §20.13, §20.14 and §20.15.
      "$coverage_control", "$coverage_get_max", "$coverage_get",
      "$coverage_merge", "$coverage_save", "$random", "$dist_chi_square",
      "$dist_erlang", "$dist_exponential", "$dist_normal", "$dist_poisson",
      "$dist_t", "$dist_uniform", "$q_full",
      // §21.3 and §21.6.
      "$fopen", "$fgetc", "$ungetc", "$fgets", "$fscanf", "$sscanf", "$fread",
      "$ftell", "$fseek", "$rewind", "$feof", "$ferror", "$sformatf",
      "$test$plusargs", "$value$plusargs"};
  return std::ranges::any_of(kFunctions, [name](std::string_view function) {
    return function == name;
  });
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
      (kSystf.type == 0 && IsBuiltInSystemFunction(call.callee));
  CallShape shape{kFunction ? vpiSysFuncCall : vpiSysTaskCall, call.callee};
  shape.user_defined = kSystf.type == vpiSysTask || kSystf.type == vpiSysFunc;
  shape.systf = kSystf.object;
  return shape;
}

// The kind of value a built-in method is called on: a string (§6.16), an enum
// (§6.19.5), a fixed-size, dynamic or associative array or a queue (§7.4,
// §7.5, §7.8, §7.10), or none of them.
enum class BuiltInHolder : uint8_t {
  kNone,
  kString,
  kEnum,
  kFixedArray,
  kDynamicArray,
  kAssocArray,
  kQueue,
};

// Whether `method` is one of the built-in methods of a value of `holder`'s
// kind, every one listed by name: §6.16's of a string, §6.19.5's of an enum,
// §7.5's of a dynamic array, §7.9's of an associative array, §7.10.2's of a
// queue, and §7.12's of any unpacked array but the ordering methods of
// §7.12.2, which an associative array has none of. Each is a function.
bool IsBuiltInMethod(BuiltInHolder holder, std::string_view method) {
  static constexpr std::string_view kEnum[] = {"first", "last", "next",
                                               "prev",  "num",  "name"};
  static constexpr std::string_view kDynamic[] = {"size", "delete"};
  static constexpr std::string_view kAssoc[] = {
      "num", "size", "delete", "exists", "first", "last", "next", "prev"};
  static constexpr std::string_view kQueue[] = {
      "size",     "insert",     "delete",   "pop_front",
      "pop_back", "push_front", "push_back"};
  static constexpr std::string_view kManipulation[] = {
      "find",       "find_index",
      "find_first", "find_first_index",
      "find_last",  "find_last_index",
      "min",        "max",
      "unique",     "unique_index",
      "sum",        "product",
      "and",        "or",
      "xor",        "map"};
  static constexpr std::string_view kOrdering[] = {"reverse", "sort", "rsort",
                                                   "shuffle"};
  const auto kLists = [method](const auto& names) {
    return std::ranges::any_of(
        names, [method](std::string_view name) { return name == method; });
  };
  switch (holder) {
    case BuiltInHolder::kString:
      return StringMethodWritesItsObject(method) ||
             StringMethodAnswersAValue(method);
    case BuiltInHolder::kEnum:
      return kLists(kEnum);
    case BuiltInHolder::kNone:
      return false;
    default:
      break;
  }
  if (kLists(kManipulation)) return true;
  if (holder == BuiltInHolder::kAssocArray) return kLists(kAssoc);
  if (kLists(kOrdering)) return true;
  if (holder == BuiltInHolder::kDynamicArray) return kLists(kDynamic);
  return holder == BuiltInHolder::kQueue && kLists(kQueue);
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
BuiltInHolder BlockHolder(const Stmt& decl, const BodyWalk& walk) {
  if (!decl.var_unpacked_dims.empty()) {
    const Expr* dim = decl.var_unpacked_dims.front();
    if (dim == nullptr) return BuiltInHolder::kDynamicArray;
    if (IsQueueDim(dim)) return BuiltInHolder::kQueue;
    return IsAssocDim(*dim, walk) ? BuiltInHolder::kAssocArray
                                  : BuiltInHolder::kFixedArray;
  }
  const int kKind = TypeVariableKind(decl.var_decl_type, walk);
  if (kKind == vpiStringVar) return BuiltInHolder::kString;
  return kKind == vpiEnumVar ? BuiltInHolder::kEnum : BuiltInHolder::kNone;
}

// The same, of a variable of the instance's module.
BuiltInHolder ModuleHolder(const RtlirVariable& var) {
  if (var.is_queue) return BuiltInHolder::kQueue;
  if (var.is_dynamic) return BuiltInHolder::kDynamicArray;
  if (var.is_assoc) return BuiltInHolder::kAssocArray;
  if (var.num_unpacked_dims > 0) return BuiltInHolder::kFixedArray;
  if (var.is_string) return BuiltInHolder::kString;
  const bool kEnum =
      !var.enum_type_name.empty() || var.decl_kind == DataTypeKind::kEnum;
  return kEnum ? BuiltInHolder::kEnum : BuiltInHolder::kNone;
}

// §8.4: the variable a call's prefix names, as the class it holds a handle of
// (empty for a variable of no class type and for no variable), the kind of
// built-in value it is, and the object standing for it.
struct PrefixVar {
  std::string_view cls;
  BuiltInHolder holder = BuiltInHolder::kNone;
  VpiObject* object = nullptr;
};

// §23.9: the variable `name` names in the scope `parent` stands for: one a
// block declares, the innermost around the statement first, or else one of the
// instance's module.
PrefixVar FindPrefixVar(const BlockParent& parent, std::string_view name,
                        const BodyWalk& walk) {
  for (const BlockParent* at = &parent; at != nullptr; at = at->outer) {
    if (at->block == nullptr) continue;
    for (const Stmt* item : BlockItems(*at->block)) {
      if (item == nullptr || item->kind != StmtKind::kVarDecl ||
          item->var_name != name) {
        continue;
      }
      const DataType& type = item->var_decl_type;
      return {type.kind == DataTypeKind::kNamed ? type.type_name
                                                : std::string_view(),
              BlockHolder(*item, walk), ChildNamed(at->scope, name)};
    }
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

// §37.42: a method task or method function call, applied through `access`,
// which joins two names, to a variable of the scope the call stands in: a
// class var, whose class says what the method is, or a string, an enum or an
// unpacked array, whose built-in methods are functions no design declares.
CallShape MethodCallShape(const Expr& access, const BlockParent& parent,
                          const BodyWalk& walk) {
  const PrefixVar kVar = FindPrefixVar(parent, access.lhs->text, walk);
  MethodCall call;
  if (kVar.holder == BuiltInHolder::kNone) {
    call = ClassMethodCall(walk, kVar.cls, access.rhs->text);
  } else if (IsBuiltInMethod(kVar.holder, access.rhs->text)) {
    call.type = vpiMethodFuncCall;
  }
  if (call.type == 0) return {};
  CallShape shape{call.type, access.rhs->text};
  shape.prefix = kVar.object;
  // Detail 11 tells a built-in method call apart from the rest, and the
  // figure's vpiUserDefn is what says which a method call is.
  shape.user_defined = call.declared;
  shape.called = MethodObject(walk, call.owner, access.rhs->text);
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
  if (callee->kind != ExprKind::kMemberAccess || !JoinsTwoNames(*callee)) {
    return {};
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
  const VpiCalleeResolver kCallees = VpiCalleesAt(CallSiteOf(parent, walk));
  for (const Expr* actual : expr.args) {
    VpiObject* arg = nullptr;
    if (actual == nullptr) {
      arg = walk.build.alloc();
      VpiMakeEmptyArgument(arg);
    } else {
      arg = VpiInstanceExpression(actual, walk.objects, walk.prefix,
                                  walk.calls.ctx, walk.build, kCallees);
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

// A scope object of `kind` hung from the scope around it, named `label` under
// the path the scope extends, which `path` is set to.
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

// §37.12 detail 1: the scope object a block that is one stands as, nested in
// the scope around it, with the variables it declares.
VpiObject* MakeBlockScope(const Stmt& stmt, int kind, const BlockParent& parent,
                          const BodyWalk& walk) {
  std::string path;
  VpiObject* block = MakeScopeObject(kind, stmt.label, parent, walk, path);
  if (stmt.kind == StmtKind::kFork) {
    block->join_type = JoinTypeOf(stmt.join_kind);
  }
  MakeBlockVariables(block, stmt, path, walk);
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
  const int kScope = BlockScopeKind(stmt);
  if (kScope != 0) return MakeBlockScope(stmt, kScope, parent, walk);
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

// The procedures one instance declares, each with the objects its body holds,
// walked with `instance_walk`, whose process each procedure's own replaces. An
// assertion the elaborator carries as a process is no procedure the source
// wrote, so it stands as none, though the statements of its action blocks are
// statements of the design all the same.
void AttachInstanceProcedures(VpiObject* instance,
                              const BodyWalk& instance_walk) {
  for (const RtlirProcess& proc : instance_walk.mod.processes) {
    // A process stands in the generate block instance its path names.
    VpiObject* scope = VpiGenScopeOf(instance, proc.gen_block_path);
    if (scope == nullptr) continue;
    const bool kIsAssertion =
        proc.is_static_assertion || proc.is_concurrent_clocked;
    BodyWalk walk = instance_walk;
    walk.process =
        kIsAssertion ? nullptr : MakeProcess(proc, scope, instance_walk.build);
    const BlockParent kParent{scope, scope->full_name};
    if (walk.process != nullptr) {
      walk.process->body = WalkStmt(proc.body, kParent, walk);
    } else if (proc.body != nullptr) {
      // The body of such a process is the assertion itself, whose label names
      // the assertion (§16.5) rather than a block around it.
      WalkSubStmts(*proc.body, kParent, walk);
    }
  }
}

}  // namespace

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build) {
  // §37.63: each procedure an instance declares is a process of it, reaching
  // the statement it runs; §37.12 detail 1: a named begin or fork, and an
  // unnamed one declaring a block item, is a scope of the instance whose
  // procedure writes it; §37.62: each event trigger is an event statement of
  // the scope it stands in, and §37.42: each call of a task, a method task or
  // a system task a call statement of it. No procedure was made, so none was
  // reached, the event statements all hung from the instance whatever block
  // they were written in, and no call a procedure wrote was an object.
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
