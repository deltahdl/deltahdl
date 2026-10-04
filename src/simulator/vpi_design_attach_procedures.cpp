#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
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

// §37.17: the object kind of a variable a block declares; an unpacked array of
// any element is one array var (§37.17 detail 1).
int BlockVariableKind(const Stmt& decl) {
  if (!decl.var_unpacked_dims.empty()) return vpiRegArray;
  return VpiDataTypeVariableKind(decl.var_decl_type.kind);
}

// §37.12 (figure): the variables a block declares hang from it, each named
// under the block's path. A block parameter is a block item declaration but no
// variable.
void MakeBlockVariables(VpiObject* block, const Stmt& stmt,
                        const std::string& path, const VpiAttachBuild& build) {
  for (const Stmt* item : BlockItems(stmt)) {
    if (item == nullptr || item->kind != StmtKind::kVarDecl ||
        item->var_is_param) {
      continue;
    }
    VpiObject* var = build.alloc();
    var->type = BlockVariableKind(*item);
    var->parent = block;
    var->name = build.keep(std::string(item->var_name));
    var->full_name = path + "." + std::string(item->var_name);
    block->children.push_back(var);
  }
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
// for a statement that calls no task; `name` is the subroutine it calls;
// `prefix` is the object a method is applied to (detail 2); `user_defined`
// is the figure's vpiUserDefn; `systf` is the systf object a call of a
// registered system task reaches.
struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
  bool user_defined = false;
  VpiObject* systf = nullptr;
};

// §13.3: whether `decls` declares a task named `name`.
bool DeclaresTask(const std::vector<ModuleItem*>& decls,
                  std::string_view name) {
  return std::ranges::any_of(decls, [name](const ModuleItem* decl) {
    return decl != nullptr && decl->kind == ModuleItemKind::kTaskDecl &&
           decl->name == name;
  });
}

// §26.2: whether the package the design declares under `package` declares a
// task named `name`.
bool PackageDeclaresTask(const RtlirDesign& design, std::string_view package,
                         std::string_view name) {
  return std::ranges::any_of(design.packages, [&](const PackageDecl* decl) {
    return decl != nullptr && decl->name == package &&
           DeclaresTask(decl->items, name);
  });
}

// §13.3: whether `name` is a task the instance's module, one of its generate
// blocks or the compilation unit declares, or, by §26.3, one the module
// imports from a package by its name or with a wildcard.
bool NamesTask(const BodyWalk& walk, std::string_view name) {
  if (DeclaresTask(walk.mod.function_decls, name) ||
      DeclaresTask(walk.design.cu_function_decls, name)) {
    return true;
  }
  if (std::ranges::any_of(walk.mod.gen_block_subroutines,
                          [name](const RtlirGenBlockSubroutine& sub) {
                            return sub.decl != nullptr &&
                                   sub.decl->kind ==
                                       ModuleItemKind::kTaskDecl &&
                                   sub.decl->name == name;
                          })) {
    return true;
  }
  return std::ranges::any_of(walk.mod.imports, [&](const RtlirImport& entry) {
    return (entry.is_wildcard || entry.item_name == name) &&
           PackageDeclaresTask(walk.design, entry.package_name, name);
  });
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

// §9.7, §15.3.3, §15.4.3, §15.4.5 and §15.4.7: the methods the built-in
// classes declare as tasks, every other method of theirs being a function.
bool IsBuiltInClassTask(std::string_view cls, std::string_view method) {
  static constexpr std::pair<std::string_view, std::string_view> kTasks[] = {
      {"process", "await"}, {"semaphore", "get"}, {"mailbox", "put"},
      {"mailbox", "get"},   {"mailbox", "peek"},
  };
  return std::ranges::any_of(kTasks, [&](const auto& task) {
    return task.first == cls && task.second == method;
  });
}

// What the method a call names is: no task, a task of a class the design
// declares, or a task of a built-in class.
enum class MethodTask : uint8_t { kNone, kDeclared, kBuiltIn };

// The kind of task `method` of the class `cls` is, found in the class or, by
// §8.13, in the classes it extends. A class the design declares answers ahead
// of a built-in one of its name, which §15.2 lets user code redefine. The
// bound stops a chain of extensions that loops.
MethodTask ClassMethodTask(const BodyWalk& walk, std::string_view cls,
                           std::string_view method) {
  constexpr int kMaxDepth = 64;
  for (int depth = 0; depth < kMaxDepth && !cls.empty(); ++depth) {
    const ClassDecl* decl = FindClassDecl(walk, cls);
    if (decl == nullptr) {
      return IsBuiltInClassTask(cls, method) ? MethodTask::kBuiltIn
                                             : MethodTask::kNone;
    }
    const ModuleItem* found = MethodNamed(*decl, method);
    if (found != nullptr) {
      return found->kind == ModuleItemKind::kTaskDecl ? MethodTask::kDeclared
                                                      : MethodTask::kNone;
    }
    cls = decl->base_class;
  }
  return MethodTask::kNone;
}

// §8.4: the class a variable of the instance's module named `name` holds a
// handle of, empty for a variable of no class type and for no variable.
std::string_view ClassOfVariable(const RtlirModule& mod,
                                 std::string_view name) {
  for (const RtlirVariable& var : mod.variables) {
    if (var.name == name) return var.class_type_name;
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

// §37.42: a system task call, named after the system task it calls. A system
// function stays a function where a statement calls it, and the evaluator runs
// it as one (§36.5), so it is no system task call. A name an application
// registered is what the registration made it, which the run calls it as.
CallShape SystemTaskCallShape(const Expr& call, const BodyWalk& walk) {
  const VpiRegisteredSystf kSystf = walk.calls.systf(call.callee);
  if (kSystf.type == vpiSysFunc) return {};
  if (kSystf.type == 0 && IsBuiltInSystemFunction(call.callee)) return {};
  CallShape shape{vpiSysTaskCall, call.callee};
  shape.user_defined = kSystf.type == vpiSysTask;
  shape.systf = kSystf.object;
  return shape;
}

// §8.4: the variable a call's prefix names, as the class it holds a handle of
// (empty for a variable of no class type and for no variable) and the object
// standing for it.
struct ClassVar {
  std::string_view cls;
  VpiObject* object = nullptr;
};

// §23.9: the variable `name` names in the scope `parent` stands for: one a
// block declares, the innermost around the statement first, or else one of the
// instance's module.
ClassVar FindClassVar(const BlockParent& parent, std::string_view name,
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
              ChildNamed(at->scope, name)};
    }
  }
  return {ClassOfVariable(walk.mod, name),
          FindObjectForFlatName(walk.objects, VpiFlatName(walk.prefix, name))};
}

// §37.42: a method task call, applied through `access`, which joins two
// names, to a class var of the scope the call stands in.
CallShape MethodTaskCallShape(const Expr& access, const BlockParent& parent,
                              const BodyWalk& walk) {
  const ClassVar kVar = FindClassVar(parent, access.lhs->text, walk);
  const MethodTask kTask = ClassMethodTask(walk, kVar.cls, access.rhs->text);
  if (kTask == MethodTask::kNone) return {};
  CallShape shape{vpiMethodTaskCall, access.rhs->text};
  shape.prefix = kVar.object;
  // Detail 11 tells a built-in method call apart from the rest, and the
  // figure's vpiUserDefn is what says which a method call is.
  shape.user_defined = kTask == MethodTask::kDeclared;
  return shape;
}

// Whether the member access or scope resolution `access` joins two plain
// names, `obj.run` or `p::t`, the one form of either this walk resolves.
bool JoinsTwoNames(const Expr& access) {
  return access.lhs != nullptr && access.rhs != nullptr &&
         access.lhs->kind == ExprKind::kIdentifier &&
         access.rhs->kind == ExprKind::kIdentifier;
}

// §37.42 with §26.3: a task call naming a package's task behind the package's
// name, `p::t`.
CallShape PackageTaskCallShape(const Expr& access, const BodyWalk& walk) {
  if (!PackageDeclaresTask(walk.design, access.lhs->text, access.rhs->text)) {
    return {};
  }
  return CallShape{vpiTaskCall, access.rhs->text};
}

// §37.42 with §37.60: what the expression statement `expr`, standing in the
// scope `parent` stands for, calls. A task is enabled with or without an
// argument list (§13.3), so the callee is the expression itself where no list
// follows it.
CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk) {
  if (expr.kind == ExprKind::kSystemCall) {
    return SystemTaskCallShape(expr, walk);
  }
  const Expr* callee = expr.kind == ExprKind::kCall ? expr.lhs : &expr;
  if (callee == nullptr) return {};
  if (callee->kind == ExprKind::kIdentifier) {
    if (!NamesTask(walk, callee->text)) return {};
    return CallShape{vpiTaskCall, callee->text};
  }
  if (callee->kind != ExprKind::kMemberAccess || !JoinsTwoNames(*callee)) {
    return {};
  }
  if (callee->is_scope_resolution) return PackageTaskCallShape(*callee, walk);
  return MethodTaskCallShape(*callee, parent, walk);
}

// §37.42: the arguments `expr` was written with, in order, each the
// expression object the instance's names resolve it to (§37.58, §37.59), an
// empty position being detail 8's empty argument. An expression of a kind the
// model builds no object for is passed over.
void MakeCallArguments(VpiObject* call, const Expr& expr,
                       const BodyWalk& walk) {
  if (expr.kind != ExprKind::kCall && expr.kind != ExprKind::kSystemCall) {
    return;
  }
  for (const Expr* actual : expr.args) {
    VpiObject* arg = nullptr;
    if (actual == nullptr) {
      arg = walk.build.alloc();
      VpiMakeEmptyArgument(arg);
    } else {
      arg = VpiInstanceExpression(actual, walk.objects, walk.prefix,
                                  walk.calls.ctx, walk.build);
    }
    if (arg != nullptr) call->arguments.push_back(arg);
  }
}

// §37.42 with §37.60: the call statement `stmt` stands as, null for a
// statement that calls no task. A call is named after what it calls; a label
// written on it names the begin §9.3.5 makes around it instead. A system task
// call is recorded as the call statement it is, which a run's invocation of a
// registered system task stands as (detail 3).
VpiObject* MakeCallStatement(const Stmt& stmt, const BlockParent& parent,
                             const BodyWalk& walk) {
  if (stmt.kind != StmtKind::kExprStmt || stmt.expr == nullptr) return nullptr;
  const CallShape kShape = CallShapeOf(*stmt.expr, parent, walk);
  if (kShape.type == 0) return nullptr;
  VpiObject* call = MakeAtomicStatement(stmt, kShape.type, parent, walk);
  call->name = walk.build.keep(std::string(kShape.name));
  call->tf_prefix = kShape.prefix;
  call->user_defined = kShape.user_defined;
  call->user_systf = kShape.systf;
  MakeCallArguments(call, *stmt.expr, walk);
  if (kShape.type == vpiSysTaskCall) {
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
  MakeBlockVariables(block, stmt, path, walk.build);
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

// The scope a process of `instance` stands in: the generate block instance
// its path names, outermost first, or the instance itself for an empty path.
VpiObject* ProcessScope(VpiObject* instance, const HierPath& path) {
  VpiObject* scope = instance;
  for (const HierStep& step : path) {
    if (scope == nullptr) return nullptr;
    std::string name(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    scope = ChildNamed(scope, name);
  }
  return scope;
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
    VpiObject* scope = ProcessScope(instance, proc.gen_block_path);
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
