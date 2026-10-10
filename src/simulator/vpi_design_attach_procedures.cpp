#include <algorithm>
#include <array>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_procedures_internal.h"
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
  const std::string kGen =
      walk.gen_prefixes->empty() ? "" : std::string(walk.gen_prefixes->back());
  return VpiFlatName(walk.prefix, kGen + scopes + std::string(name));
}

// §37.12 (figure): the variables a block declares hang from it, each named
// under the block's path and keyed as the run keys its storage. A block
// parameter is a block item declaration but no variable.
void MakeBlockVariables(VpiObject* block, const Stmt& stmt,
                        const std::string& path, const BlockParent& parent,
                        const BodyWalk& walk) {
  for (const Stmt* item : BlockItems(stmt)) {
    if (item->kind != StmtKind::kVarDecl || item->var_is_param) continue;
    VpiObject* var = walk.build.alloc();
    var->type = BlockVariableKind(*item, walk);
    var->parent = block;
    var->name = walk.build.keep(std::string(item->var_name));
    var->full_name = path + "." + std::string(item->var_name);
    var->run_key = BlockVariableRunKey(item->var_name, stmt, parent, walk);
    block->children.push_back(var);
  }
}

// §15.5.1 with §23.6: the name a trigger names its event by as written, an
// identifier or a hierarchical name of identifiers joined by periods, `m.e`;
// empty for a target written through anything else, such as a select of an
// array of events, which names no one declaration of the design.
std::string EventTriggerTargetName(const Stmt& stmt) {
  std::vector<std::string_view> names;
  if (!ChainNames(*stmt.expr, names)) return {};
  std::string joined(names.front());
  for (std::size_t i = 1; i < names.size(); ++i) {
    joined += "." + std::string(names[i]);
  }
  return joined;
}

// §23.9 with §23.8: the named event object `name`, written by a statement
// standing in `parent`, resolves to: one a block around the statement
// declares, the innermost first, or else one found below the instance or, by
// an upward name, below an instance enclosing it, the nearest first. Null where
// the name reaches no object the design built, such as a class's event
// property, which each object of the class holds for itself.
VpiObject* TriggeredEvent(const std::string& name, const BlockParent& parent,
                          const BodyWalk& walk) {
  const BlockParent* where = nullptr;
  if (BlockVarDecl(parent, name, where) != nullptr) {
    return ChildNamed(where->scope, name);
  }
  std::string scope = walk.prefix;
  for (;;) {
    VpiObject* found =
        FindObjectForFlatName(walk.objects, VpiFlatName(scope, name));
    if (found != nullptr || scope.empty()) return found;
    const std::size_t kDot = scope.rfind('.');
    scope.resize(kDot == std::string::npos ? 0 : kDot);
  }
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
  const std::string kTarget = EventTriggerTargetName(stmt);
  if (kTarget.empty()) return obj;
  VpiObject* event = TriggeredEvent(kTarget, parent, walk);
  if (event != nullptr) obj->children.push_back(event);
  return obj;
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

// §7.12.1: the array locator methods, whose calls §37.42 detail 1 has
// vpiWith reach the with expression of.
constexpr std::array<std::string_view, 10> kLocatorMethods = {
    "find",      "find_index",      "find_first", "find_first_index",
    "find_last", "find_last_index", "min",        "max",
    "unique",    "unique_index"};

// §18.7 with §37.34: the constraint the inline constraint block `block` of
// the call `call` of randomize stands as, a constraint §37.31 detail 3 calls
// inline. A name in it finds the properties of the class `defn` of the
// randomized object, and of those it extends, ahead of the declarations of
// the scope the call stands in.
VpiObject* InlineConstraint(const ClassMember& block, VpiObject* call,
                            const VpiObject* defn, const BlockParent& parent,
                            const BodyWalk& walk) {
  static const GenBlockPrefixes kNoGenBlocks;
  VpiObject* constraint = VpiMakeConstraint(
      block, call,
      {walk.objects, walk.prefix,
       walk.gen_prefixes != nullptr ? *walk.gen_prefixes : kNoGenBlocks,
       VpiClassNameScope(defn, parent.scope, walk.build), walk.calls.ctx},
      walk.build);
  constraint->inline_constraint = true;
  return constraint;
}

// §37.42 detail 1: what a call `expr` of a randomize method or an array
// locator method is written with, hung from `call`'s vpiWith: the inline
// constraint block of a call of randomize (§18.7), a constraint §37.31 detail 3
// calls inline, or the with expression of a locator method's call. Any other
// call, with clause or not, has no vpiWith.
void MakeWithClause(VpiObject* call, const Expr& expr,
                    const BlockParent& parent, const BodyWalk& walk) {
  call->tf_with_method =
      call->type == vpiMethodFuncCall &&
      (call->name == "randomize" ||
       std::ranges::find(kLocatorMethods, call->name) != kLocatorMethods.end());
  if (!call->tf_with_method) return;
  // §18.7: the identifier list of a restricted block, randomize() with (a)
  // {...}, is kept as a with expression too, so the block is looked for first.
  if (expr.inline_constraint != nullptr) {
    call->tf_with = InlineConstraint(
        *expr.inline_constraint, call,
        MethodCallClassDefn(*expr.lhs, parent, walk), parent, walk);
  } else if (expr.with_expr != nullptr) {
    call->tf_with = VpiCallSiteExpression(expr.with_expr, walk.objects,
                                          CallSiteOf(parent, walk),
                                          walk.calls.ctx, walk.build);
  }
}

// §37.42: give `call` what the shape `shape` of the call `called`, standing
// in `parent`, says it is: its kind, its name, what a method is applied to
// (detail 2), the subroutine it calls, whether that is user-defined, the
// systf of a registered system task or function, its arguments and its with
// clause (detail 1).
void FillCall(VpiObject* call, const CallShape& shape, const Expr& called,
              const BlockParent& parent, const BodyWalk& walk) {
  call->type = shape.type;
  call->name = walk.build.keep(std::string(shape.name));
  call->tf_prefix = shape.prefix;
  call->prefix_members = shape.prefix_members;
  call->tf_decl = shape.called;
  call->user_defined = shape.user_defined;
  call->user_systf = shape.systf;
  MakeCallArguments(call, called, parent, walk);
  MakeWithClause(call, called, parent, walk);
}

// §37.42 with §37.60: the call statement `stmt` stands as, null for a
// statement that calls nothing the walk resolves. A call is named after what
// it calls; a label written on it names the begin §9.3.5 makes around it
// instead. It is marked as written as a statement, which tells a function call
// standing as one from a function call standing as an expression. A system
// task or function call decompiles to the call written (detail 9), and is
// recorded as the call statement it is, which a run's invocation of a
// registered system task or function stands as (detail 3). A function call
// written in a void cast, void'(f()); (§13.4.1), is the call it wraps: the
// parser records that statement as the cast, the one cast a statement can be.
VpiObject* MakeCallStatement(const Stmt& stmt, const BlockParent& parent,
                             const BodyWalk& walk) {
  if (stmt.kind != StmtKind::kExprStmt) return nullptr;
  const Expr* called =
      stmt.expr->kind == ExprKind::kCast ? stmt.expr->lhs : stmt.expr;
  const CallShape kShape = CallShapeOf(*called, parent, walk);
  if (kShape.type == 0) return nullptr;
  VpiObject* call = MakeAtomicStatement(stmt, kShape.type, parent, walk);
  call->written_as_stmt = true;
  FillCall(call, kShape, *called, parent, walk);
  if (kShape.type == vpiSysTaskCall || kShape.type == vpiSysFuncCall) {
    call->decompile = VpiExprDecompile(called);
    walk.calls.sites[{called, walk.prefix}] = call;
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

// What a statement at `parent` builds with, while `parent` and `walk` live.
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
          },
          [site = CallSiteOf(parent, walk), &walk](const Expr* expr,
                                                   const VpiObject* target) {
            return VpiCallSiteAssignedExpression(
                {expr, target}, walk.objects, site, walk.calls.ctx, walk.build);
          },
          [&walk](std::string_view name) {
            return VpiImportedPropertyDecl(name, walk.mod.imports,
                                           walk.objects);
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
  const int kAtomic = VpiBareAtomicKind(stmt.kind);
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

// §37.63 detail 1: the always type of a procedure of `kind`, the keyword that
// opened it, 0 for an initial or final procedure, which has none.
int AlwaysTypeOf(RtlirProcessKind kind) {
  if (kind == RtlirProcessKind::kInitial || kind == RtlirProcessKind::kFinal) {
    return 0;
  }
  if (kind == RtlirProcessKind::kAlwaysComb) return vpiAlwaysComb;
  if (kind == RtlirProcessKind::kAlwaysFF) return vpiAlwaysFF;
  return kind == RtlirProcessKind::kAlwaysLatch ? vpiAlwaysLatch : vpiAlways;
}

// §37.63: the object a procedure stands as, one of the three kinds the
// `process` class groups, with detail 1's always type for an always procedure.
VpiObject* MakeProcess(const RtlirProcess& proc, VpiObject* scope,
                       const VpiAttachBuild& build) {
  VpiObject* process = build.alloc();
  process->always_type = AlwaysTypeOf(proc.kind);
  process->type = vpiAlways;
  if (proc.kind == RtlirProcessKind::kInitial) process->type = vpiInitial;
  if (proc.kind == RtlirProcessKind::kFinal) process->type = vpiFinal;
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
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &entry.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    make(entry, scope, StmtBuildAt(kParent, walk));
  }
}

// The properties one instance declares, each in the generate block instance
// writing it, walked with `instance_walk`.
void AttachInstanceProperties(VpiObject* instance,
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
}

// The assertions one instance writes as items, each in the generate block
// instance writing it, and the procedures it declares with the objects their
// bodies hold, walked with `instance_walk`, whose process each procedure's
// own replaces. An assertion the elaborator carries as a process is no
// procedure the source wrote, a concurrent one being the item's (§37.50).
void AttachInstanceProcedures(VpiObject* instance,
                              const BodyWalk& instance_walk) {
  AttachScopedItems(
      instance, instance_walk, instance_walk.mod.assertions,
      [&instance_walk](const RtlirAssertion& assertion, VpiObject* scope,
                       const VpiStmtBuild& with) {
        VpiMakeItemAssertion(assertion, scope, instance_walk.calls.ctx, with);
      });
  for (const RtlirProcess& proc : instance_walk.mod.processes) {
    // A process stands in the generate block instance its path names.
    VpiObject* scope = VpiGenScopeOf(instance, proc.gen_block_path);
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &proc.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    if (!proc.is_static_assertion) {
      walk.process = MakeProcess(proc, scope, instance_walk.build);
      walk.process->body = WalkProcessBody(proc, kParent, walk);
    } else if (proc.body->is_deferred) {
      // §16.4.3: a deferred assertion item is the statement it runs (§37.55).
      MakeBuiltStmt(*proc.body, kParent, walk);
    }
  }
}

}  // namespace

bool ShapeExprCall(const Expr& call, VpiObject* made, const BlockParent& parent,
                   const BodyWalk& walk) {
  const CallShape kShape = CallShapeOf(call, parent, walk);
  if (kShape.type == 0) return false;
  FillCall(made, kShape, call, parent, walk);
  return true;
}

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build) {
  // §37.63: each procedure an instance declares is a process of it, reaching
  // the statement it runs; §37.12: each begin or fork is a block of the
  // instance whose procedure writes it, and detail 1 makes a named one, and an
  // unnamed one declaring a block item, a scope; §37.62: each event trigger
  // is an event statement, §37.42: each call of a task, a method task or a
  // system task a call statement, and each statement VpiBuiltStmtKind names
  // an object of its kind, each hung from the block or statement it stands in.
  if (design->top_modules.empty() || design->top_modules.front() == nullptr) {
    return;
  }
  // The first top carries the empty prefix and is keyed under its own name.
  // §37.51: every instance's properties are built ahead of every assertion,
  // which may instantiate one through an instance below its own (§23.6).
  const std::string kFirstTop(design->top_modules.front()->name);
  const auto kWalk = [&](void (*attach)(VpiObject*, const BodyWalk&)) {
    WalkInstancePaths(
        design, [&](const RtlirModule* mod, const std::string& prefix) {
          attach(FindObjectForFlatName(objects,
                                       prefix.empty() ? kFirstTop : prefix),
                 BodyWalk{*design, *mod, objects, prefix, calls, build});
        });
  };
  kWalk(AttachInstanceProperties);
  kWalk(AttachInstanceProcedures);
}

}  // namespace delta
