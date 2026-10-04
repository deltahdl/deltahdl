#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
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
// between them leaves as it was.
struct BlockParent {
  VpiObject* scope;
  const std::string& path;
};

// What a walk of one procedure body builds with: the objects the instance's
// declarations stand as, keyed under its prefix, the process the body runs in
// (null for an assertion the elaborator carries as a process), and the build.
struct BodyWalk {
  const VpiObjectMap& objects;
  const std::string& prefix;
  VpiObject* process;
  const VpiAttachBuild& build;
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
  WalkSubStmts(stmt, BlockParent{block, path}, walk);
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
  WalkStmtItself(*stmt, BlockParent{begin, path}, walk);
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

// The procedures one instance declares, each with the objects its body holds.
// An assertion the elaborator carries as a process is no procedure the source
// wrote, so it stands as none, though the statements of its action blocks are
// statements of the design all the same.
void AttachInstanceProcedures(const RtlirModule& mod, VpiObject* instance,
                              const std::string& prefix,
                              const VpiObjectMap& objects,
                              const VpiAttachBuild& build) {
  for (const RtlirProcess& proc : mod.processes) {
    VpiObject* scope = ProcessScope(instance, proc.gen_block_path);
    if (scope == nullptr) continue;
    const bool kIsAssertion =
        proc.is_static_assertion || proc.is_concurrent_clocked;
    VpiObject* process =
        kIsAssertion ? nullptr : MakeProcess(proc, scope, build);
    const BodyWalk kWalk{objects, prefix, process, build};
    const BlockParent kParent{scope, scope->full_name};
    if (process != nullptr) {
      process->body = WalkStmt(proc.body, kParent, kWalk);
    } else if (proc.body != nullptr) {
      // The body of such a process is the assertion itself, whose label names
      // the assertion (§16.5) rather than a block around it.
      WalkSubStmts(*proc.body, kParent, kWalk);
    }
  }
}

}  // namespace

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiAttachBuild& build) {
  // §37.63: each procedure an instance declares is a process of it, reaching
  // the statement it runs; §37.12 detail 1: a named begin or fork, and an
  // unnamed one declaring a block item, is a scope of the instance whose
  // procedure writes it; §37.62: each event trigger is an event statement of
  // the scope it stands in. No procedure was made, so none was reached, and
  // the event statements all hung from the instance whatever block they were
  // written in.
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
          AttachInstanceProcedures(*mod, instance, prefix, objects, build);
        }
      });
}

}  // namespace delta
