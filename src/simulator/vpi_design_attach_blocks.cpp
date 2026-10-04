#include <algorithm>
#include <string>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
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

// Where the scopes a statement holds hang: the scope object around it, and the
// path a named one among them is named under, which an unnamed scope between
// them leaves as it was.
struct BlockParent {
  VpiObject* scope;
  const std::string& path;
};

void WalkStmt(const Stmt* stmt, const BlockParent& parent,
              const VpiAttachBuild& build);

// The statements `stmt` holds, each walked for the scopes it writes.
void WalkSubStmts(const Stmt& stmt, const BlockParent& parent,
                  const VpiAttachBuild& build) {
  ForEachChildStmt(&stmt,
                   [&](const Stmt* sub) { WalkStmt(sub, parent, build); });
}

void WalkStmt(const Stmt* stmt, const BlockParent& parent,
              const VpiAttachBuild& build) {
  if (stmt == nullptr) return;
  const int kKind = BlockScopeKind(*stmt);
  if (kKind == 0) {
    WalkSubStmts(*stmt, parent, build);
    return;
  }
  VpiObject* block = build.alloc();
  block->type = kKind;
  block->parent = parent.scope;
  std::string path = parent.path;
  if (!stmt->label.empty()) {
    block->name = build.keep(std::string(stmt->label));
    path += "." + std::string(stmt->label);
    block->full_name = path;
  }
  if (stmt->kind == StmtKind::kFork) {
    block->join_type = JoinTypeOf(stmt->join_kind);
  }
  parent.scope->children.push_back(block);
  MakeBlockVariables(block, *stmt, path, build);
  WalkSubStmts(*stmt, BlockParent{block, path}, build);
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

}  // namespace

void AttachBlockScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                       const VpiAttachBuild& build) {
  // §37.12 detail 1: a named begin or fork, and an unnamed one declaring a
  // block item, is a scope of the instance whose procedure writes it; none was
  // made, so no name reached a block and no scope held one.
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
        if (instance == nullptr) return;
        for (const RtlirProcess& proc : mod->processes) {
          // An assertion the elaborator carries as a process wrote no block.
          if (proc.is_static_assertion || proc.is_concurrent_clocked) continue;
          VpiObject* scope = ProcessScope(instance, proc.gen_block_path);
          if (scope == nullptr) continue;
          WalkStmt(proc.body, BlockParent{scope, scope->full_name}, build);
        }
      });
}

}  // namespace delta
