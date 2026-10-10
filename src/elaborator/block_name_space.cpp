#include "elaborator/block_name_space.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

void CollectNameSpaceLabels(const Stmt* s, std::vector<BlockLabel>& out) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    if (!s->label.empty()) out.emplace_back(s->label, s->range.start);
    return;
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectNameSpaceLabels(sub, out); });
}

// The user-defined type a block's typedef declares, or empty for any other
// block item declaration and for §6.18's forward typedef, which announces the
// type its later definition declares.
static std::string_view BlockTypedefName(const Stmt* s) {
  const ModuleItem* item = s->decl_item;
  if (item->kind != ModuleItemKind::kTypedef ||
      item->typedef_type.kind == DataTypeKind::kImplicit)
    return {};
  return item->name;
}

void CheckBlockNameSpace(const std::vector<Stmt*>& stmts,
                         std::unordered_set<std::string_view> names,
                         DiagEngine& diag) {
  // §23.9 states the rule the closing sentence of §3.13 gives every name
  // space, that an identifier declares one item in a scope, and names the
  // constructs that are scopes, so the report is filed under it.
  auto declare = [&](std::string_view name, SourceLoc loc) {
    if (name.empty() || names.insert(name).second) return;
    diag.Error(loc, std::format("redeclaration of '{}'", name),
               Subclause("23.9"));
  };
  for (const Stmt* child : stmts) {
    if (child == nullptr) continue;
    if (child->kind == StmtKind::kVarDecl) {
      declare(child->var_name, child->range.start);
      continue;
    }
    if (child->kind == StmtKind::kBlockItemDecl) {
      declare(BlockTypedefName(child), child->range.start);
      continue;
    }
    std::vector<BlockLabel> labels;
    CollectNameSpaceLabels(child, labels);
    for (const auto& [label, loc] : labels) declare(label, loc);
  }
}

void CheckNestedBlockNameSpaces(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  // A declaration written directly inside a fork lands in Stmt::fork_stmts on
  // a node whose kind is StmtKind::kFork, so that list is the fork-join
  // block's own name space.
  if (s->kind == StmtKind::kBlock) CheckBlockNameSpace(s->stmts, {}, diag);
  if (s->kind == StmtKind::kFork) CheckBlockNameSpace(s->fork_stmts, {}, diag);
  // §3.13 puts no condition on where a block stands, so every position a
  // statement holds a statement in is one a block may stand in.
  // ForEachChildStmt in elaborator_validate_internal.h states those positions
  // once for the whole elaborator.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckNestedBlockNameSpaces(sub, diag); });
}

}  // namespace delta
