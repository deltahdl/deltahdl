#include "elaborator/local_type_sites.h"

#include <vector>

#include "elaborator/type_site_lookup.h"
#include "parser/ast_stmt.h"

namespace delta {

void LocalTypeSites::OpenItems(const std::vector<ModuleItem*>& items,
                               const TypeSite& module) {
  if (sites_.empty()) sites_.push_back(module);
  const TypeSite* outer = &sites_.back();
  sites_.push_back({&items, items.size(), module.kind, outer});
}

void LocalTypeSites::OpenStmts(const std::vector<Stmt*>& stmts,
                               const TypeSite& module) {
  std::vector<ModuleItem*>& decls = decls_.emplace_back();
  for (const Stmt* stmt : stmts) {
    if (stmt->kind == StmtKind::kBlockItemDecl) {
      decls.push_back(stmt->decl_item);
    }
  }
  OpenItems(decls, module);
}

void LocalTypeSites::Restore(Depth depth) {
  sites_.resize(depth.sites);
  decls_.resize(depth.decls);
}

}  // namespace delta
