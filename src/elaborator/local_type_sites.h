#pragma once

#include <cstddef>
#include <deque>
#include <vector>

#include "elaborator/type_site_lookup.h"

namespace delta {

struct ModuleItem;
struct Stmt;

// The sites of the scopes within a module that a walk of its items is inside,
// the innermost last: each generate block (§27.5), task or function, and
// begin-end or fork-join block (§23.9) around the item walked. The typedefs
// and imports each of them declares name the types of the variables it
// declares over those of the scopes around it (§6.18), the module's site
// being the outermost.
class LocalTypeSites {
 public:
  // How many scopes the walk is inside, to restore on leaving those opened
  // after it.
  struct Depth {
    std::size_t sites = 0;
    std::size_t decls = 0;
  };

  Depth Here() const { return {sites_.size(), decls_.size()}; }

  // Opens the generate block whose items are `items`, in the module whose
  // site is `module`.
  void OpenItems(const std::vector<ModuleItem*>& items, const TypeSite& module);

  // Opens the task, function or block whose declarations and statements are
  // `stmts`, in the module whose site is `module`: the block item
  // declarations among them, typedefs and imports.
  void OpenStmts(const std::vector<Stmt*>& stmts, const TypeSite& module);

  // Leaves each scope opened since the walk was `depth` deep.
  void Restore(Depth depth);

  // The site of the innermost scope opened; null where none is.
  const TypeSite* Innermost() const {
    return sites_.empty() ? nullptr : &sites_.back();
  }

 private:
  // The module's site, once a scope is open, then each scope's.
  std::deque<TypeSite> sites_;
  // The block item declarations of each task, function or block opened.
  std::deque<std::vector<ModuleItem*>> decls_;
};

}  // namespace delta
