#pragma once

#include <cstddef>
#include <deque>
#include <vector>

#include "elaborator/type_site_lookup.h"

namespace delta {

struct ModuleItem;
struct Stmt;

class LocalTypeSites {
 public:
  struct Depth {
    std::size_t sites = 0;
    std::size_t decls = 0;
  };

  Depth Here() const { return {sites_.size(), decls_.size()}; }

  void OpenItems(const std::vector<ModuleItem*>& items, const TypeSite& module);

  void OpenStmts(const std::vector<Stmt*>& stmts, const TypeSite& module);

  void Restore(Depth depth);

  const TypeSite* Innermost() const {
    return sites_.empty() ? nullptr : &sites_.back();
  }

 private:
  std::deque<TypeSite> sites_;
  std::deque<std::vector<ModuleItem*>> decls_;
};

}  // namespace delta
