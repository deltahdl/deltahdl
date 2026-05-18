#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "parser/ast.h"

namespace delta {

// §16.12 anchors property semantics on the flattened form produced by the
// §F.4.1 rewriting algorithm. Both subclauses share one legality rule: a
// flattened property that is not legal makes its source not legal.

struct FlattenedProperty {
  std::string_view name;
  std::size_t formal_count = 0;
  int disable_iff_count = 0;
  bool legal = false;
  int remaining_instances = 0;
};

class PropertyRegistry {
 public:
  void Register(const ModuleItem* decl);

  const ModuleItem* Find(std::string_view name) const;

  // §F.4.1 step 1 inlines callees recursively; this returns the total
  // `disable iff` count after that inlining finishes.
  int FlattenedDisableIffCount(const ModuleItem* decl) const;

  FlattenedProperty Flatten(std::string_view name,
                            std::size_t actual_arg_count) const;

  // §F.4.1 closes by saying a rewritten property may be the top-level
  // property of a concurrent assertion.
  static bool IsAcceptableAsTopLevelConcurrent(const FlattenedProperty& fp);

 private:
  std::unordered_map<std::string_view, const ModuleItem*> by_name_;
};

}  // namespace delta
