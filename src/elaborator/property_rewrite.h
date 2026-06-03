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

  // §16.8: it is an error if a cyclic dependency among named sequences
  // results from their instantiations. Returns true iff `decl` lies on a
  // cycle in the directed graph whose edges are sequence-to-sequence
  // instance references (including self-recursion).
  bool HasCyclicSequenceDependency(const ModuleItem* decl) const;

  // §16.12.17 / §F.7: the dependency digraph has the named properties as its
  // vertices and a property-to-property instantiation as each edge. A named
  // property is recursive iff it is in a nontrivial strongly connected
  // component — equivalently, iff it can be reached from itself by following
  // those edges (covering both direct self-instantiation and mutual
  // recursion).
  bool IsRecursiveProperty(const ModuleItem* decl) const;

  // §F.7 RESTRICTION 1: returns true iff a recursive property can be reached in
  // the dependency digraph from `decl`, including `decl` itself. This is the
  // precise notion of "depends on a recursive property".
  bool ReachesRecursiveProperty(const ModuleItem* decl) const;

 private:
  std::unordered_map<std::string_view, const ModuleItem*> by_name_;
};

}  // namespace delta
