#pragma once

#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;

// §16.14.6.1: the values a pending instance of a procedural concurrent
// assertion saved when it was placed in the procedural assertion queue: the
// value of each const cast expression and of each automatic variable of the
// property and of its action block, keyed by the expression site, which the
// evaluation of that instance reads in the site's place for as long as the
// instance is evaluated, where a static variable is sampled in the Preponed
// region of each tick. One instance keeps its own, so a statement a loop
// reaches once per value of an automatic loop variable queues one instance
// per value.
struct InstanceBindings {
  std::vector<std::pair<const Expr*, Logic4Vec>> values;

  // The value saved for `site`, or nullptr where none was.
  const Logic4Vec* Find(const Expr* site) const {
    for (const auto& [bound, value] : values) {
      if (bound == site) return &value;
    }
    return nullptr;
  }
};

}  // namespace delta
