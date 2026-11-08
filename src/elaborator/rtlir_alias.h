#pragma once

#include <vector>

#include "elaborator/rtlir_scopes.h"

namespace delta {

struct Expr;

struct RtlirAlias {
  std::vector<Expr*> nets;
  GenBlockPrefixes gen_block_prefixes;
};

}  // namespace delta
