#pragma once

#include <vector>

#include "elaborator/rtlir_scopes.h"

namespace delta {

struct Expr;

// §10.11: the nets an alias statement joins, as written. Kept apart from
// rtlir.h, which stood at the size the assert-no-oversized-source-files job
// fails at.
struct RtlirAlias {
  std::vector<Expr*> nets;
  GenBlockPrefixes gen_block_prefixes;  // §27.5: the blocks it stands in.
};

}  // namespace delta
