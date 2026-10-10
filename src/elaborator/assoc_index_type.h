#pragma once

#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"

namespace delta {

struct Expr;

// §7.8.5 (printed page 165): `real` and `shortreal`, and any type that holds
// one, are illegal as an associative array's index type. Reports, at `loc`,
// the first of the unpacked dimensions `dims` whose index type is such a type,
// a typedef name being judged by the type it stands for.
void CheckRealAssocIndexTypes(const std::vector<Expr*>& dims, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag);

}  // namespace delta
