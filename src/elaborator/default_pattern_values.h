#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

// §10.9 (printed page 260) gives an assignment pattern no self-determined
// type, so an untyped one stands only where an assignment-like context gives
// it one, and §10.8 (printed pages 259-260) leaves the default correspondence
// between a pattern's `default:` value and the fields or elements it covers
// out of those contexts. §10.9.1 (printed page 262) applies the value to
// elements of a simple type, never to an aggregate whole. Reports each untyped
// pattern the module `decl` writes as the value of a `default:` key, in a
// parameter, a declaration's initializer, a continuous assignment or a
// statement of a process or a subroutine.
void CheckUntypedDefaultPatternValues(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
