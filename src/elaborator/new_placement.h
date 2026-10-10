#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

// §7.5.1 (printed pages 158–159) with A.6.2: `new`, whether it constructs a
// dynamic array (`new [n]`) or an object, is no expression. It stands only as
// the whole right-hand side of a blocking assignment or of a variable's
// declaration assignment, and a `new [n]` only where that left-hand side is a
// dynamic array. Reports, among the module `decl`'s items, procedural blocks
// and subroutines:
// - a `new` written as an operand of a larger right-hand side;
// - a `new` on the right-hand side of a nonblocking or continuous assignment;
// - a `new` assigned to a variable, or to an element of one, that the
//   declaration makes a fixed-size or associative array or a value of a
//   built-in type, none of which a `new` constructs.
// A target whose type is a name (a class, or a typedef that may stand for a
// dynamic array) is left alone, as is a `new` among a call's arguments, which
// the parser reports. Each select of the left-hand side takes one dimension.
void CheckNewPlacement(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
