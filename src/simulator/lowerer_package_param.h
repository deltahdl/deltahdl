#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct ModuleItem;
struct Variable;

// The width a parameter's declaration fixes as far as it folds with no name
// in scope, for the storage created before any parameter holds a value; 0
// where the declaration fixes none or a range's bound names a parameter, the
// storage then taking 32 bits until the initializer's own width replaces it
// (InitPackageParam).
uint32_t DeclaredParamStorageWidth(const ModuleItem* item, SimContext& ctx);

// §11.6.1 (printed page 299) with §6.12.1: `value`, the right-hand side of an
// assignment to `var` of an integral type, as `var` holds it at `width` bits:
// a real rounded to an integer rather than carried as its double's bits, cut
// or extended, its x and z bits taken as 0 for a 2-state type (§6.11.2) and
// signed as the declaration is. The words are copied, as an initializer that
// is a bare name answers that name's own storage.
Logic4Vec HeldAtWidth(Logic4Vec value, uint32_t width, const Variable& var,
                      Arena& arena);

// §6.20.2 (printed pages 126-127) with §11.6.1 (printed 299): a parameter
// declared with a range or a type keeps that range whatever its value, and
// its initializer is the right-hand side of an assignment to it, so the
// value is evaluated at the declared width, which an unbased unsized literal
// fills (§5.7.1), and cut or extended to it, as ReevaluateParamValue
// (lowerer_register.cpp) sizes a module's; one declared with neither takes
// its value's range. HeldAtWidth converts the value to an integral type,
// rounding a real, and a real type holds a real (§6.12.1).
void InitPackageParam(const ModuleItem* item, Variable* var, SimContext& ctx,
                      Arena& arena);

}  // namespace delta
