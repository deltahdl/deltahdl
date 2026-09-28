#pragma once

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleItem;

// §6.25 (printed pages 144 and 145) with §8.25: a typedef a parameterized
// class declares, reached through a specialization, `C#(t_t0,3)::t_array a0;`,
// is the typedef written in terms of that specialization's parameters. When
// `item` declares a variable so, its type is rewritten to the typedef's type
// with each type parameter replaced by the type the specialization binds it
// to, and each packed and unpacked dimension folded with the values the
// specialization binds the value parameters to; the typedef's unpacked
// dimensions become the declaration's, where it writes none of its own. A
// parameter the specialization leaves out takes its default. `module_scope`
// and `typedefs` are the declaring module's, which the specialization's
// arguments are written in. Answers whether the declaration was rewritten; a
// class, typedef or dimension this cannot resolve leaves it as it was.
bool SpecializeClassScopedTypedef(ModuleItem* item, const CompilationUnit* unit,
                                  const ScopeMap& module_scope,
                                  const TypedefMap& typedefs, Arena& arena);

}  // namespace delta
