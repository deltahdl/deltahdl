#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

// §17.2 and §17.3's ps_checker_identifier: the checker an instance names by
// its package, `p::chk`, or by a name an import of the package made visible
// in the instantiating scope `mod`, `chk` under `import p::*` or `import
// p::chk` (§26.3); nullptr where it names none.
ModuleDecl* PackageCheckerNamedBy(const ModuleItem* item,
                                  const RtlirModule* mod,
                                  const CompilationUnit* unit);

// The formals an instance of a checker binds, each with the value of its
// actual in the instantiating scope where that actual is an elaboration-time
// constant.
using BoundCheckerFormals =
    std::vector<std::pair<std::string_view, std::optional<int64_t>>>;

// The formals of a checker that are elaboration-time constants, with their
// values.
using ConstantCheckerFormals =
    std::vector<std::pair<std::string_view, int64_t>>;

// §17.3: the formals of the checker `decl` the instance `item` binds, by
// position or by name, each actual folded in `scope`, the instantiating one.
BoundCheckerFormals BindCheckerActuals(const ModuleItem* item,
                                       const ModuleDecl* decl,
                                       const ScopeMap& scope);

// §17.2 and §17.9: a checker formal whose actual, or default where the
// instance binds none, is an elaboration-time constant is that constant within
// the checker, so a generate construct of the checker tests it (§27.5). The
// defaults are folded in `scope`, the checker's own.
ConstantCheckerFormals CheckerConstantFormals(const ModuleDecl* decl,
                                              const BoundCheckerFormals& bound,
                                              const ScopeMap& scope);

}  // namespace delta
