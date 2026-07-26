#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast.h"

namespace delta {

// The signal scopes a specify-block check works against. A PortMap indexes a
// module's declared ports by name, a SignalSet is a bare set of names (module
// locals, or the specparams a delay expression may read).
using PortMap = std::unordered_map<std::string_view, const PortDecl*>;
using SignalSet = std::unordered_set<std::string_view>;

// Helpers defined in elaborator_validate_specify.cpp and shared with the
// timing-check limit validators in elaborator_validate_specify_limits.cpp.

// §30.4.1: the specparams a module declares, which are the only names a delay
// or limit expression may read besides constants.
SignalSet CollectSpecparams(const ModuleItem* item);

// §30.4.1: rejects an operand of a delay or limit expression that is neither
// constant nor one of `specparams`.
// `what` names the construct in the diagnostic; the default suits a module
// path delay, and a timing-check limit passes its own wording.
void CheckDelayExpr(const Expr* e, SourceLoc loc, const SignalSet& specparams,
                    DiagEngine& diag,
                    std::string_view what = "module path delay operand");

// Timing-check and pulse-control validators, defined in
// elaborator_validate_specify_limits.cpp and run per module by
// ValidateOneSpecifyModule.
void ValidateTimingCheckLimitOperands(const ModuleDecl* mod, DiagEngine& diag);

// §31.3, §31.4: the limits of the timing checks that take only non-negative
// limits shall be non-negative constant expressions. Checks every limit a
// timing check of `kind` carries -- the two-limit forms ($fullskew's pair,
// $width's limit and threshold) hold both in the same list, so each is
// reached. `task` names the system task in the diagnostic, `$` included. Only
// a limit that folds to a concrete negative integer is diagnosed; one that
// cannot be folded is left to later stages.
//
// The signed-limit checks $setuphold and $recrem are excluded by construction:
// their limits may legally be negative, so no kind of theirs is ever passed.
void ValidateTimingCheckLimitNonNegative(const ModuleDecl* mod,
                                         DiagEngine& diag, TimingCheckKind kind,
                                         std::string_view task);
void ValidateConditionExprs(const ModuleDecl* mod, const PortMap& port_map,
                            DiagEngine& diag);
void ValidatePulseControlTerminals(const ModuleDecl* mod,
                                   const PortMap& port_map, DiagEngine& diag);

}  // namespace delta
