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

// §6.20.5: every specparam a delay expression inside `block` may read. A
// specparam "may be declared inside a specify block or in the module body", and
// §30.5 lets a module path delay name one without saying which site it came
// from, so both are collected: CollectSpecparams above reads the block and this
// adds the ones `mod` declares outside every block.
SignalSet CollectSpecparamsInScope(const ModuleDecl* mod,
                                   const ModuleItem* block);

// The specify-block construct one checked expression belongs to. Two of them
// are required to be constant expressions over specparams: the path_delay_value
// of a module path (§30.5) and the timing_check_limit of a timing check
// (§31.2). `operand` names the construct in the diagnostic and `subclause` is
// the one requiring that construct's expression be constant.
struct SpecifyConstantExpr {
  std::string_view operand;
  Subclause subclause;
};

// §30.4.1: rejects an operand of a delay or limit expression that is neither
// constant nor one of `specparams`.
void CheckDelayExpr(const Expr* e, SourceLoc loc, const SignalSet& specparams,
                    DiagEngine& diag, SpecifyConstantExpr constant_expr);

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
//
// `subclause` is the one the check's own subclause of §31.3 or §31.4 states the
// rule in, which is the subclause the caller names alongside the task.
void ValidateTimingCheckLimitNonNegative(const ModuleDecl* mod,
                                         DiagEngine& diag, TimingCheckKind kind,
                                         std::string_view task,
                                         Subclause subclause);
void ValidateConditionExprs(const ModuleDecl* mod, const PortMap& port_map,
                            DiagEngine& diag);
void ValidatePulseControlTerminals(const ModuleDecl* mod,
                                   const PortMap& port_map, DiagEngine& diag);

}  // namespace delta
