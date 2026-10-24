#pragma once

#include <string_view>
#include <unordered_set>

#include "elaborator/const_eval.h"

namespace delta {

class DiagEngine;
class PropertyRegistry;
struct ModuleDecl;
struct ModuleInUnit;
struct ModuleItem;
struct RtlirModule;
struct Stmt;

// §6.21: the names of the variables with an automatic lifetime in scope in the
// module item `item`: those its statements declare `automatic` and, for an
// automatic task or function, its formals and every local not declared
// `static`.
std::unordered_set<std::string_view> CollectItemAutomaticVarNames(
    const ModuleItem* item);

// §16.14.1 and §16.14.3: the first concurrent assert, assume or cover statement
// the statement `s` holds, `s` itself among them, in source order; null where
// it holds none. A procedural concurrent assertion is parsed as an immediate
// assertion's statement marked is_procedural_concurrent, so an immediate one
// is not counted.
const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s);

// The rules of Clause 16 on the assertions, sequences and properties the
// module `decl` declares that the elaboration of each item does not check
// itself, its named sequences and properties in `registry`, each violation
// reported to `diag`.
void ValidateAssertionRules(const ModuleDecl* decl,
                            const PropertyRegistry& registry, DiagEngine& diag);

// The rules of §16.8.2, §16.9.3, §16.12.14 and §16.13.6 on the expressions of
// the assertions, sequences, properties and procedures the module `decl`
// declares: what a sampled value function may read and how it is clocked,
// what an abort condition may reference, which sequences `triggered` may be
// applied to, and what a local variable formal argument may be bound to and
// must be assigned. `scope` holds the module's declaration and the
// compilation unit that resolves the subroutine a call attached to a sequence
// names, `mod` gives the clock a procedure infers and the default clocking,
// `params` the module's parameters by value, and `registry` its named
// sequences and properties.
void ValidateAssertionExprRules(const ModuleInUnit& scope,
                                const RtlirModule* mod, const ScopeMap& params,
                                const PropertyRegistry& registry,
                                DiagEngine& diag);

// §16.7, §16.12.10, §16.12.11 and §16.12.13: the bounds of the cycle delays
// and of the nexttime, always and eventually operators the module `decl`
// writes other than as integer literals, folded with the parameters in
// `params` and, where a bound names a sequence's formal, with that formal
// bound to each instance's actual; a negative bound, an inverted range and an
// operator bound that does not fold to a constant are reported to `diag`.
void ValidateAssertionBoundRules(const ModuleDecl* decl, const ScopeMap& params,
                                 DiagEngine& diag);

// §16.9.4, §16.9.11 and §16.13.6: the rules on an assertion or a sequence as a
// whole the module `decl` declares, its named sequences and properties in
// `registry`: a global clocking future sampled value function stands in no
// assertion holding a sequence match item, a sequence triggered is applied to
// ends on the clock of the context the method stands in, a procedure's being
// the clock `mod` infers for it, and no sequence depends on its own end point
// through triggered.
void ValidateAssertionContextRules(const ModuleDecl* decl,
                                   const RtlirModule* mod,
                                   const PropertyRegistry& registry,
                                   DiagEngine& diag);

// §16.8.2 and §16.10, by the flow of Annex F.5.4: no local variable of a
// sequence or property the module `decl` declares, and no output local
// variable formal argument, is referenced at a point where it is unassigned,
// and no sequence triggered or matched is applied to references the formal a
// local variable is bound to before it assigns it; each violation is
// reported to `diag`.
void ValidateLocalVariableFlow(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
