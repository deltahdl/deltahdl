#pragma once

#include <functional>
#include <string_view>

namespace delta {

class DiagEngine;
struct ModuleDecl;

// §23.9 with §16.8 and §16.12: every name a concurrent assertion statement, a
// named sequence or a named property of `decl` reads without a hierarchical
// path (ModuleItem::assertion_reads) resolves to a formal or a local variable
// of the declaration, to a sequence, property or clocking block of `decl`, or
// to a name `declared` answers for the enclosing scope; a read that resolves
// to none is an error. §16.10: where the name is a local variable of a sequence
// or property the text instantiates, the report says so, the local being
// visible only in that declaration's body.
void ReportAssertionUnresolved(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& declared, DiagEngine& diag);

// §16.8: an actual argument bound to a formal that the instantiated sequence
// or property writes in a cycle delay or a repetition bound shall be an
// elaboration-time constant. Reports each identifier passed whole to such a
// formal (ModuleItem::assertion_instance_args) that `is_variable` answers for,
// a formal of the instantiating declaration aside, whose own actual is
// checked where that declaration is instantiated.
void ReportNonConstantBoundActuals(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& is_variable, DiagEngine& diag);

}  // namespace delta
