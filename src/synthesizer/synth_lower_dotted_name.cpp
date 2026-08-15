#include <string_view>

#include "synthesizer/synth_lower.h"

namespace delta {

// §23.7 rules on "the first component of the name", which is the leftmost
// identifier: Parser::ParseMemberAccessChain in src/parser/expr_parser.cpp
// builds the chain leftwards through Expr::lhs. Empty when the chain bottoms
// out at something other than an identifier.
static std::string_view DottedNameFirstComponent(const Expr* e) {
  const Expr* n = e;
  while (n && n->kind == ExprKind::kMemberAccess) n = n->lhs;
  if (n && n->kind == ExprKind::kIdentifier) return n->text;
  return {};
}

// Which of §23.7's three dotted-name constructs `expr` is, and the subclause
// that defines it. signal_widths_ holds the data objects of the module the
// name was written in, recorded by SynthLower::MapPorts.
NonSynthRule SynthLower::DottedNameRule(const Expr* expr) const {
  // §23.7.1 is settled at the node with no lookup, because the operator is
  // written there: "A name with a package or class scope resolution prefix
  // (::) shall always resolve in a downwards manner".
  if (expr->is_scope_resolution) {
    return {
        "a name with a scope resolution operator prefix has no lowering in "
        "the synthesizer",
        "23.7.1"};
  }
  // §23.7 decides the other two: "The distinguishing aspect of a hierarchical
  // name is that the first component of the name matches a scope name while
  // the first name component of a member select matches a data object or
  // interface port name."
  if (signal_widths_.count(DottedNameFirstComponent(expr)) != 0) {
    return {"a member of a packed structure has no lowering in the synthesizer",
            "7.2.1"};
  }
  // §23.6 defines what a first component naming no data object is. A component
  // matching nothing this module declares lands here too, which is the answer
  // §23.7 gives rather than a fallback.
  return {"a hierarchical name has no lowering in the synthesizer", "23.6"};
}

}  // namespace delta
