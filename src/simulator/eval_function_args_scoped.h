#pragma once

#include <string>

namespace delta {

struct Expr;

// §23.6 with §3.12.1 (printed page 56): the key a plain identifier is looked
// up by. The parser keeps a `$root` or `$unit` prefix in Expr::scope_prefix
// rather than in the identifier's text (Parser::MakeSysScopePrefix in
// src/parser/expr_parser_calls.cpp), so the key is "$root.x", which
// SimContext::FindVariable reads straight out of the variable table, or
// "$unit.g", the key the compilation unit's own storage stands under
// (CreateUnitDataVariables in lowerer_package_data.cpp) and no module's
// declaration is keyed by, so `$unit::g` names the unit's g past a module's
// own `int g` as §3.12.1 has the prefix do; an identifier of no such prefix
// is looked up by its text. Shared by EvalIdentifier (evaluation.cpp), which
// reads a value by it, and the argument binds of eval_function_args.cpp,
// which bind a ref, aggregate or queue formal to the variable the actual
// names (§13.5.2, printed 349): bound by the text alone, `f($unit::q)` from a
// module declaring its own q bound the module's. A package's `p::x` is a
// member access rather than a prefixed identifier and is read elsewhere
// (BuildMemberName in eval_expr.cpp).
std::string IdentifierLookupKey(const Expr* expr);

}  // namespace delta
