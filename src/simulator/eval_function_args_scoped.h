#pragma once

#include <string>

namespace delta {

struct Expr;

std::string IdentifierLookupKey(const Expr* expr);

std::string DeclaredKindsKey(const Expr* expr);

}  // namespace delta
