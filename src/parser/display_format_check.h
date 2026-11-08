#pragma once

namespace delta {

class DiagEngine;
struct Expr;

void CheckDisplayFormatLiterals(const Expr* call, DiagEngine& diag);

}  // namespace delta
