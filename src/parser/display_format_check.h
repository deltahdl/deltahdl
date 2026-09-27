#pragma once

namespace delta {

class DiagEngine;
struct Expr;

// §21.2.1.1 (printed page 656): "It shall be an error if an undefined format
// specifier appears in a string literal argument" of a display task. The
// literal is in the source, so the misuse is reported where the call is
// parsed. `call` is a system call; a call that takes no format is left alone.
void CheckDisplayFormatLiterals(const Expr* call, DiagEngine& diag);

}  // namespace delta
