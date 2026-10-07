#pragma once

namespace delta {

class DiagEngine;
struct Expr;

// §21.2.1.1 (printed page 656) makes a format specifier the standard does not
// define an error when it is written in a string literal argument of a display
// task. The literal is in the source, so the misuse is reported where the call
// is parsed. `call` is a system call; one taking no format is left alone.
void CheckDisplayFormatLiterals(const Expr* call, DiagEngine& diag);

}  // namespace delta
