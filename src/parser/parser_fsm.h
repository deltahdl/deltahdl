#pragma once

#include "lexer/lexer.h"
#include "parser/ast_design.h"

namespace delta {

// §40.4: give each module of `unit` the FSMs that the state_vector pragmas
// `lexer` recorded inside its definition identify (§40.4.1 to §40.4.3), each
// with the enumeration name its pragma or the signal's declaration gives it
// and the parameters tagged with that name as its legal states (§40.4.6). A
// pragma whose FSM has no enumeration name identifies no states, and is left
// out.
void BindFsmPragmas(const Lexer& lexer, CompilationUnit& unit);

}  // namespace delta
