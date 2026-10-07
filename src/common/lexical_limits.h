#pragma once

#include <cstddef>

namespace delta {

// §5.6 lets an implementation cap identifier length, but at no fewer than 1024
// characters, and requires an error report for an identifier past the cap. This
// is that implementation-specific limit, set at the smallest value the clause
// admits.
//
// It is one constant rather than a literal at each place that reads it because
// §38.37.1 makes a rule out of the two agreeing: of the tfname a PLI
// application registers a system task or system function under, the length cap
// is the one SystemVerilog identifiers have. A second literal is a second
// limit, and the rule would then hold only for as long as nobody edited one of
// them.
//
// A user-defined system task or system function name written in a SystemVerilog
// source file is not measured against this. §5.6 caps an identifier, which it
// defines as a simple or an escaped identifier, and §5.6.3 hands a $-prefixed
// name to Clause 36, whose §36.3 lets such a name be any length with every
// character significant -- see LexSystemIdentifier in src/lexer/lexer.cpp,
// which checks no length.
inline constexpr size_t kMaxIdentifierLength = 1024;

}  // namespace delta
