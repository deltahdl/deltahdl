#pragma once

#include <cstddef>

namespace delta {

// §5.6: "Implementations may set a limit on the maximum length of identifiers,
// but the limit shall be at least 1024 characters. If an identifier exceeds the
// implementation-specific length limit, an error shall be reported." This is
// that implementation-specific limit, set at the smallest value the clause
// admits.
//
// It is one constant rather than a literal at each place that reads it because
// §38.37.1 makes a rule out of the two agreeing: of the tfname a PLI
// application registers a system task or system function under, "the maximum
// name length shall be the same as for SystemVerilog identifiers". A second
// literal is a second limit, and the rule would then hold only for as long as
// nobody edited one of them.
//
// A user-defined system task or system function name written in a SystemVerilog
// source file is not measured against this. §5.6 caps an identifier, which it
// defines as "either a simple identifier or an escaped identifier", and §5.6.3
// hands a $-prefixed name to Clause 36, whose §36.3 says "the name can be any
// size, and all characters are significant" -- see LexSystemIdentifier in
// src/lexer/lexer.cpp, which checks no length.
inline constexpr size_t kMaxIdentifierLength = 1024;

}  // namespace delta
