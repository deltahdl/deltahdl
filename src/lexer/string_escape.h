#pragma once

#include <string>
#include <string_view>

namespace delta {

// Interprets escape sequences in a SystemVerilog string literal per §5.9.1.
// Input is the raw string content (without surrounding quotes).
// Handles: \n \t \\ \" \v \f \a \ddd (octal) \xdd (hex).
// Unknown escapes: the backslash is dropped (e.g., \b → b).
std::string InterpretStringEscapes(std::string_view raw);

}  // namespace delta
