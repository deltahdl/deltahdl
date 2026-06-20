#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

// Parse the numeric value of an integer literal token's text, ignoring the
// optional size/base prefix and underscore separators. Shared between the
// literal parsing in expr_parser.cpp and the assignment-pattern parsing in
// expr_parser_patterns.cpp; defined once in expr_parser.cpp.
uint64_t ParseIntText(std::string_view text);

}  // namespace delta
