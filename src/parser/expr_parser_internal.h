#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

class Arena;
struct Expr;

// Parse the numeric value of an integer literal token's text, ignoring the
// optional size/base prefix and underscore separators. Shared between the
// literal parsing in expr_parser.cpp and the assignment-pattern parsing in
// expr_parser_patterns.cpp; defined once in expr_parser.cpp.
uint64_t ParseIntText(std::string_view text);

// Builds a width/type cast whose target type is carried by an AST node
// (cast->rhs) and whose value is carried by cast->lhs. The cast inherits the
// type node's start location. Pure node construction; the caller has already
// parsed both operands. Shared between the cast parsing in expr_parser.cpp and
// the sized integer literal followed by '(expr) in expr_parser_literals.cpp;
// defined once in expr_parser.cpp.
Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value);

}  // namespace delta
