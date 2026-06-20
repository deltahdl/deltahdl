#ifndef DELTA_ELABORATOR_CROSS_BIN_WITH_COVERGROUP_H
#define DELTA_ELABORATOR_CROSS_BIN_WITH_COVERGROUP_H

#include <cstdint>
#include <string_view>

namespace delta {

// §19.6.1.2 governs the "with" clause and "matches" clause that a
// select_expression may carry when defining a cross bin. The select_expression
// grammar itself (with_covergroup_expression, integer_covergroup_expression,
// cross_identifier) belongs to §19.6's Syntax 19-4; the helpers here model the
// two compile-time legality rules the text of §19.6.1.2 adds, while the runtime
// selection semantics of the with/matches clause live in the simulator (see the
// §19.6.1.2 helpers in coverage.h).

// §19.6.1.2: when a cross_identifier is used as a select_expression, only the
// cross_identifier of the enclosing cross may be used; any other
// cross_identifier shall be disallowed. Returns true when the referenced
// cross_identifier is the enclosing cross and is therefore legal.
bool CrossIdentifierSelectIsLegal(std::string_view referenced_cross,
                                  std::string_view enclosing_cross);

// §19.6.1.2: the integer_covergroup_expression of a matches clause shall
// evaluate to a positive integer (or be the $ token, which is always legal and
// handled separately). A value that is zero or negative is illegal. Returns
// true when the evaluated integer is a positive count.
bool CrossMatchesCountIsLegal(int64_t evaluated_count);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CROSS_BIN_WITH_COVERGROUP_H
