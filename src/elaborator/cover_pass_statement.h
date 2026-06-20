#pragma once

#include <cstdint>

namespace delta {

// §16.14.3: the kinds of statement that may appear as a cover statement's
// optional pass statement, distinguished for the rule that the pass statement
// shall not include any concurrent assert, assume, or cover statement.
enum class CoverPassStatementForm : uint8_t {
  kConcurrentAssert,
  kConcurrentAssume,
  kConcurrentCover,
  kOther,
};

// §16.14.3: a cover statement may have an optional pass statement, and that
// pass statement shall not include any concurrent assert, assume, or cover
// statement. Returns whether a statement of the given form is permitted as the
// pass statement.
bool CoverPassStatementAllows(CoverPassStatementForm form);

}  // namespace delta
