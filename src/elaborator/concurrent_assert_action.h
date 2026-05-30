#pragma once

#include <cstdint>

namespace delta {

// §16.14.1: the kinds of statement that may appear in an assert statement's
// action_block, distinguished for the rule that the action_block shall not
// contain any concurrent assert, assume, or cover statement, while it may
// contain immediate assertion statements (and other ordinary statements).
enum class ActionBlockStatementForm : uint8_t {
  kConcurrentAssert,
  kConcurrentAssume,
  kConcurrentCover,
  kImmediateAssertion,
  kOther,
};

// §16.14.1: an assert statement's action_block shall not include any concurrent
// assert, assume, or cover statement; it may, however, contain immediate
// assertion statements. Returns whether a statement of the given form is
// permitted inside the action_block.
bool ConcurrentAssertActionBlockAllows(ActionBlockStatementForm form);

}  // namespace delta
