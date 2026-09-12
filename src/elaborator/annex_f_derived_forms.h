#pragma once

#include <cstdint>

#include "elaborator/annex_f_neutral_satisfaction.h"

namespace delta {

// §F.3.4 lists the derived forms of Annex F: the shapes the concrete syntax
// writes, each defined as a composition of the §F.3.2 primitives, so that the
// satisfaction relations of §F.5 need only be stated for the primitives. This
// file holds the derived forms as functions from a concrete shape to the
// primitive form it stands for.

// §16.14's four concurrent assertion directives, where §F.3.2's assertion
// production A has three roles.
enum class ConcurrentAssertionDirective : std::uint8_t {
  kAssert,
  kAssume,
  kCover,
  kRestrict,
};

// §F.3.4.1: restrict property is defined as assume property, so the role a
// restrict statement takes in the §F.3.2 grammar is the assume role, and each
// of the other three directives is its own role. §16.14.4 says the same from
// the language's side, that a restrict property statement has the semantics of
// an assume property statement, and what sets it apart there -- that it is not
// verified in simulation and has no action block -- is nothing the
// satisfaction of a word sees.
AssertionStatement::Role RoleOfConcurrentAssertionDirective(
    ConcurrentAssertionDirective directive);

}  // namespace delta
