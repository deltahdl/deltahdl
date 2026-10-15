#pragma once

#include <cstddef>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

// §23.9 with §16.8 and §16.12: a name the property_spec of a concurrent
// assertion, or the body of a named sequence or property, reads, and where
// the read stands. The name of a member, written after `.` or `::`, is no
// such read; the name a member access starts from, `top` of `top.a`, is one,
// and heads_member_access marks it, since §26.2 holds that name in a package
// to what the package declares or imports.
struct AssertionRead {
  std::string_view name;
  SourceLoc loc;
  bool heads_member_access = false;
};

// §16.8: an identifier written as the whole of a positional actual argument
// of an instance in such a text: the name of what is instantiated, the
// position of the argument, the identifier and where it stands.
struct AssertionInstanceArg {
  std::string_view callee;
  size_t index = 0;
  std::string_view name;
  SourceLoc loc;
};

}  // namespace delta
