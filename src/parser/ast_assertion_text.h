#pragma once

#include <cstddef>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

struct AssertionRead {
  std::string_view name;
  SourceLoc loc;
  bool heads_member_access = false;
};

struct AssertionInstanceArg {
  std::string_view callee;
  size_t index = 0;
  std::string_view name;
  SourceLoc loc;
};

}  // namespace delta
