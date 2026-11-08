#pragma once

#include <string_view>

#include "parser/ast_type.h"

namespace delta {

struct RtlirIoDecl {
  std::string_view name;
  Direction direction = Direction::kNone;
  std::string_view object_name;
  bool is_interface_port = false;
};

}  // namespace delta
