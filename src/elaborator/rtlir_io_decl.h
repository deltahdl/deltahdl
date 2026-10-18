#pragma once

#include <string_view>

#include "parser/ast_type.h"

namespace delta {

// §37.13: a port declaration that no port without an expression stands for,
// and so no RtlirPort brings: a declaration a non-ANSI port expression names,
// `input [1:0] a;` under `a[0]` or `input b;` under `{b, c}` (§23.2.2.1), or an
// ANSI port written with an explicit name, `output .P1(r[3:0])` (§23.2.2.2).
// `object_name` is the net or variable the declaration's io decl reaches
// through vpiExpr, empty where its expression is no single name. The simulator
// builds the io decl of a port without an expression from the same record.
// Kept apart from rtlir.h, which stands near the size the
// assert-no-oversized-source-files job fails at.
struct RtlirIoDecl {
  std::string_view name;
  Direction direction = Direction::kNone;
  std::string_view object_name;
  // §37.13 detail 3: the declaration is of an interface port, whose io decl has
  // no direction. A declaration a port expression names never is.
  bool is_interface_port = false;
};

}  // namespace delta
