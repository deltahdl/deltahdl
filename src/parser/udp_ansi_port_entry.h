#pragma once

#include <string_view>

#include "common/source_loc.h"
#include "parser/ast_expr.h"

namespace delta {

// One entry of A.5.2's `udp_declaration_port_list`, read out of the source but
// not yet placed on the UdpDecl it belongs to. §29.3.1's rules about a UDP's
// ports are stated over which of the two entry forms was written and where it
// stands, so those are what an entry carries away from the port list. Kept
// out of parser.h because it is a record the UDP parser hands about rather
// than a part of the Parser.
struct UdpAnsiPortEntry {
  bool is_output = false;
  bool is_inout = false;
  bool declares_reg = false;
  // A.5.2's `= constant_expression`, as written; null where the entry wrote
  // none, or wrote one after an output declared without reg, which is not a
  // place the grammar puts one.
  Expr* initial_expr = nullptr;
  std::string_view name;
  SourceLoc loc;
};

}  // namespace delta
