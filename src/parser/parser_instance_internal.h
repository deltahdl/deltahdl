#pragma once

#include "parser/parser.h"

namespace delta {

// Parses the shared tail of a gate or UDP instance: an optional instance name
// with an optional [range], followed by the parenthesized terminal list
// (terminal {, terminal}). The name's presence is decided by the caller and
// passed via `has_name`, because gate and UDP instances guard the optional
// name differently (gate: CheckIdentifier(); UDP: CheckIdentifier() &&
// !Check(kLParen)). The body that consumes the range and terminals is
// identical for both, so it lives here in a single place.
//
// Defined once in parser_toplevel.cpp. Terminal-count validation is each
// call site's own, the gate's by its A.3.4 type and the UDP's by A.5.4's
// udp_instance.
void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);

// Whether an expression has one of A.8.5's net_lvalue forms, which A.3.3
// makes the output_terminal and inout_terminal of a gate and A.5.4 the
// output_terminal of a UDP instance. Defined once in parser_toplevel.cpp.
bool IsNetLvalue(const Expr* e);

}  // namespace delta
