#pragma once

#include "parser/parser.h"

namespace delta {

// Parses the shared tail of a gate or UDP instance: an optional instance name
// with an optional [range], followed by the parenthesized terminal list
// (terminal {, terminal}). The name's presence is decided by the caller and
// passed via `has_name`, because gate and UDP instances guard the optional
// name differently (gate: Check(kIdentifier); UDP: CheckIdentifier() &&
// !Check(kLParen)). The body that consumes the range and terminals is
// identical for both, so it lives here in a single place.
//
// Defined once in parser_toplevel.cpp. Terminal-count/lvalue validation is
// gate-specific and remains at the gate call site.
void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);

}  // namespace delta
