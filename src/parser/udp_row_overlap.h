#pragma once

// §29.3.4 (printed page 863): "It shall be illegal to have the same combination
// of inputs, including edges, specify different output values." Two rows of a
// UDP table cover the same combination where every input field of the one
// admits a value the other's admits -- `?` standing for 0, 1 and x, `b` for 0
// and 1, and an edge for the transitions Table 29-1 gives it -- and, for a
// sequential UDP, their current-state fields admit a common state.
//
// A level row and an edge row are not compared: where the two "specify
// different output values, the result is specified by the level-sensitive
// case" (§29.9, printed page 869), so they are no conflict. Nor are two edge
// rows with the edge on different inputs, a transition being of one input at a
// time.

#include "parser/ast_specify.h"

namespace delta {

// Whether rows `a` and `b` cover a common combination of inputs and, for a
// state they share, give it different outputs -- a `-` output being the
// current state it keeps. Defined in udp_row_overlap.cpp.
bool UdpRowsConflict(const UdpTableRow& a, const UdpTableRow& b);

}  // namespace delta
