#pragma once

// §32.4.4 with §23.3.3.7: an inout port binding kept as two nets, the port's
// own and its connection's, so that an interconnect delay annotated to the
// port has somewhere to sit between them.

#include <string>

#include "elaborator/rtlir_scopes.h"

namespace delta {

struct Expr;
struct Net;
class SimContext;

// The two nets of one inout port binding and the names §32.4.4 annotates
// between them: `outer` is the net the parent connected to the port and
// `inner` the port's own net in the instance; `outer_origin` and
// `inner_origin` are the hierarchical prefixes of the parent and of the
// instance (Net::driver_origins), `port` the port's dotted name, the source
// a driver standing for it is annotated from (Net::driver_ports), and
// `source` and `load` the connection's and the port's SDF names.
struct InoutPortLinkEnds {
  Net& outer;
  Net& inner;
  std::string outer_origin;
  std::string inner_origin;
  std::string port;
  std::string source;
  std::string load;
};

// §23.3.3.7 permits the two nets of a port to be merged and does not require
// it; §32.4.4 has a reference at or below an annotated load see the delayed
// value and one before it the undelayed value, which one merged net cannot
// show. Joins the two nets of `ends` in both directions instead, each net
// driving the other with the resolution of its own drivers but the one the
// other net gave it, so that no value latches around the loop:
//
// - toward the port, each driver of `outer` reaches `inner` across the delay
//   annotated to the port from the source that driver stands for, read when
//   it changes, as an input port connection reads it, since $sdf_annotate
//   annotates while the design runs;
// - toward the connection, `inner`'s drivers reach `outer` at once, as a
//   driver standing for the port, so a delay annotated from the port to
//   another load on `outer` is the one that load takes.
void LinkInoutPortNets(InoutPortLinkEnds ends, SimContext& ctx);

// §4.9.6 (printed page 71) with §23.3.3.3 (printed page 747): an inout port
// connected to a select of a net or to a concatenation of nets, the connection
// being `connection`, written in the parent whose prefix is `outer_origin`,
// inside the generate blocks `gen_blocks`. `inner` is the port's own net, in
// the instance whose prefix is `inner_origin`, and `port` its dotted name.
struct InoutPortConnection {
  const Expr& connection;
  Net& inner;
  std::string outer_origin;
  std::string inner_origin;
  std::string port;
  const GenBlockPrefixes& gen_blocks;
};

// Such a connection cannot share one net with the port, so each part of it is
// linked to the bits of `inner` its place gives, the last part the least
// significant, as LinkInoutPortNets links two whole nets, the link driving and
// reading only the bits of the two nets the part joins. A part that is no net
// of the parent, which §23.3.3.3 forbids and the elaborator reports, links
// nothing, and neither does the rest of the connection then.
void LinkInoutPortConnection(const InoutPortConnection& conn, SimContext& ctx);

// §32.4.4: a hierarchical name the way an SDF file writes it. The design spells
// a path with `.` and SDF spells it with `/`, and the annotator matched the
// entry's names against the second spelling (CollectInterconnectTopology in
// src/simulator/specify_interconnect.cpp), so a name handed to it has to be in
// that spelling too.
std::string SdfHierName(const std::string& dotted);

}  // namespace delta
