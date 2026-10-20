#pragma once

#include <map>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct RtlirModule;

// §23.3.3.7.1: the nets the port connections of a design merge through its
// interconnect nets. Every port connection involving an interconnect net merges
// the two nets, so a chain of interconnect nets across the hierarchy is one net
// with whatever typed net any of its connections reaches, and only a chain that
// reaches none is of interconnect type at the end of elaboration. The
// connections are kept as the instances are elaborated and judged once the
// whole design has been, since the typed net may stand in an instance not yet
// reached, above the connection or beside it.
class InterconnectMerges {
 public:
  // The net named `name` in the elaborated module `mod`.
  using Net = std::pair<const RtlirModule*, std::string_view>;

  // A port connection joining the interconnect nets `outer`, written in the
  // instantiation, and `inner`, the port's own net in the instance, reported at
  // `loc` as port `port` of instance `inst` if what it merges into stays an
  // interconnect net.
  void Join(Net outer, Net inner, SourceLoc loc, std::string_view port,
            std::string_view inst);

  // The interconnect net `net` connected through a port to something other
  // than an interconnect net, or standing on a gate terminal (§23.3.3.7.2),
  // which gives its merged net a type other than interconnect.
  void MarkTyped(Net net);

  // Reports each joining connection whose merged net reaches no net marked
  // typed, then forgets every connection.
  void Report(DiagEngine& diag);

 private:
  struct Pending {
    int node = 0;
    SourceLoc loc;
    std::string_view port;
    std::string_view inst;
  };

  int Node(Net net);
  int Root(int node);

  std::map<Net, int> nodes_;
  std::vector<Net> nets_;
  std::vector<int> parents_;
  std::vector<bool> typed_;
  std::vector<Pending> pending_;
};

}  // namespace delta
