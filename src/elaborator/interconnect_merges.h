#pragma once

#include <map>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"

namespace delta {

class DiagEngine;
struct RtlirModule;

class InterconnectMerges {
 public:
  using Net = std::pair<RtlirModule*, std::string_view>;

  void Join(Net outer, Net inner, SourceLoc loc, std::string_view port,
            std::string_view inst);

  void MarkTyped(Net net, NetType type);

  void Resolve(DiagEngine& diag);

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
  std::vector<NetType> types_;
  std::vector<Pending> pending_;
};

}  // namespace delta
