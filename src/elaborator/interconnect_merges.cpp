#include "elaborator/interconnect_merges.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir.h"

namespace delta {

namespace {

// Whether the interconnect net `name` of `mod` was given a net type of its own
// while `mod` was elaborated, as one on a gate terminal is (§23.3.3.7.2).
bool Retyped(const RtlirModule& mod, std::string_view name) {
  return std::ranges::any_of(mod.nets, [name](const RtlirNet& net) {
    return net.name == name && net.net_type != NetType::kInterconnect;
  });
}

}  // namespace

int InterconnectMerges::Node(Net net) {
  auto [it, added] = nodes_.try_emplace(net, static_cast<int>(nets_.size()));
  if (added) {
    nets_.push_back(net);
    parents_.push_back(it->second);
    typed_.push_back(false);
  }
  return it->second;
}

int InterconnectMerges::Root(int node) {
  while (parents_[node] != node) {
    parents_[node] = parents_[parents_[node]];
    node = parents_[node];
  }
  return node;
}

void InterconnectMerges::Join(Net outer, Net inner, SourceLoc loc,
                              std::string_view port, std::string_view inst) {
  const int kOuter = Node(outer);
  parents_[Root(Node(inner))] = Root(kOuter);
  pending_.push_back({kOuter, loc, port, inst});
}

void InterconnectMerges::MarkTyped(Net net) { typed_[Node(net)] = true; }

void InterconnectMerges::Report(DiagEngine& diag) {
  for (std::size_t node = 0; node < nets_.size(); ++node) {
    const auto& [mod, name] = nets_[node];
    if (typed_[node] || Retyped(*mod, name)) {
      typed_[Root(static_cast<int>(node))] = true;
    }
  }
  for (const Pending& pending : pending_) {
    if (typed_[Root(pending.node)]) continue;
    diag.Error(pending.loc,
               std::format("simulated net for port '{}' of instance '{}' has "
                           "interconnect type at end of elaboration",
                           pending.port, pending.inst),
               Subclause("23.3.3.7.1"));
  }
  nodes_.clear();
  nets_.clear();
  parents_.clear();
  typed_.clear();
  pending_.clear();
}

}  // namespace delta
