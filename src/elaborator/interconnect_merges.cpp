#include "elaborator/interconnect_merges.h"

#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/rtlir.h"

namespace delta {

namespace {

// The net `net` names given the type `merged` its merged net reaches, where
// that is a built-in net type; an interconnect net whose chain reaches none
// keeps the type it has, which a gate terminal may have made a wire
// (§23.3.3.7.2). An interconnect port's own net stands among no module's nets,
// and takes its type with the net the port is connected to.
void GiveMergedType(const InterconnectMerges::Net& net, NetType merged) {
  if (NetTypeGroup(merged) < 0) return;
  for (RtlirNet& declared : net.first->nets) {
    if (declared.name == net.second) declared.net_type = merged;
  }
}

}  // namespace

NetType MergedInterconnectNetType(NetType merged, NetType incoming) {
  if (NetTypeGroup(incoming) < 0) return merged;
  if (NetTypeGroup(merged) < 0) return incoming;
  return DissimilarNetResultIsInternal(merged, incoming) ? merged : incoming;
}

int InterconnectMerges::Node(Net net) {
  auto [it, added] = nodes_.try_emplace(net, static_cast<int>(nets_.size()));
  if (added) {
    nets_.push_back(net);
    parents_.push_back(it->second);
    typed_.push_back(false);
    types_.push_back(NetType::kInterconnect);
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

void InterconnectMerges::MarkTyped(Net net, NetType type) {
  const int kNode = Node(net);
  typed_[kNode] = true;
  types_[kNode] = MergedInterconnectNetType(types_[kNode], type);
}

void InterconnectMerges::Resolve(DiagEngine& diag) {
  for (std::size_t node = 0; node < nets_.size(); ++node) {
    const int kRoot = Root(static_cast<int>(node));
    if (typed_[node]) typed_[kRoot] = true;
    types_[kRoot] = MergedInterconnectNetType(types_[kRoot], types_[node]);
  }
  for (std::size_t node = 0; node < nets_.size(); ++node) {
    GiveMergedType(nets_[node], types_[Root(static_cast<int>(node))]);
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
  types_.clear();
  pending_.clear();
}

}  // namespace delta
