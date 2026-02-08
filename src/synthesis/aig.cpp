#include "synthesis/aig.h"

#include <algorithm>

namespace delta {

// ---------------------------------------------------------------------------
// AigGraph
// ---------------------------------------------------------------------------

AigGraph::AigGraph() {
  // Node 0 is the constant-false node.
  AigNode constant{};
  constant.id = 0;
  constant.fanin0 = 0;
  constant.fanin1 = 0;
  nodes.push_back(constant);
}

uint32_t AigGraph::AddInput() {
  uint32_t id = AllocNode();
  inputs.push_back(id);
  return AigLit(id, false);
}

uint32_t AigGraph::AddAnd(uint32_t lit0, uint32_t lit1) {
  // Trivial cases: AND with constant.
  if (lit0 == kConstFalse || lit1 == kConstFalse) {
    return kConstFalse;
  }
  if (lit0 == kConstTrue) {
    return lit1;
  }
  if (lit1 == kConstTrue) {
    return lit0;
  }

  // Idempotent / complementary.
  if (lit0 == lit1) {
    return lit0;
  }
  if (AigVar(lit0) == AigVar(lit1)) {
    return kConstFalse;  // a & ~a = 0
  }

  // Canonicalize: smaller literal first.
  if (lit0 > lit1) {
    std::swap(lit0, lit1);
  }

  // Structural hashing lookup.
  uint64_t key = HashKey(lit0, lit1);
  auto it = strash_.find(key);
  if (it != strash_.end()) {
    return AigLit(it->second, false);
  }

  // Create new AND node.
  uint32_t id = AllocNode();
  nodes[id].fanin0 = lit0;
  nodes[id].fanin1 = lit1;
  strash_[key] = id;

  return AigLit(id, false);
}

uint32_t AigGraph::AddNot(uint32_t lit) const { return lit ^ 1u; }

uint32_t AigGraph::AddOr(uint32_t a, uint32_t b) {
  // De Morgan: a | b = ~(~a & ~b)
  return AddNot(AddAnd(AddNot(a), AddNot(b)));
}

uint32_t AigGraph::AddXor(uint32_t a, uint32_t b) {
  // a ^ b = (a & ~b) | (~a & b)
  uint32_t left = AddAnd(a, AddNot(b));
  uint32_t right = AddAnd(AddNot(a), b);
  return AddOr(left, right);
}

uint32_t AigGraph::AddMux(uint32_t sel, uint32_t a, uint32_t b) {
  // sel ? a : b = (sel & a) | (~sel & b)
  uint32_t when_true = AddAnd(sel, a);
  uint32_t when_false = AddAnd(AddNot(sel), b);
  return AddOr(when_true, when_false);
}

void AigGraph::AddOutput(uint32_t lit) { outputs.push_back(lit); }

size_t AigGraph::NodeCount() const { return nodes.size(); }

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

uint64_t AigGraph::HashKey(uint32_t lit0, uint32_t lit1) {
  return (static_cast<uint64_t>(lit0) << 32) | static_cast<uint64_t>(lit1);
}

uint32_t AigGraph::AllocNode() {
  auto id = static_cast<uint32_t>(nodes.size());
  AigNode node{};
  node.id = id;
  nodes.push_back(node);
  return id;
}

}  // namespace delta
