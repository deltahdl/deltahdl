#pragma once

#include <cstdint>
#include <unordered_map>
#include <vector>

namespace delta {

struct AigNode {
  uint32_t id = 0;
  uint32_t fanin0 = 0;
  uint32_t fanin1 = 0;
};

inline uint32_t AigLit(uint32_t id, bool compl_flag) {
  return (id << 1) | static_cast<uint32_t>(compl_flag);
}

inline uint32_t AigVar(uint32_t lit) { return lit >> 1; }

inline bool AigIsCompl(uint32_t lit) { return (lit & 1u) != 0; }

class AigGraph {
 public:
  static constexpr uint32_t kConstFalse = 0;
  static constexpr uint32_t kConstTrue = 1;

  AigGraph();

  uint32_t AddInput();

  uint32_t AddAnd(uint32_t lit0, uint32_t lit1);

  uint32_t AddNot(uint32_t lit) const;

  uint32_t AddOr(uint32_t a, uint32_t b);

  uint32_t AddXor(uint32_t a, uint32_t b);

  uint32_t AddMux(uint32_t sel, uint32_t a, uint32_t b);

  void AddOutput(uint32_t lit);

  uint32_t AddLatch(uint32_t next_state);

  size_t NodeCount() const;

  std::vector<AigNode> nodes;
  std::vector<uint32_t> inputs;
  std::vector<uint32_t> outputs;

  std::vector<std::pair<uint32_t, uint32_t>> latches;

 private:
  static uint64_t HashKey(uint32_t lit0, uint32_t lit1);

  uint32_t AllocNode();

  std::unordered_map<uint64_t, uint32_t> strash_;
};

}  // namespace delta
