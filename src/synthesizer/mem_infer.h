#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

struct RtlirModule;

struct MemoryPort {
  std::string name;
  uint32_t addr_width = 0;
  uint32_t data_width = 0;
  bool is_write = false;
  Edge clock_edge = Edge::kNone;
};

struct InferredMemory {
  std::string name;
  uint32_t depth = 0;
  uint32_t data_width = 0;
  std::vector<MemoryPort> read_ports;
  std::vector<MemoryPort> write_ports;
};

std::vector<InferredMemory> InferMemories(const RtlirModule* mod);

}  // namespace delta
