#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

// Forward declarations
struct RtlirModule;

/// A single port on an inferred memory.
struct MemoryPort {
  std::string name;
  uint32_t addr_width = 0;
  uint32_t data_width = 0;
  bool is_write = false;
  Edge clock_edge = Edge::kNone;
};

/// An inferred memory block detected from array access patterns.
struct InferredMemory {
  std::string name;
  uint32_t depth = 0;
  uint32_t data_width = 0;
  std::vector<MemoryPort> read_ports;
  std::vector<MemoryPort> write_ports;
};

/// Analyze always_ff blocks in an RTLIR module for array access patterns
/// (indexed reads/writes like mem[addr]) and return detected memories.
std::vector<InferredMemory> InferMemories(const RtlirModule* mod);

}  // namespace delta
