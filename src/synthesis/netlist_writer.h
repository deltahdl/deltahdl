#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "synthesis/aig.h"

namespace delta {

// --- Netlist output format selector ---

enum class NetlistFormat : uint8_t {
  kVerilog,
  kBlif,
  kJson,
  kEdif,
};

// --- Netlist writer ---
//
// Serializes an AigGraph into standard netlist interchange formats.
// Each method returns the formatted string (caller decides whether to write
// to a file, pipe to stdout, etc.).
//
// Since AIG nodes do not carry port names, generic names are synthesized:
//   Inputs:   i0, i1, ...
//   Outputs:  o0, o1, ...
//   Internal: n<node_id>

class NetlistWriter {
 public:
  /// Write BLIF (Berkeley Logic Interchange Format).
  static std::string WriteBlif(const AigGraph& aig,
                               std::string_view module_name);

  /// Write gate-level Verilog.
  static std::string WriteVerilog(const AigGraph& aig,
                                  std::string_view module_name);

  /// Write JSON (nextpnr interchange).
  static std::string WriteJson(const AigGraph& aig,
                               std::string_view module_name);

  /// Write EDIF (basic structure).
  static std::string WriteEdif(const AigGraph& aig,
                               std::string_view module_name);

  /// Dispatch by format enum.
  static std::string Write(const AigGraph& aig, std::string_view module_name,
                           NetlistFormat fmt);
};

}  // namespace delta
