#pragma once

#include "synth/aig.h"

#include <cstdint>
#include <string>

namespace delta {

// --- Output netlist formats ---

enum class NetlistFormat : uint8_t {
    Verilog,  // Structural Verilog gate-level netlist
    Blif,     // Berkeley Logic Interchange Format
    Json,     // JSON netlist (Yosys-compatible)
    Edif,     // Electronic Design Interchange Format
};

// --- Netlist writer ---
//
// Serializes an AIG (or mapped netlist) to various industry-standard
// output formats for downstream place-and-route or formal verification.

class NetlistWriter {
public:
    /// Write the AIG to a file in the specified format.
    void write(const AigGraph& graph, NetlistFormat fmt, const std::string& filename);

private:
    /// Emit structural Verilog (AND/NOT gates).
    void write_verilog(const AigGraph& graph, const std::string& filename);

    /// Emit BLIF for academic/research tools.
    void write_blif(const AigGraph& graph, const std::string& filename);

    /// Emit JSON netlist (Yosys-compatible schema).
    void write_json(const AigGraph& graph, const std::string& filename);

    /// Emit EDIF for vendor tool import.
    void write_edif(const AigGraph& graph, const std::string& filename);
};

} // namespace delta
