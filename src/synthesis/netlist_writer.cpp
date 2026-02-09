#include "synthesis/netlist_writer.h"

#include <algorithm>
#include <initializer_list>
#include <string>
#include <unordered_set>
#include <vector>

namespace delta {
namespace {

// ---------------------------------------------------------------------------
// Common helpers
// ---------------------------------------------------------------------------

std::unordered_set<uint32_t> BuildInputSet(const AigGraph& aig) {
  return {aig.inputs.begin(), aig.inputs.end()};
}

/// Map a node id to its signal name: inputs -> i<idx>, AND nodes -> n<id>.
std::string NodeName(uint32_t node_id, const std::vector<uint32_t>& inputs) {
  if (node_id == 0) {
    return "const0";
  }
  auto it = std::find(inputs.begin(), inputs.end(), node_id);
  if (it != inputs.end()) {
    auto idx = static_cast<size_t>(it - inputs.begin());
    return "i" + std::to_string(idx);
  }
  return "n" + std::to_string(node_id);
}

/// Collect AND node IDs transitively referenced by outputs.
std::vector<uint32_t> ReferencedAnds(
    const AigGraph& aig, const std::unordered_set<uint32_t>& input_set) {
  std::unordered_set<uint32_t> visited;
  std::vector<uint32_t> stack;

  for (uint32_t out_lit : aig.outputs) {
    uint32_t var = AigVar(out_lit);
    if (var != 0 && input_set.count(var) == 0) {
      stack.push_back(var);
    }
  }

  std::vector<uint32_t> result;
  while (!stack.empty()) {
    uint32_t nid = stack.back();
    stack.pop_back();
    if (visited.count(nid) != 0) {
      continue;
    }
    visited.insert(nid);
    result.push_back(nid);
    const AigNode& node = aig.nodes[nid];
    for (uint32_t fanin : {node.fanin0, node.fanin1}) {
      uint32_t v = AigVar(fanin);
      if (v != 0 && input_set.count(v) == 0) {
        stack.push_back(v);
      }
    }
  }
  std::sort(result.begin(), result.end());
  return result;
}

/// Collect all complemented literals used by AND nodes and outputs.
std::unordered_set<uint32_t> CollectComplements(
    const AigGraph& aig, const std::vector<uint32_t>& ands) {
  std::unordered_set<uint32_t> compl_lits;
  for (uint32_t nid : ands) {
    const AigNode& node = aig.nodes[nid];
    if (AigIsCompl(node.fanin0)) {
      compl_lits.insert(node.fanin0);
    }
    if (AigIsCompl(node.fanin1)) {
      compl_lits.insert(node.fanin1);
    }
  }
  for (uint32_t out_lit : aig.outputs) {
    if (AigIsCompl(out_lit) && AigVar(out_lit) != 0) {
      compl_lits.insert(out_lit);
    }
  }
  return compl_lits;
}

/// BLIF name for a literal: base name or base_inv for complemented.
std::string BlifLitName(uint32_t lit, const std::vector<uint32_t>& inputs) {
  uint32_t var = AigVar(lit);
  std::string base = NodeName(var, inputs);
  if (AigIsCompl(lit)) {
    return base + "_inv";
  }
  return base;
}

/// Verilog expression for a literal.
std::string VerilogLitExpr(uint32_t lit, const std::vector<uint32_t>& inputs) {
  if (lit == AigGraph::kConstFalse) {
    return "1'b0";
  }
  if (lit == AigGraph::kConstTrue) {
    return "1'b1";
  }
  uint32_t var = AigVar(lit);
  std::string base = NodeName(var, inputs);
  if (AigIsCompl(lit)) {
    return "~" + base;
  }
  return base;
}

// ---------------------------------------------------------------------------
// BLIF sub-routines
// ---------------------------------------------------------------------------

/// Emit BLIF inverter .names blocks for every complemented literal.
void EmitBlifInverters(std::string& out, const AigGraph& aig,
                       const std::vector<uint32_t>& ands) {
  auto compl_lits = CollectComplements(aig, ands);
  // Sort for deterministic output.
  std::vector<uint32_t> sorted(compl_lits.begin(), compl_lits.end());
  std::sort(sorted.begin(), sorted.end());
  for (uint32_t lit : sorted) {
    std::string base = NodeName(AigVar(lit), aig.inputs);
    std::string inv = base + "_inv";
    out += ".names " + base + " " + inv + "\n";
    out += "0 1\n";
  }
}

/// Emit BLIF output connection .names blocks.
void EmitBlifOutputs(std::string& out, const AigGraph& aig) {
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    uint32_t lit = aig.outputs[i];
    std::string oname = "o" + std::to_string(i);
    if (lit == AigGraph::kConstFalse) {
      out += ".names " + oname + "\n";
      continue;
    }
    if (lit == AigGraph::kConstTrue) {
      out += ".names " + oname + "\n";
      out += "1\n";
      continue;
    }
    std::string src = BlifLitName(lit, aig.inputs);
    out += ".names " + src + " " + oname + "\n";
    out += "1 1\n";
  }
}

// ---------------------------------------------------------------------------
// Verilog sub-routines
// ---------------------------------------------------------------------------

void AppendVerilogPortList(std::string& out, const AigGraph& aig) {
  bool first = true;
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    if (!first) {
      out += ", ";
    }
    out += "i" + std::to_string(i);
    first = false;
  }
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    if (!first) {
      out += ", ";
    }
    out += "o" + std::to_string(i);
    first = false;
  }
}

void AppendVerilogInputDecls(std::string& out, const AigGraph& aig) {
  if (aig.inputs.empty()) {
    return;
  }
  out += "  input";
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    out += (i == 0 ? " " : ", ");
    out += "i" + std::to_string(i);
  }
  out += ";\n";
}

void AppendVerilogOutputDecls(std::string& out, const AigGraph& aig) {
  if (aig.outputs.empty()) {
    return;
  }
  out += "  output";
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    out += (i == 0 ? " " : ", ");
    out += "o" + std::to_string(i);
  }
  out += ";\n";
}

// ---------------------------------------------------------------------------
// JSON sub-routines
// ---------------------------------------------------------------------------

void AppendJsonPorts(std::string& out, const AigGraph& aig) {
  size_t total = aig.inputs.size() + aig.outputs.size();
  size_t idx = 0;
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    out += "    \"i" + std::to_string(i) + "\": {\"direction\": \"input\"}";
    out += (++idx < total ? ",\n" : "\n");
  }
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    out += "    \"o" + std::to_string(i) + "\": {\"direction\": \"output\"}";
    out += (++idx < total ? ",\n" : "\n");
  }
}

void AppendJsonCells(std::string& out, const AigGraph& aig,
                     const std::vector<uint32_t>& ands) {
  for (size_t k = 0; k < ands.size(); ++k) {
    uint32_t nid = ands[k];
    std::string name = NodeName(nid, aig.inputs);
    const AigNode& node = aig.nodes[nid];
    std::string f0 = VerilogLitExpr(node.fanin0, aig.inputs);
    std::string f1 = VerilogLitExpr(node.fanin1, aig.inputs);
    out += "    \"" + name + "\": {\"type\": \"AND\", ";
    out += "\"connections\": {\"A\": \"" + f0 + "\", ";
    out += "\"B\": \"" + f1 + "\"}}";
    out += (k + 1 < ands.size() ? ",\n" : "\n");
  }
}

void AppendJsonNetnames(std::string& out, const AigGraph& aig,
                        const std::vector<uint32_t>& ands) {
  size_t total = aig.inputs.size() + aig.outputs.size() + ands.size();
  size_t idx = 0;
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    std::string name = "i" + std::to_string(i);
    out += "    \"" + name + "\": {\"bits\": [" + std::to_string(i) + "]}";
    out += (++idx < total ? ",\n" : "\n");
  }
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    std::string name = "o" + std::to_string(i);
    size_t bit = aig.inputs.size() + i;
    out += "    \"" + name + "\": {\"bits\": [" + std::to_string(bit) + "]}";
    out += (++idx < total ? ",\n" : "\n");
  }
  for (size_t k = 0; k < ands.size(); ++k) {
    std::string name = NodeName(ands[k], aig.inputs);
    size_t bit = aig.inputs.size() + aig.outputs.size() + k;
    out += "    \"" + name + "\": {\"bits\": [" + std::to_string(bit) + "]}";
    out += (++idx < total ? ",\n" : "\n");
  }
}

}  // namespace

// ---------------------------------------------------------------------------
// NetlistWriter public methods
// ---------------------------------------------------------------------------

std::string NetlistWriter::WriteBlif(const AigGraph& aig,
                                     std::string_view module_name) {
  auto input_set = BuildInputSet(aig);
  auto ands = ReferencedAnds(aig, input_set);
  std::string out;

  out += ".model ";
  out += module_name;
  out += "\n";

  // Inputs line.
  out += ".inputs";
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    out += " i" + std::to_string(i);
  }
  out += "\n";

  // Outputs line.
  out += ".outputs";
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    out += " o" + std::to_string(i);
  }
  out += "\n";

  // Inverter definitions.
  EmitBlifInverters(out, aig, ands);

  // AND gate definitions.
  for (uint32_t nid : ands) {
    const AigNode& node = aig.nodes[nid];
    std::string name = NodeName(nid, aig.inputs);
    std::string f0 = BlifLitName(node.fanin0, aig.inputs);
    std::string f1 = BlifLitName(node.fanin1, aig.inputs);
    out += ".names " + f0 + " " + f1 + " " + name + "\n";
    out += "11 1\n";
  }

  // Output connections.
  EmitBlifOutputs(out, aig);

  out += ".end\n";
  return out;
}

std::string NetlistWriter::WriteVerilog(const AigGraph& aig,
                                        std::string_view module_name) {
  auto input_set = BuildInputSet(aig);
  auto ands = ReferencedAnds(aig, input_set);
  std::string out;

  out += "module ";
  out += module_name;
  out += "(";
  AppendVerilogPortList(out, aig);
  out += ");\n";

  AppendVerilogInputDecls(out, aig);
  AppendVerilogOutputDecls(out, aig);

  // Wire declarations for internal AND nodes.
  for (uint32_t nid : ands) {
    std::string name = NodeName(nid, aig.inputs);
    out += "  wire " + name + ";\n";
  }

  // AND gate assignments.
  for (uint32_t nid : ands) {
    const AigNode& node = aig.nodes[nid];
    std::string name = NodeName(nid, aig.inputs);
    std::string f0 = VerilogLitExpr(node.fanin0, aig.inputs);
    std::string f1 = VerilogLitExpr(node.fanin1, aig.inputs);
    out += "  assign " + name + " = " + f0 + " & " + f1 + ";\n";
  }

  // Output assignments.
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    std::string oname = "o" + std::to_string(i);
    std::string expr = VerilogLitExpr(aig.outputs[i], aig.inputs);
    out += "  assign " + oname + " = " + expr + ";\n";
  }

  out += "endmodule\n";
  return out;
}

std::string NetlistWriter::WriteJson(const AigGraph& aig,
                                     std::string_view module_name) {
  auto input_set = BuildInputSet(aig);
  auto ands = ReferencedAnds(aig, input_set);
  std::string out;
  std::string mod(module_name);

  out += "{\n";
  out += "  \"module\": \"" + mod + "\",\n";

  out += "  \"ports\": {\n";
  AppendJsonPorts(out, aig);
  out += "  },\n";

  out += "  \"cells\": {\n";
  AppendJsonCells(out, aig, ands);
  out += "  },\n";

  out += "  \"netnames\": {\n";
  AppendJsonNetnames(out, aig, ands);
  out += "  }\n";

  out += "}\n";
  return out;
}

std::string NetlistWriter::WriteEdif(const AigGraph& aig,
                                     std::string_view module_name) {
  auto input_set = BuildInputSet(aig);
  auto ands = ReferencedAnds(aig, input_set);
  std::string out;
  std::string mod(module_name);

  out += "(edif " + mod + "\n";
  out += "  (edifVersion 2 0 0)\n";
  out += "  (edifLevel 0)\n";
  out += "  (keywordMap (keywordLevel 0))\n";

  out += "  (library work\n";
  out += "    (edifLevel 0)\n";
  out += "    (technology (numberDefinition))\n";
  out += "    (cell " + mod + "\n";
  out += "      (cellType GENERIC)\n";

  // Interface: ports.
  out += "      (interface\n";
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    out += "        (port i" + std::to_string(i) + " (direction INPUT))\n";
  }
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    out += "        (port o" + std::to_string(i) + " (direction OUTPUT))\n";
  }
  out += "      )\n";

  // Contents: instances.
  out += "      (contents\n";
  for (uint32_t nid : ands) {
    std::string name = NodeName(nid, aig.inputs);
    out += "        (instance " + name + " (viewRef netlist))\n";
  }
  out += "      )\n";

  out += "    )\n";
  out += "  )\n";
  out += ")\n";
  return out;
}

std::string NetlistWriter::Write(const AigGraph& aig,
                                 std::string_view module_name,
                                 NetlistFormat fmt) {
  switch (fmt) {
    case NetlistFormat::kBlif:
      return WriteBlif(aig, module_name);
    case NetlistFormat::kVerilog:
      return WriteVerilog(aig, module_name);
    case NetlistFormat::kJson:
      return WriteJson(aig, module_name);
    case NetlistFormat::kEdif:
      return WriteEdif(aig, module_name);
  }
  return "";
}

}  // namespace delta
