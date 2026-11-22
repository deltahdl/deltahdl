#pragma once

#include <algorithm>
#include <string>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

constexpr const char* kAssertionSites =
    "interface bus(input logic clk); logic a;\n"
    "  ai: assert property (@(posedge clk) a);\n"
    "endinterface\n"
    "program prg(input logic clk); logic a;\n"
    "  ap: assert property (@(posedge clk) a);\n"
    "endprogram\n"
    "checker chk(logic clk, logic a);\n"
    "  ac: assert property (@(posedge clk) a);\n"
    "endchecker\n"
    "module sub(input logic clk); logic a;\n"
    "  as: assert property (@(posedge clk) a);\n"
    "  if (1) begin : sg sg1: assert property (@(posedge clk) a); end\n"
    "endmodule\n"
    "module top; logic clk, a; wire n; parameter int P = 1;\n"
    "  bus b(clk); prg p(clk); sub u1(clk); sub u2(clk);\n"
    "  chk k(clk, a);\n"
    "  am: assert property (@(posedge clk) a);\n"
    "  d0: assert #0 (a);\n"
    "  for (genvar i = 0; i < 2; i++) begin : g\n"
    "    ag: assert property (@(posedge clk) a);\n"
    "  end\n"
    "  always @(posedge clk) pc: assert property (a);\n"
    "  always @(negedge clk) aa: assert (a);\n"
    "  initial begin ad: assert (a); df: assert final (a); end\n"
    "endmodule\n";

inline std::string AssertionSiteFullName(vpiHandle obj) {
  const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
  return name == nullptr ? "" : name;
}

inline std::vector<std::string> AssertionFullNamesUnder(vpiHandle ref) {
  std::vector<std::string> names;
  vpiHandle it = vpi_iterate(vpiAssertion, ref);
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    names.push_back(AssertionSiteFullName(obj));
  }
  std::ranges::sort(names);
  return names;
}

}  // namespace delta
