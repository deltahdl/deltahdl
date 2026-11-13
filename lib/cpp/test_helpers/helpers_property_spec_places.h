#pragma once

#include <string>

constexpr const char* kPropertySpecPlaces[] = {
    "module",  "procedural", "generate", "interface", "program",
    "checker", "property",   "package",  "unit"};

inline std::string PropertySpecIn(const std::string& place,
                                  const std::string& spec) {
  const std::string kSignals = "  logic clk; bit a, b, c, d;\n";
  const std::string kAssertion =
      "  a1: assert property (@(posedge clk) " + spec + ");\n";
  if (place == "procedural") {
    return "module m;\n" + kSignals +
           "  always @(posedge clk) assert property (" + spec +
           ");\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + kSignals + "  if (1) begin : g" +
           kAssertion.substr(1) + "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kSignals + kAssertion + "end" + place + "\n";
  }
  const std::string kDeclared = "  property q; " + spec + "; endproperty\n";
  if (place == "property") {
    return "module m;\n" + kSignals + kDeclared + "endmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + kSignals + kDeclared + "endpackage\n";
  }
  if (place == "unit") return "\n" + kSignals + kDeclared;
  return "module m;\n" + kSignals + kAssertion + "endmodule\n";
}
