#pragma once

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

inline constexpr const char* kPlacedRandVars =
    "  rand bit [3:0] a, b, c;\n"
    "  rand bit [1:0] u[4];\n"
    "  rand real r;\n";

inline std::string CountHeld(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

inline std::string HeldLoop(const std::string& call, const std::string& check) {
  return "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (" +
         call + " && (" + check +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

inline std::string HeldInClass(const std::string& items,
                               const std::string& check) {
  return "class C;\n" + std::string(kPlacedRandVars) +
         "  bit g = 1;\n"
         "  constraint k { " +
         items +
         " }\n"
         "endclass\n"
         "module t;\n" +
         HeldLoop("o.randomize()", check);
}

inline std::string HeldOutOfBlock(const std::string& items,
                                  const std::string& check) {
  return "class C;\n" + std::string(kPlacedRandVars) +
         "  bit g = 1;\n"
         "  constraint k;\n"
         "endclass\n"
         "constraint C::k { " +
         items +
         " }\n"
         "module t;\n" +
         HeldLoop("o.randomize()", check);
}

inline std::string HeldInline(const std::string& items,
                              const std::string& check) {
  return "class C;\n" + std::string(kPlacedRandVars) +
         "  bit g = 1;\n"
         "endclass\n"
         "module t;\n" +
         HeldLoop("o.randomize() with { " + items + " }", check);
}

inline std::string HeldInScope(const std::string& items,
                               const std::string& check) {
  std::string c = check;
  for (std::size_t at = c.find("o."); at != std::string::npos;
       at = c.find("o.", at)) {
    c.erase(at, 2);
  }
  return "module t;\n"
         "  bit [3:0] a, b, c;\n"
         "  bit [1:0] u[4];\n"
         "  real r;\n"
         "  bit g = 1;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (std::randomize(a, b, c, u, r) with { " +
         items + " } && (" + c +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}
