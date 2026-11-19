#pragma once

#include <cstdint>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

enum class NetDeclarationPlace : std::uint8_t {
  kCompilationUnit,
  kInterface,
  kGenerate,
  kProgram
};

inline std::string NetStrengthDeclaredIn(NetDeclarationPlace place,
                                         const std::string& decl) {
  std::string src;
  switch (place) {
    case NetDeclarationPlace::kCompilationUnit:
      src = decl +
            "\nmodule t;\n"
            "  initial #1 $display(\"%v\", n);\n"
            "endmodule\n";
      break;
    case NetDeclarationPlace::kInterface:
      src = "interface ifc;\n  " + decl +
            "\nendinterface\n"
            "module t;\n"
            "  ifc i();\n"
            "  initial #1 $display(\"%v\", i.n);\n"
            "endmodule\n";
      break;
    case NetDeclarationPlace::kGenerate:
      src = "module t;\n  if (1) begin : g\n    " + decl +
            "\n  end\n"
            "  initial #1 $display(\"%v\", g.n);\n"
            "endmodule\n";
      break;
    default:
      src = "program p;\n  " + decl +
            "\n  initial #1 $display(\"%v\", n);\n"
            "endprogram\n"
            "module t;\n"
            "  p p1();\n"
            "endmodule\n";
      break;
  }
  SimFixture f;
  return RunCapture(src, f);
}
