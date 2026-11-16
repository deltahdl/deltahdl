#pragma once

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "helpers_constraint_item_places.h"

using namespace delta;

inline constexpr const char* kSoftVars =
    "  rand bit [3:0] a, b;\n"
    "  rand bit [1:0] u[4];\n"
    "  bit g = 1;\n";

inline std::string SoftCount(const std::string& before, const std::string& body,
                             const std::string& after, const std::string& call,
                             const std::string& check) {
  SimFixture f;
  return RunCapture(before + "class C;\n" + body + "endclass\n" + after +
                        "module t;\n"
                        "  int n, held = 0;\n"
                        "  initial begin\n"
                        "    static C o = new;\n"
                        "    for (n = 0; n < 32; n++)\n"
                        "      if ((" +
                        call + ") && (" + check +
                        ")) held++;\n"
                        "    $display(\"%0d\", held);\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

inline std::string SoftAt(ItemPlace place, const std::string& items,
                          const std::string& check) {
  switch (place) {
    case ItemPlace::kOutOfBlock:
      return SoftCount("", std::string(kSoftVars) + "  constraint k;\n",
                       "constraint C::k { " + items + " }\n", "o.randomize()",
                       check);
    case ItemPlace::kInline:
      return SoftCount("", kSoftVars, "",
                       "o.randomize() with { " + items + " }", check);
    case ItemPlace::kScope: {
      std::string c = check;
      for (std::size_t at = c.find("o."); at != std::string::npos;
           at = c.find("o.", at)) {
        c.erase(at, 2);
      }
      SimFixture f;
      return RunCapture(
          "module t;\n"
          "  bit [3:0] a, b;\n"
          "  bit [1:0] u[4];\n"
          "  bit g = 1;\n"
          "  int n, held = 0;\n"
          "  initial begin\n"
          "    for (n = 0; n < 32; n++)\n"
          "      if (std::randomize(a, b, u) with { " +
              items + " } && (" + c +
              ")) held++;\n"
              "    $display(\"%0d\", held);\n"
              "  end\n"
              "endmodule\n",
          f);
    }
    default:
      return SoftCount(
          "", std::string(kSoftVars) + "  constraint k { " + items + " }\n", "",
          "o.randomize()", check);
  }
}

inline bool BothValuesDrawn(const std::string& count) {
  const int kHeld = std::stoi(count);
  return kHeld > 0 && kHeld < 32;
}
