#pragma once

#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

// Elaborates a top module that instantiates the canonical two-port child
//   module child(input logic a, output logic b); assign b = a; endmodule
// using the given connection clause (e.g. ".a, .b" or ".*"), then asserts the
// resolved port bindings carry the expected names and directions. Shared by the
// implicit-named (§23.3.2.3) and wildcard (§23.3.2.4) connection test suites,
// which differ only in the connection clause.
inline void ExpectTwoPortDirections(ElabFixture& f,
                                    const std::string& connection) {
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(" +
          connection +
          ");\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[0].direction, Direction::kInput);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].direction, Direction::kOutput);
}
