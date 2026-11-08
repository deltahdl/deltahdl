#pragma once

#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_type.h"

using namespace delta;

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
