#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(PortDeclElaboration, InputPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic [7:0] d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "d");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
}

TEST(PortDeclElaboration, OutputPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(output logic [3:0] q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "q");
  EXPECT_EQ(mod->ports[0].direction, Direction::kOutput);
}

TEST(PortDeclElaboration, InoutPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(inout wire [7:0] bus);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
}

TEST(PortDeclElaboration, RefPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(ref logic [7:0] d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "d");
  EXPECT_EQ(mod->ports[0].direction, Direction::kRef);
}

TEST(PortDeclElaboration, NonAnsiOutputVariablePortInitializerKept) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(q, r);\n"
      "  output logic q = 1'b0;\n"
      "  output var int r = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_NE(mod->ports[0].init_value, nullptr);
  EXPECT_NE(mod->ports[1].init_value, nullptr);
}

TEST(PortDeclElaboration, NonAnsiInitializerOnAnotherPortIsReported) {
  ElabFixture f;
  Elaborate(
      "module m(s, a, b, c);\n"
      "  output s = 1'b1;\n"
      "  input logic a = 1'b0;\n"
      "  inout wire b = 1'b0;\n"
      "  ref logic c = 1'b0;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "initializer on output port 's', which is a net and no variable",
      1, "23.2.2.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "default value on port 'a'; defaults are only "
                            "allowed with ANSI-style port declarations",
                            1, "23.2.2.4"));
  EXPECT_TRUE(
      ReportedError(diags, "default value on inout port 'b'", 1, "23.2.2.4"));
  EXPECT_TRUE(
      ReportedError(diags, "default value on ref port 'c'", 1, "23.2.2.4"));
}

}  // namespace
