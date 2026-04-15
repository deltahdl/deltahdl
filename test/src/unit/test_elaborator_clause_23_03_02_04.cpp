#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: .* implicitly connects all ports where name and type match ---

TEST(WildcardPortConnectionElaboration, MatchingSignalsConnectSuccessfully) {
  EXPECT_TRUE(
      ElabOk("module sub(input a, output b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module m;\n"
             "  logic a, b;\n"
             "  sub u1(.*);\n"
             "endmodule\n"));
}

TEST(WildcardPortConnectionElaboration, WildcardCreatesBindings) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_NE(bindings[1].connection, nullptr);
}

TEST(WildcardPortConnectionElaboration, WildcardBindingHasCorrectDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.*);\n"
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

TEST(WildcardPortConnectionElaboration, WildcardMultiplePorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 3u);
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_NE(bindings[1].connection, nullptr);
  EXPECT_NE(bindings[2].connection, nullptr);
}

TEST(WildcardPortConnectionElaboration, WildcardDoesNotCreateImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& net : mod->nets) {
    EXPECT_NE(net.name, "a");
  }
}

// --- R2: Named connections can mix with .* to override or leave ports
//         unconnected ---

TEST(WildcardPortConnectionElaboration, NamedOverrideWithWildcard) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c, x;\n"
      "  child u0(.a(x), .*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 3u);
}

TEST(WildcardPortConnectionElaboration, EmptyPortOverrideDisconnectsPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.b(), .*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- R4a: .* uses default value when name not in scope ---

TEST(WildcardPortConnectionElaboration, DefaultValueUsedWhenNameNotInScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(WildcardPortConnectionElaboration, MultipleDefaultValuesUsed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b = 1'b0,\n"
      "             input logic c = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- R7: Different instances in same parent can mix connection styles ---

TEST(WildcardPortConnectionElaboration, MixedStylesInSameParent) {
  EXPECT_TRUE(
      ElabOk("module child(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic a, b, c, d, e, f;\n"
             "  child u0(a, b);\n"
             "  child u1(.a(c), .b(d));\n"
             "  child u2(.a, .b);\n"
             "  child u3(.*);\n"
             "endmodule\n"));
}

}  // namespace
