#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(NamedPortConnectionElaboration, PortBindingResolvesChild) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "child");
  EXPECT_EQ(mod->children[0].port_bindings.size(), 2);
}

TEST(NamedPortConnectionElaboration, PortBindingDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2);

  struct {
    const char* port_name;
    Direction direction;
  } const kExpected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kOutput},
  };
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(bindings[i].port_name, kExpected[i].port_name);
    EXPECT_EQ(bindings[i].direction, kExpected[i].direction);
  }
}

TEST(NamedPortConnectionElaboration, PortBindingPortMismatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u0(.bogus(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);

  EXPECT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(NamedPortConnectionElaboration, EmptyNamedPortDoesNotUseDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] y;\n"
      "  child u(.a(), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  const RtlirPortBinding* a_binding = nullptr;
  for (const auto& b : bindings) {
    if (b.port_name == "a") {
      a_binding = &b;
      break;
    }
  }
  ASSERT_NE(a_binding, nullptr);
  EXPECT_EQ(a_binding->connection, nullptr);
}

TEST(NamedPortConnectionElaboration, OmittedPortWithoutDefaultIsUnconnected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a ^ b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.a(x), .c(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  for (const auto& b : bindings) {
    EXPECT_NE(b.port_name, "b");
  }
}

TEST(NamedPortConnectionElaboration, OmittedOutputPortHasNoBinding) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b, output logic c);\n"
      "  assign b = a;\n"
      "  assign c = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  for (const auto& b : bindings) {
    EXPECT_NE(b.port_name, "c");
  }
}

TEST(NamedPortConnectionElaboration, ReversedOrderBindsCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.b(y), .a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  bool found_a = false, found_b = false;
  for (const auto& b : bindings) {
    if (b.port_name == "a") {
      EXPECT_EQ(b.direction, Direction::kInput);
      found_a = true;
    } else if (b.port_name == "b") {
      EXPECT_EQ(b.direction, Direction::kOutput);
      found_b = true;
    }
  }
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
}

}  // namespace
