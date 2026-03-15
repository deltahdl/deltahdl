#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, PortBinding_ResolvesChild) {
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

TEST(Elaboration, PortBinding_Direction) {
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

TEST(Elaboration, PortBinding_PortMismatch) {
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

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface simple_if(input logic data);\n"
      "endinterface\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_if u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

TEST(ModuleInstantiation, NamedPortConnection) {
  EXPECT_TRUE(
      ElabOk("module sub(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic x, y;\n"
             "  sub u0(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(ModulePortConnections, NamedPortConnectionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inv(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  inv u0(.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
