#include "fixture_elaborator.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfInterfaceIdentifiersMultiple) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
}

TEST(ParserSection23, NonAnsiPortsBasic) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortA) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortB) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(ParserSection23, NonAnsiPortsMixed) {
  auto r = Parse(
      "module m(a, b, c, d);\n"
      "  input a, b;\n"
      "  output [3:0] c;\n"
      "  inout d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  struct Expected {
    const char* name;
    Direction dir;
  };
  Expected expected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kInput},
      {"c", Direction::kOutput},
      {"d", Direction::kInout},
  };
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, Sec23_2_2_NonAnsiPortDeclarations) {
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

TEST(ParserSection23, NonAnsiInoutPort) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, NonAnsiMultiplePortsSameDir) {
  auto r = Parse(
      "module m(x, y, z);\n"
      "  output x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(mod->ports[i].direction, Direction::kOutput);
  }
}

}  // namespace
