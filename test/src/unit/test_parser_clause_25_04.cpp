// §25.4

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceDeclaration, WithPorts) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
}

TEST(InterfaceDeclaration, WithOutputPort) {
  auto r = Parse(
      "interface ifc(output logic done);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "done");
}

TEST(InterfaceDeclaration, WithInoutPort) {
  auto r = Parse(
      "interface ifc(inout logic shared);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "shared");
}

TEST(InterfaceDeclaration, WithMixedDirectionPorts) {
  auto r = Parse(
      "interface i1(input a, output b, inout c);\n"
      "  wire d;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->interfaces[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->interfaces[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->interfaces[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->interfaces[0]->ports[2].name, "c");
}

}  // namespace
