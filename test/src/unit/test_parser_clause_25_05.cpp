// §25.5: Modports

#include "fixture_parser.h"

using namespace delta;

namespace {

// §A.2.9 modport_declaration ::= modport modport_item { , modport_item } ;
TEST(ParserA29, BasicModportDecl) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  modport target(input a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "target");
}

// modport_simple_ports_declaration ::=
//   port_direction modport_simple_port { , modport_simple_port }
TEST(ParserA29, MultipleSimplePortsSameDir) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c;\n"
      "  modport target(input a, b, c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_EQ(mp->ports[1].name, "b");
  EXPECT_EQ(mp->ports[2].name, "c");
}

// Direction persists across simple ports (§25.5)
TEST(ParserA29, DirectionPersistsAcrossPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c, d;\n"
      "  modport target(input a, b, output c, d);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[3].direction, Direction::kOutput);
}

}  // namespace
