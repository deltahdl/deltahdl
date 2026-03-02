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

TEST(ParserSection25, ModportImportWithDirectionFirst) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(input data, import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_FALSE(mp->ports[0].is_import);
}

static void VerifyModportPorts(const std::vector<ModportPort>& ports,
                               const ModportPortExpected expected[],
                               size_t count) {
  ASSERT_EQ(ports.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(Parser, InterfaceWithModport) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "master");
  ModportPortExpected expected[] = {{Direction::kOutput, "data"}};
  VerifyModportPorts(mp->ports, expected, std::size(expected));
}

TEST(Parser, ModportMultipleGroups) {
  auto r = Parse(
      "interface bus;\n"
      "  logic addr;\n"
      "  logic data;\n"
      "  modport slave(input addr, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "slave");
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
}

// 16. Interface with modport declarations
TEST(ParserClause03, Cl3_13_InterfaceWithModports) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  logic valid, ready;\n"
      "  modport master (output data, output valid, input ready);\n"
      "  modport slave (input data, input valid, output ready);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_EQ(ifc->name, "bus_if");
  ASSERT_EQ(ifc->modports.size(), 2u);
  EXPECT_EQ(ifc->modports[0]->name, "master");
  EXPECT_EQ(ifc->modports[1]->name, "slave");
}

}  // namespace
