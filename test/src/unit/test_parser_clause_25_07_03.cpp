// §25.7.3: Example of exporting tasks and functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA29, ExportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Write");
}

TEST(ParserA29, ExportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_export);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

// modport_tf_port ::= method_prototype (task prototype)
TEST(ParserA29, ImportTaskPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
}

TEST(ParserA29, ExportTaskPrototype) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target(export task Read(input logic [7:0] addr));\n"
              "endinterface\n"));
}

TEST(ParserA29, FullPrototypeMixed) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic req, gnt;\n"
              "  logic [7:0] addr, data;\n"
              "  modport init(\n"
              "    input gnt,\n"
              "    output req, addr,\n"
              "    ref data,\n"
              "    import task Read(input logic [7:0] raddr),\n"
              "           task Write(input logic [7:0] waddr)\n"
              "  );\n"
              "endinterface\n"));
}

TEST(ParserA29, ExportFlag_NotImport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_TRUE(mp->ports[0].is_export);
}

TEST(ParserA29, ImportMultiplePrototypes) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(\n"
      "    import task Read(input logic [7:0] raddr),\n"
      "           task Write(input logic [7:0] waddr)\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].prototype->name, "Write");
}

}  // namespace
