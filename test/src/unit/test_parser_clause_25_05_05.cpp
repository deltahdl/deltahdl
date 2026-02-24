// §25.5.5: Clocking blocks and modports

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

namespace {

// modport_clocking_declaration ::= clocking clocking_identifier
TEST(ParserA29, ClockingInModport) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "sb");
}

TEST(ParserA29, ClockingMixedWithDirectionPorts) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport DUT(input clk, req, output gnt);\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  EXPECT_EQ(iface->modports[0]->name, "DUT");
  EXPECT_EQ(iface->modports[1]->name, "STB");
  EXPECT_TRUE(iface->modports[1]->ports[0].is_clocking);
}

TEST(ParserA29, MixedDirImportClocking) {
  EXPECT_TRUE(
      ParseOk("interface A_Bus(input logic clk);\n"
              "  wire req, gnt;\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport STB(\n"
              "    input req,\n"
              "    output gnt,\n"
              "    import Read,\n"
              "    clocking sb\n"
              "  );\n"
              "endinterface\n"));
}

TEST(ParserA29, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

// Complex integration: all production alternatives together
TEST(ParserA29, AllAlternativesTogether) {
  EXPECT_TRUE(
      ParseOk("interface complex_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "  logic [7:0] addr, data;\n"
              "  clocking sb @(posedge clk);\n"
              "    input gnt;\n"
              "    output req, addr;\n"
              "  endclocking\n"
              "  modport DUT(\n"
              "    input clk, req, addr,\n"
              "    output gnt,\n"
              "    ref data\n"
              "  );\n"
              "  modport STB(clocking sb);\n"
              "  modport TB(\n"
              "    input gnt,\n"
              "    output req, addr,\n"
              "    import Read, Write\n"
              "  );\n"
              "endinterface\n"));
}

// Additional AST verification for clocking port details
TEST(ParserA29, ClockingPort_NotImportExport) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

}  // namespace
