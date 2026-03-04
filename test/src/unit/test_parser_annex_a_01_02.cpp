#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, DescriptionPackageItem) {
  auto r = Parse("function int add(int a, int b); return a + b; endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

TEST(SourceText, AllDescriptionTypes) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "class C; endclass\n"
      "checker chk; endchecker\n"
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 0 ; 1 : 1 ; endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design work.m;\n"
      "  default liblist work;\n"
      "endconfig\n"
      "bind m chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(ParserAnnexA, A1ProgramDecl) {
  auto r = Parse(
      "program test_prog(input logic clk);\n"
      "  initial $display(\"Hello\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
}

TEST(ParserAnnexA, A1CompilationUnitMultipleItems) {
  auto r = Parse(
      "package p; endpackage\n"
      "module m; endmodule\n"
      "interface i; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
}

TEST(ParserAnnexA051, UdpWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection29, UdpCoexistsWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST_F(ConfigParseTest, ConfigCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    config cfg;
      design lib.top;
    endconfig
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, MultipleConfigs) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib.top1;
    endconfig
    config cfg2;
      design lib.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  EXPECT_EQ(unit->configs[1]->name, "cfg2");
}

TEST(Parser, InterfaceAndModule) {
  auto r = Parse(
      "interface bus; endinterface\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->modules.size(), 1);
}

TEST(SourceText, DescriptionInterface) {
  auto r = Parse("interface ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

TEST(SourceText, InterfaceWithLifetime) {
  auto r = Parse("interface automatic ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

TEST(SourceText, InterfaceEndLabel) {
  auto r = Parse("interface ifc; endinterface : ifc\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A2ClassDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  rand bit [7:0] payload;\n"
      "  function void display();\n"
      "    $display(\"pkt\");\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(ParserCh501, Sec5_1_EmptyCuCompletelyEmpty) {

  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
}

}
