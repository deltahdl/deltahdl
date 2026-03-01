// §19.3: Defining the coverage model: covergroup

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.11 Production #1: covergroup_declaration
// =============================================================================
TEST(ParserA211, CovergroupDecl_Basic) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_EQ(item->name, "cg");
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA211, CovergroupDecl_WithClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input bit [3:0] y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithPortsAndEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x) @(posedge clk);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithBlockEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin test_phase or end test_phase);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup : cg\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cg");
}

// =============================================================================
// §A.2.11 Production #5: coverage_event
// =============================================================================
TEST(ParserA211, CoverageEvent_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_NegedgeClocking) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge clk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_BlockEventBegin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin test_phase);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_BlockEventEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(end test_phase);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #6: block_event_expression
// =============================================================================
TEST(ParserA211, BlockEventExpression_BeginHierarchical) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.test.run_phase);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BlockEventExpression_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin phase1 or end phase2);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #7: hierarchical_btf_identifier
// =============================================================================
TEST(ParserA211, HierarchicalBtfIdentifier_Simple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin my_task);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserAnnexA, A2CovergroupDecl) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA211, CovergroupDecl_WithEmptyPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg();\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageSpecOrOption_CoverSpec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// Additional comprehensive tests
// =============================================================================
TEST(ParserA211, FullCovergroup_MultipleElements) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    option.auto_bin_max = 64;\n"
              "    cp_addr: coverpoint addr {\n"
              "      bins low = {[0:63]};\n"
              "      bins mid = {[64:191]};\n"
              "      bins high = {[192:255]};\n"
              "    }\n"
              "    cp_data: coverpoint data;\n"
              "    cross cp_addr, cp_data;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleCoverpoints) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    type_option.weight = 2;\n"
              "    cp1: coverpoint a iff (enable);\n"
              "    cp2: coverpoint b;\n"
              "    cp3: coverpoint c {\n"
              "      bins low = {[0:3]};\n"
              "      bins high = {[4:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input int threshold);\n"
              "    coverpoint x {\n"
              "      bins below = {[0:threshold]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_InPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endpackage\n"));
}

TEST(ParserA211, CoverGroup_NegedgeEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge rst_n);\n"
              "    coverpoint state;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup my_cg @(posedge clk);\n"
      "    coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_cg");
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_TRUE(item->loc.IsValid());
}

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

// =============================================================================
// LRM section 40.5.2 -- Coverage with assertion and covergroup constructs
// The VPI coverage API queries are applied to assertion handles and
// covergroup instances. These tests verify the parser handles the
// constructs that coverage queries operate on.
// =============================================================================
TEST(ParserSection40, CovergroupWithCoverpoint) {
  // Covergroup with coverpoint -- target of vpi_get(vpiCovered, ...)
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endmodule
  )"));
}

}  // namespace
