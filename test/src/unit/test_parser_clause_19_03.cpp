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

}  // namespace
