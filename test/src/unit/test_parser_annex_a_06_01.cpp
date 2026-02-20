#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static ModuleItem* FindAlias(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlias) return item;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.6.1 Production: continuous_assign (parsing)
// continuous_assign ::=
//   assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
//   | assign [ delay_control ] list_of_variable_assignments ;
// =============================================================================

TEST(ParserA601, ContinuousAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  ASSERT_NE(cas[0]->assign_lhs, nullptr);
  ASSERT_NE(cas[0]->assign_rhs, nullptr);
}

TEST(ParserA601, ContinuousAssign_DriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 2u);
}

TEST(ParserA601, ContinuousAssign_DriveStrengthReversed) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 5u);
  EXPECT_EQ(cas[0]->drive_strength1, 3u);
}

TEST(ParserA601, ContinuousAssign_DelaySingle) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_DelayRiseFall) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_DelayRiseFallDecay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_NE(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_StrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (pull0, pull1) #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->drive_strength0, 0u);
  EXPECT_NE(cas[0]->drive_strength1, 0u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
}

// =============================================================================
// A.6.1 Production: list_of_net_assignments (parsing)
// list_of_net_assignments ::= net_assignment { , net_assignment }
// =============================================================================

TEST(ParserA601, ListOfNetAssignments_Two) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
}

TEST(ParserA601, ListOfNetAssignments_Three) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d, e, f;\n"
      "  assign a = b, c = d, e = f;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 3u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
  EXPECT_EQ(cas[2]->assign_lhs->text, "e");
}

TEST(ParserA601, ListOfNetAssignments_SharedStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign (strong0, strong1) #10 a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[1]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 4u);
  EXPECT_EQ(cas[1]->drive_strength1, 4u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[1]->assign_delay, nullptr);
}

// =============================================================================
// A.6.1 Production: net_assignment (parsing)
// net_assignment ::= net_lvalue = expression
// =============================================================================

TEST(ParserA601, NetAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] sum;\n"
      "  wire carry;\n"
      "  assign {carry, sum} = 5'b10101;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA601, NetAssignment_ExprRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b, sum;\n"
      "  assign sum = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_rhs->kind, ExprKind::kBinary);
}

TEST(ParserA601, NetAssignment_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, sel, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_rhs, nullptr);
}

// =============================================================================
// A.6.1 Production: net_alias (parsing)
// net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
// =============================================================================

TEST(ParserA601, NetAlias_TwoNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

TEST(ParserA601, NetAlias_ThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 3u);
}

TEST(ParserA601, NetAlias_FourNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b = c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 4u);
}

TEST(ParserA601, NetAlias_BitSelect) {
  // §10.11: alias with bit-selects for byte-swapping
  auto r = Parse(
      "module m;\n"
      "  wire [31:0] A, B;\n"
      "  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

