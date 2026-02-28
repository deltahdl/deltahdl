// §10.3.2: The continuous assignment statement

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

namespace {

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

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(ParserSection6, VariableContinuousAssign) {
  // §6.5: Variables can be written by one continuous assignment.
  auto r = Parse(
      "module t;\n"
      "  logic vw;\n"
      "  assign vw = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 10.3.4 -- Continuous assignment with drive strengths
// =============================================================================
TEST(ParserSection10, ContinuousAssignMultipleTargets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  int count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) count++;
  }
  EXPECT_GE(count, 1);
}

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindItemByKind(ParseResult4b& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindContAssign(ParseResult4b& r) {
  return FindItemByKind(r, ModuleItemKind::kContAssign);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 3. Continuous assignment with assign (Active region)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_ContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  wire a, b;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

TEST(ParserSection6, RealVariableContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  real circ;\n"
      "  assign circ = 2.0 * 3.14;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

}  // namespace
