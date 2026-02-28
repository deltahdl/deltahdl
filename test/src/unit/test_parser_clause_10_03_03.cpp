// §10.3.3: Continuous assignment delays

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2ContinuousAssignWithDelay) {
  auto r = Parse("module m; wire y; assign #5 y = a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      EXPECT_NE(item->assign_delay, nullptr);
    }
  }
}

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

// --- delay3 on continuous assignments ---
// delay3: single value on continuous assign.
TEST(ParserA223, Delay3AssignSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #5 out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
  EXPECT_EQ(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_decay, nullptr);
}

// delay3: three values on continuous assign (rise, fall, charge_decay).
TEST(ParserA223, Delay3AssignThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(10, 20, 30) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 10u);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_fall->int_val, 20u);
  ASSERT_NE(item->assign_delay_decay, nullptr);
  EXPECT_EQ(item->assign_delay_decay->int_val, 30u);
}

// delay2: parenthesized single value — #(expr).
TEST(ParserA223, Delay2ParenSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(5) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
}

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

struct ParseResult6h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6h Parse(const std::string& src) {
  ParseResult6h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// §6.7.1: Wire with delay and initializer together.
TEST(ParserSection6, Sec6_7_1_WireDelayWithInit) {
  auto r = Parse(
      "module t;\n"
      "  wire #3 w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->init_expr, nullptr);
}

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection11, MinTypMaxInContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  assign #(1:2:3) a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
