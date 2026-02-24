// §10.3.3: Continuous assignment delays

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

namespace {

TEST(ParserAnnexA, A2ContinuousAssignWithDelay) {
  auto r = Parse("module m; wire y; assign #5 y = a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      EXPECT_NE(item->assign_delay, nullptr);
    }
  }
}

bool ParseOk(const std::string &src) {
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
  auto *item = r.cu->modules[0]->items[2];
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
  auto *item = r.cu->modules[0]->items[2];
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
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
}

}  // namespace
