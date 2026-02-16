#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_06 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_06 Parse(const std::string& src) {
  ParseResult3_06 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 3.6 -- Checkers
// =============================================================================

// §3.6: Checker encapsulates assertions (assert property, cover property,
//        property/sequence declarations) — the primary purpose of checkers.
TEST(ParserSection3, Sec3_6_AssertionsInChecker) {
  auto r = Parse(
      "checker req_ack_chk(logic clk, req, ack);\n"
      "  property req_followed_by_ack;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (req_followed_by_ack);\n"
      "  cover property (req_followed_by_ack);\n"
      "endchecker : req_ack_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "req_ack_chk");
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 3u);
  bool has_prop = false, has_assert = false, has_cover = false;
  for (const auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) has_prop = true;
    if (item->kind == ModuleItemKind::kAssertProperty) has_assert = true;
    if (item->kind == ModuleItemKind::kCoverProperty) has_cover = true;
  }
  EXPECT_TRUE(has_prop);
  EXPECT_TRUE(has_assert);
  EXPECT_TRUE(has_cover);
}

// §3.6: Checker also encapsulates "modeling code" — variables, initial blocks,
//        always blocks used alongside assertions for auxiliary verification.
TEST(ParserSection3, Sec3_6_ModelingCodeInChecker) {
  auto r = Parse(
      "checker model_chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "  always @(flag) flag <= ~flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool has_initial = false, has_always = false;
  for (const auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) has_initial = true;
    if (item->kind == ModuleItemKind::kAlwaysBlock) has_always = true;
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_always);
  EXPECT_GE(r.cu->checkers[0]->items.size(), 3u);  // var + initial + always
}
