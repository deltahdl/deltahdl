// §16.9.2: Repetition in sequences

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// sequence_expr ::= expression_or_dist [ boolean_abbrev ]
TEST(ParserA210, SequenceExpr_ExprWithBooleanAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3]);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #33: boolean_abbrev
// boolean_abbrev ::=
//     consecutive_repetition | nonconsecutive_repetition | goto_repetition
// =============================================================================
// §A.2.10 Production #34: sequence_abbrev
// sequence_abbrev ::= consecutive_repetition
// §A.2.10 Production #35: consecutive_repetition
// consecutive_repetition ::= [* const_or_range_expression ] | [*] | [+]
TEST(ParserA210, ConsecutiveRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*] ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [+] ##1 b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #36: nonconsecutive_repetition
// nonconsecutive_repetition ::= [= const_or_range_expression ]
// =============================================================================
TEST(ParserA210, NonconsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, NonconsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=1:3] |-> b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #37: goto_repetition
// goto_repetition ::= [-> const_or_range_expression ]
// =============================================================================
TEST(ParserA210, GotoRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->2] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, GotoRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->1:3] |-> b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #38: const_or_range_expression
// const_or_range_expression ::=
//     constant_expression | cycle_delay_const_range_expression
// =============================================================================
TEST(ParserA210, ConstOrRangeExpr_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*5]);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConstOrRangeExpr_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*2:8]);\n"
              "endmodule\n"));
}

// sequence_instance with sequence_abbrev
TEST(ParserA210, SequenceExpr_SequenceInstanceWithAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s [*3] |-> c);\n"
              "endmodule\n"));
}

}  // namespace
