// §16.10: Local variables

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

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #29: sequence_match_item
// sequence_match_item ::=
//     operator_assignment | inc_or_dec_expression | subroutine_call
// =============================================================================
TEST(ParserA210, SequenceMatchItem_Assignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #40: assertion_variable_declaration
// assertion_variable_declaration ::=
//     var_data_type list_of_variable_decl_assignments ;
// =============================================================================
TEST(ParserA210, AssertionVariableDecl_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_InSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    int x;\n"
              "    (a, x = b) ##1 (c == x);\n"
              "  endsequence\n"
              "endmodule\n"));
}

// sequence_match_item ::= inc_or_dec_expression
TEST(ParserA210, SequenceMatchItem_IncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x++) |-> c);\n"
              "endmodule\n"));
}

// assertion_variable_declaration — multiple vars and complex type
TEST(ParserA210, AssertionVariableDecl_MultipleVars) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    logic [7:0] y;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
