// §16.12.16: Case

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= case (...) property_case_item ... endcase
TEST(ParserA210, PropertyExpr_Case) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      2'b01: c |-> d;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #20: property_case_item
// property_case_item ::=
//     expression_or_dist { , expression_or_dist } : property_expr ;
//   | default [ : ] property_expr ;
// =============================================================================
TEST(ParserA210, PropertyCaseItem_MultiExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00, 2'b01: a |-> b;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyCaseItem_DefaultOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      default: a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// property_case_item — default without colon
TEST(ParserA210, PropertyCaseItem_DefaultNoColon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      default a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// §16.14.6 -- Property case (additional tests)
// =============================================================================
TEST(ParserSection16, PropertyCaseWithDefaultOnly) {
  auto r = Parse(
      "module m;\n"
      "  property p_mode;\n"
      "    case (mode)\n"
      "      default: a |-> b;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
