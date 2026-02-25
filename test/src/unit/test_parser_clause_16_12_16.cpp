// §16.12.16: Case

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

}  // namespace
