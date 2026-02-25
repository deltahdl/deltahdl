// §16.12.1: Property instantiation

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

// =============================================================================
// §A.2.10 Production #9: property_instance
// property_instance ::=
//     ps_or_hierarchical_property_identifier [ ( [property_list_of_arguments] )
//     ]
// =============================================================================
TEST(ParserA210, PropertyInstance_InAssert) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a |-> b; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyInstance_WithArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(a, b));\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(.x(a), .y(b)));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #11: property_actual_arg
// property_actual_arg ::= property_expr | sequence_actual_arg
// =============================================================================
TEST(ParserA210, PropertyActualArg_Expr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x); x; endproperty\n"
              "  assert property (p(a && b));\n"
              "endmodule\n"));
}

// property_expr ::= property_instance
TEST(ParserA210, PropertyExpr_PropertyInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a; endproperty\n"
              "  assert property (@(posedge clk) p);\n"
              "endmodule\n"));
}

}  // namespace
