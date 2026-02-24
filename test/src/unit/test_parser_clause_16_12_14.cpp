// §16.12.14: Abort properties

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

// property_expr ::= accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_AcceptOn) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  assert property (@(posedge clk) accept_on(done) req |-> ack);\n"
      "endmodule\n"));
}

// property_expr ::= reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_RejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncAcceptOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_accept_on(done) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncRejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

}  // namespace
