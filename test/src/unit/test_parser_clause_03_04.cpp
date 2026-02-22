#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult304 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult304 Parse(const std::string &src) {
  ParseResult304 result;
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

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static bool HasItemOfKind(const std::vector<ModuleItem *> &items,
                          ModuleItemKind kind) {
  for (const auto *item : items)
    if (item->kind == kind) return true;
  return false;
}

// =============================================================================
// LRM §3.4 — Programs
// =============================================================================

// §3.4 LRM example (verbatim) with end label:
//   program test (input clk, input [16:1] addr, inout [7:0] data);
//   initial begin ... end
//   endprogram : test
TEST(ParserClause03, Cl3_4_LrmExample) {
  auto r = Parse(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram : test\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test");
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->programs[0]->ports[1].name, "addr");
  EXPECT_EQ(r.cu->programs[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->programs[0]->ports[2].direction, Direction::kInout);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

// §3.4: "A program block can contain data declarations, class definitions"
TEST(ParserClause03, Cl3_4_DataAndClassDeclarations) {
  auto r = Parse(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  class my_trans; int data; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->programs[0]->items.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kClassDecl));
  // §3.4: Multiple programs each create separate scopes
  EXPECT_TRUE(
      ParseOk("program p1; logic a; endprogram\n"
              "program p2; logic b; endprogram\n"));
}

// §3.4: "A program block can contain ... subroutine definitions ...
//        initial ... final procedures"
TEST(ParserClause03, Cl3_4_SubroutinesAndProcedures) {
  auto r = Parse(
      "program p;\n"
      "  function int get_val; return 42; endfunction\n"
      "  task run_test; endtask\n"
      "  initial $display(\"test\");\n"
      "  final $display(\"done\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kTaskDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

// §3.4: "It cannot contain always procedures ... module instances"
TEST(ParserClause03, Cl3_4_RejectsDisallowedItems) {
  EXPECT_TRUE(
      Parse("program p; always @(*) begin end endprogram\n").has_errors);
  EXPECT_TRUE(
      Parse("program p; always_comb begin end endprogram\n").has_errors);
  EXPECT_TRUE(
      Parse("program p; always_ff @(posedge clk) begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(
      Parse("program p; always_latch begin end endprogram\n").has_errors);
  EXPECT_TRUE(Parse("module c; endmodule\n"
                    "program p; c i(); endprogram\n")
                  .has_errors);
  // Interface and program instances hit the same instantiation path.
  EXPECT_TRUE(Parse("interface ifc; endinterface\n"
                    "program p; ifc i(); endprogram\n")
                  .has_errors);
}
