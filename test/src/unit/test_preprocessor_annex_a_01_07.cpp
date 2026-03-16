#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProgramItemsParsing, SubroutinesAndProcedures) {
  auto r = ParseWithPreprocessor(
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

TEST(ProgramItemsParsing, RejectsDisallowedItems) {
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always @(*) begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always_comb begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(ParseWithPreprocessor(
                  "program p; always_ff @(posedge clk) begin end endprogram\n")
                  .has_errors);
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always_latch begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(ParseWithPreprocessor("module c; endmodule\n"
                                    "program p; c i(); endprogram\n")
                  .has_errors);

  EXPECT_TRUE(ParseWithPreprocessor("interface ifc; endinterface\n"
                                    "program p; ifc i(); endprogram\n")
                  .has_errors);
}

TEST(ProgramItemsParsing, DataAndClassDeclarations) {
  auto r = ParseWithPreprocessor(
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

  EXPECT_TRUE(
      ParseOk("program p1; logic a; endprogram\n"
              "program p2; logic b; endprogram\n"));
}

TEST(ProgramItemsParsing, IfdefSelectsProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_INIT\n"
      "program p;\n"
      "`ifdef HAS_INIT\n"
      "  initial $display(\"yes\");\n"
      "`endif\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ProgramItemsParsing, IfndefOmitsProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_FINAL\n"
      "program p;\n"
      "`ifndef HAS_FINAL\n"
      "  final $display(\"no\");\n"
      "`endif\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(ProgramItemsParsing, MacroExpandsToProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define PROG_BODY initial $display(\"macro\");\n"
      "program p;\n"
      "  `PROG_BODY\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
