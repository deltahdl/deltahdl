#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, LrmExample) {
  auto r = ParseWithPreprocessor(
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

}  // namespace
