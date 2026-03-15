#include <string>

#include "fixture_elaborator.h"

namespace {

TEST(IdentifierElaboration, SimpleIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] abc_123;\n"
             "  assign abc_123 = 8'd0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, IdentifierWithDollarElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] n$657;\n"
             "  assign n$657 = 8'd0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, IdentifierStartingWithUnderscoreElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] _bus3;\n"
             "  assign _bus3 = 8'd0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, SingleCharIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic x;\n"
             "  assign x = 1'b0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, UnderscoreOnlyIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic _;\n"
             "  assign _ = 1'b0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, CaseSensitiveIdentifiersElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] data, Data, DATA;\n"
             "  assign data = 8'd1;\n"
             "  assign Data = 8'd2;\n"
             "  assign DATA = 8'd3;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, MaxLengthIdentifierElaborates) {
  std::string long_id(1024, 'a');
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] " +
             long_id +
             ";\n"
             "  assign " +
             long_id +
             " = 8'd0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, IdentifierAsModuleNameElaborates) {
  EXPECT_TRUE(
      ElabOk("module my_module_99;\n"
             "  logic x;\n"
             "  assign x = 1'b0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, MixedCharClassIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] _start, mid$dle, end_99;\n"
             "  assign _start = 8'd0;\n"
             "  assign mid$dle = 8'd0;\n"
             "  assign end_99 = 8'd0;\n"
             "endmodule\n"));
}

TEST(IdentifierElaboration, IdentifierInExpressionElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c;\n"
             "  assign a = b + c;\n"
             "endmodule\n"));
}

}  // namespace
