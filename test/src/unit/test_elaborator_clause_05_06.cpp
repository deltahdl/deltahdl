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

// §5.6: "Identifiers shall be case sensitive." Referencing a name whose case
// does not exactly match a declared identifier must fail elaboration's
// symbol resolution (the only declared name is "foo"; "Foo" is a distinct,
// undeclared identifier on the right-hand side and cannot be implicitly
// netted into existence).
TEST(IdentifierElaboration, CaseMismatchedReferenceFailsToResolve) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic foo;\n"
      "  logic x;\n"
      "  assign x = Foo;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §5.6: "If an identifier exceeds the implementation-specific length limit,
// an error shall be reported." A 1025-character identifier in elaboration
// input must cause an error to be reported on the elaborator's diagnostic
// engine.
TEST(IdentifierElaboration, IdentifierExceedingMaxLengthReportsError) {
  ElabFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrc("module m;\n"
               "  logic " +
                   long_id +
                   ";\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
