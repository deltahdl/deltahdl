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

TEST(IdentifierElaboration, IdentifierInExpressionElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c;\n"
             "  assign a = b + c;\n"
             "endmodule\n"));
}

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

TEST(IdentifierElaboration, IdentifierExceedingMaxLengthReportsError) {
  ElabFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrc(
      "module m;\n"
      "  logic " +
          long_id +
          ";\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The §5.6 length limit governs every identifier, escaped ones included. Here
// the name is written with escaped-identifier syntax (a leading backslash and a
// terminating space, the §5.6.1 dependency) and driven end-to-end through parse
// and elaborate; a 1024-character escaped name stays within the limit and
// elaborates cleanly.
TEST(IdentifierElaboration, EscapedIdentifierMaxLengthElaborates) {
  std::string long_id(1024, 'a');
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\" +
             long_id +
             " ;\n"
             "  assign \\" +
             long_id +
             " = 1'b0;\n"
             "endmodule\n"));
}

// Negative form of the length rule on the escaped-identifier input path: an
// escaped name of 1025 characters exceeds the limit and is rejected during the
// lexing performed by elaboration, exactly like an over-length simple name.
TEST(IdentifierElaboration, EscapedIdentifierExceedingMaxLengthReportsError) {
  ElabFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrc(
      "module m;\n"
      "  logic \\" +
          long_id +
          " ;\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
