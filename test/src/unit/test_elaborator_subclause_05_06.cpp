#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'Foo'", 4,
                            "23.9"));
}

TEST(IdentifierElaboration, IdentifierExceedingMaxLengthReportsError) {
  ElabFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic " +
          long_id +
          ";\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "identifier exceeds maximum length of 1024 characters", 2, "5.6"));
}

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

TEST(IdentifierElaboration, EscapedIdentifierExceedingMaxLengthReportsError) {
  ElabFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic \\" +
          long_id +
          " ;\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "identifier exceeds maximum length of 1024 characters", 2, "5.6"));
}

}  // namespace
