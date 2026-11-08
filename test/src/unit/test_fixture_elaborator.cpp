#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kUnparseableSrc =
    "module m;\n"
    "  logic x\n"
    "endmodule\n";

constexpr const char* kWellFormedSrc =
    "module m;\n"
    "  logic x;\n"
    "  assign x = 1'b1;\n"
    "endmodule\n";

TEST(ElaboratorFixture, ElaborateSrcFailsTheTestWhenTheSourceDoesNotParse) {
  ElabFixture f;
  EXPECT_NONFATAL_FAILURE(ElaborateSrc(kUnparseableSrc, f),
                          "the source did not parse");
}

TEST(ElaboratorFixture, ElaborateSrcAcceptsASourceThatParses) {
  ElabFixture f;
  auto* design = ElaborateSrc(kWellFormedSrc, f);
  EXPECT_NE(design, nullptr);
}

TEST(ElaboratorFixture, ElaborateSrcStillElaboratesAPackageOnlySource) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int W = 8;\n"
      "endpackage\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaboratorFixture, ElaborateSrcAllowingParseErrorsReportsWithoutFailing) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kUnparseableSrc, f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElaboratorFixture, ElabOkAlreadyFailsTheTestWhenTheSourceDoesNotParse) {
  ElabFixture f;
  EXPECT_NONFATAL_FAILURE(ElabOk(kUnparseableSrc, f),
                          "the source did not parse");
}

TEST(ElaboratorFixture, ASecondWellFormedSourceOnOneFixtureRaisesNoFailure) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kUnparseableSrc, f);
  auto* design = ElaborateSrc(kWellFormedSrc, f);
  EXPECT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected ';', got 'endmodule'", 3, "6.8"));
}

constexpr const char* kWellFormedSrcWithDirective =
    "`define WIDTH 8\n"
    "module m;\n"
    "  logic [`WIDTH-1:0] x;\n"
    "  assign x = '0;\n"
    "endmodule\n";

TEST(ElaboratorFixture,
     ElaborateWithPreprocessorFailsTheTestWhenTheSourceDoesNotParse) {
  ElabFixture f;
  EXPECT_NONFATAL_FAILURE(ElaborateWithPreprocessor(kUnparseableSrc, f),
                          "the source did not preprocess and parse");
}

TEST(ElaboratorFixture, ElaborateWithPreprocessorAcceptsASourceThatParses) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(kWellFormedSrcWithDirective, f);
  EXPECT_NE(design, nullptr);
}

TEST(ElaboratorFixture,
     ElaborateWithPreprocessorStillElaboratesAPackageOnlySource) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "package p;\n"
      "  localparam int W = 8;\n"
      "endpackage\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaboratorFixture,
     ElaborateWithPreprocessorAllowingParseErrorsReportsWithoutFailing) {
  ElabFixture f;
  ElaborateWithPreprocessorAllowingParseErrors(kUnparseableSrc, f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElaboratorFixture, ElaborateWithPreprocessorHonoursAutoTop) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  logic x;\n"
      "endmodule\n"
      "module b;\n"
      "  logic y;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules.size(), 2u);
}

TEST(ElaboratorFixture, ElabOkAcceptsAClassOnlySource) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int data;\n"
             "endclass\n"));
}

constexpr const char* kElaboratorRejectsSrc =
    "interface class IC;\n"
    "  pure virtual function void foo();\n"
    "endclass\n"
    "class C implements IC;\n"
    "endclass\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kUnreadReport =
    "the source drew an error the case never read";

void HandOverARejectionNobodyReads() {
  ElabFixture f;
  ElaborateSrc(kElaboratorRejectsSrc, f);
}

TEST(ElaboratorFixture, ElaborateSrcFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverARejectionNobodyReads(), kUnreadReport);
}

TEST(ElaboratorFixture, TheUnreadRejectionReportQuotesTheSource) {
  EXPECT_NONFATAL_FAILURE(HandOverARejectionNobodyReads(),
                          "class C implements IC;\n");
}

TEST(ElaboratorFixture,
     ElaborateSrcRaisesNothingForTheCaseThatReadsARejection) {
  ElabFixture f;
  ElaborateSrc(kElaboratorRejectsSrc, f);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
}

void HandOverAPreprocessedRejectionNobodyReads() {
  ElabFixture f;
  ElaborateWithPreprocessor(kElaboratorRejectsSrc, f);
}

TEST(ElaboratorFixture,
     ElaborateWithPreprocessorFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverAPreprocessedRejectionNobodyReads(),
                          kUnreadReport);
}

TEST(ElaboratorFixture, AFixtureReturnedByValueReportsAnUnreadRejectionOnce) {
  EXPECT_NONFATAL_FAILURE(
      static_cast<void>(RunGenerateElaboration(kElaboratorRejectsSrc)),
      kUnreadReport);
}

}  // namespace
