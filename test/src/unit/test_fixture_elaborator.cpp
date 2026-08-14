// Tests over lib/cpp/test_fixtures/fixture_elaborator.h itself.
//
// The fixture decides what every elaborator test is able to observe, so a
// defect in it is not one wrong answer but a whole tier reporting rules as
// covered that never ran. What is asserted here is the one question the
// fixture asks on the case's behalf: whether the source it was handed parsed.
// A case that hands over a fragment and then asserts a rejection is satisfied
// by the parser's own errors, so it passes whether the rule it names exists or
// not, and it goes on passing for as long as it stands.
//
// EXPECT_NONFATAL_FAILURE, from gtest/gtest-spi.h, is what lets a case assert
// that a helper raised a failure without failing the case that checks it.

#include <gtest/gtest-spi.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A data declaration with no terminating semicolon. Parser::ParseDataDecl
// reaches Expect(TokenKind::kSemicolon) with `endmodule` current, and
// Parser::Expect reports at src/parser/parser.cpp:144-147, so the source is
// rejected for certain and for one reason.
//
// It stands in for the shapes that actually cost coverage, which were subtler:
// DpiDeclElab.PureVsContextDifferenceUnderSameLinkageIsError wrote a DPI
// qualifier after the linkage name, and
// RecursivePropertyRestrictionEnforcement.FinalOnPureVirtualError trailed a
// bare `final` after a port list where A.2.6 puts `: final` after the
// `function` keyword. Both read as SystemVerilog and neither is any, and both
// passed for as long as they stood.
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
  RtlirDesign* design = nullptr;
  EXPECT_NO_NONFATAL_FAILURE(design = ElaborateSrc(kWellFormedSrc, f));
  EXPECT_NE(design, nullptr);
}

// The deliberate behaviour recorded at fixture_elaborator.h:25-28: a source
// with no top-level module elaborates the compilation unit as-is rather than
// dereferencing an empty module list. A fix that objected to every source it
// could not name a top for would break this.
TEST(ElaboratorFixture, ElaborateSrcStillElaboratesAPackageOnlySource) {
  ElabFixture f;
  EXPECT_NO_NONFATAL_FAILURE(
      ElaborateSrc("package p;\n"
                   "  localparam int W = 8;\n"
                   "endpackage\n",
                   f));
}

// The escape hatch for a case whose subject is the parser's own report. It
// must not raise the failure, or such a case would have nowhere to go.
TEST(ElaboratorFixture, ElaborateSrcAllowingParseErrorsRaisesNoFailure) {
  ElabFixture f;
  EXPECT_NO_NONFATAL_FAILURE(
      ElaborateSrcAllowingParseErrors(kUnparseableSrc, f));
}

// The permissive form still reports what the parser found; it withholds the
// harness failure, not the diagnostics the case came for.
TEST(ElaboratorFixture, ElaborateSrcAllowingParseErrorsStillRecordsTheErrors) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kUnparseableSrc, f);
  EXPECT_TRUE(f.has_errors);
}

// ElabOk has asked this question since it was written. Pinning it here stops a
// later change quietly removing the guard from both helpers at once, which is
// what would restore the defect this file exists to keep out.
TEST(ElaboratorFixture, ElabOkAlreadyFailsTheTestWhenTheSourceDoesNotParse) {
  ElabFixture f;
  EXPECT_NONFATAL_FAILURE(ElabOk(kUnparseableSrc, f),
                          "the source did not parse");
}

// A fixture handed a rejected source and then a well-formed one must not
// report the second as unparseable. ElaborateSrc reads DiagEngine::ErrorCount
// across the parse rather than DiagEngine::HasErrors for this reason: after
// the first rejection HasErrors answers for the whole engine.
TEST(ElaboratorFixture, ASecondWellFormedSourceOnOneFixtureRaisesNoFailure) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kUnparseableSrc, f);
  EXPECT_NO_NONFATAL_FAILURE(ElaborateSrc(kWellFormedSrc, f));
}

}  // namespace
