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
// A case below that asserts the harness stayed quiet needs no macro saying so.
// The harness reports through ADD_FAILURE, which fails whichever case is
// running, so a guard that fired when it should not have fails the case that
// called it. Only the two cases asserting that the harness did speak need
// EXPECT_NONFATAL_FAILURE, from gtest/gtest-spi.h, which lets a case assert a
// failure was raised without failing the case that checks it.

#include <gtest/gtest-spi.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A data declaration with no terminating semicolon. Parser::ParseDataDecl
// reaches Expect(TokenKind::kSemicolon) with `endmodule` current, and
// Parser::Expect reports at src/parser/parser.cpp:138-148, so the source is
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

// Passes today and must keep passing: it is what stops a fix that objects to
// every source rather than to the ones that did not parse.
TEST(ElaboratorFixture, ElaborateSrcAcceptsASourceThatParses) {
  ElabFixture f;
  auto* design = ElaborateSrc(kWellFormedSrc, f);
  EXPECT_NE(design, nullptr);
}

// The deliberate behaviour recorded at fixture_elaborator.h: a source with no
// top-level module elaborates the compilation unit as-is rather than
// dereferencing an empty module list. A fix that objected to every source it
// could not name a top for would break this.
TEST(ElaboratorFixture, ElaborateSrcStillElaboratesAPackageOnlySource) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int W = 8;\n"
      "endpackage\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The escape hatch for a case whose subject is the parser's own report. It
// withholds the harness failure, not the diagnostics the case came for: were
// it to raise one, this case would fail on it rather than on the assertion.
TEST(ElaboratorFixture, ElaborateSrcAllowingParseErrorsReportsWithoutFailing) {
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
// the first rejection HasErrors answers for the whole engine, so the guard
// would fire on every later source and this case would fail.
TEST(ElaboratorFixture, ASecondWellFormedSourceOnOneFixtureRaisesNoFailure) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kUnparseableSrc, f);
  auto* design = ElaborateSrc(kWellFormedSrc, f);
  EXPECT_NE(design, nullptr);
}

// The same question for the helper a case calls when it needs a compiler
// directive to reach the elaborator. The source below carries one, because a
// misspelled directive is what a case using this helper is most likely to get
// wrong and it is reported by the preprocessor rather than the parser.
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

// Passes today and must keep passing: it is what stops a fix that objects to
// every source rather than to the ones that did not get through.
TEST(ElaboratorFixture, ElaborateWithPreprocessorAcceptsASourceThatParses) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(kWellFormedSrcWithDirective, f);
  EXPECT_NE(design, nullptr);
}

// The deliberate behaviour recorded at fixture_elaborator.h: a source with no
// top-level module elaborates the compilation unit as-is rather than
// dereferencing an empty module list.
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

// The escape hatch for a case whose subject is a preprocessor or parser report.
TEST(ElaboratorFixture,
     ElaborateWithPreprocessorAllowingParseErrorsReportsWithoutFailing) {
  ElabFixture f;
  ElaborateWithPreprocessorAllowingParseErrors(kUnparseableSrc, f);
  EXPECT_TRUE(f.has_errors);
}

// §23.3.1 roots every uninstantiated module when no top is named, which is the
// branch `auto_top` selects. Two modules are declared rather than one because a
// single-module source makes the two branches agree: the last module is then
// also the only root, so a fix that reached the parse check by way of the
// auto_top branch and changed which modules are tops would pass on it.
TEST(ElaboratorFixture, ElaborateWithPreprocessorHonoursAutoTop) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  logic x;\n"
      "endmodule\n"
      "module b;\n"
      "  logic y;\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules.size(), 2u);
}

}  // namespace
