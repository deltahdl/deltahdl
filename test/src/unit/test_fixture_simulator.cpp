// Tests over lib/cpp/test_fixtures/fixture_simulator.h itself.
//
// What is asserted here is the one question the fixture asks on the case's
// behalf: whether a case handed a source deltahdl rejected read the
// diagnostics before the fixture was gone, through has_errors or the engine. A
// case that never does asserts about a design that was never elaborated, and
// it passes whether the rule it names exists or not.
//
// A case below that asserts the fixture stayed quiet needs no macro saying so,
// for the reason test_fixture_elaborator.cpp gives: the fixture reports through
// ADD_FAILURE, which fails whichever case is running. A case asserting that it
// did report builds the fixture inside a function of its own and hands the
// call to EXPECT_NONFATAL_FAILURE, from gtest/gtest-spi.h, so the fixture's
// destruction falls inside the statement the macro watches.

#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The source parses, and §8.26 rejects it at line 4 because C implements none
// of the pure virtual methods IC declares.
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
  SimFixture f;
  ElaborateSrc(kElaboratorRejectsSrc, f);
}

TEST(SimulatorFixture, ElaborateSrcFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverARejectionNobodyReads(), kUnreadReport);
}

// Passes today and must keep passing: it is what stops a check that fails a
// case for the rejection itself rather than for leaving it unread.
TEST(SimulatorFixture, ElaborateSrcRaisesNothingForTheCaseThatReadsARejection) {
  SimFixture f;
  ElaborateSrc(kElaboratorRejectsSrc, f);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
}

// ElaborateSrcAllTops hands the source over as ElaborateSrc does.
void HandOverAnAllTopsRejectionNobodyReads() {
  SimFixture f;
  ElaborateSrcAllTops(kElaboratorRejectsSrc, f);
}

TEST(SimulatorFixture,
     ElaborateSrcAllTopsFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverAnAllTopsRejectionNobodyReads(),
                          kUnreadReport);
}

// The seeded fixture had no has_errors before it carried the check, so the
// rejection here could not be read through the answer at all.
void HandOverASeededRejectionNobodyReads() {
  SimFixtureSeeded f;
  ElaborateSrc(kElaboratorRejectsSrc, f);
}

TEST(SimulatorFixture, TheSeededFixtureFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverASeededRejectionNobodyReads(), kUnreadReport);
}

}  // namespace
