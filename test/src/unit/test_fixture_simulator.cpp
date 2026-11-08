#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(SimulatorFixture, ElaborateSrcRaisesNothingForTheCaseThatReadsARejection) {
  SimFixture f;
  ElaborateSrc(kElaboratorRejectsSrc, f);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
}

void HandOverAnAllTopsRejectionNobodyReads() {
  SimFixture f;
  ElaborateSrcAllTops(kElaboratorRejectsSrc, f);
}

TEST(SimulatorFixture,
     ElaborateSrcAllTopsFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverAnAllTopsRejectionNobodyReads(),
                          kUnreadReport);
}

void HandOverASeededRejectionNobodyReads() {
  SimFixtureSeeded f;
  ElaborateSrc(kElaboratorRejectsSrc, f);
}

TEST(SimulatorFixture, TheSeededFixtureFailsTheCaseThatNeverReadsARejection) {
  EXPECT_NONFATAL_FAILURE(HandOverASeededRejectionNobodyReads(), kUnreadReport);
}

}  // namespace
