#include <gtest/gtest-spi.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A shared harness answers a question, and a case trusts the answer to be
// about what it asked. Where the answer is that something is absent -- no
// module, no binding, no diagnostic -- a source that never parsed produces the
// same answer the rule under test does, and the case passes whether the rule
// is implemented, implemented backwards, or absent. That is the shape these
// three pin: the harness must tell a source it could not read from a source it
// read and rejected, and it must go on telling an accepted source from a
// rejected one, or the first claim would be satisfied by a harness that
// complains about everything.

TEST(ElaboratorHarness, ASourceThatDoesNotParseFailsTheCaseThatWroteIt) {
  // `before` is reserved by Table B.1, so this declares no net and the module
  // does not parse. The keyword scan over test/src/ reads design elements and
  // deliberately leaves nets alone, which makes a net the one shape of this
  // defect only the harness can catch -- and the reason the two are
  // complementary rather than one of them being redundant.
  EXPECT_NONFATAL_FAILURE(ElabOk("module m;\n"
                                 "  wire before;\n"
                                 "endmodule\n"),
                          "did not parse");
}

TEST(ElaboratorHarness, ASourceTheElaboratorRejectsIsReportedAsRejected) {
  // Parses, so the harness has no complaint of its own; §8.26 rejects it,
  // which is the answer the case asked for. Without this the claim above
  // would be met by a harness that failed every case handed to it.
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElaboratorHarness, ASourceTheElaboratorAcceptsIsReportedAsAccepted) {
  // The other half of the control: a harness that answered "rejected" to
  // everything would satisfy the case above and fail this one.
  EXPECT_TRUE(ElabOk("module m;\nendmodule\n"));
}

// The same claim for the entry point that keeps its diagnostics in a fixture
// the case reads afterwards. There the parser's complaints and the
// elaborator's arrive in one answer, so a case asserting that elaboration
// reported something is satisfied by a source that never got that far.

TEST(ElaboratorHarness, AnUnreadableSourceFailsTheCaseThatElaboratesIt) {
  ElabFixture f;
  EXPECT_NONFATAL_FAILURE(Elaborate("module m;\n"
                                    "  wire before;\n"
                                    "endmodule\n",
                                    f),
                          "did not parse");
}

TEST(ElaboratorHarness, AReadableSourceLeavesTheFixtureWithNothingToReport) {
  ElabFixture f;
  Elaborate("module m;\nendmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
