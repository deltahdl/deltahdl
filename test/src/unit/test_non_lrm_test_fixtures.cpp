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

// The same defect reaches every case that takes a fixture rather than an
// answer, and there the harness cannot tell a case what it did not ask. What
// it can tell is whether anybody asked at all: a source the elaborator
// rejected, whose diagnostics no assertion ever read, made every absence the
// case went on to assert. These three pin that, and the two controls are what
// stop a fixture that failed every case from satisfying the first.

// Parses; §8.26.2 requires a class implementing an interface class to define
// every pure virtual method it inherits, and this one defines none. So the
// rejection is the elaborator's rather than the parser's, which is what makes
// it a rejection a case could go on to ignore.
constexpr const char* kRejected =
    "interface class IC;\n"
    "  pure virtual function void foo();\n"
    "endclass\n"
    "class C implements IC;\n"
    "endclass\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kAccepted = "module m;\nendmodule\n";

// Answers how many failures `body` produced, collecting them rather than
// reporting them. The fixture lives inside `body`, so the destructor that
// reports an unread rejection runs while the collection is still in place.
template <typename Body>
int FailuresFrom(Body body) {
  testing::TestPartResultArray results;
  {
    testing::ScopedFakeTestPartResultReporter reporter(
        testing::ScopedFakeTestPartResultReporter::
            INTERCEPT_ONLY_CURRENT_THREAD,
        &results);
    body();
  }
  return results.size();
}

TEST(HarnessDiagnostics, ARejectionNoAssertionReadFailsTheCaseThatIgnoredIt) {
  EXPECT_EQ(FailuresFrom([] {
              ElabFixture f;
              ElaborateSrc(kRejected, f);
            }),
            1);
}

TEST(HarnessDiagnostics, ARejectionAnAssertionReadIsThatCaseToJudge) {
  // Reading is the whole of it. The case has taken the diagnostics into
  // account, and what it concluded from them is its own business.
  EXPECT_EQ(FailuresFrom([] {
              ElabFixture f;
              ElaborateSrc(kRejected, f);
              EXPECT_TRUE(f.has_errors);
            }),
            0);
}

TEST(HarnessDiagnostics, AnAcceptedSourceLeavesNothingToHaveIgnored) {
  // Without this a fixture that failed every case would satisfy the first.
  EXPECT_EQ(FailuresFrom([] {
              ElabFixture f;
              ElaborateSrc(kAccepted, f);
            }),
            0);
}

}  // namespace
