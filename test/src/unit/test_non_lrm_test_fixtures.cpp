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
  // `cell` is reserved by Table B.1 -- §33.4.1 uses it for the cell clause of
  // a config -- so this declares no module, and the elaborator is handed
  // nothing. A case asserting a rejection here would be asserting nothing.
  EXPECT_NONFATAL_FAILURE(ElabOk("module cell;\nendmodule\n"), "did not parse");
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

}  // namespace
