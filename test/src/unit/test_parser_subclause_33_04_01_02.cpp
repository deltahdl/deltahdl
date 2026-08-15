#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConfigDefaultClause, DefaultUseClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default use work.alt;\n"
      "endconfig\n");
  // A default_clause admits only a liblist_clause, so the parser demands the
  // 'liblist' keyword and reports its absence under §33.4.1.5, the subclause
  // stating that clause. The message names both the 'liblist' wanted and the
  // 'use' found in its place.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'liblist', got 'use'", 3, "33.4.1.5"));
}

TEST(ConfigDefaultClause, DefaultLiblistAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
