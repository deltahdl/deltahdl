#include "fixture_parser.h"

using namespace delta;

namespace {

// §33.4.1.2 item 2: the use expansion clause cannot follow a default
// selection clause; the parser rejects `default use ...`.
TEST(ConfigDefaultClause, DefaultUseClauseRejected) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  default use work.alt;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// Positive control: a valid default+liblist pair parses cleanly.
TEST(ConfigDefaultClause, DefaultLiblistAccepted) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  default liblist work;\n"
                 "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
