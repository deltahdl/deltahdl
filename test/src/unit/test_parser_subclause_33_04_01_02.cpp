#include <gtest/gtest.h>

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
  // "The use expansion clause (see 33.4.1.6) cannot be used with a default
  // selection clause", so the pairing is reported under §33.4.1.2, at the
  // 'use' written where only a liblist may stand.
  EXPECT_TRUE(ReportedError(r.diags, "use expansion clause cannot be used", 3,
                            "33.4.1.2"));
}

TEST(ConfigDefaultClause, DefaultUseClauseIsTheOnlyReport) {
  // The use clause is read to its end, so the config's terminator and the
  // declarations after it are read as what they are and draw no report.
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default use work.alt;\n"
      "  cell adder liblist work;\n"
      "endconfig\n"
      "module top;\n"
      "endmodule\n");
  EXPECT_EQ(r.diags.size(), 1u);
  EXPECT_TRUE(ReportedError(r.diags, "use expansion clause cannot be used", 3,
                            "33.4.1.2"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
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
