#include "fixture_parser.h"

using namespace delta;

namespace {

// §33.4.1.1 item 1: a config with no design statement violates the
// "one and only one" rule.
TEST(ConfigDesignStatement, ZeroDesignStatementsRejected) {
  auto r = Parse("config c;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// §33.4.1.1 item 1: two design statements in the same config also
// violate the "one and only one" rule.
TEST(ConfigDesignStatement, DuplicateDesignStatementsRejected) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  design work.other;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// §33.4.1.1 item 5 (positive): design statement before rules — accepted.
TEST(ConfigDesignStatement, DesignBeforeRulesAccepted) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  default liblist work;\n"
                 "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

// §33.4.1.1 item 5 (negative): a rule appearing before the design
// statement is rejected.
TEST(ConfigDesignStatement, RuleBeforeDesignRejected) {
  auto r = Parse("config c;\n"
                 "  default liblist work;\n"
                 "  design work.top;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
