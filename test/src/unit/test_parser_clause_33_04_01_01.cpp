#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConfigDesignStatement, ZeroDesignStatementsRejected) {
  auto r = Parse("config c;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigDesignStatement, DuplicateDesignStatementsRejected) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  design work.other;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigDesignStatement, DesignBeforeRulesAccepted) {
  auto r = Parse("config c;\n"
                 "  design work.top;\n"
                 "  default liblist work;\n"
                 "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigDesignStatement, RuleBeforeDesignRejected) {
  auto r = Parse("config c;\n"
                 "  default liblist work;\n"
                 "  design work.top;\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

}
