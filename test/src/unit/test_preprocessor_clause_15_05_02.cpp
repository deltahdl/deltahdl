#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(NamedEventWaitPreprocessor, BareAtFormSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  event ev;\n"
      "  initial @ev;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@ev"), std::string::npos);
}

TEST(NamedEventWaitPreprocessor, ParenthesizedAtFormSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  event ev;\n"
      "  initial @(ev);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(ev)"), std::string::npos);
}

TEST(NamedEventWaitPreprocessor, HierarchicalEventWaitSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial @(c1.ev);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(c1.ev)"), std::string::npos);
}

TEST(NamedEventWaitPreprocessor, MacroExpansionInWaitIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EV my_event\n"
      "module m;\n"
      "  event my_event;\n"
      "  initial @`EV;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@my_event"), std::string::npos);
}

TEST(NamedEventWaitPreprocessor, TriggerOperatorSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  event ev;\n"
      "  initial -> ev;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("-> ev"), std::string::npos);
}

}  // namespace
