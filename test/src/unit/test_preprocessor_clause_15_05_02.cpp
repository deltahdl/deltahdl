#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §15.5.2: The basic wait mechanism uses the @ operator with a
// hierarchical_event_identifier. The text of the @-wait must pass
// through the preprocessor unmodified so the lexer/parser can recognize
// it as the wait syntax.
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

// §15.5.2: The parenthesized wait form "@(hierarchical_event_identifier)"
// must also survive preprocessing intact (it routes through §9.4.2's
// event_control alternative for the same operator).
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

// §15.5.2: A hierarchical_event_identifier (named event reached through
// a dotted instance path) must survive preprocessing unchanged.
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

// §15.5.2: A macro that expands to a named-event identifier shall
// produce a valid @-wait after expansion (the @ operator binds to the
// expanded hierarchical_event_identifier).
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

// §15.5 (parent): A named event is triggered explicitly via "->". The
// trigger operator that pairs with the §15.5.2 wait must also survive
// preprocessing so the wait/trigger ordering rule can be enforced
// downstream.
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
