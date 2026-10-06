#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_fsm_pragma_lexing.h"

using namespace delta;

namespace {

// §40.4 writes the FSM pragmas as the text of a comment, so they reach the
// lexer that records them only if the preprocessor hands each comment on with
// its text. A parameter's enum-only pragma and a signal's state_vector pragma,
// run through the preprocessor as every compiled source is, are both still
// recorded from the preprocessed text (#5135).
TEST(FsmPragmaPreprocessing, PragmasSurviveThePreprocessor) {
  PreprocFixture f;
  auto out = Preprocess(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
  EXPECT_EQ(pragmas[1].form, "state_vector");
  EXPECT_EQ(pragmas[1].signal, "st");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "fsm_e");
}

// The pragma keeps its text on a line whose macro usages the preprocessor
// expands: the bit range is substituted and the enum-only pragma behind it is
// still recorded.
TEST(FsmPragmaPreprocessing, PragmaSurvivesBesideAnExpandedMacro) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 2\n"
      "module top;\n"
      "  logic [`W-1:0] /* tool enum fsm_e */ nxt;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("[2-1:0]"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
}

// §40.4.7 lets the pragmas stand in a one-line comment as well, and that
// comment's text reaches the lexer the same way.
TEST(FsmPragmaPreprocessing, OneLineCommentPragmaSurvivesThePreprocessor) {
  PreprocFixture f;
  auto out = Preprocess(
      "module top;\n"
      "  // tool state_vector cs enum my_fsm\n"
      "  logic [1:0] cs;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_EQ(pragmas[0].enum_name, "my_fsm");
}

// A macro usage whose argument list runs onto the next line is read with that
// line joined to it (§22.5.1), and a pragma written on the line read ahead
// keeps its text: the enum-only pragma behind the usage is still recorded.
TEST(FsmPragmaPreprocessing, PragmaOnALineReadAheadForAUsageSurvives) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W(a, b) a+b\n"
      "module top;\n"
      "  logic [`W(1,\n"
      "           1)-1:0] /* tool enum fsm_e */ nxt;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("-1:0] /* tool enum fsm_e */ nxt;"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
}

// A one-line comment ending a line of a usage that runs onto the next line
// keeps its text, and the line joined after it is still read as source rather
// than swallowed into the comment.
TEST(FsmPragmaPreprocessing, OneLineCommentPragmaInAJoinedUsageSurvives) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W(a, b) a+b\n"
      "module top;\n"
      "  logic [`W(1, // tool state_vector cs enum my_fsm\n"
      "           1)-1:0] cs;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("-1:0] cs;"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_EQ(pragmas[0].enum_name, "my_fsm");
}

// The same holds for a one-line comment on a line read ahead, between the line
// the usage opens on and the one it closes on.
TEST(FsmPragmaPreprocessing, OneLineCommentPragmaOnALineReadAheadSurvives) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W(a, b) a+b\n"
      "module top;\n"
      "  logic [`W(1,\n"
      "           1 // tool enum fsm_e\n"
      "           )-1:0] nxt;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("-1:0] nxt;"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
}

// Each one-line comment of a usage that runs onto later lines keeps its text
// and stays a comment of its own, so two pragmas written on two of its lines
// are both recorded.
TEST(FsmPragmaPreprocessing, OneLineCommentPragmasOnTwoLinesOfAUsageSurvive) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W(a, b) a+b\n"
      "module top;\n"
      "  logic [`W(1, // tool enum fsm_e\n"
      "           1)-1:0] st; // tool state_vector st enum fsm_e\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("-1:0] st;"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
  EXPECT_EQ(pragmas[1].form, "state_vector");
  EXPECT_EQ(pragmas[1].signal, "st");
  EXPECT_EQ(pragmas[1].enum_name, "fsm_e");
}

// A block comment the usage's last line opens and leaves open runs on past the
// usage (A.9.2), so a one-line comment moved out of the usage is written ahead
// of it rather than inside it: the pragma is recorded, and the block comment
// still hides the directive on the line it runs onto.
TEST(FsmPragmaPreprocessing, OneLineCommentPragmaBeforeAnOpenBlockComment) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W(a, b) a+b\n"
      "module top;\n"
      "  logic [`W(1, // tool enum fsm_e\n"
      "           1)-1:0] nxt; /* a block comment\n"
      "           `define X 1 */\n"
      "`ifdef X\n"
      "  int defined_x;\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("-1:0] nxt;"), std::string::npos);
  EXPECT_EQ(out.find("defined_x"), std::string::npos);
  auto pragmas = CollectFsmPragmas(out);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_e");
}

}  // namespace
