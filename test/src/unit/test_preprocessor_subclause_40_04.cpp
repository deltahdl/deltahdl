#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_fsm_pragma_lexing.h"

using namespace delta;

namespace {

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
