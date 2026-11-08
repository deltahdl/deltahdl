#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

std::string TheFigure() {
  return "module m3;\n"
         "\n"
         "reg[31:0] cs;\n"
         "reg[31:0] /* tool enum MY_FSM */ ns;\n"
         "reg[31:0] clk;\n"
         "reg[31:0] rst;\n"
         "\n"
         "// tool state_vector cs enum MY_FSM\n"
         "\n"
         "parameter // tool enum MY_FSM\n"
         "p1=10,\n"
         "p2=11,\n"
         "p3=12;\n"
         "\n"
         "endmodule // m3\n";
}

TEST(FsmPragmaExampleLexing, TheFigureIsDrawnWithThreePragmasOfOneFsm) {
  auto pragmas = CollectFsmPragmas(TheFigure());
  ASSERT_EQ(pragmas.size(), 3u);

  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].signal.empty());

  EXPECT_EQ(pragmas[1].form, "state_vector");

  EXPECT_EQ(pragmas[2].form, "enum_only");
  EXPECT_TRUE(pragmas[2].signal.empty());

  for (const auto& p : pragmas) {
    EXPECT_TRUE(p.has_enum);
    EXPECT_EQ(p.enum_name, "MY_FSM");
  }
}

TEST(FsmPragmaExampleLexing,
     TheSignalFollowingTheFirstPragmaHoldsTheNextState) {
  const std::vector<std::string> kNextState = {"ns"};

  EXPECT_EQ(KindBeforeEnumPragma(TheFigure(), 0), TokenKind::kRBracket);
  EXPECT_EQ(NamesFollowingEnumPragma(TheFigure(), 0), kNextState);
}

TEST(FsmPragmaExampleLexing, TheStateVectorPragmaNamesTheCurrentStateSignal) {
  auto pragmas = CollectFsmPragmas(TheFigure());
  ASSERT_EQ(pragmas.size(), 3u);
  EXPECT_EQ(pragmas[1].form, "state_vector");
  EXPECT_EQ(pragmas[1].signal, "cs");
  EXPECT_EQ(pragmas[1].enum_name, "MY_FSM");
}

TEST(FsmPragmaExampleLexing, TheNamesFollowingTheLastPragmaArePossibleStates) {
  const std::vector<std::string> kPossibleStates = {"p1", "p2", "p3"};

  EXPECT_EQ(KindBeforeEnumPragma(TheFigure(), 1), TokenKind::kKwParameter);
  EXPECT_EQ(NamesFollowingEnumPragma(TheFigure(), 1), kPossibleStates);
}

TEST(FsmPragmaExampleLexing, TheClosingCommentIsNoPragmaAndNothingIsReported) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", TheFigure());
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();

  EXPECT_EQ(lexer.FsmStatePragmas().size(), 3u);
  EXPECT_TRUE(lexer.FsmPartSelectPragmas().empty());
  EXPECT_TRUE(lexer.FsmConcatPragmas().empty());
  EXPECT_TRUE(diag.Diagnostics().empty());
}

}  // namespace
