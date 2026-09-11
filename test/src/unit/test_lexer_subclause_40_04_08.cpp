#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"

using namespace delta;

// §40.4.8 — Example. The clause is one sentence pointing at Figure 40-2, "an
// example of FSM specified with pragmas", and the figure is one module carrying
// the whole of §40.4 at once:
//
//     module m3;
//
//     reg[31:0] cs;
//     reg[31:0] /* tool enum MY_FSM */ ns;
//     reg[31:0] clk;
//     reg[31:0] rst;
//
//     // tool state_vector cs enum MY_FSM
//
//     parameter // tool enum MY_FSM
//     p1=10,
//     p2=11,
//     p3=12;
//
//     endmodule // m3
//
// The three annotations drawn on the figure say what the module means: signal
// `ns` holds the next state, signal `cs` holds the current state, and `p1`,
// `p2` and `p3` are the possible states of the FSM. Each of those is a rule
// stated in its own subclause - §40.4.4, §40.4.1, §40.4.6 - and each of those
// subclauses has a file of its own here that writes a source to suit it. What
// this clause adds is that the three hold together in one module: the figure
// mixes the block-comment and one-line forms §40.4.7 allows, writes the
// current-state pragma on a line of its own after the declaration it is about,
// and ties all three to one FSM by the single enumeration name MY_FSM. So these
// cases read the figure as written rather than a source shaped to one rule, and
// read each annotation off the pragma the figure hangs it on.

namespace {

// Figure 40-2 verbatim, down to the spacing of `reg[31:0]` and the closing
// comment on `endmodule`. It is built on each call rather than held in a
// constant of its own, a std::string at namespace scope being an initializer
// that runs before main with nowhere to throw to.
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

// The figure is drawn with three pragmas and no more: the next-state signal's,
// the current-state signal's, and the possible states'. Two are written after
// `//` and one between `/*` and `*/`, so the figure is also §40.4.7's claim
// standing in one module. They carry one enumeration name between them, which
// is the whole of what makes this one FSM rather than three annotations that
// happen to share a module.
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

// "Signal ns holds the next state" - §40.4.4's rule, read off where the figure
// puts the pragma rather than off the name the annotation happens to point at.
// The enumeration pragma stands after the bit range of one declaration among
// four that are alike but for their names, and `ns` is the signal following it.
// A reader that took the next-state signal from anywhere else would name `cs`,
// `clk` or `rst` just as readily.
TEST(FsmPragmaExampleLexing,
     TheSignalFollowingTheFirstPragmaHoldsTheNextState) {
  const std::vector<std::string> kNextState = {"ns"};

  EXPECT_EQ(KindBeforeEnumPragma(TheFigure(), 0), TokenKind::kRBracket);
  EXPECT_EQ(NamesFollowingEnumPragma(TheFigure(), 0), kNextState);
}

// "Signal cs holds the current state" - §40.4.1's rule. The figure names that
// signal inside the pragma instead of by position, and writes the pragma on a
// line of its own two lines below the declaration it is about, so the current
// state is read from the pragma's own operand and the distance from the
// declaration is nothing to it.
TEST(FsmPragmaExampleLexing, TheStateVectorPragmaNamesTheCurrentStateSignal) {
  auto pragmas = CollectFsmPragmas(TheFigure());
  ASSERT_EQ(pragmas.size(), 3u);
  EXPECT_EQ(pragmas[1].form, "state_vector");
  EXPECT_EQ(pragmas[1].signal, "cs");
  EXPECT_EQ(pragmas[1].enum_name, "MY_FSM");
}

// "p1, p2, and p3 are possible states of the FSM" - §40.4.6's rule. The figure
// takes that clause's first placement, the pragma immediately after the
// `parameter` keyword with no bit width, and the states are the names following
// it as far as the semicolon that ends the declaration. They are read from the
// third pragma rather than the first, which is why the figure needs both to be
// reachable.
TEST(FsmPragmaExampleLexing, TheNamesFollowingTheLastPragmaArePossibleStates) {
  const std::vector<std::string> kPossibleStates = {"p1", "p2", "p3"};

  EXPECT_EQ(KindBeforeEnumPragma(TheFigure(), 1), TokenKind::kKwParameter);
  EXPECT_EQ(NamesFollowingEnumPragma(TheFigure(), 1), kPossibleStates);
}

// The figure closes with `endmodule // m3`, a one-line comment that is not a
// pragma, and §40.4.7 having opened the `//` path to the recognizer is what
// makes that worth saying: the recognizer reads every one-line comment now, and
// a module's ordinary closing comment must come back out of it unchanged. The
// figure is a well-formed module besides, so lexing it reports nothing.
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
