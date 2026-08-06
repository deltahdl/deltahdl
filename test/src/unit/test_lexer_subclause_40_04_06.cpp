#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"

using namespace delta;

// §40.4.6 — Specifying possible states of FSM.
//
// The possible states of an FSM can be specified with the same enumeration-name
// pragma (§40.4.1's separate `/* tool enum E */` form), written on a parameter
// declaration whose parameters enumerate the legal states. The LRM gives two
// placements:
//
//     parameter /* tool enum enumeration_name */
//     S0 = 0, s1 = 1, s2 = 2, s3 = 3;
//
// and, when a bit width is used for the parameters, immediately after the
// width:
//
//     parameter [1:0] /* tool enum enumeration_name */
//     S0 = 0, s1 = 1, s2 = 2, s3 = 3;
//
// Lexically nothing new happens here. §40.4.1 already recognizes the enum-only
// pragma context-independently, so it is recognized just the same whether it
// follows a `logic` bit range, the `parameter` keyword, or a parameter bit
// width. The interpretation that these parameters are the FSM's possible states
// is a semantic FSM-extraction layer on top of the tokens — the same kind of
// semantic decision §40.4.4/§40.4.5 noted the lexer does not make. These tests
// observe that the existing recognition surfaces the enum pragma in both
// §40.4.6 placements, and that every state-naming parameter reaches the token
// stream.

namespace {

// Collects the state-naming parameters S0, s1, s2, s3 from `src` in the order
// they appear in the token stream.
std::vector<std::string> CollectStateParams(const std::string& src) {
  auto idents = CollectIdentifiers(src);
  std::vector<std::string> states;
  for (const auto& id : idents) {
    if (id == "S0" || id == "s1" || id == "s2" || id == "s3") {
      states.push_back(id);
    }
  }
  return states;
}

// Asserts the single enum-only `myFSM` pragma surfaced by a §40.4.6 parameter
// declaration; the pragma binds the enumeration and carries no signal name.
void ExpectSingleMyFsmEnumPragma(const std::vector<FsmPragmaInfo>& pragmas) {
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  EXPECT_TRUE(pragmas[0].signal.empty());
}

// Claim A — the possible states are specified with the enum-only pragma placed
// immediately after the `parameter` keyword. The enum pragma is recognized in
// this placement, binding the FSM enumeration name, and each state-naming
// parameter (S0, s1, s2, s3) reaches the token stream — the raw material a
// downstream extractor reads to learn the FSM's legal states.
TEST(FsmPossibleStatesPragmaLexing, RecognizesEnumPragmaAfterParameterKeyword) {
  const std::string kSrc =
      "module fsm;\n"
      "  parameter /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  // The enum-only pragma carries no signal name; it only binds the enumeration.
  ExpectSingleMyFsmEnumPragma(pragmas);

  auto states = CollectStateParams(kSrc);
  ASSERT_EQ(states.size(), 4u);
  EXPECT_EQ(states[0], "S0");
  EXPECT_EQ(states[1], "s1");
  EXPECT_EQ(states[2], "s2");
  EXPECT_EQ(states[3], "s3");
}

// Claim B — when a bit width is used for the parameters, the pragma is placed
// immediately after the bit width instead. Recognition is unchanged: the same
// enum pragma is surfaced, and the bit-range tokens between `parameter` and the
// pragma do not disturb it. The state-naming parameters still reach the stream.
TEST(FsmPossibleStatesPragmaLexing,
     RecognizesEnumPragmaAfterParameterBitWidth) {
  const std::string kSrc =
      "module fsm;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ExpectSingleMyFsmEnumPragma(pragmas);

  auto states = CollectStateParams(kSrc);
  ASSERT_EQ(states.size(), 4u);
  EXPECT_EQ(states[0], "S0");
  EXPECT_EQ(states[3], "s3");
}

}  // namespace
