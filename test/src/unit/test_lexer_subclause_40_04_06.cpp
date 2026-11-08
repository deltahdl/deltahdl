#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_fsm_pragma_lexing.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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

void ExpectSingleMyFsmEnumPragma(const std::vector<FsmPragmaInfo>& pragmas) {
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  EXPECT_TRUE(pragmas[0].signal.empty());
}

TEST(FsmPossibleStatesPragmaLexing, RecognizesEnumPragmaAfterParameterKeyword) {
  const std::string kSrc =
      "module fsm;\n"
      "  parameter /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ExpectSingleMyFsmEnumPragma(pragmas);

  auto states = CollectStateParams(kSrc);
  ASSERT_EQ(states.size(), 4u);
  EXPECT_EQ(states[0], "S0");
  EXPECT_EQ(states[1], "s1");
  EXPECT_EQ(states[2], "s2");
  EXPECT_EQ(states[3], "s3");
}

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

TEST(FsmPossibleStatesPragmaLexing, ThePragmaStandsWhereTheClausePutsIt) {
  const std::string kAfterKeyword =
      "module fsm;\n"
      "  parameter OTHER = 9;\n"
      "  parameter /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";
  const std::string kAfterWidth =
      "module fsm;\n"
      "  parameter OTHER = 9;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";
  const std::vector<std::string> kStates = {"S0", "s1", "s2", "s3"};

  EXPECT_EQ(KindBeforeEnumPragma(kAfterKeyword), TokenKind::kKwParameter);
  EXPECT_EQ(NamesFollowingEnumPragma(kAfterKeyword), kStates);

  EXPECT_EQ(KindBeforeEnumPragma(kAfterWidth), TokenKind::kRBracket);
  EXPECT_EQ(NamesFollowingEnumPragma(kAfterWidth), kStates);
}

}  // namespace
