#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_fsm_pragma_lexing.h"

using namespace delta;

namespace {

void ExpectCsThenMyFsmPragmas(const std::vector<FsmPragmaInfo>& pragmas) {
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_FALSE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "myFSM");
}

void ExpectOnlyCsIsSignalBearing(const std::vector<FsmPragmaInfo>& pragmas) {
  int signal_bearing = 0;
  for (const auto& p : pragmas) {
    if (!p.signal.empty()) {
      ++signal_bearing;
      EXPECT_EQ(p.signal, "cs");
    }
  }
  EXPECT_EQ(signal_bearing, 1);
}

std::vector<std::string> CollectDeclOrder(
    const std::string& src, const std::vector<std::string>& names) {
  auto idents = CollectIdentifiers(src);
  std::vector<std::string> decl_order;
  for (const auto& id : idents) {
    for (const auto& want : names) {
      if (id == want) {
        decl_order.push_back(id);
        break;
      }
    }
  }
  return decl_order;
}

TEST(FsmSameDeclarationPragmaLexing,
     RecognizesCurrentAndNextStateSignalsInSameDeclaration) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ExpectCsThenMyFsmPragmas(pragmas);

  auto decl_order = CollectDeclOrder(kSrc, {"cs", "ns", "nonstate"});
  ASSERT_EQ(decl_order.size(), 3u);
  EXPECT_EQ(decl_order[0], "cs");
  EXPECT_EQ(decl_order[1], "ns");
  EXPECT_EQ(decl_order[2], "nonstate");
}

TEST(FsmSameDeclarationPragmaLexing, NothingIsAssumedAboutAdditionalSignals) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  for (const auto& p : pragmas) {
    EXPECT_NE(p.signal, "ns");
    EXPECT_NE(p.signal, "nonstate");
  }

  ExpectOnlyCsIsSignalBearing(pragmas);
}

TEST(FsmSameDeclarationPragmaLexing,
     TwoSignalDeclarationAssignsCurrentThenNextState) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ExpectCsThenMyFsmPragmas(pragmas);

  auto decl_order = CollectDeclOrder(kSrc, {"cs", "ns"});
  ASSERT_EQ(decl_order.size(), 2u);
  EXPECT_EQ(decl_order[0], "cs");
  EXPECT_EQ(decl_order[1], "ns");

  ExpectOnlyCsIsSignalBearing(pragmas);
}

TEST(FsmSameDeclarationPragmaLexing, MultipleTrailingSignalsAreAllIgnored) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, idle, extra;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  for (const auto& p : pragmas) {
    EXPECT_NE(p.signal, "ns");
    EXPECT_NE(p.signal, "idle");
    EXPECT_NE(p.signal, "extra");
  }

  ExpectOnlyCsIsSignalBearing(pragmas);

  auto decl_order = CollectDeclOrder(kSrc, {"cs", "ns", "idle", "extra"});
  ASSERT_EQ(decl_order.size(), 4u);
  EXPECT_EQ(decl_order[0], "cs");
  EXPECT_EQ(decl_order[1], "ns");
  EXPECT_EQ(decl_order[2], "idle");
  EXPECT_EQ(decl_order[3], "extra");
}

TEST(FsmSameDeclarationPragmaLexing, TheRuleReachesTheSignalsFollowingPragma) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic [1:0] before_decl;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;\n"
      "  logic [1:0] after_decl;\n"
      "endmodule\n";

  auto following = NamesFollowingEnumPragma(kSrc);
  ASSERT_EQ(following.size(), 3u);
  EXPECT_EQ(following[0], "cs");
  EXPECT_EQ(following[1], "ns");
  EXPECT_EQ(following[2], "nonstate");
}

}  // namespace
