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

TEST(FsmNextStatePragmaLexing, NextStateSignalSpecifiedByEnumPragma) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "  logic [7:0] cur_state;\n"
      "  logic [7:0] /* tool enum state_e */ nxt_state;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 2u);

  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");

  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "state_e");
  EXPECT_TRUE(pragmas[1].signal.empty());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", kSrc);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  bool found_nxt = false;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kIdentifier && t.text == "nxt_state") {
      found_nxt = true;
    }
  }
  EXPECT_TRUE(found_nxt);
}

TEST(FsmNextStatePragmaLexing, NextStatePragmaOmittedWhenNoNextStateSignal) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "  logic [7:0] cur_state;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
}

TEST(FsmNextStatePragmaLexing, NextStatePragmaInAOneLineComment) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "  logic [7:0] cur_state;\n"
      "  logic [7:0] // tool enum state_e\n"
      "    nxt_state;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "state_e");
  EXPECT_TRUE(pragmas[1].signal.empty());
}

TEST(FsmNextStatePragmaLexing, EachNextStatePragmaKeepsItsOwnEnumerationName) {
  const std::string kSrc =
      "module two_fsms;\n"
      "  /* tool state_vector cs_a enum fsm_a */\n"
      "  logic [1:0] /* tool enum fsm_a */ ns_a;\n"
      "  /* tool state_vector cs_b enum fsm_b */\n"
      "  logic [1:0] /* tool enum fsm_b */ ns_b;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 4u);

  EXPECT_EQ(pragmas[0].signal, "cs_a");
  EXPECT_EQ(pragmas[0].enum_name, "fsm_a");
  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_EQ(pragmas[1].enum_name, "fsm_a");

  EXPECT_EQ(pragmas[2].signal, "cs_b");
  EXPECT_EQ(pragmas[2].enum_name, "fsm_b");
  EXPECT_EQ(pragmas[3].form, "enum_only");
  EXPECT_EQ(pragmas[3].enum_name, "fsm_b");
}

}  // namespace
