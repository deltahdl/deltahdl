#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
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

// Plain-data copy of a recognized FSM pragma so assertions do not depend on
// string_views that point into a transient SourceManager.
struct FsmPragmaInfo {
  std::string form;
  std::string signal;
  std::string enum_name;
  bool has_enum = false;
};

std::vector<FsmPragmaInfo> CollectFsmPragmas(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<FsmPragmaInfo> out;
  for (const auto& p : lexer.FsmStatePragmas()) {
    out.push_back(
        {p.form == Lexer::FsmStatePragma::Form::kStateVector ? "state_vector"
                                                             : "enum_only",
         std::string(p.signal_name), std::string(p.enum_name), p.has_enum});
  }
  return out;
}

std::vector<std::string> CollectIdentifiers(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  std::vector<std::string> out;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kIdentifier) {
      out.push_back(std::string(t.text));
    }
  }
  return out;
}

// Claim A — the possible states are specified with the enum-only pragma placed
// immediately after the `parameter` keyword. The enum pragma is recognized in
// this placement, binding the FSM enumeration name, and each state-naming
// parameter (S0, s1, s2, s3) reaches the token stream — the raw material a
// downstream extractor reads to learn the FSM's legal states.
TEST(FsmPossibleStatesPragmaLexing, RecognizesEnumPragmaAfterParameterKeyword) {
  const std::string src =
      "module fsm;\n"
      "  parameter /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  // The enum-only pragma carries no signal name; it only binds the enumeration.
  EXPECT_TRUE(pragmas[0].signal.empty());

  auto idents = CollectIdentifiers(src);
  std::vector<std::string> states;
  for (const auto& id : idents) {
    if (id == "S0" || id == "s1" || id == "s2" || id == "s3") {
      states.push_back(id);
    }
  }
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
  const std::string src =
      "module fsm;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  EXPECT_TRUE(pragmas[0].signal.empty());

  auto idents = CollectIdentifiers(src);
  std::vector<std::string> states;
  for (const auto& id : idents) {
    if (id == "S0" || id == "s1" || id == "s2" || id == "s3") {
      states.push_back(id);
    }
  }
  ASSERT_EQ(states.size(), 4u);
  EXPECT_EQ(states[0], "S0");
  EXPECT_EQ(states[3], "s3");
}

}  // namespace
