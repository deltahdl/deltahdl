#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// §40.4.4 — Specifying signal that holds next state.
//
// The signal that holds the FSM's next state is named with the very same
// enumeration pragma defined by §40.4.1's separate-pragma form:
//
//     logic [7:0] /* tool enum enumeration_name */ signal_name
//
// Lexically this is identical to the §40.4.1 "enum-only" pragma written after a
// signal's bit range, so the lexer already records it as a
// FsmStatePragma::Form::kEnumOnly. What is distinctive about §40.4.4 is the
// role: the annotated signal is the next-state signal (not the state vector),
// linked to its FSM solely through the shared enumeration name. These tests
// observe that existing recognition applying §40.4.4's rule, and that the
// pragma may be omitted when the FSM has no next-state signal.

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

// C1: the next-state signal is specified by the enumeration pragma placed after
// the bit range. The current-state signal names the FSM via a `state_vector`
// pragma; a separate next-state signal carries only `/* tool enum state_e */`,
// tying it to the same FSM through the shared enumeration name. Both pragmas are
// recorded, the next-state signal's as a standalone enum-only pragma, and the
// next-state signal's own name still reaches the token stream.
TEST(FsmNextStatePragmaLexing, NextStateSignalSpecifiedByEnumPragma) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "  logic [7:0] cur_state;\n"
      "  logic [7:0] /* tool enum state_e */ nxt_state;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 2u);

  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");

  // The next-state signal is identified purely by the enum pragma; it shares the
  // enumeration name with the current-state signal but carries no signal name of
  // its own in the pragma.
  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "state_e");
  EXPECT_TRUE(pragmas[1].signal.empty());

  // The pragma is a comment: the next-state signal's declaration still lexes,
  // with its name appearing in the token stream right after the bit range.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
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

// C2: the next-state pragma may be omitted when the FSM has no next-state
// signal. With only the current-state pragma present, the lexer records that
// FSM pragma and no enum-only pragma for an absent next-state signal.
TEST(FsmNextStatePragmaLexing, NextStatePragmaOmittedWhenNoNextStateSignal) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "  logic [7:0] cur_state;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
}

}  // namespace
