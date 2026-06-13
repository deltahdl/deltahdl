#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Plain-data copy of a recognized §40.4.2 part-select FSM pragma so that
// assertions do not depend on string_views into a transient SourceManager.
struct PartSelectPragmaInfo {
  std::string signal;
  int msb = 0;
  int lsb = 0;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<PartSelectPragmaInfo> CollectPartSelectPragmas(
    const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<PartSelectPragmaInfo> out;
  for (const auto& p : lexer.FsmPartSelectPragmas()) {
    out.push_back({std::string(p.signal_name), p.msb, p.lsb,
                   std::string(p.fsm_name), std::string(p.enum_name)});
  }
  return out;
}

// §40.4.2: a part-select of a vector signal can hold the current state of the
// FSM. The pragma names the base signal, its part-select range, an FSM name,
// and the bound enumeration name.
TEST(FsmPartSelectPragmaLexing, RecognizesPartSelectPragma) {
  auto pragmas =
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] my_fsm "
                               "enum state_e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].msb, 3);
  EXPECT_EQ(pragmas[0].lsb, 0);
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// §40.4.2's form names a part-select `signal_name[n:n]` — a vector bit range.
// A bracketed reference that is not a two-bound numeric range (a missing colon,
// or non-numeric bounds) does not match the part-select form and is not
// recognized, even when the surrounding FSM and enum names are well formed.
TEST(FsmPartSelectPragmaLexing, MalformedPartSelectRangeIsNotRecognized) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3] my_fsm enum "
                               "state_e */")
          .empty());
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[hi:lo] my_fsm "
                               "enum state_e */")
          .empty());
}

// §40.4.2: when a part-select holds the current state, the user needs to also
// specify a name for the FSM. A part-select pragma without an FSM name (the
// word between the part-select and the `enum` binding) is not recognized.
TEST(FsmPartSelectPragmaLexing, FsmNameIsRequired) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] enum "
                               "state_e */")
          .empty());
}

// §40.4.2's pragma binds the enumeration with the literal `enum` keyword
// (`... FSM_name enum enumeration_name`). A pragma with the full five trailing
// words but some other token in the binding position — rather than too few
// words — is not recognized: the keyword itself is required, not merely a word
// in that slot.
TEST(FsmPartSelectPragmaLexing, RequiresLiteralEnumKeywordInBinding) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] my_fsm "
                               "uses state_e */")
          .empty());
}

// The leading `tool` and `state_vector` keywords are required, just as for the
// whole-signal current-state pragma.
TEST(FsmPartSelectPragmaLexing, RequiresToolAndStateVectorKeywords) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* state_vector cur_state[3:0] my_fsm enum "
                               "state_e */")
          .empty());
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool vector cur_state[3:0] my_fsm enum "
                               "state_e */")
          .empty());
}

// The pragma is written inside the module definition where the signal is
// declared, and is recognized there while the surrounding source still lexes
// into its ordinary token stream.
TEST(FsmPartSelectPragmaLexing, RecognizedWithinModuleBody) {
  const std::string src =
      "module fsm;\n"
      "  logic [7:0] bus;\n"
      "  /* tool state_vector bus[3:0] my_fsm enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectPartSelectPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "bus");
  EXPECT_EQ(pragmas[0].msb, 3);
  EXPECT_EQ(pragmas[0].lsb, 0);
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
}

// The part-select form is recorded as its own kind of FSM pragma: it does not
// appear among the §40.4.1 whole-signal pragmas, and the whole-signal form does
// not appear among the part-select pragmas.
TEST(FsmPartSelectPragmaLexing, PartSelectIsSeparateFromSimpleSignalPragma) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  const std::string src = "/* tool state_vector cur_state[3:0] my_fsm enum e */";
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_EQ(lexer.FsmPartSelectPragmas().size(), 1u);
  EXPECT_TRUE(lexer.FsmStatePragmas().empty());

  SourceManager mgr2;
  DiagEngine diag2(mgr2);
  const std::string simple = "/* tool state_vector cur_state enum e */";
  auto fid2 = mgr2.AddFile("<test>", simple);
  Lexer lexer2(mgr2.FileContent(fid2), fid2, diag2);
  lexer2.LexAll();
  EXPECT_TRUE(lexer2.FsmPartSelectPragmas().empty());
  EXPECT_EQ(lexer2.FsmStatePragmas().size(), 1u);
}

}  // namespace
