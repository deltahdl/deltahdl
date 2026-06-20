#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Plain-data copy of a recognized §40.4.3 concatenation FSM pragma so that
// assertions do not depend on string_views into a transient SourceManager.
struct ConcatPragmaInfo {
  std::vector<std::string> signals;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<ConcatPragmaInfo> CollectConcatPragmas(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<ConcatPragmaInfo> out;
  for (const auto& p : lexer.FsmConcatPragmas()) {
    ConcatPragmaInfo info;
    for (const auto& s : p.signal_names) {
      info.signals.push_back(std::string(s));
    }
    info.fsm_name = std::string(p.fsm_name);
    info.enum_name = std::string(p.enum_name);
    out.push_back(std::move(info));
  }
  return out;
}

// §40.4.3: the concatenation is composed of all the signals specified. Every
// listed member is recorded, regardless of the irregular whitespace around the
// commas and braces that may split the comment body into separate words.
TEST(FsmConcatPragmaLexing, ComposedOfAllSignalsWithIrregularSpacing) {
  auto pragmas =
      CollectConcatPragmas("/* tool state_vector { a , b,c } my_fsm enum e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"a", "b", "c"}));
}

// §40.4.3: the concatenation is composed of all the signals specified — the
// minimal case being a single whole signal between the braces, written as one
// contiguous word. That single member is recorded.
TEST(FsmConcatPragmaLexing, SingleSignalConcatenationRecordsThatSignal) {
  auto pragmas = CollectConcatPragmas(
      "/* tool state_vector {only} my_fsm enum state_e "
      "*/");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"only"}));
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// §40.4.3: bit-selects or part-selects of signals cannot be used in the
// concatenation. A member that is a bit-select or a part-select makes the
// whole pragma unrecognized as a concatenation current-state pragma.
TEST(FsmConcatPragmaLexing, BitSelectOrPartSelectMemberRejected) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi[0], lo} my_fsm enum e */")
          .empty());
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi[3:0], lo} my_fsm enum e "
                           "*/")
          .empty());
}

// §40.4.3's form includes an FSM name and an enumeration name bound with the
// literal `enum` keyword. A concatenation pragma missing the FSM name, or with
// some other token in the binding position, is not recognized.
TEST(FsmConcatPragmaLexing, RequiresFsmNameAndEnumBinding) {
  // Missing the FSM name between the braces and the `enum` keyword.
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo} enum state_e */")
          .empty());
  // The binding keyword must literally be `enum`.
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo} my_fsm uses state_e "
                           "*/")
          .empty());
}

// §40.4.3's form lists the signals between braces; an empty brace pair names no
// signals for the concatenation to be composed of, so it is not recognized.
TEST(FsmConcatPragmaLexing, EmptyConcatenationIsNotRecognized) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {} my_fsm enum state_e */")
          .empty());
}

// §40.4.3's concatenation form is brace-delimited; without a closing brace the
// signal list is unterminated and the pragma is not recognized as a
// concatenation current-state pragma.
TEST(FsmConcatPragmaLexing, UnclosedBraceIsNotRecognized) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo my_fsm enum state_e "
                           "*/")
          .empty());
}

// The concatenation form is recorded as its own kind of FSM pragma: it does not
// appear among the §40.4.1 whole-signal pragmas nor the §40.4.2 part-select
// pragmas.
TEST(FsmConcatPragmaLexing, ConcatIsSeparateFromOtherFsmPragmas) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  const std::string src = "/* tool state_vector {hi, lo} my_fsm enum e */";
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_EQ(lexer.FsmConcatPragmas().size(), 1u);
  EXPECT_TRUE(lexer.FsmStatePragmas().empty());
  EXPECT_TRUE(lexer.FsmPartSelectPragmas().empty());
}

// The pragma is written inside the module definition where the signals are
// declared, and is recognized there while the surrounding source still lexes
// into its ordinary token stream.
TEST(FsmConcatPragmaLexing, RecognizedWithinModuleBody) {
  const std::string src =
      "module fsm;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  /* tool state_vector {hi, lo} my_fsm enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectConcatPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"hi", "lo"}));
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

}  // namespace
