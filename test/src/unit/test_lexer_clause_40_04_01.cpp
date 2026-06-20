#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// R1: `/* tool state_vector signal_name */` names the vector signal that holds
// the current state; `tool` and `state_vector` are the required keywords.
TEST(FsmStatePragmaLexing, RecognizesCurrentStatePragma) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector cur_state */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_FALSE(pragmas[0].has_enum);
}

// R2: the same pragma may carry the enumeration name; `enum` is the required
// keyword that binds the signal to the FSM.
TEST(FsmStatePragmaLexing, RecognizesCombinedEnumPragma) {
  auto pragmas =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// The leading `tool` keyword is required: an ordinary comment is not an FSM
// pragma and is discarded like any other comment.
TEST(FsmStatePragmaLexing, RequiresToolKeyword) {
  EXPECT_TRUE(CollectFsmPragmas("/* state_vector cur_state */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* just an ordinary comment */").empty());
}

// `state_vector` is a required keyword of the current-state form; substituting
// any other word leaves the comment unrecognized.
TEST(FsmStatePragmaLexing, RequiresStateVectorKeyword) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool vector cur_state */").empty());
}

// `enum` is the required keyword that binds an enumeration name. Naming the
// enumeration without the keyword is not a valid binding and is not recognized;
// with the keyword the binding is captured.
TEST(FsmStatePragmaLexing, EnumKeywordRequiredToBindName) {
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state state_e */").empty());
  auto bound =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");
  ASSERT_EQ(bound.size(), 1u);
  EXPECT_TRUE(bound[0].has_enum);
}

// The pragma is written inside the module definition where the signal is
// declared, and is recognized there while the surrounding source still lexes
// into its ordinary token stream.
TEST(FsmStatePragmaLexing, PragmaWithinModuleBody) {
  const std::string src =
      "module fsm;\n"
      "  logic [2:0] cur_state;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// The separate enum pragma sits immediately after the bit range of the signal
// declaration; being a comment it is invisible to the token stream yet is still
// recorded as an FSM pragma.
TEST(FsmStatePragmaLexing, SeparatePragmaInDeclarationIsInvisibleToTokens) {
  const std::string src = "logic [7:0] /* tool enum state_e */ cur_state;";

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  // The pragma comment leaks no tokens between the bit range and the name.
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].text, "cur_state");

  ASSERT_EQ(lexer.FsmStatePragmas().size(), 1u);
  EXPECT_EQ(lexer.FsmStatePragmas()[0].form,
            Lexer::FsmStatePragma::Form::kEnumOnly);
  EXPECT_EQ(lexer.FsmStatePragmas()[0].enum_name, "state_e");
}

// The enumeration name may be supplied by a separate pragma instead of the
// combined form: a `state_vector` pragma names the signal and a distinct `enum`
// pragma in the declaration binds the enumeration. Both are recognized and the
// lexer keeps each as its own FSM pragma.
TEST(FsmStatePragmaLexing, SeparateEnumPragmaPairsWithStateVectorPragma) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cur_state */\n"
      "  logic [2:0] /* tool enum state_e */ cur_state;\n"
      "endmodule\n";
  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 2u);

  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_FALSE(pragmas[0].has_enum);

  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "state_e");
}

// A pragma that carries only the `tool` keyword, or names a keyword without its
// required operand (the signal for `state_vector`, the name for `enum`), is
// incomplete and is not recognized as an FSM pragma.
TEST(FsmStatePragmaLexing, IncompletePragmasAreNotRecognized) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* tool state_vector */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* tool enum */").empty());
}

// The bracketed part-select and braced concatenation current-state forms belong
// to descendant subclauses (§40.4.2 / §40.4.3); the §40.4.1 recognizer names
// only a simple signal and leaves those forms alone.
TEST(FsmStatePragmaLexing, IgnoresPartSelectAndConcatenationForms) {
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state[1:0] fsm enum e */")
          .empty());
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector {hi, lo} fsm enum e */").empty());
}

}  // namespace
