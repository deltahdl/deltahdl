#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.16.1: "str.len() returns the length of the string, i.e., the number of
// characters in the string". `S` holds "abc", so `N` resolves to 3.
//
// 3 is not reachable by accident from anything else this declaration records.
// §11.10 packs "abc" into the constant number 0x616263, which is 6382179, so an
// implementation that returned the packed value of `S` misses. A `string`
// declaration carries no packed range, so `RtlirParamDecl::decl_width` is 0 for
// `S` and an implementation that returned the declared width misses too. Only a
// count of the characters reaches 3.
TEST(StringLenElaboration, LenOfAStringLocalparamFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abc\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

// §6.16.1 states the empty string separately: "If str is "", then str.len()
// returns 0". `N` resolves to 0.
//
// 0 is also what `RtlirParamDecl::resolved_value` holds before anything
// resolves it, so the value alone would pass against an elaborator that folded
// nothing at all. That is why this test asserts `is_resolved` as well: the two
// together separate a fold that answered 0 from a parameter left unresolved.
TEST(StringLenElaboration, LenOfTheEmptyStringFoldsToZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 0);
}

// §6.16 rules that "strings can be of arbitrary length and no truncation
// occurs", so a nine-character string has length 9 and `N` resolves to 9.
//
// Nine characters is past what the packed form fits. §11.10 keeps one byte per
// character, and `RtlirParamDecl::resolved_value` is 64 bits, so the packed
// value of "abcdefghi" holds at most its last eight characters. Any
// implementation that derived the length from `resolved_value` reaches at most
// 8 here, which is why the string is nine characters and not four.
TEST(StringLenElaboration,
     LenOfAStringLongerThanSixtyFourBitsFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abcdefghi\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 9);
}

// §5.9 makes `\n` in a string literal one character, so "a\nb" holds the three
// characters `a`, newline and `b`, and §6.16.1's count of them is 3.
//
// The source text between the quotes is four characters wide, so 3 and 4
// separate a count of the decoded characters from a count of the literal's
// spelling. An implementation that measured the token's text reaches 4.
TEST(StringLenElaboration, LenCountsAnEscapeSequenceAsOneCharacter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\nb\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

// §6.16 gives `parameter string default_name = "John Smith";` as its own
// declaration example, so a string parameter is as likely to be written in the
// parameter port list as in the module body. The elaborator resolves the two on
// different paths, and a fold reached from only the body would leave this one
// unresolved. "hello" is five characters, so `N` resolves to 5.
//
// 5 is not reachable from the packed value of "hello", which §11.10 makes
// 0x68656C6C6F, and not from the declared width of a `string`, which carries no
// packed range.
TEST(StringLenElaboration, LenOfAStringParameterPortFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter string S = \"hello\") ();\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 5);
}

// The boundary the five tests above need. §5.13 rules that "a built-in method
// can only be associated with a particular data type", and §6.16.1 associates
// len() with `string` alone. `S` is declared `int` here, so `S.len()` names no
// built-in method and there is no length to fold: `N` stays unresolved.
//
// Without this, a fix that answered len() for every parameter whatever its
// declared type would satisfy all five.
//
// §6.20.4 reports the declaration as well, because a call that names no
// built-in method is not one of the operands §11.2.1 lists and so `S.len()` is
// not a constant expression. Both claims are asserted here: which rule rejects
// the source, and that the value behind it did not fold.
TEST(StringLenElaboration, LenOfAnIntegerParameterDoesNotFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int S = 3;\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_FALSE(n->is_resolved);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

// §6.16 rules that "A string variable shall not contain the special character
// "\0". Assigning the value 0 to a string character shall be ignored." So the
// value of "a\0b" is the two characters "ab", and §6.16.1's count of them is 2.
//
// 2 is the number the run time already answers, because Lowerer::LowerParams
// packs the parameter through StripStringZeros in src/simulator/lowerer.cpp.
// Before this case the fold answered 3 and the same expression gave different
// answers in the two places it can be asked.
TEST(StringLenElaboration, LenIgnoresANulEscapeInTheInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\0b\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 2);
}

// The same rule reached through the other escape form. §5.6's hex escape and
// its octal escape are decoded by separate branches of ConstDecodeEscape in
// src/elaborator/const_eval.cpp, so a repair written into one branch would
// leave the other counting a character the string does not have.
TEST(StringLenElaboration, LenIgnoresAHexNulEscapeInTheInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\x00b\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 2);
}

// An initializer of nothing but the forbidden character. §6.16 rules that "An
// empty string has zero length", and this is the input where keeping the zero
// bytes and dropping them differ by the whole of the answer rather than by one.
TEST(StringLenElaboration, LenOfAnAllNulInitializerIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"\\0\\0\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 0);
}

// §11.2.1 lists "parameters" among the operands a constant expression consists
// of, so `B = A` is one and B holds A's ten characters. len() folding to 10 is
// what says the characters were recorded: StringParamLength answers nothing at
// all unless RtlirParamDecl::is_string_value is set, so before this the call
// did not fold rather than folding wrong.
TEST(StringLenElaboration,
     LenOfAParameterInitializedFromAnotherParameterFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter string A = \"John Smith\";\n"
      "  parameter string B = A;\n"
      "  localparam int N = B.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 10);
}

// §6.16.1's len() written inside a generate block. §27.4 makes a generate
// block "a separate scope and a new level of hierarchy when it is
// instantiated", and §6.16.1 says nothing that would stop there, so the
// block's own S is what the call names and N folds to 3 exactly as
// StringLenElaboration.LenOfAStringLocalparamFoldsToTheCharacterCount above
// has it at module level. 3 is unreachable from anything else the declaration
// records for the reason that case gives.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamRangeRegistryGuard:
// StringParamLength in src/elaborator/const_eval_builtin_method.cpp answers
// from the registered module, there is none for the whole of a block's body,
// and the call does not fold, leaving N unresolved.
TEST(StringLenElaboration,
     LenOfAGenerateBlockStringLocalparamFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string S = \"abc\";\n"
      "      localparam int N = S.len();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

}  // namespace
