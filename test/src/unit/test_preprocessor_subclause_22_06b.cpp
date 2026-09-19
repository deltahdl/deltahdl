#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <string>
#include <utility>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// The substituted text keeps the blanks around each directive it once held, so
// the expected text is compared with every white-space character removed.
static std::string WithoutWhitespace(std::string text) {
  text.erase(std::remove_if(text.begin(), text.end(),
                            [](unsigned char c) { return std::isspace(c); }),
             text.end());
  return text;
}

// §22.6 lets the conditional compilation directives stand anywhere in the
// source description (printed page 712), and §22.5.1 has a compiler directive
// written in a macro's text take effect when the macro is used (printed page
// 710), so an `ifdef or `ifndef inside a macro body is evaluated at each usage
// against the defines in force there. The preprocessor once copied the
// directive text through into the output, where the lexer reported the
// backtick under §5.2. UVM's m_uvm_field_op_begin macro is the shape of the
// first group of cases.
TEST(Preprocessor, ConditionalInFunctionMacroBodyAtLineHeadTakesIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`OPB(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("if(((3)&1)&&(!(3)))begin"),
            std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyAtLineHeadSkipsIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define LEGACY\n"
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`OPB(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("if((!(3)))begin"),
            std::string::npos);
  EXPECT_EQ(WithoutWhitespace(result).find("&1"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyMidLineTakesIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB2(F) (`ifndef LEGACY (F)&1 `else 0 `endif)\n"
      "y = `OPB2(2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("y=((2)&1);"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyMidLineTakesElse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"LEGACY", "1"}};
  auto result = Preprocess(
      "`define OPB2(F) (`ifndef LEGACY (F)&1 `else 0 `endif)\n"
      "y = `OPB2(2);\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("y=(0);"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInObjectMacroBodyMidLineTakesIfdef) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x = `M;\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInObjectMacroBodyMidLineTakesElse) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=0;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

// A body that opens with the conditional is text to evaluate, not a directive
// line to hand to the directive reader, when the usage heads a line.
TEST(Preprocessor, ConditionalOpeningObjectMacroBodyAtLineHead) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x =\n"
      "`M\n"
      ";\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

// The UVM shape proper: the macro holding the conditional is used inside
// another macro's body, so the conditional is met while that body is expanded.
TEST(Preprocessor, ConditionalInMacroBodyUsedByOuterMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`define FIELD(FLAG) begin `OPB(FLAG) end end\n"
      "`FIELD(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(
      WithoutWhitespace(result).find("beginif(((3)&1)&&(!(3)))beginendend"),
      std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

// The condition is read against the defines in force at the usage, not at the
// definition: a macro defined after the body is written still selects.
TEST(Preprocessor, ConditionalInMacroBodySeesDefineAfterDefinition) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int p = `M;\n"
      "`define A\n"
      "int q = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intp=0;"), std::string::npos);
  EXPECT_NE(WithoutWhitespace(result).find("intq=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}
