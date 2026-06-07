#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, UndefPreviouslyDefinedMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, UndefinedMacroHasNoValue) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n"
      "int x = `FOO;\n",
      f);

  EXPECT_NE(result.find("`FOO"), std::string::npos);
}

TEST(Preprocessor, UndefUndefinedMacroNoError) {
  PreprocFixture f;
  Preprocess("`undef NEVER_DEFINED\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, UndefThenRedefine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define VAL 1\n"
      "`undef VAL\n"
      "`define VAL 2\n"
      "int x = `VAL;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('2'), std::string::npos);
}

TEST(Preprocessor, UndefInInactiveConditionalSkipped) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define KEEP 42\n"
      "`ifdef UNDEF_MACRO\n"
      "`undef KEEP\n"
      "`endif\n"
      "int x = `KEEP;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, UndefDoesNotAffectOtherMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 1\n"
      "`define B 2\n"
      "`undef A\n"
      "int x = `B;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('2'), std::string::npos);
}

// Syntax 22-4 accepts an escaped identifier as the `undef argument. The
// directive's name parser must take the escaped-name branch and remove the
// macro stored under that escaped key, just like a simple identifier.
TEST(Preprocessor, UndefEscapedIdentifierMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define \\M@CRO 7\n"
      "`undef \\M@CRO\n"
      "`ifdef \\M@CRO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}


