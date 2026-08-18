#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/standard_pragmas.h"

// §22.11.1 "Standard pragmas" states what the reset and resetall pragmas do:
// they restore the default values and state of the pragma_keywords belonging
// to the pragmas they affect, and those defaults are the values the tool
// defines before any SystemVerilog text has been processed. reset restores the
// state of every pragma_name written as one of its own pragma_keywords;
// resetall restores the state of every pragma_name the implementation
// recognises. The third standard pragma, protect, specifies protected
// envelopes and is Clause 34's.
//
// The state a reset here has to restore is the protect pragma's, since protect
// is the one pragma_name this implementation recognises (standard_pragmas.cpp).
// Its keyword values live on the preprocessor rather than in the text it
// produces, so the cases below keep the Preprocessor alive and read
// ProtectKeywords().ValueOf back off it.

using namespace delta;

namespace {

// Preprocesses `src` on a caller-owned Preprocessor, so the pragma keyword
// state the run leaves behind is still there to read.
std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                             Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Pragma_Reset_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Resetall_NoError) {
  PreprocFixture f;
  Preprocess("`pragma resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma reset my_pragma\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Pragma_Resetall_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma resetall\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Pragma_Reset_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess(
      "wire a;\n"
      "`pragma reset my_pragma\n"
      "wire b;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

TEST(Preprocessor, Pragma_Resetall_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess(
      "wire a;\n"
      "`pragma resetall\n"
      "wire b;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

// §22.11.1: a value a directive wrote against a pragma_keyword stands until
// something puts it back, so this is the control the reset cases below are read
// against. Without it a keyword scope that recorded nothing would satisfy every
// one of them.
TEST(StandardPragmas, KeywordValueStandsWhenNothingResetsIt) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`pragma protect author=\"ada\"\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  ProtectKeywordValue author = pp.ProtectKeywords().ValueOf("author");
  EXPECT_FALSE(author.defaulted);
  EXPECT_EQ(author.value, "ada");
}

// §22.11.1: the reset pragma restores the default values and state of the
// pragma_keywords of the pragma its own pragma_keyword names. The protect
// keyword written before it is back at its default afterwards, which is the
// value it had before any text was processed.
TEST(StandardPragmas, ResetRestoresTheNamedPragmasKeywordDefaults) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset protect\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf("author").defaulted);
}

// §22.11.1: resetall restores the state of every pragma_name the
// implementation recognises, so it reaches the protect pragma without naming
// it. A resetall that restored only the pragmas a directive had named would
// leave this keyword where it was.
TEST(StandardPragmas, ResetallRestoresEveryRecognizedPragma) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf("author").defaulted);
}

// §22.11.1: reset restores the pragmas its pragma_keywords name and no others.
// §22.11 leaves the interpretation of the source text alone for a pragma_name
// the implementation does not recognise, so naming one restores nothing — an
// implementation reading any reset as a resetall clears the keyword here.
TEST(StandardPragmas, ResetNamingAnUnrecognizedPragmaRestoresNothing) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset my_pragma\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "ada");
}

// §22.11.1: a reset with no pragma_keyword at all names no pragma, so it
// restores nothing. This is the boundary of the rule above: what a reset acts
// on is what it names, and naming nothing is not naming everything.
TEST(StandardPragmas, ResetNamingNoPragmaRestoresNothing) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "ada");
}

// §22.11.1: the default a reset restores is the value the tool defines before
// any SystemVerilog text has been processed, so a keyword written again after
// a reset takes effect exactly as it did the first time. A reset that left the
// keyword unwritable, or that recorded itself as a value, would not.
TEST(StandardPragmas, KeywordWrittenAfterAResetTakesEffectAgain) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma resetall\n"
      "`pragma protect author=\"grace\"\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "grace");
}

// §22.11.1: the pragma_names resetall restores are the ones the implementation
// recognises. protect is the one this implementation carries keyword state for,
// and the two standard reset pragmas hold none of their own, so neither is a
// pragma either of them restores.
TEST(StandardPragmas, RecognizedPragmaNamesAreWhatResetallReaches) {
  EXPECT_TRUE(IsRecognizedPragmaName("protect"));
  EXPECT_FALSE(IsRecognizedPragmaName("my_pragma"));
  EXPECT_FALSE(IsRecognizedPragmaName(kResetPragmaName));
  EXPECT_FALSE(IsRecognizedPragmaName(kResetallPragmaName));
}

}  // namespace
