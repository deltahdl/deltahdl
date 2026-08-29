// §34.5.6.1 Syntax, for the protect pragma keyword that carries whatever
// further documentation a design offers about its author.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression: the keyword is written with an '=' and a
// string against it. A string is one written thing, so the parenthesized
// spelling §22.5.1 also gives a pragma_value -- a list of further expressions
// -- is not the value this keyword is defined with.
//
// The cases below are of two kinds. The first three ask whether the directive
// carrying the expression is consumed, which is what the preprocessor does with
// every protect pragma directive it reads. The last two ask what the keyword
// records, which is what the spelling of the value decides: a list records
// nothing, so documentation an earlier directive wrote still stands and a
// keyword no directive wrote stands at its default. #3269 is the defect those
// two close, the parentheses and the subkeywords of a list having been recorded
// as the documentation itself.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectedTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

// Syntax 34.5.6.1: the author_info protect pragma expression takes the form
// `author_info = <string>`. The preprocessor accepts and consumes it.
TEST_F(ProtectedTest, AuthorInfoStringExpressionConsumed) {
  auto result =
      Preprocess("`pragma protect author_info = \"Acme IP Group, Rev 3\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

// The author_info expression carries arbitrary additional author text in its
// string operand without disturbing the surrounding design source.
//
// The envelope carries no data block. §34.5.15.1 spells that expression as the
// keyword standing alone and §34.5.15.2 has it indicate that a data block
// begins on the next line in the file, so a data_block written here would take
// the line beneath it as the block's characters and report that line for not
// being written in the coding scheme in effect (issue #3272). A block is no
// part of what this case claims, which is that the expression above it is
// consumed and the design text on either side of the envelope is not.
TEST_F(ProtectedTest, AuthorInfoInEnvelopePreservesSource) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect author_info = \"contact: ip-support@example.com\"\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);

  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// The <string> operand of `author_info = <string>` is still a well-formed
// expression at its degenerate boundary: an empty string. The directive line is
// accepted without error and consumed just like a non-empty operand.
TEST_F(ProtectedTest, AuthorInfoEmptyStringOperandConsumed) {
  auto result = Preprocess("`pragma protect author_info = \"\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

// A reading of `src` with the preprocessor kept alive after it. What an
// author_info expression leaves behind is a value in effect at the point the
// reading has reached rather than anything the produced text shows, so it is
// read off the preprocessor once the whole text has passed through.
struct DocumentedAuthor {
  SourceManager files;
  DiagEngine reports{files};
  Preprocessor reading{files, reports, PreprocConfig{}};
  std::string produced;

  explicit DocumentedAuthor(const std::string& src) {
    produced = reading.Preprocess(files.AddFile("<test>", src));
  }

  ProtectKeywordValue Documented() const {
    return reading.ProtectKeywords().ValueOf(kAuthorInfoKeyword);
  }
};

// One protect pragma directive with `spelled` standing against the keyword
// exactly as given, so the spelling of the value is what a case varies.
std::string Documents(std::string_view spelled) {
  std::string directive = "`pragma protect author_info=";
  directive.append(spelled).append("\n");
  return directive;
}

// A list written against the keyword on a text whose earlier directive already
// documented the author. §34.5.6.1 defines the expression with a string, and
// §22.5.1 makes a parenthesized pragma_value a list of further expressions
// rather than one written thing, so the list documents nothing. Documenting
// nothing is not documenting the empty string, and the text the earlier
// directive wrote is what the keyword still records.
//
// Only that earlier directive tells the two apart. With the list standing
// alone there is no text for it to take away, so a reading that wiped the text
// and a reading that let it stand both end with nothing recorded. #3269 is the
// defect this closes: the subkeyword list was recorded as the documentation.
TEST(ProtectAuthorInfoSyntax,
     AListLeavesTheDocumentationAlreadyWrittenStanding) {
  std::string source = Documents("\"Acme IP Group, Rev 3\"");
  source += Documents("(team=\"Acme IP Group\", revision=\"3\")");
  DocumentedAuthor run(source);
  EXPECT_FALSE(run.reports.HasErrors());
  EXPECT_FALSE(run.Documented().defaulted);
  EXPECT_EQ(run.Documented().value, "Acme IP Group, Rev 3");
}

// The same list on a text no directive documented the author in. It documents
// nothing, so the keyword stands at the default ProtectKeywordScope::ValueOf in
// src/preprocessor/protect_keywords.cpp gives a keyword no directive wrote: the
// empty string, reported as defaulted.
//
// That is what makes the case above about the spelling of the value rather than
// about the text that happened to stand ahead of it.
TEST(ProtectAuthorInfoSyntax,
     AListWithNothingDocumentedBeforeItLeavesTheDefault) {
  DocumentedAuthor run(Documents("(team=\"Acme IP Group\", revision=\"3\")"));
  EXPECT_FALSE(run.reports.HasErrors());
  EXPECT_TRUE(run.Documented().defaulted);
  EXPECT_TRUE(run.Documented().value.empty());
}

}  // namespace
