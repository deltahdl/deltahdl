#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// Exercises the syntax of the `key_block` protect pragma keyword (§34.5.27.1).
// The syntax block defines the keyword as the bare word `key_block` with no
// same-line argument (the encoded key block content, if any, appears on a
// following line per the Description). Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// and consumes the directive line.
struct ProtectKeyBlockSyntaxTest : ::testing::Test {
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

// Only the key_block directive line is removed; neighboring source text
// survives, confirming it is the key_block keyword line that the pragma path
// consumes.
TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect key_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as encoded key block
// content belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_block\nENCODEDKEYBLOCKDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("ENCODEDKEYBLOCKDATA"), std::string::npos);
}

// The bare keyword has no same-line argument grammar (unlike sibling protect
// keywords that take `= <string>` or a parenthesized list), so a token
// juxtaposed after it cannot be its argument. What it would have to be instead
// is a second pragma_expression, and Syntax 22-8 separates those with a comma:
//
//   pragma ::=
//     `pragma pragma_name [ pragma_expression { , pragma_expression } ]
//
// key_block on its own is already a complete pragma_expression, so an
// identifier following it with nothing but white space between is outside the
// grammar and is diagnosed. Reporting it is what shows the argument was never
// absorbed -- a key_block that had acquired same-line argument parsing would
// take TRAILINGTOKEN silently and there would be nothing to diagnose. This is
// the same-line counterpart to the next-line case above.
//
// The malformed expression does not cost the surrounding source: the directive
// line is still consumed whole, so the stray token does not reach the output
// and the neighboring lines pass through.
TEST_F(ProtectKeyBlockSyntaxTest, KeyBlockHasNoSameLineArgument) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_block TRAILINGTOKEN\nendmodule\n");
  // Syntax 22-8 separates two expressions with a comma, so the stray token is
  // what §22.11 turns away rather than anything this keyword states.
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 2,
                            "22.11"));
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("TRAILINGTOKEN"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.27.1 defines is the
// spelling: the keyword stands alone, with nothing written against it, and the
// block it announces begins on the line beneath. So the question a case asks of
// this keyword is what became of that line.
//
// There is no value to read back, a key block being neither a name nor a
// designation. What the line being taken leaves behind is a key: §34.5.27 has
// the recovered text read for the expressions that open the region's data, so a
// reading that took the line opens the data block and the design comes back,
// and a reading that did not leaves the block shut. That is what the cases
// below ask, and they ask it of an envelope this tool produced, whose
// announcement is then rewritten in the spellings §34.5.27.1 does not define.
//
// Where a key block may stand, and what several of them must agree about, is
// §34.5.27.2's and is stated in test_preprocessor_subclause_34_05_27.cpp.

// The entity a region designates to open its keys, the name picking that key
// out, and the key itself.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "meridian-trust-wrapping-key";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends the region to a key block rather than to a key of its
// author's.
constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";

// The announcement §34.5.27.1 defines, as the tool writes it.
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The envelope this tool writes for a region whose keys travel in a block of
// its own, checked on the way out to be one: the design is gone and the
// announcement is there to be rewritten.
std::string EnvelopeWithAKeyBlock() {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("key_keyowner", kEntity));
  region.append(Writes("key_keyname", kKeyName));
  region.append(Writes("data_keyname", kDataKeyName));
  region.append(kEncodingSealedDesign);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, kKeyBlockLine)) << envelope;
  return envelope;
}

// That envelope with the announcement the tool made spelled `announced`
// instead. `announced` is one line, so every line of the envelope keeps the
// number it had.
std::string EnvelopeAnnouncing(std::string_view announced) {
  std::string envelope = EnvelopeWithAKeyBlock();
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  std::string rewritten = envelope;
  rewritten.replace(at, kKeyBlockLine.size(), announced);
  return rewritten;
}

// The line the announcement spoke for, which is the encoded block beneath it.
std::string BlockLineOf(const std::string& envelope) {
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  size_t from = at + kKeyBlockLine.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

// §34.5.27.1: the expression is the keyword and nothing else, and what it
// states is that the block begins on the line beneath it. A reading that took
// that line has the keys the block carried, so the data block opens and the
// design the region sealed comes back.
TEST(ProtectKeyBlockSyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  ReadSource run(EnvelopeWithAKeyBlock(),
                 ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// The other half of speaking for a line: the line spoken for is key material
// rather than text of the design, so it does not come back out.
TEST(ProtectKeyBlockSyntax, TheLineTheKeywordSpokeForIsNotDesignText) {
  std::string envelope = EnvelopeWithAKeyBlock();
  ReadSource run(envelope, ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, BlockLineOf(envelope))) << run.text;
}

// The negative that makes the spelling matter: the same name with a
// pragma_value written against it is the expression written in a spelling
// §34.5.27.1 does not define, so it speaks for no line. The block is never
// opened, the keys it carried are never reached, and the design stays sealed.
TEST(ProtectKeyBlockSyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string envelope =
      EnvelopeAnnouncing("`pragma protect key_block=\"a-value-of-its-own\"\n");
  ReadSource run(envelope, ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(Holds(run.text, BlockLineOf(EnvelopeWithAKeyBlock())))
      << run.text;
}

// §22.5.1 gives a pragma_value a parenthesized spelling as well, and it is a
// value against the keyword just as the single one is. §34.5.27.1 writes
// nothing against the keyword at all, so this speaks for no line either.
TEST(ProtectKeyBlockSyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  ReadSource run(
      EnvelopeAnnouncing("`pragma protect key_block=(bytes=\"20\")\n"),
      ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// §34.5.27.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so the line beneath it is announced by
// nothing.
TEST(ProtectKeyBlockSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadSource run(EnvelopeAnnouncing("`pragma protect key_block_of_theirs\n"),
                 ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.27.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectKeyBlockSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_block =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// Where the spelling stops. §34.5.27.2 makes a key block found in an input file
// outside every previously generated protected block an error, and that is a
// rule about the keyword being written rather than about what it carries: the
// spelling §34.5.27.1 defines decides what the keyword announces and not
// whether it was found. test_preprocessor_subclause_34_05_27.cpp states the
// rule for the name carrying a value, and the bare spelling is reported the
// same way.
TEST(ProtectKeyBlockSyntax, TheSpellingDecidesWhatIsAnnouncedNotWhatIsFound) {
  std::string src = "module m;\n";
  src.append(kKeyBlockLine).append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

}  // namespace
