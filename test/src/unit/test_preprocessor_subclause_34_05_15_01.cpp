// §34.5.15.1 Syntax, for the protect pragma keyword that carries an encrypted
// region's data. The syntax block defines the keyword as the bare word
// `data_block`, with no pragma_value written against it.
//
// What the spelling settles is where the block stands. §34.5.15.2 has the
// expression indicate "that a data block begins on the next line in the file",
// so the word standing alone is what speaks for the line beneath the directive:
// that line is the block rather than text of the design, and a tool that wrote
// the block against the keyword instead produces an envelope no reading of this
// subclause opens. That divergence was issue #3272, and the cases below are
// what hold the two halves to the one spelling.
//
// Protect pragmas are processed at the preprocessor stage, where the generic
// `pragma` handler recognizes the keyword and consumes the directive line.
// §34.5.15.2's remaining two sentences -- what the encrypting half writes and
// what the decrypting half reverses -- are covered in
// test_preprocessor_subclause_34_05_15_02.cpp, and §34.5.15's condition on
// where a block may stand in an input file in
// test_preprocessor_subclause_34_05_15.cpp.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// A reading of a source text with nothing configured, which is the state a
// tool reading protected source starts in: no key is supplied, so a block that
// is announced is one nothing opens.
struct ProtectDataBlockSyntaxTest : ::testing::Test {
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

// The bare `data_block` keyword is accepted and the directive line is
// stripped. Nothing encloses it here, so the word describes no protected
// region and there is nothing for it to be the block of.
TEST_F(ProtectDataBlockSyntaxTest, PragmaProtectDataBlockConsumed) {
  auto result = Preprocess("`pragma protect data_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the data_block directive line is removed; neighboring source text
// survives, confirming it is the data_block keyword line that the pragma
// path consumes.
//
// The line beneath it survives too, and that is the half of this the standard
// decides. §34.5.15.2 has the expression speak for the next line only where a
// previously generated envelope encloses it, so with none open here the word
// takes nothing with it and `endmodule` reaches the step after the
// preprocessor as design text.
TEST_F(ProtectDataBlockSyntaxTest,
       DataBlockDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.15.1 defines is the spelling:
// the keyword and nothing else, with §34.5.15.2 putting the block on the line
// beneath it. The cases below are written on that spelling.

// The design one region below seals, and the key it is sealed under. Nothing
// of the design survives the alphabet a block is written in, so finding it in
// what a reading produced is finding a block that opened.
constexpr std::string_view kOpenedDesign =
    "module recovered_design_m; endmodule\n";
constexpr std::string_view kSyntaxRegionKey = "one-key-for-the-syntax-case";

// Characters the coding scheme in effect does write, standing for bytes no
// encryption ever produced. A line of them is a line a reading can take as a
// block and cannot open, which is what makes it tell a line that was taken
// from a line that was passed on.
constexpr std::string_view kUnopenableBlock = "AAAA";

// A decryption envelope as another tool wrote it, holding `described`.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// §34.5.15.1: the keyword standing alone is the spelling, and §34.5.15.2 has it
// indicate that a data block begins on the next line in the file. Inside an
// envelope the directive is consumed and so is the line beneath it, that line
// being the block rather than text of the design.
//
// The block here is one no key opens, which is what makes the line's absence
// from the output mean it was taken. A reading that never announced anything
// would leave those characters standing as design text and report nothing at
// all, so the report and the absence are the two halves of one claim.
TEST(ProtectDataBlockSyntax, TheKeywordAloneTakesTheLineBeneathItAsTheBlock) {
  PreprocFixture f;
  std::string described = "`pragma protect data_block\n";
  described.append(kUnopenableBlock).append("\n");
  std::string read = Preprocess(ForeignEnvelope(described), f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 3,
      "34.3.2"));
  EXPECT_EQ(read.find(kUnopenableBlock), std::string::npos) << read;
  EXPECT_EQ(read.find("data_block"), std::string::npos) << read;
}

// The keyword written as one expression of §22.11's comma-separated list, with
// a second expression after it. The keyword ends at the comma, so the
// expression past it takes effect and the keyword still speaks for the line
// beneath the directive rather than for the rest of the directive's own text.
//
// One report names both halves. §34.5.11.2 has the data_method state the
// algorithm a block is to be decrypted with, and this implementation provides
// one cipher that des-cbc is not; that value is read only once a line has been
// taken as the block. So a reading that swallowed the comma into a pragma_value
// of data_block would report nothing here: no block would have been announced,
// and des-cbc would never have been in effect over one.
TEST(ProtectDataBlockSyntax, TheKeywordAloneEndsAtTheComma) {
  PreprocFixture f;
  std::string described =
      "`pragma protect data_block, data_method=\"des-cbc\"\n";
  described.append(kUnopenableBlock).append("\n");
  Preprocess(ForeignEnvelope(described), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data block states an encryption algorithm this "
                            "implementation does not provide: des-cbc",
                            3, "34.5.11.2"));
}

// The spelling driven from end to end, which is the case issue #3272 exists
// for. The envelope is written out here as §34.5.15.1 defines it -- the keyword
// alone on its directive -- with the block on §34.5.15.2's next line in the
// file, and a reading holding the region's key hands the design to the step
// after the preprocessor.
//
// The block is produced by EncryptProtectedRegion
// (src/preprocessor/protect_processing.h) rather than written out, because what
// a block holds depends on the key the region was sealed under. What is written
// out is where the keyword and the block stand relative to each other, which is
// the thing under test: a reading that expected the block against the keyword
// takes this line for design text, and the design never arrives.
TEST(ProtectDataBlockSyntax, TheBlockBeneathTheKeywordAloneIsRecovered) {
  std::string envelope = "`pragma protect begin_protected\n";
  envelope.append("`pragma protect data_block\n");
  envelope.append(EncryptProtectedRegion(kOpenedDesign, kSyntaxRegionKey));
  envelope.append("\n`pragma protect end_protected\n");

  PreprocFixture f;
  PreprocConfig config;
  config.protect_key = std::string(kSyntaxRegionKey);
  std::string read = Preprocess(envelope, f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kOpenedDesign), std::string::npos) << read;
  EXPECT_EQ(read.find("data_block"), std::string::npos) << read;
}

}  // namespace
