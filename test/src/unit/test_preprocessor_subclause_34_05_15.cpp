// §34.5.15, for the protect pragma keyword that carries an encrypted region's
// data, read on the side that produces one.
//
// §34.5.15.2 states one condition on an encrypting tool's input, and it is the
// whole of what this file covers:
//
//   It shall be an error if a data_block is found in an input file unless it
//   is contained within a previously generated begin_protected-end_protected
//   block, in which case it is ignored.
//
// What the rule costs an author is a design that leaves the tool unsealed with
// nothing said about it. A block written where no previously generated block
// encloses it is the block of no envelope -- there is nothing it could have
// come out of, and no key that could open it -- so a tool that passed over it
// in silence would copy those characters into its output as ordinary source
// text and hand back a file whose author believes it carries an encrypted
// model.
//
// The condition costs the report rather than the transformation. §34.5.15 says
// nothing about stopping, and the rest of the file is ordinary source, so the
// reading runs to the end of the input and the line is carried like any other.
// Each case below therefore names the report rather than asking whether the
// text came back.
//
// §34.5.15.1's syntax -- the keyword written as the bare word -- is covered in
// test_preprocessor_subclause_34_05_15_01.cpp, on the reading that consumes the
// directive. This file is about where a block may stand rather than how it is
// spelled, so it is the encrypting half of §34.3 that is driven here:
// src/preprocessor/protect_input_line.cpp decides whether a previously
// generated block contains a line, and reports the ones it does not.
//
// §34.5.3.1's and §34.5.4.1's words are what delimit a previously generated
// block, and §34.5.1.1's and §34.5.2.1's pair delimits a region to be
// encrypted. Both pairs appear below, because the rule turns on the first pair
// and not on the second: a block inside a region an author is about to seal is
// still a block no earlier envelope produced.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_protect_read.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

// A block written in the clear, as a tool reading a text would meet one. What
// it says is deliberately not a value any coding scheme writes, so nothing here
// turns on the characters being readable as a block: the rule is about where
// the expression stands.
constexpr std::string_view kBlockDirective =
    "`pragma protect data_block=\"NOTABLOCKOFANYENVELOPE\"\n";

// A second one, differing in what it carries so that a report naming one of
// them cannot be mistaken for a report naming the other.
constexpr std::string_view kSecondBlockDirective =
    "`pragma protect data_block=\"NORISTHISABLOCKOFANY\"\n";

// The design an author seals, which stands inside a region wherever one is
// written below. Nothing of it survives an encrypted block, so finding these
// characters in a produced text is finding a region that was not sealed.
constexpr std::string_view kEncodingSealedDesign = "  initial result = 42;\n";

// A previously generated protected block, delimited by the two words §34.5.3.1
// and §34.5.4.1 define, holding `inside`.
std::string SealedModel(std::string_view inside) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(inside);
  text.append("`pragma protect end_protected\n");
  return text;
}

// An encryption region, delimited by the two words §34.5.1.1 and §34.5.2.1
// define, holding `inside` and then the design.
std::string Region(std::string_view inside) {
  std::string text = "`pragma protect begin\n";
  text.append(inside).append(kEncodingSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: a block no previously generated block contains.
// ---------------------------------------------------------------------------

// The condition at its plainest: the expression standing in an input file with
// no previously generated block anywhere in the text. There is no envelope for
// it to be the block of, so it is reported, and the report stands on the line
// the author wrote it on.
TEST(ProtectDataBlockEncryptionInput, ABlockContainedByNothingIsReported) {
  std::string src = "module m;\n";
  src.append(kBlockDirective);
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 2,
                            "34.5.15"));
}

// What the condition costs is the report rather than the transformation. The
// text around the expression is ordinary source, so the reading runs to the end
// of it and hands back what it was given character for character -- which is
// what tells a report apart from a refusal to do the work.
TEST(ProtectDataBlockEncryptionInput, TheReportedTextIsHandedBackUnchanged) {
  std::string src = "module m;\n";
  src.append(kBlockDirective);
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.text, src);
}

// The rule is stated of a block rather than of the first one, so a text writing
// two of them outside every previously generated block has written two blocks
// of no envelope. Each is reported where it stands: one report for the pair
// would leave an author who fixed the line they were shown believing the file
// was clean.
TEST(ProtectDataBlockEncryptionInput, EachBlockContainedByNothingIsReported) {
  std::string src(kBlockDirective);
  src.append(kSecondBlockDirective);
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 1,
                            "34.5.15"));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 2,
                            "34.5.15"));
}

// The region an author is about to seal is not what contains a block for the
// purpose of this rule. §34.5.15 names the previously generated
// begin_protected-end_protected block and nothing else, so a block written
// between the words that delimit a region to encrypt has still come out of no
// envelope, and it is reported exactly as one written in the open is.
//
// This is the input the rule would be silently wrong about were the two pairs
// of delimiters read as one thing: the region's own text goes into a block of
// its own, so a reading that treated the enclosure as enough would produce an
// envelope and say nothing.
TEST(ProtectDataBlockEncryptionInput, ABlockInsideARegionToSealIsReportedToo) {
  std::string src = Region(kBlockDirective);
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 2,
                            "34.5.15"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: a block a previously generated block does contain.
// ---------------------------------------------------------------------------

// The other half of the same sentence, and the input every case above is read
// against: the same expression, written inside the pair of words a previously
// generated block is delimited by. It belongs to the envelope that block is,
// so §34.5.15 has it ignored rather than objected to and the run reports
// nothing at all.
TEST(ProtectDataBlockEncryptionInput, ABlockASealedModelContainsIsIgnored) {
  EncryptionRun run(SealedModel(kBlockDirective));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The arrangement an author sealing an already-protected model writes: the
// previously generated block stands inside the region being encrypted, and its
// own block is contained by it. Nothing is reported, and the model travels into
// the enclosing envelope as the bytes it is written with rather than staying
// readable in the output.
TEST(ProtectDataBlockEncryptionInput, ASealedModelInsideARegionCarriesItsOwn) {
  EncryptionRun run(Region(SealedModel(kBlockDirective)));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, "NOTABLOCKOFANYENVELOPE"));
}

// Where the containment stops. The word §34.5.4.1 defines ends the previously
// generated block, so a block written past it is contained by nothing again --
// and a reading that never came back out of the model would pass over this one
// in the silence the case above is entitled to.
TEST(ProtectDataBlockEncryptionInput, ABlockPastTheSealedModelIsReported) {
  std::string src(SealedModel(kBlockDirective));
  src.append(kSecondBlockDirective);
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, "NORISTHISABLOCKOFANY"), "34.5.15"));
}

}  // namespace
