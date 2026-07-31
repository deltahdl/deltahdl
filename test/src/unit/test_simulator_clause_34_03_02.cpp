// §34.3.2 Decryption -- what the replacement hands the compilation step.
//
// The subclause's rules are all transformations of one source text into
// another, and the preprocessor file beside this one is where each of them is
// observed as text. What that file cannot settle is whether the text a
// replacement leaves behind is still a design the rest of the tool can read.
//
// The two rules about the recovered text make that a real question. A macro
// usage recovered out of a data_block has to be substituted once the block is
// opened, and an envelope recovered out of one has to be recognized and
// replaced in its turn: in both cases the construct reaches the front end only
// because a step ahead of it put it into the source, so a replacement that
// stitched the recovered text in a line short, a directive out of place or a
// macro left unexpanded would produce something that reads as text and fails
// as source.
//
// Each design below is therefore real, encrypted from an envelope its author
// specified and driven through the whole preprocess -> parse -> elaborate ->
// lower -> simulate pipeline. Each declares `result` outside every envelope
// and assigns it inside the innermost one, so a run whose recovered design
// never arrived still elaborates and answers -- with the value the design
// started at rather than the one the protected code computes.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "helpers_preprocess_and_get.h"
#include "preprocessor/protect_processing.h"

namespace {

// The key the author encrypted under, and a key that is not it.
constexpr std::string_view kExchangeKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

// What a user who supplies `key` gives the tool.
PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

// A whole decryption envelope standing for `body`, formed by putting `body`
// through the encrypting half under the author's key. The rules act on what a
// data_block records, so every envelope here records text that was really
// encrypted rather than a string arranged to look as though it had been.
std::string EnvelopeOf(const std::string& body) {
  std::string region = "`pragma protect begin\n";
  region += body;
  region += "`pragma protect end\n";
  return EncryptEnvelopes(region, kExchangeKey);
}

// Runs `src`, which already carries its envelopes, through the pipeline with
// `key` supplied for reading them back, keeping the value of `result` the run
// left behind.
struct RecoveredDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  RecoveredDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)) {
    auto fid = f.mgr.AddFile("<test>", src);
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

// A macro usage sealed in a data_block, substituted once the block is opened.
// The design the front end elaborates is the one that substitution produced: a
// usage carried through unexpanded would reach the lexer as a directive the
// parser has no place for, and a substitution arriving at the wrong text would
// answer with some other number than this one.
TEST(EnvelopeDecryptionSimulation, AMacroInARecoveredDesignReachesTheRun) {
  std::string src = "`define ANSWER 42\n";
  src += "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf("  initial result = `ANSWER;\n");
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// An envelope sealed inside another envelope's block, carrying the design. The
// outer replacement puts the enclosed envelope into the source and its own
// replacement puts the design there, so the module the front end elaborates is
// the one both replacements built.
TEST(EnvelopeDecryptionSimulation, ADesignInAnEnclosedEnvelopeReachesTheRun) {
  std::string sealed = EnvelopeOf("  initial result = 42;\n");
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(sealed);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The same arrangement read with a key that is not the author's. The outer
// block never opens, so the enclosed envelope is never put into the source and
// the design it carried never reaches the front end: the module elaborates
// with the value it started at. Read against the run above, this is what makes
// that one an observation of two replacements having happened rather than of
// code that was in the file all along.
TEST(EnvelopeDecryptionSimulation, AnEnclosedDesignStaysSealedUnderAnotherKey) {
  std::string sealed = EnvelopeOf("  initial result = 42;\n");
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(sealed);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kOtherKey);
  EXPECT_TRUE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 1U);
}

// The two rules meeting on a running design: the macro is sealed two
// envelopes deep, so it waits on the outer replacement to put the enclosed
// envelope into the file and on the enclosed one to put the usage there. What
// the front end elaborates is what both replacements and the substitution
// after them left behind.
TEST(EnvelopeDecryptionSimulation, AMacroSealedTwoEnvelopesDeepReachesTheRun) {
  std::string sealed = EnvelopeOf("  initial result = `ANSWER;\n");
  std::string body = "`define ANSWER 42\n";
  body += sealed;
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(body);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The envelope sealing a whole design element rather than a piece of one,
// which is how protected IP is usually delivered. No part of the module is in
// the file until the replacement puts it there, so the declaration the parser
// and the elaborator work from arrived entirely out of a data_block.
TEST(EnvelopeDecryptionSimulation, AWholeSealedModuleReachesTheRun) {
  std::string body = "module t;\n";
  body += "  int result = 42;\n";
  body += "endmodule\n";
  RecoveredDesignRun run(EnvelopeOf(body), kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The envelope an IP author specifies rather than one this file composed, with
// the pragma expressions of §22.11 written in their string-valued form on the
// directive that opens it. Those expressions describe the envelope the
// replacement is read according to, and they have to come back as directives:
// one carried into the recovered text as design source would reach the lexer
// and the run would not get as far as a value.
TEST(EnvelopeDecryptionSimulation, AStringSpecifiedEnvelopeDeliversItsDesign) {
  std::string authored = "module t;\n";
  authored += "  int result = 7;\n";
  authored += "`pragma protect author=\"Widget Works\"\n";
  authored += "`pragma protect data_keyowner=\"Widget Works\", begin\n";
  authored += "  initial result = 99;\n";
  authored += "`pragma protect end\n";
  authored += "endmodule\n";
  std::string src = EncryptEnvelopes(authored, kExchangeKey);
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 99U);
}

// The other value form §22.11 gives a pragma expression: a parenthesized list
// of further expressions rather than a single string. The whole of it has to
// survive as one value on the directive delimiting the envelope -- a reading
// that stopped at a comma inside the parentheses would leave a directive the
// pragma grammar rejects, and the block behind it would never be reached.
TEST(EnvelopeDecryptionSimulation, AListSpecifiedEnvelopeDeliversItsDesign) {
  std::string authored = "module t;\n";
  authored += "  int result = 7;\n";
  authored += "`pragma protect decrypt_license=(library=\"dec.so\", ";
  authored += "entry=\"check\", feature=\"core\"), begin\n";
  authored += "  initial result = 99;\n";
  authored += "`pragma protect end\n";
  authored += "endmodule\n";
  std::string src = EncryptEnvelopes(authored, kExchangeKey);
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 99U);
}

}  // namespace
