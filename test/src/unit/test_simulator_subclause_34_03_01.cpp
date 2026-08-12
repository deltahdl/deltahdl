// §34.3.1 Encryption -- an envelope the author specified, end to end.
//
// The subclause's rules are all transformations of one source text into
// another, and the preprocessor file beside this one is where each of them is
// observed. What that file cannot settle is whether the text the
// transformation produces is still something the rest of the tool can read.
//
// The rule at issue is the one that forms a decryption envelope by
// transforming the expressions specifying the encryption envelope. Those
// expressions are the author's own, written in the directive syntax of §22.11
// under the reserved names of §34.4 and carrying the value forms §34.5 gives
// them, and the transformation writes them out again onto the envelope it
// produces. So they are read twice: once when the source text is transformed,
// and once when the produced envelope is read back. A carry that mangled a
// value, dropped a quote, or left the expressions in the text as design source
// instead of directives would survive a string comparison and fail here.
//
// Every design below is therefore real source, encrypted from an envelope the
// author specified, and driven through the whole preprocess -> parse ->
// elaborate -> lower -> simulate pipeline. Each declares `result` outside the
// envelope and assigns it inside, so a run whose protected code never arrived
// still elaborates and answers -- with the value the design started at rather
// than the one the protected code computes.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "preprocessor/protect_processing.h"

namespace {

// The key the author specified for encryption, and a key that is not it.
constexpr std::string_view kExchangeKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

// What a user who supplies `key` gives the tool.
PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

// Encrypts `src` under the author's exchange key and runs the transformed text
// through the pipeline with `key` supplied for reading it back, keeping the
// value of `result` the run left behind.
struct SpecifiedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  SpecifiedDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kExchangeKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

// The dependency the rule consumes at its plainest: the directive syntax of
// §22.11 carrying reserved names of §34.4 with string values, written beside
// the delimiter and on a directive of its own. Both spellings specify the
// envelope, both are carried onto the envelope produced, and the design that
// arrives is the one the author wrote. Expressions that came back as anything
// other than directives would reach the lexer as design source and the run
// would not get this far.
TEST(EnvelopeEncryptionSimulation, ASpecifiedEnvelopeDeliversItsDesign) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The other value form §34.5 gives a keyword: a parenthesized list of further
// expressions rather than a single string. It is written beside the delimiter,
// where the whole of it has to be carried across as one value -- a carry that
// stopped at the comma inside the parentheses would leave a directive the
// pragma grammar rejects, and the design would not reach this value.
TEST(EnvelopeEncryptionSimulation, AParenthesizedValueIsCarriedWhole) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "feature=\"runIt\"), begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The same design read with a key that is not the one the author specified.
// The body was encrypted under the exchange key, so nothing opens it, the
// protected code never reaches the compilation step, and the design runs with
// the value it started at. The pair of runs is what makes the first one an
// observation of an envelope having been formed rather than of code that was
// in the text all along.
TEST(EnvelopeEncryptionSimulation, ASpecifiedEnvelopeStaysSealedUnderAnother) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kOtherKey);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 9,
      "34.3.2"));
  EXPECT_EQ(run.result, 1U);
}

}  // namespace
