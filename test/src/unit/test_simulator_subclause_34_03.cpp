// §34.3 Processing protected envelopes -- what the compilation step reads.
//
// Envelope decryption is defined by what it hands on: the cleartext of each
// decryption envelope, for the compilation step that follows. Whether the
// cleartext really does reach that step is not visible in the preprocessor's
// own state, so the designs here are encrypted from real source, driven
// through the whole preprocess -> parse -> elaborate -> lower -> simulate
// pipeline, and read through the value the recovered code computes.
//
// The same runs carry the other half of the pair. A design only reaches the
// simulator if envelope encryption left it recoverable, and it only reaches it
// intact if that process applied no interpretation of its own to the text it
// was encrypting.
//
// Every envelope is written as the real `pragma directive syntax of §22.11,
// and every design is a real module, so nothing here is assembled from an
// intermediate the pipeline would not have produced for itself.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "preprocessor/protect_processing.h"

namespace {

// The key the design was encrypted under, and a key that is not it.
constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kStrangerKey = "not-the-authors-key";

// What a user who supplies `key` gives the tool.
PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

// Encrypts `src` under the author's key and runs the transformed text through
// the pipeline with `key` supplied for envelope decryption, keeping the value
// of `result` the run left behind. Every design below declares `result` with a
// value of its own outside the envelope, so a run whose protected code never
// arrived still elaborates and still answers -- with the value the design
// started at rather than the one the protected code computes.
struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  ProtectedDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

// The pair of processes end to end: a design is encrypted into a decryption
// envelope, the envelope is decrypted on the way into the compilation step,
// and the design the envelope stood for is what runs. The variable is declared
// outside the envelope and assigned inside it, so reaching this value also
// says that the lines around the envelope and the lines recovered from it were
// compiled as one text rather than two.
TEST(ProtectedEnvelopeProcessingSimulation, ProtectedDesignRunsWithTheKey) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The same design read with a key that is not the one it was encrypted under.
// No cleartext can be put back, so the protected code never reaches the
// compilation step and the design runs with the value it started at. The pair
// of runs is what makes the first one an observation of decryption rather than
// of code that was in the text all along.
TEST(ProtectedEnvelopeProcessingSimulation, ProtectedDesignStaysSealedWithout) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kStrangerKey);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 9,
      "34.3.2"));
  EXPECT_EQ(run.result, 1U);
}

// Every envelope the source text holds is decrypted, so a design split across
// two of them arrives whole. Each envelope carries one of the two declarations
// the computation needs, so a run that recovered only one of them would not
// elaborate at all, let alone reach this value.
TEST(ProtectedEnvelopeProcessingSimulation, EveryEnvelopeOfADesignArrives) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "`pragma protect begin\n"
      "  int scale = 6;\n"
      "`pragma protect end\n"
      "  initial result = addend * scale;\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// What decryption hands on is source text for the step that follows, and the
// encrypting half handed it across without reading it. A macro defined and
// used inside the region shows both halves at once: nothing expanded it on the
// way in, and the compilation step expanded it on the way out.
TEST(ProtectedEnvelopeProcessingSimulation, MacroInsideTheRegionExpandsAfter) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`define ANSWER 42\n"
      "  initial result = `ANSWER;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The other dependency these rules consume, written as its own source syntax
// and driven through the pipeline. Putting the compiler directives back to
// their defaults is a change to the preprocessor's directive state, and the
// obligation to decrypt is not part of that state: the envelopes on either
// side of the reset are both processed, and what the first one contributed
// survives for the second to compute with. A reset that swept the key or the
// envelopes away with the rest would leave the design at the value it started
// at instead.
TEST(ProtectedEnvelopeProcessingSimulation, ResettingDirectivesKeepsTheKey) {
  ProtectedDesignRun run(
      "`pragma protect begin\n"
      "`define ANSWER 42\n"
      "`pragma protect end\n"
      "`resetall\n"
      "`pragma protect begin\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = `ANSWER;\n"
      "endmodule\n"
      "`pragma protect end\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// An expression describing the envelope is written ahead of the delimiter and
// so is outside the region, whether it stands on a directive of its own or
// beside the delimiter on one line. Neither spelling says anything about the
// design the region holds, so the design that runs is the same one.
TEST(ProtectedEnvelopeProcessingSimulation, DescribingExpressionsChangeNone) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
