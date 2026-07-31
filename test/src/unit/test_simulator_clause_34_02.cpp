// §34.2 Overview -- the region a protected envelope delimits, end to end.
//
// An envelope marks a region of the source text for a transformation that
// happens before the source language processor analyses it. Whether the
// delimiting directives really do leave that region to be analysed is not
// visible in preprocessor state alone, so the designs here are driven through
// the whole preprocess -> parse -> elaborate -> lower -> simulate pipeline and
// observed through the value the enclosed code computes.
//
// The delimiters are written as the real `pragma directive syntax of §22.11,
// which is the dependency every rule in this subclause consumes: the envelope
// state is only ever reached by way of a directive the preprocessor tokenized
// and parsed for itself. The same run's preprocessor is read back afterwards,
// so the simulated design and the envelopes recorded over it come from one
// pass rather than from two separately built inputs.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_preprocess_and_get.h"
#include "preprocessor/protect_envelope.h"

namespace {

// Runs `src` through the full pipeline, keeping the Preprocessor so the
// envelopes it recorded on the way past can be read beside the simulated
// result.
struct EnvelopeSimRun {
  SimFixture f;
  Preprocessor pp{f.mgr, f.diag, {}};
  uint64_t result = 0;

  explicit EnvelopeSimRun(const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile("<test>", src), "result", pp);
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

// An encryption envelope wrapped around a module's procedural code: the pair
// of directives delimits the region and contributes nothing else, so the code
// between them elaborates and runs.
TEST(ProtectedEnvelopeRegionSimulation, EncryptionEnvelopeRegionStillRuns) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
}

// The other mode over the same design. Its region is protected code while the
// envelope is open, and the envelope is closed by the end of the file, so the
// design that ran is a complete one rather than a truncated region.
TEST(ProtectedEnvelopeRegionSimulation, DecryptionEnvelopeRegionStillRuns) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin_protected\n"
      "  initial result = 17;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 17U);
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kDecryption);
}

// An expression written before the opening directive describes the envelope
// rather than anything in the design, so it changes nothing about what the
// enclosed code computes while still being recorded against the envelope.
TEST(ProtectedEnvelopeRegionSimulation, EnvelopeKeywordLeavesTheDesignAlone) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin_protected\n"
      "  initial result = 7;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 7U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
}

// Nested envelopes over a running design: the inner pair closes first and the
// enclosing pair second, and the code they both surround is analysed once,
// not once per envelope.
TEST(ProtectedEnvelopeRegionSimulation, NestedEnvelopeRegionsStillRun) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "  initial result = 9;\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 9U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].mode,
            EnvelopeMode::kDecryption);
}

// The same design as the test above, with the describing expression and the
// opening delimiter written into one directive instead of two. Distributing
// the expressions differently is not allowed to change the outcome, so the
// keyword takes the same role, the envelope covers the same code, and the code
// computes the same value.
TEST(ProtectedEnvelopeRegionSimulation, OneDirectiveCarriesBothExpressions) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect data_method = \"aes128-cbc\", begin_protected\n"
      "  initial result = 7;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 7U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 3U);
}

}  // namespace
