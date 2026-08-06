// §34.5.2.2 Description -- what the expression that closes an encryption
// envelope leaves for the step that runs the design.
//
// The rule the subclause states as encryption input is settled by text that
// reaches the simulator rather than by text a tool writes out. The expression
// says where the region that is to be encrypted stops, so it divides one
// source text into a part sealed and a part carried across, and the design that
// runs is the two parts put back together as one. Nothing in the
// preprocessor's own state says whether that really happened: it is a property
// of the text that arrives, so the designs here are written as real modules,
// encrypted from real directive syntax, driven through the whole preprocess ->
// parse -> elaborate -> lower -> simulate pipeline, and read through the value
// the recovered design computes.
//
// Every design declares `result` with a value of its own outside every region,
// so a run that lost either half of the division still elaborates and still
// answers -- with the value the design started at rather than the one the two
// halves compute together.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "helpers_preprocess_and_get.h"
#include "preprocessor/protect_processing.h"

namespace {

// The key the designs below are sealed under and read back with.
constexpr std::string_view kAuthorKey = "acme-exchange-key";

// Encrypts `src` under the author's key and runs the transformed text through
// the pipeline with the same key supplied for reading the regions back, keeping
// the value of `result` the run left behind.
struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  explicit ProtectedDesignRun(const std::string& src)
      : pp(f.mgr, f.diag, ReadingKey()) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }

  // What the author who sealed these designs hands back to the tool reading
  // them. One key does both halves of the pair, so a design comes back only if
  // the same key that sealed it is supplied here.
  static PreprocConfig ReadingKey() {
    PreprocConfig config;
    config.protect_key = kAuthorKey;
    return config;
  }
};

// The point at which a region stops divides one design rather than selecting a
// design of its own. The declaration the computation reads stands ahead of the
// expression and the statement doing the computing stands after it, so reaching
// this value says the half that was sealed and the half that was carried across
// were compiled as one text.
TEST(ProtectEndDescriptionSimulation, TheTwoHalvesOfThePointAreOneDesign) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "  initial result = addend * 6;\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The same division read through a compiler directive, which is what makes the
// two halves one text rather than two texts that happen to be adjacent. The
// multiplier is defined inside the region and used after the expression closing
// it, so the run answers only if what the region held was put back where the
// region stood and was in effect for the text below it.
TEST(ProtectEndDescriptionSimulation, WhatTheRegionHeldIsInEffectAfterIt) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`define SCALE 6\n"
      "`pragma protect end\n"
      "  int addend = 7;\n"
      "  initial result = addend * `SCALE;\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// Each expression stops a region of its own, so one design may be divided more
// than once. The value depends on all three parts: the first region supplies
// what is multiplied, the cleartext between the regions supplies the
// multiplier, and the second region does the multiplying. A run that lost any
// one of them answers with the value the design started at.
TEST(ProtectEndDescriptionSimulation, ADesignDividedTwiceRunsAsOne) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "  int scale = 6;\n"
      "`pragma protect begin\n"
      "  initial result = addend * scale;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The construct this rule reads its hardest case against, built from the syntax
// that really produces it and driven end to end. A previously generated
// protected block is not written by hand here: it is a design this tool sealed
// on its own, delimited by the expression §34.5.4 defines, and it stands among
// the lines of a second design being sealed now.
//
// The value needs all three zones the closing expression leaves between them.
// What is multiplied comes out of the block that was sealed twice over, the
// multiplier out of the region sealed once around it, and the statement doing
// the multiplying stands after the word in the clear. A reading that stopped
// the outer region at anything the enclosed block wrote, rather than at the
// word written for it, would put one of the three somewhere the run cannot
// reach it, and the design would answer with the value it started at.
TEST(ProtectEndDescriptionSimulation, ADoublySealedDesignReturnsEveryZone) {
  std::string sealed = "`pragma protect begin\n";
  sealed.append("  int addend = 7;\n");
  sealed.append("`pragma protect end\n");
  std::string src = "module t;\n";
  src.append("  int result = 1;\n");
  src.append("`pragma protect begin\n");
  src.append(EncryptEnvelopes(sealed, kAuthorKey));
  src.append("  int scale = 6;\n");
  src.append("`pragma protect end\n");
  src.append("  initial result = addend * scale;\n");
  src.append("endmodule\n");
  ProtectedDesignRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
