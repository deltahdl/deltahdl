// §34.5.1.2 Description -- what the expression that opens an encryption
// envelope leaves for the step that runs the design.
//
// Two of the subclause's rules are settled by text that reaches the simulator
// rather than by text a tool writes out. The expression marks the point at
// which encryption begins, so it divides one source text into a part carried
// across and a part sealed, and the design that runs is the two parts put back
// together as one. And everything occurring between that expression and the
// closing one that answers it is encrypted into the block, comments, compiler
// directives and further protect pragmas included, so nothing a region held is
// left behind by the sealing of it.
//
// Neither is visible in the preprocessor's own state: whether the sealed half
// really is compiled with the half around it is a property of the text that
// arrives, so the designs here are written as real modules, encrypted from real
// directive syntax, driven through the whole preprocess -> parse -> elaborate
// -> lower -> simulate pipeline, and read through the value the recovered
// design computes. A design missing any line of what a region held answers with
// the value it started at instead.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "helpers_preprocess_and_get.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace {

// The key the designs below are sealed under and read back with.
constexpr std::string_view kAuthorKey = "acme-exchange-key";

// The entity that provided the key a region's own keys travel under, and one of
// its keys, for the arrangement §34.5.27 defines.
constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

// What a user who supplies `key` gives the tool.
PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

// Encrypts `src` under the author's key and runs the transformed text through
// the pipeline with the same key supplied for reading the regions back, keeping
// the value of `result` the run left behind. Every design declares `result`
// with a value of its own outside every region, so a run whose sealed lines
// never arrived still elaborates and still answers -- with the value the design
// started at rather than the one the sealed lines compute.
struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  explicit ProtectedDesignRun(const std::string& src)
      : pp(f.mgr, f.diag, KeyConfig(kAuthorKey)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

// The same run, for the arrangement §34.5.27 defines. A region designating a
// key of an entity gets a key of the tool's own making for its data, and that
// made key travels in a key block encrypted under the designated one, so the
// design reaches the simulator only if the block was written where a reader
// meets it before the data block it opens. Both halves are handed the same list
// of keys, which is what an author and a reader holding one entity's keys each
// have.
struct KeyBlockDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  KeyBlockDesignRun(const std::string& src, const ProtectKeyList& keys)
      : pp(f.mgr, f.diag, ListConfig(keys)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, "", keys));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }

  static PreprocConfig ListConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }
};

// The point at which encryption begins divides one design rather than selecting
// a design of its own. The declaration the computation reads stands ahead of
// the expression and the statement doing the computing stands after it, so
// reaching this value says the half that was sealed and the half that was
// carried across were compiled as one text.
TEST(ProtectBeginDescriptionSimulation, TheTwoHalvesOfThePointAreOneDesign) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "  int addend = 7;\n"
      "`pragma protect begin\n"
      "  initial result = addend * 6;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// Every kind of line a region can hold, sealed together and put back together.
// A comment, a compiler directive, a declaration and a statement stand between
// the delimiters, and the value depends on all four of them: the directive
// supplies the multiplier, the declaration supplies what is multiplied, and the
// statement is what does the multiplying. A region that had dropped any of them
// on the way into its block answers with the value the design started at.
TEST(ProtectBeginDescriptionSimulation, EveryLineBetweenTheDelimitersReturns) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  // the multiplier this design was written around\n"
      "`define SCALE 6\n"
      "  int addend = 7;\n"
      "  initial result = addend * `SCALE;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The arrangement the subclause permits inside an open region: a model sealed
// already, standing among the lines of a model being sealed now. Its lines are
// a byte stream to the encryption enclosing them, so the design reaches the
// simulator only if the outer sealing preserved the inner envelope exactly and
// the reading then opened both of them in turn.
TEST(ProtectBeginDescriptionSimulation, ADesignSealedTwiceOverStillRuns) {
  std::string sealed = "`pragma protect begin\n";
  sealed += "  initial result = 42;\n";
  sealed += "`pragma protect end\n";
  std::string src = "module t;\n  int result = 1;\n";
  src += "`pragma protect begin\n";
  src += EncryptEnvelopes(sealed, kAuthorKey);
  src += "`pragma protect end\nendmodule\n";
  ProtectedDesignRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The blocks §34.5.27 defines, driven from the real designating syntax through
// the whole pipeline. The subclause here says only that such a block is found
// within the pair of delimiters, and what that placement is worth is settled by
// a run: a reader meets the key block, opens it, and holds the region's key by
// the time it reaches the data block, so the sealed statement arrives and the
// design computes with it. A block written outside the pair, or after the block
// it opens, would leave the design at the value it started at.
TEST(ProtectBeginDescriptionSimulation, ADesignWhoseKeysTravelInBlocksRuns) {
  ProtectKey held;
  held.owner = kKeyProvider;
  held.name = kKeyProviderKeyName;
  held.key = kKeyProviderKey;
  ProtectKeyList keys;
  keys.Add(held);
  std::string src = "module t;\n  int result = 1;\n";
  src += "`pragma protect begin\n";
  src += "`pragma protect key_keyowner=\"aegis-custody\"\n";
  src += "`pragma protect key_keyname=\"wrapping-2026\"\n";
  src += "  initial result = 42;\n";
  src += "`pragma protect end\nendmodule\n";
  KeyBlockDesignRun run(src, keys);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
