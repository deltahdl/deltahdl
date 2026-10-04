// §37.3.6 Object protection properties: an object is protected when it
// represents code contained in a decryption envelope. The preprocessor is what
// knows which text that is, so it marks the source it reads a recovered design
// out of as protected, and every later stage asks the SourceManager whether a
// position resolves into such a source (SourceManager::IsProtected).

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kKey = "protection-exchange-key";

// A design with a module sealed in an envelope and one written in the clear.
constexpr std::string_view kAuthored =
    "`pragma protect begin\n"
    "module sealed_m;\n"
    "endmodule\n"
    "`pragma protect end\n"
    "module clear_m;\n"
    "endmodule\n";

// The reading of the envelope this tool writes for `kAuthored`, under the
// exchange key, with the preprocessed text registered with its origins as a
// compile registers it.
struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;
  uint32_t file_id = 0;

  ReadEnvelope() {
    PreprocConfig config;
    config.protect_key = std::string(kKey);
    Preprocessor pp(mgr, diag, config);
    std::string envelope = EncryptEnvelopes(kAuthored, kKey);
    text = pp.Preprocess(mgr.AddFile("<test>", envelope));
    file_id = mgr.AddPreprocessedFile("<preprocessed>", text, pp.LineOrigins());
  }

  // The position in the preprocessed text of the line holding `needle`.
  SourceLoc LineHolding(std::string_view needle) const {
    uint32_t line = 1;
    size_t at = text.find(needle);
    EXPECT_NE(at, std::string::npos) << text;
    for (size_t i = 0; i < at && i < text.size(); ++i) {
      if (text[i] == '\n') ++line;
    }
    return SourceLoc{file_id, line, 1};
  }
};

// A line of the recovered design resolves into a protected source.
TEST(ProtectedSourceMarking, TheRecoveredDesignIsProtected) {
  ReadEnvelope read;
  EXPECT_TRUE(read.mgr.IsProtected(read.LineHolding("module sealed_m;")));
}

// A line written in the clear beside the envelope does not.
TEST(ProtectedSourceMarking, TheCleartextBesideItIsNot) {
  ReadEnvelope read;
  EXPECT_FALSE(read.mgr.IsProtected(read.LineHolding("module clear_m;")));
}

// A source that was never an envelope's is not protected, and a position
// standing in no source is not either.
TEST(ProtectedSourceMarking, AnOrdinarySourceIsNot) {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("<test>", "module m;\nendmodule\n");
  EXPECT_FALSE(mgr.IsProtected(SourceLoc{file_id, 1, 1}));
  EXPECT_FALSE(mgr.IsProtected(SourceLoc::None()));
}

// A source marked protected is answered for at every position in it, with no
// preprocessed text over it.
TEST(ProtectedSourceMarking, AMarkedSourceIsProtectedThroughout) {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("<recovered>", "module m;\nendmodule\n");
  mgr.MarkProtected(file_id);
  EXPECT_TRUE(mgr.IsProtected(SourceLoc{file_id, 2, 1}));
}

}  // namespace
