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

constexpr std::string_view kAuthored =
    "`pragma protect begin\n"
    "module sealed_m;\n"
    "endmodule\n"
    "`pragma protect end\n"
    "module clear_m;\n"
    "endmodule\n";

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

TEST(ProtectedSourceMarking, TheRecoveredDesignIsProtected) {
  ReadEnvelope read;
  EXPECT_TRUE(read.mgr.IsProtected(read.LineHolding("module sealed_m;")));
}

TEST(ProtectedSourceMarking, TheCleartextBesideItIsNot) {
  ReadEnvelope read;
  EXPECT_FALSE(read.mgr.IsProtected(read.LineHolding("module clear_m;")));
}

TEST(ProtectedSourceMarking, AnOrdinarySourceIsNot) {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("<test>", "module m;\nendmodule\n");
  EXPECT_FALSE(mgr.IsProtected(SourceLoc{file_id, 1, 1}));
  EXPECT_FALSE(mgr.IsProtected(SourceLoc::None()));
}

TEST(ProtectedSourceMarking, AMarkedSourceIsProtectedThroughout) {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("<recovered>", "module m;\nendmodule\n");
  mgr.MarkProtected(file_id);
  EXPECT_TRUE(mgr.IsProtected(SourceLoc{file_id, 2, 1}));
}

}  // namespace
