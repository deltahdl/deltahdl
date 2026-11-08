#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

using namespace delta;

namespace {

TEST(SourceManager, LineZeroQuotesNoText) {
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");

  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 0, 1}), "");
  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 1, 1}), "module one_cell;");
}

TEST(SourceManager, PreprocessedLineWithNoOriginIsReportedAsItStands) {
  SourceManager mgr;
  uint32_t written = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");
  std::vector<OutputLineOrigin> origins = {{0, 0}, {written, 2}};
  uint32_t id = mgr.AddPreprocessedFile("<preprocessed>",
                                        "`line 1\nendmodule\n", origins);

  EXPECT_EQ(mgr.FormatLoc(SourceLoc{id, 1, 3}), "<preprocessed>:1:3");
  EXPECT_EQ(mgr.FormatLoc(SourceLoc{id, 2, 3}), "cell.sv:2:3");
}

TEST(SourceManager, FileItDoesNotHoldHasNoContent) {
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");

  EXPECT_EQ(mgr.FileContent(0), "");
  EXPECT_EQ(mgr.FileContent(id + 1), "");
  EXPECT_EQ(mgr.FileContent(id), "module one_cell;\nendmodule\n");
}

TEST(SourceManager, QuotedLineEndsBeforeACarriageReturnAndLineFeed) {
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\r\nendmodule\r\n");

  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 1, 1}), "module one_cell;");
  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 2, 1}), "endmodule");
}

}  // namespace
