#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

using namespace delta;

namespace {

// No clause of IEEE 1800-2023 says how a tool keeps the text it read, so these
// cases cover SourceManager on its own terms: what it answers for a position or
// a file it holds nothing for, and which characters end a line it quotes.

TEST(SourceManager, LineZeroQuotesNoText) {
  // Lines count from 1, so line 0 names no line of the file. A manager that
  // indexed its table with the line less one would read before the table.
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");

  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 0, 1}), "");
  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 1, 1}), "module one_cell;");
}

TEST(SourceManager, PreprocessedLineWithNoOriginIsReportedAsItStands) {
  // A line of preprocessed text whose origin names no file was written by no
  // file the user can open, so its position is the one in the text itself. The
  // second line, whose origin is known, is what shows the table was read.
  SourceManager mgr;
  uint32_t written = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");
  std::vector<OutputLineOrigin> origins = {{0, 0}, {written, 2}};
  uint32_t id = mgr.AddPreprocessedFile("<preprocessed>",
                                        "`line 1\nendmodule\n", origins);

  EXPECT_EQ(mgr.FormatLoc(SourceLoc{id, 1, 3}), "<preprocessed>:1:3");
  EXPECT_EQ(mgr.FormatLoc(SourceLoc{id, 2, 3}), "cell.sv:2:3");
}

TEST(SourceManager, FileItDoesNotHoldHasNoContent) {
  // File ids count from 1, so 0 names no file, and neither does an id past the
  // last one registered.
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\nendmodule\n");

  EXPECT_EQ(mgr.FileContent(0), "");
  EXPECT_EQ(mgr.FileContent(id + 1), "");
  EXPECT_EQ(mgr.FileContent(id), "module one_cell;\nendmodule\n");
}

TEST(SourceManager, QuotedLineEndsBeforeACarriageReturnAndLineFeed) {
  // A file written with CRLF line endings quotes each line without either
  // character, as one written with LF alone does.
  SourceManager mgr;
  uint32_t id = mgr.AddFile("cell.sv", "module one_cell;\r\nendmodule\r\n");

  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 1, 1}), "module one_cell;");
  EXPECT_EQ(mgr.GetLineText(SourceLoc{id, 2, 1}), "endmodule");
}

}  // namespace
