#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_dump.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumplimitSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }

  static std::size_t CountTimestamps(const std::string& content) {
    return CountOccurrences(content, "\n#");
  }
};

TEST_F(DumplimitSysTask, LimitReachedStopsDumpAndInsertsComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#10\n"), std::string::npos);
  auto comment = content.find("$comment");
  ASSERT_NE(comment, std::string::npos);
  auto text = content.find("Dump limit of", comment);
  ASSERT_NE(text, std::string::npos);
  EXPECT_LT(text, content.find("$end", comment));
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, NothingFollowsTheLimitComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("Dump limit of");
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(content.find('#', pos), std::string::npos);
}

TEST_F(DumplimitSysTask, LimitCommentInsertedOnlyOnce) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "Dump limit of"), 1u);
}

TEST_F(DumplimitSysTask, BelowLimitDumpingContinuesWithoutComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(1000000);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, LargerByteBudgetRecordsMoreOfTheDump) {
  const char* const kSmall =
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n";
  const char* const kLarge =
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(400);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n";
  auto small = RunVcd(kSmall);
  auto small_count = CountTimestamps(small);
  ASSERT_NE(small.find("Dump limit of 200"), std::string::npos);
  auto large = RunVcd(kLarge);
  ASSERT_NE(large.find("Dump limit of 400"), std::string::npos);
  EXPECT_GT(CountTimestamps(large), small_count);
}

TEST_F(DumplimitSysTask, MidSimulationLimitAppliesToBytesAlreadyWritten) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    repeat (10) #10 data = data + 1;\n"
      "    $dumplimit(1);\n"
      "    repeat (10) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#90\n"), std::string::npos);
  EXPECT_NE(content.find("Dump limit of 1 "), std::string::npos);
  EXPECT_EQ(content.find("#100\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, FilesizeFromParameter) {
  auto content = RunVcd(
      "module t;\n"
      "  parameter LIMIT = 200;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(LIMIT);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, FilesizeFromLocalparam) {
  auto content = RunVcd(
      "module t;\n"
      "  localparam LIMIT = 200;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(LIMIT);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, FilesizeFromVariable) {
  auto content = RunVcd(
      "module t;\n"
      "  int lim;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    lim = 200;\n"
      "    $dumplimit(lim);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, FilesizeFromExpression) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(100 + 100);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, DumplimitAfterDumpfileAndDumpvarsSequence) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#10\n"), std::string::npos);
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, DumplimitInvokedFromTaskBody) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task cap;\n"
      "    $dumplimit(200);\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    cap;\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumplimitSysTask, WithoutDumpFileDumplimitIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumplimit(200);\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.Vcd().GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
