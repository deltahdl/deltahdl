#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpportslimitSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t"});
  }
};

TEST_F(DumpportslimitSysTask, LimitReachedStopsPortDumpAndInsertsComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n"), std::string::npos);
  auto comment = content.find("$comment");
  ASSERT_NE(comment, std::string::npos);
  auto text = content.find("Dump limit of 300", comment);
  ASSERT_NE(text, std::string::npos);
  EXPECT_LT(text, content.find("$end", comment));
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, NothingFollowsTheLimitComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("Dump limit of");
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(content.find('#', pos), std::string::npos);
}

TEST_F(DumpportslimitSysTask, BelowLimitDumpingContinuesWithoutComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(1000000, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, NoFilenameLimitAppliesToAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilesizeFromParameter) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  parameter LIMIT = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(LIMIT, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilesizeFromLocalparam) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  localparam LIMIT = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(LIMIT, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilesizeFromVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  int lim = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(lim, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilesizeFromVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  int lim;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    lim = 300;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(lim, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilesizeFromExpression) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(100 + 200, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilenameFromStringVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilenameFromStringVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn = \"p.dump\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask,
       FilenameFromIntegralVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [47:0] fn;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, UnknownFilenameLeavesDumpUnlimited) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"other.vcd\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, UnknownFilenameInVariableLeavesDumpUnlimited) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn = \"other.vcd\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, MissingFilesizeIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit;\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dumpportslimit requires a filesize argument", 6,
                            "21.7.3.4"));
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, MissingFilesizeEmptyParenIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit();\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dumpportslimit requires a filesize argument", 6,
                            "21.7.3.4"));
  EXPECT_EQ(content.find("$comment"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, NullFilesizeWithFilenameIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dumpportslimit requires a filesize argument", 6,
                            "21.7.3.4"));
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(DumpportslimitSysTask, LargerByteBudgetRecordsMoreOfTheDump) {
  auto count_timestamps = [](const std::string& content) {
    std::size_t n = 0;
    for (auto pos = content.find("\n#"); pos != std::string::npos;
         pos = content.find("\n#", pos + 1)) {
      ++n;
    }
    return n;
  };
  auto src = [](const char* limit) {
    return std::string(
               "module t;\n"
               "  logic [7:0] d;\n"
               "  initial begin\n"
               "    d = 8'h00;\n"
               "    $dumpports(, \"p.dump\");\n"
               "    $dumpportslimit(") +
           limit +
           ", \"p.dump\");\n"
           "    repeat (40) #10 d = d + 1;\n"
           "  end\n"
           "endmodule\n";
  };
  SimFixture f_small;
  auto small = RunVcd(f_small, src("300"));
  EXPECT_FALSE(f_small.diag.HasErrors());
  ASSERT_NE(small.find("Dump limit of 300"), std::string::npos);
  SimFixture f_large;
  auto large = RunVcd(f_large, src("450"));
  EXPECT_FALSE(f_large.diag.HasErrors());
  ASSERT_NE(large.find("Dump limit of 450"), std::string::npos);
  EXPECT_GT(count_timestamps(large), count_timestamps(small));
}

TEST_F(DumpportslimitSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    d = 8'h11;\n"
      "    #10 $dumpportslimit(300);\n"
      "    #10 d = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(DumpportslimitSysTask, MissingFilesizeNames21_7_3_4) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] e;\n"
         "  initial begin\n"
         "    e = 8'h01;\n"
         "    $dumpports(, \"q.dump\");\n"
         "    $dumpportslimit;\n"
         "    repeat (4) #10 e = e + 1;\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires a filesize argument", 6, "21.7.3.4"));
}

}  // namespace
}  // namespace delta
