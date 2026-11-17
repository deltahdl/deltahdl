#include <gtest/gtest.h>
#include <unistd.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_placeholder_paths.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

std::string FilePath(const std::string& tag, int index) {
  return PlaceholderPath("t210301b", tag, index);
}

std::string RunWithPaths(const std::string& tag, const std::string& src,
                         SimFixture& f) {
  return RunWithPlaceholderPaths("t210301b", tag, src, f);
}

void RemovePaths(const std::string& tag) {
  RemovePlaceholderPaths("t210301b", tag);
}

std::string RunWithStdin(const std::string& input, const std::string& src,
                         SimFixture& f) {
  const std::string kPath = FilePath("stdin", 0);
  SeedFile(kPath, input);
  int saved = dup(0);
  std::freopen(kPath.c_str(), "r", stdin);
  std::string out = RunCapture(src, f);
  while (std::fgetc(stdin) != EOF) {
  }
  dup2(saved, 0);
  close(saved);
  clearerr(stdin);
  std::remove(kPath.c_str());
  return out;
}

TEST(OpeningAndClosingFiles, OringTwoFileDescriptorsDoesNotReachBothFiles) {
  SimFixture f;
  RunWithPaths("orfd",
               "module t;\n"
               "  integer a, b;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\", \"w\");\n"
               "    b = $fopen(\"<P1>\", \"w\");\n"
               "    $fdisplay(a | b, \"both\");\n"
               "    $fclose(a);\n"
               "    $fclose(b);\n"
               "  end\n"
               "endmodule\n",
               f);
  bool in_a = SlurpFile(FilePath("orfd", 0)).find("both") != std::string::npos;
  bool in_b = SlurpFile(FilePath("orfd", 1)).find("both") != std::string::npos;
  EXPECT_FALSE(in_a && in_b);
  RemovePaths("orfd");
}

TEST(OpeningAndClosingFiles, AnMcdOpenOfAnExistingFileDiscardsItsContent) {
  SimFixture f;
  SeedFile(FilePath("mcdtrunc", 0), "old content\n");
  RunWithPaths("mcdtrunc",
               "module t;\n"
               "  integer m;\n"
               "  initial begin\n"
               "    m = $fopen(\"<P0>\");\n"
               "    $fdisplay(m, \"new\");\n"
               "    $fclose(m);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("mcdtrunc", 0)), "new\n");
  RemovePaths("mcdtrunc");
}

TEST(OpeningAndClosingFiles, AClosedMcdBitIsHandedOutAgain) {
  SimFixture f;
  std::string out = RunWithPaths("mcdreuse",
                                 "module t;\n"
                                 "  integer a, b, c;\n"
                                 "  initial begin\n"
                                 "    a = $fopen(\"<P0>\");\n"
                                 "    b = $fopen(\"<P1>\");\n"
                                 "    $fclose(a);\n"
                                 "    c = $fopen(\"<P2>\");\n"
                                 "    $display(\"%0d\", c == a);\n"
                                 "    $fclose(b);\n"
                                 "    $fclose(c);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  RemovePaths("mcdreuse");
}

TEST(OpeningAndClosingFiles, AnOredCloseFreesEveryBitItNames) {
  SimFixture f;
  std::string out = RunWithPaths("mcdorreuse",
                                 "module t;\n"
                                 "  integer a, b, c, d;\n"
                                 "  initial begin\n"
                                 "    a = $fopen(\"<P0>\");\n"
                                 "    b = $fopen(\"<P1>\");\n"
                                 "    $fclose(a | b);\n"
                                 "    c = $fopen(\"<P2>\");\n"
                                 "    d = $fopen(\"<P3>\");\n"
                                 "    $display(\"%0d\", (c | d) == (a | b));\n"
                                 "    $fclose(c | d);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  RemovePaths("mcdorreuse");
}

TEST(OpeningAndClosingFiles,
     AnMcdOpenFailsOnceEveryUserChannelIsOpenAndSucceedsAfterAClose) {
  SimFixture f;
  std::string out = RunWithPaths(
      "mcdfull",
      "module t;\n"
      "  integer m[30];\n"
      "  integer x, y;\n"
      "  initial begin\n"
      "    foreach (m[i]) m[i] = $fopen($sformatf(\"<P0>_%0d\", i));\n"
      "    x = $fopen(\"<P1>\");\n"
      "    $display(\"%0d\", x);\n"
      "    $fclose(m[5]);\n"
      "    y = $fopen(\"<P1>\");\n"
      "    $display(\"%0d\", y == m[5]);\n"
      "    foreach (m[i]) $fclose(m[i]);\n"
      "    $fclose(y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n1\n");
  for (int i = 0; i < 30; ++i) {
    std::remove((FilePath("mcdfull", 0) + "_" + std::to_string(i)).c_str());
  }
  RemovePaths("mcdfull");
}

TEST(OpeningAndClosingFiles, NoOutputReachesAnMcdAfterItIsClosed) {
  SimFixture f;
  RunWithPaths("mcdclosed",
               "module t;\n"
               "  integer m;\n"
               "  initial begin\n"
               "    m = $fopen(\"<P0>\");\n"
               "    $fdisplay(m, \"before\");\n"
               "    $fclose(m);\n"
               "    $fdisplay(m, \"after\");\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("mcdclosed", 0)), "before\n");
  RemovePaths("mcdclosed");
}

TEST(OpeningAndClosingFiles, NoOutputReachesAnyChannelOfAnOredCloseAfterward) {
  SimFixture f;
  RunWithPaths("orclosed",
               "module t;\n"
               "  integer a, b;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\");\n"
               "    b = $fopen(\"<P1>\");\n"
               "    $fclose(a | b);\n"
               "    $fdisplay(a, \"after a\");\n"
               "    $fdisplay(b, \"after b\");\n"
               "    $fdisplay(a | b, \"after both\");\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("orclosed", 0)), "");
  EXPECT_EQ(SlurpFile(FilePath("orclosed", 1)), "");
  RemovePaths("orclosed");
}

TEST(OpeningAndClosingFiles, DISABLED_NoOutputReachesStdoutAfterItIsClosed) {
  SimFixture f;
  testing::internal::CaptureStdout();
  RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $fclose(32'h8000_0001);\n"
      "    $fdisplay(32'h8000_0001, \"after close\");\n"
      "  end\n"
      "endmodule\n",
      f);
  std::fflush(stdout);
  std::string written = testing::internal::GetCapturedStdout();
  EXPECT_EQ(written.find("after close"), std::string::npos) << written;
}

TEST(OpeningAndClosingFiles, DISABLED_NoOutputReachesStderrAfterItIsClosed) {
  SimFixture f;
  testing::internal::CaptureStderr();
  RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $fclose(32'h8000_0002);\n"
      "    $fdisplay(32'h8000_0002, \"after close\");\n"
      "  end\n"
      "endmodule\n",
      f);
  std::fflush(stderr);
  std::string written = testing::internal::GetCapturedStderr();
  EXPECT_EQ(written.find("after close"), std::string::npos) << written;
}

TEST(OpeningAndClosingFiles, DISABLED_NoInputComesFromStdinAfterItIsClosed) {
  SimFixture f;
  EXPECT_EQ(RunWithStdin("Q",
                         "module t;\n"
                         "  integer c;\n"
                         "  initial begin\n"
                         "    $fclose(32'h8000_0000);\n"
                         "    c = $fgetc(32'h8000_0000);\n"
                         "    $display(\"%0d\", c);\n"
                         "  end\n"
                         "endmodule\n",
                         f),
            "-1\n");
}

TEST(OpeningAndClosingFiles,
     OutputThroughTheStderrDescriptorReachesStandardError) {
  SimFixture f;
  testing::internal::CaptureStderr();
  testing::internal::CaptureStdout();
  RunCapture(
      "module t;\n"
      "  initial $fdisplay(32'h8000_0002, \"to standard error\");\n"
      "endmodule\n",
      f);
  std::fflush(stdout);
  std::fflush(stderr);
  std::string to_out = testing::internal::GetCapturedStdout();
  std::string to_err = testing::internal::GetCapturedStderr();
  EXPECT_NE(to_err.find("to standard error"), std::string::npos) << to_err;
  EXPECT_EQ(to_out.find("to standard error"), std::string::npos) << to_out;
}

TEST(OpeningAndClosingFiles, InputThroughTheStdinDescriptorReadsStandardInput) {
  SimFixture f;
  EXPECT_EQ(RunWithStdin("line one\nline two\n",
                         "module t;\n"
                         "  string s;\n"
                         "  integer n;\n"
                         "  initial begin\n"
                         "    n = $fgets(s, 32'h8000_0000);\n"
                         "    $write(\"%0d:%s\", n, s);\n"
                         "  end\n"
                         "endmodule\n",
                         f),
            "9:line one\n");
}

TEST(OpeningAndClosingFiles, AReadThroughTheStderrDescriptorIsRefused) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  integer c;\n"
                       "  initial begin\n"
                       "    c = $fgetc(32'h8000_0002);\n"
                       "    $display(\"%0d\", c);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-1\n");
}

TEST(OpeningAndClosingFiles, AnMcdOredWithOneWritesTheFileAndStandardOutput) {
  SimFixture f;
  testing::internal::CaptureStdout();
  std::string out = RunWithPaths("mcdor1",
                                 "module t;\n"
                                 "  integer m;\n"
                                 "  initial begin\n"
                                 "    m = $fopen(\"<P0>\");\n"
                                 "    $fdisplay(m | 1, \"fan out\");\n"
                                 "    $fclose(m);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  std::fflush(stdout);
  std::string written = out + testing::internal::GetCapturedStdout();
  EXPECT_NE(written.find("fan out"), std::string::npos) << written;
  EXPECT_EQ(SlurpFile(FilePath("mcdor1", 0)), "fan out\n");
  RemovePaths("mcdor1");
}

}  // namespace
