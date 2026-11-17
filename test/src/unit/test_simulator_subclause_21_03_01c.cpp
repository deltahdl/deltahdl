#include <gtest/gtest.h>
#include <sys/stat.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

std::string FilePath(const std::string& tag, int index) {
  return "/tmp/deltahdl_t210301c_" + tag + "_" + std::to_string(index);
}

std::string RunWithPaths(const std::string& tag, std::string src,
                         SimFixture& f) {
  for (int i = 0; i < 4; ++i) {
    const std::string kToken = "<P" + std::to_string(i) + ">";
    for (size_t at = src.find(kToken); at != std::string::npos;
         at = src.find(kToken)) {
      src.replace(at, kToken.size(), FilePath(tag, i));
    }
  }
  return RunCapture(src, f);
}

void RemovePaths(const std::string& tag) {
  for (int i = 0; i < 4; ++i) std::remove(FilePath(tag, i).c_str());
}

TEST(OpeningAndClosingFiles, TypeWTruncatesAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("truncW", 0), "0123456789");
  RunWithPaths("truncW",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w\");\n"
               "    $fwrite(fd, \"ab\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("truncW", 0)), "ab");
  RemovePaths("truncW");
}

TEST(OpeningAndClosingFiles, TypeWbTruncatesAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("truncWb", 0), "0123456789");
  RunWithPaths("truncWb",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"wb\");\n"
               "    $fwrite(fd, \"ab\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("truncWb", 0)), "ab");
  RemovePaths("truncWb");
}

TEST(OpeningAndClosingFiles, TypeWPlusTruncatesAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("truncWPlus", 0), "0123456789");
  RunWithPaths("truncWPlus",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w+\");\n"
               "    $fwrite(fd, \"ab\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("truncWPlus", 0)), "ab");
  RemovePaths("truncWPlus");
}

TEST(OpeningAndClosingFiles, TypeWPlusBTruncatesAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("truncWPlusB", 0), "0123456789");
  RunWithPaths("truncWPlusB",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w+b\");\n"
               "    $fwrite(fd, \"ab\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("truncWPlusB", 0)), "ab");
  RemovePaths("truncWPlusB");
}

TEST(OpeningAndClosingFiles, TypeWbPlusTruncatesAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("truncWbPlus", 0), "0123456789");
  RunWithPaths("truncWbPlus",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"wb+\");\n"
               "    $fwrite(fd, \"ab\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("truncWbPlus", 0)), "ab");
  RemovePaths("truncWbPlus");
}

TEST(OpeningAndClosingFiles, TypeAAppendsToAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("appA", 0), "old");
  RunWithPaths("appA",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"a\");\n"
               "    $fwrite(fd, \"new\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("appA", 0)), "oldnew");
  RemovePaths("appA");
}

TEST(OpeningAndClosingFiles, TypeAbAppendsToAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("appAb", 0), "old");
  RunWithPaths("appAb",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"ab\");\n"
               "    $fwrite(fd, \"new\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("appAb", 0)), "oldnew");
  RemovePaths("appAb");
}

TEST(OpeningAndClosingFiles, TypeAPlusAppendsToAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("appAPlus", 0), "old");
  RunWithPaths("appAPlus",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"a+\");\n"
               "    $fwrite(fd, \"new\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("appAPlus", 0)), "oldnew");
  RemovePaths("appAPlus");
}

TEST(OpeningAndClosingFiles, TypeAPlusBAppendsToAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("appAPlusB", 0), "old");
  RunWithPaths("appAPlusB",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"a+b\");\n"
               "    $fwrite(fd, \"new\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("appAPlusB", 0)), "oldnew");
  RemovePaths("appAPlusB");
}

TEST(OpeningAndClosingFiles, TypeAbPlusAppendsToAnExistingFile) {
  SimFixture f;
  SeedFile(FilePath("appAbPlus", 0), "old");
  RunWithPaths("appAbPlus",
               "module t;\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"ab+\");\n"
               "    $fwrite(fd, \"new\");\n"
               "    $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("appAbPlus", 0)), "oldnew");
  RemovePaths("appAbPlus");
}

TEST(OpeningAndClosingFiles, TypeWCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createW", 0).c_str());
  std::string out = RunWithPaths("createW",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"w\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createW", 0)).good());
  RemovePaths("createW");
}

TEST(OpeningAndClosingFiles, TypeWbCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createWb", 0).c_str());
  std::string out = RunWithPaths("createWb",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"wb\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createWb", 0)).good());
  RemovePaths("createWb");
}

TEST(OpeningAndClosingFiles, TypeWPlusCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createWPlus", 0).c_str());
  std::string out = RunWithPaths("createWPlus",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"w+\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createWPlus", 0)).good());
  RemovePaths("createWPlus");
}

TEST(OpeningAndClosingFiles, TypeWPlusBCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createWPlusB", 0).c_str());
  std::string out = RunWithPaths("createWPlusB",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"w+b\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createWPlusB", 0)).good());
  RemovePaths("createWPlusB");
}

TEST(OpeningAndClosingFiles, TypeWbPlusCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createWbPlus", 0).c_str());
  std::string out = RunWithPaths("createWbPlus",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"wb+\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createWbPlus", 0)).good());
  RemovePaths("createWbPlus");
}

TEST(OpeningAndClosingFiles, TypeACreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createA", 0).c_str());
  std::string out = RunWithPaths("createA",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"a\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createA", 0)).good());
  RemovePaths("createA");
}

TEST(OpeningAndClosingFiles, TypeAbCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createAb", 0).c_str());
  std::string out = RunWithPaths("createAb",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"ab\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createAb", 0)).good());
  RemovePaths("createAb");
}

TEST(OpeningAndClosingFiles, TypeAPlusCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createAPlus", 0).c_str());
  std::string out = RunWithPaths("createAPlus",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"a+\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createAPlus", 0)).good());
  RemovePaths("createAPlus");
}

TEST(OpeningAndClosingFiles, TypeAPlusBCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createAPlusB", 0).c_str());
  std::string out = RunWithPaths("createAPlusB",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"a+b\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createAPlusB", 0)).good());
  RemovePaths("createAPlusB");
}

TEST(OpeningAndClosingFiles, TypeAbPlusCreatesAMissingFile) {
  SimFixture f;
  std::remove(FilePath("createAbPlus", 0).c_str());
  std::string out = RunWithPaths("createAbPlus",
                                 "module t;\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"ab+\");\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_TRUE(std::ifstream(FilePath("createAbPlus", 0)).good());
  RemovePaths("createAbPlus");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeWPlusPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readWPlus",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"w+\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readWPlus");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeWPlusBPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readWPlusB",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"w+b\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readWPlusB");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeWbPlusPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readWbPlus",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"wb+\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readWbPlus");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeAPlusPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readAPlus",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"a+\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readAPlus");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeAPlusBPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readAPlusB",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"a+b\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readAPlusB");
}

TEST(OpeningAndClosingFiles, DISABLED_TypeAbPlusPermitsReading) {
  SimFixture f;
  std::string out = RunWithPaths("readAbPlus",
                                 "module t;\n"
                                 "  integer fd, c;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", \"ab+\");\n"
                                 "    $fwrite(fd, \"hi\");\n"
                                 "    void'($rewind(fd));\n"
                                 "    c = $fgetc(fd);\n"
                                 "    $display(\"%c\", c);\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "h\n");
  RemovePaths("readAbPlus");
}

TEST(OpeningAndClosingFiles, EveryWriteTypeOnAnUnwritableFileReturnsZero) {
  SimFixture f;
  SeedFile(FilePath("permw", 0), "x");
  chmod(FilePath("permw", 0).c_str(), 0444);
  std::string out =
      RunWithPaths("permw",
                   "module t;\n"
                   "  initial begin\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"w\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"wb\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"a\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"ab\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"w+\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"w+b\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"wb+\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"a+\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"a+b\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"ab+\") == 0);\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  EXPECT_EQ(out, std::string(10, '1'));
  chmod(FilePath("permw", 0).c_str(), 0644);
  RemovePaths("permw");
}

TEST(OpeningAndClosingFiles, EveryReadTypeOnAnUnreadableFileReturnsZero) {
  SimFixture f;
  SeedFile(FilePath("permr", 0), "x");
  chmod(FilePath("permr", 0).c_str(), 0000);
  std::string out =
      RunWithPaths("permr",
                   "module t;\n"
                   "  initial begin\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"r\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"rb\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"r+\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"r+b\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"rb+\") == 0);\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  EXPECT_EQ(out, std::string(5, '1'));
  chmod(FilePath("permr", 0).c_str(), 0644);
  RemovePaths("permr");
}

TEST(OpeningAndClosingFiles, EveryUpdateTypeOnAReadOnlyFileReturnsZero) {
  SimFixture f;
  SeedFile(FilePath("permru", 0), "x");
  chmod(FilePath("permru", 0).c_str(), 0444);
  std::string out =
      RunWithPaths("permru",
                   "module t;\n"
                   "  initial begin\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"r+\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"r+b\") == 0);\n"
                   "    $write(\"%0d\", $fopen(\"<P0>\", \"rb+\") == 0);\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  EXPECT_EQ(out, std::string(3, '1'));
  chmod(FilePath("permru", 0).c_str(), 0644);
  RemovePaths("permru");
}

TEST(OpeningAndClosingFiles, AnMcdOpenOfAnUnwritableFileReturnsZero) {
  SimFixture f;
  SeedFile(FilePath("permmcd", 0), "x");
  chmod(FilePath("permmcd", 0).c_str(), 0444);
  std::string out = RunWithPaths("permmcd",
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    $write(\"%0d\", $fopen(\"<P0>\") == 0);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, std::string(1, '1'));
  chmod(FilePath("permmcd", 0).c_str(), 0644);
  RemovePaths("permmcd");
}

TEST(OpeningAndClosingFiles, EveryWriteTypeInAMissingDirectoryReturnsZero) {
  SimFixture f;
  std::string out = RunWithPaths(
      "nodir",
      "module t;\n"
      "  initial begin\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"w\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"wb\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"a\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"ab\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"w+\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"w+b\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"wb+\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"a+\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"a+b\") == 0);\n"
      "    $write(\"%0d\", $fopen(\"<P0>_missing_dir/file\", \"ab+\") == 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, std::string(10, '1'));
  RemovePaths("nodir");
}

TEST(OpeningAndClosingFiles,
     ATwoCharacterTypeInAnIntegralVariableOpensAsThatType) {
  SimFixture f;
  SeedFile(FilePath("int2", 0), "seed");
  std::string out = RunWithPaths("int2",
                                 "module t;\n"
                                 "  bit [15:0] t = \"r+\";\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", t);\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fwrite(fd, \"Z\");\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_EQ(SlurpFile(FilePath("int2", 0)), "Zeed");
  RemovePaths("int2");
}

TEST(OpeningAndClosingFiles,
     AThreeCharacterTypeInAnIntegralVariableOpensAsThatType) {
  SimFixture f;
  SeedFile(FilePath("int3", 0), "seed");
  std::string out = RunWithPaths("int3",
                                 "module t;\n"
                                 "  bit [23:0] t = \"a+b\";\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", t);\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fwrite(fd, \"Z\");\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_EQ(SlurpFile(FilePath("int3", 0)), "seedZ");
  RemovePaths("int3");
}

TEST(OpeningAndClosingFiles, ATypeInAWiderIntegralVariableOpensAsThatType) {
  SimFixture f;
  SeedFile(FilePath("int8", 0), "seed");
  std::string out = RunWithPaths("int8",
                                 "module t;\n"
                                 "  bit [63:0] t = \"r+\";\n"
                                 "  integer fd;\n"
                                 "  initial begin\n"
                                 "    fd = $fopen(\"<P0>\", t);\n"
                                 "    $display(\"%0d\", fd != 0);\n"
                                 "    $fwrite(fd, \"Z\");\n"
                                 "    $fclose(fd);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  EXPECT_EQ(out, "1\n");
  EXPECT_EQ(SlurpFile(FilePath("int8", 0)), "Zeed");
  RemovePaths("int8");
}

TEST(OpeningAndClosingFiles,
     DISABLED_AnUnknownTypeInAStringVariableIsReported) {
  SimFixture f;
  RunWithPaths("badAStringVar",
               "module t;\n"
               "  string t = \"rw\";\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", t);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 5,
      "21.3.1"));
  RemovePaths("badAStringVar");
}

TEST(OpeningAndClosingFiles,
     DISABLED_AnUnknownTypeInAnIntegralVariableIsReported) {
  SimFixture f;
  RunWithPaths("badAnIntegral",
               "module t;\n"
               "  bit [15:0] t = \"wx\";\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", t);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 5,
      "21.3.1"));
  RemovePaths("badAnIntegral");
}

TEST(OpeningAndClosingFiles,
     DISABLED_AnUnknownTypeInAnEmptyStringVariableIsReported) {
  SimFixture f;
  RunWithPaths("badAnEmptyStr",
               "module t;\n"
               "  string t = \"\";\n"
               "  integer fd;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", t);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 5,
      "21.3.1"));
  RemovePaths("badAnEmptyStr");
}

TEST(OpeningAndClosingFiles, FopenAndFcloseRunInsideAClassMethod) {
  SimFixture f;
  RunWithPaths("cls",
               "module t;\n"
               "  class C;\n"
               "    function void go();\n"
               "      integer fd, m;\n"
               "      fd = $fopen(\"<P0>\", \"w\");\n"
               "      m = $fopen(\"<P1>\");\n"
               "      $fdisplay(fd, \"fd form\");\n"
               "      $fdisplay(m, \"mcd form\");\n"
               "      $fclose(fd);\n"
               "      $fclose(m);\n"
               "    endfunction\n"
               "  endclass\n"
               "  C h = new;\n"
               "  initial h.go();\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("cls", 0)), "fd form\n");
  EXPECT_EQ(SlurpFile(FilePath("cls", 1)), "mcd form\n");
  RemovePaths("cls");
}

}  // namespace
