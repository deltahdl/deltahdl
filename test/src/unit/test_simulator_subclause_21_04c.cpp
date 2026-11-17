#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <ios>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string LoadWith(SimFixture& f, const std::string& tag,
                     const std::string& text, std::string src) {
  std::string path = "/tmp/deltahdl_t2104c_" + tag + ".mem";
  {
    std::ofstream ofs(path, std::ios::binary);
    ofs << text;
  }
  for (size_t at = src.find("<F>"); at != std::string::npos;
       at = src.find("<F>")) {
    src.replace(at, 3, path);
  }
  std::string out = RunCapture(src, f);
  std::remove(path.c_str());
  return out;
}

std::string ModuleCall(const std::string& decl, const std::string& call,
                       const std::string& show) {
  return "module t;\n" + decl +
         "\n"
         "  initial begin\n"
         "    " +
         call +
         ";\n"
         "    $display(" +
         show +
         ");\n"
         "  end\n"
         "endmodule\n";
}

TEST(ReadmemMemoryNames, AClassPropertyNamedBareInAMethodLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "classprop", "11 22\n",
                     "class C;\n"
                     "  reg [7:0] data [0:1];\n"
                     "  function void load(); $readmemh(\"<F>\", data); "
                     "endfunction\n"
                     "endclass\n"
                     "module t;\n"
                     "  C c;\n"
                     "  initial begin\n"
                     "    c = new;\n"
                     "    c.load();\n"
                     "    $display(\"%h %h\", c.data[0], c.data[1]);\n"
                     "  end\n"
                     "endmodule\n"),
            "11 22\n");
}

TEST(ReadmemMemoryNames, DISABLED_APackageArrayNamedWithItsScopeLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "pkgscope", "33 44\n",
                     "package p;\n"
                     "  reg [7:0] pm [0:1];\n"
                     "endpackage\n" +
                         ModuleCall("", "$readmemh(\"<F>\", p::pm)",
                                    "\"%h %h\", p::pm[0], p::pm[1]")),
            "33 44\n");
}

TEST(ReadmemMemoryNames, AnImportedPackageArrayNamedBareLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "pkgimport", "55 66\n",
                     "package p;\n"
                     "  reg [7:0] pm [0:1];\n"
                     "endpackage\n"
                     "module t;\n"
                     "  import p::*;\n"
                     "  initial begin\n"
                     "    $readmemh(\"<F>\", pm);\n"
                     "    $display(\"%h %h\", pm[0], pm[1]);\n"
                     "  end\n"
                     "endmodule\n"),
            "55 66\n");
}

TEST(ReadmemMemoryNames, ACompilationUnitArrayLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "unit", "77 88\n",
                     "reg [7:0] um [0:1];\n" +
                         ModuleCall("", "$readmemh(\"<F>\", um)",
                                    "\"%h %h\", um[0], um[1]")),
            "77 88\n");
}

constexpr const char* kOutsideSlice = "start/finish address outside the slice";

TEST(ReadmemSliceBounds, FinishOutsideTheSliceIsReported) {
  SimFixture f;
  LoadWith(f, "slice_fin", "1 2 3 4\n",
           ModuleCall("  reg [7:0] mem [0:15];",
                      "$readmemh(\"<F>\", mem[4:7], 5, 9)", "\"done\""));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideSlice, 4, "21.4"));
}

TEST(ReadmemSliceBounds, AStartAloneOutsideTheSliceIsReported) {
  SimFixture f;
  LoadWith(f, "slice_start", "1 2 3 4\n",
           ModuleCall("  reg [7:0] mem [0:15];",
                      "$readmemh(\"<F>\", mem[4:7], 2)", "\"done\""));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideSlice, 4, "21.4"));
}

TEST(ReadmemSliceBounds, AClassPropertySliceOutsideItsBoundsIsReported) {
  SimFixture f;
  LoadWith(f, "slice_class", "1 2 3 4\n",
           "class C;\n"
           "  reg [7:0] arr [0:15];\n"
           "endclass\n"
           "module t;\n"
           "  C c;\n"
           "  initial begin\n"
           "    c = new;\n"
           "    $readmemh(\"<F>\", c.arr[4:7], 2, 9);\n"
           "  end\n"
           "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideSlice, 8, "21.4"));
}

TEST(ReadmemSliceBounds,
     DISABLED_AHierarchicalSliceOutsideItsBoundsIsReported) {
  SimFixture f;
  LoadWith(f, "slice_hier", "1 2 3 4\n",
           "module u;\n"
           "  reg [7:0] mem [0:15];\n"
           "endmodule\n"
           "module t;\n"
           "  u inst();\n"
           "  initial $readmemh(\"<F>\", t.inst.mem[4:7], 2, 9);\n"
           "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideSlice, 6, "21.4"));
}

TEST(ReadmemSliceBounds, AddressesInsideTheSliceLoadWithoutAReport) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "slice_ok", "a1 a2\n",
                     ModuleCall("  reg [7:0] mem [0:15];",
                                "$readmemh(\"<F>\", mem[4:7], 5, 6)",
                                "\"%h %h\", mem[5], mem[6]")),
            "a1 a2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ReadmemHighestDimension,
     DISABLED_AStartAloneSelectsAHighestDimensionWord) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "md_start", "1 2 3 4\n",
                     ModuleCall("  reg [7:0] m [0:2][0:1];",
                                "$readmemh(\"<F>\", m, 1)",
                                "\"%h %h %h %h %h\", m[0][0], m[1][0], "
                                "m[1][1], m[2][0], m[2][1]")),
            "xx 01 02 03 04\n");
}

TEST(ReadmemHighestDimension,
     DISABLED_StartAboveFinishStepsDownOverWholeWords) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "md_down", "1 2 3 4 5 6\n",
                     ModuleCall("  reg [7:0] m [0:2][0:1];",
                                "$readmemh(\"<F>\", m, 2, 0)",
                                "\"%h %h %h %h %h %h\", m[2][0], m[2][1], "
                                "m[1][0], m[1][1], m[0][0], m[0][1]")),
            "01 02 03 04 05 06\n");
}

TEST(ReadmemAnyTime, ACallInAProgramBlockLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "program", "5a 5b\n",
                     "program p;\n"
                     "  reg [7:0] mem [0:1];\n"
                     "  initial begin\n"
                     "    #3 $readmemh(\"<F>\", mem);\n"
                     "    $display(\"%0t %h %h\", $time, mem[0], mem[1]);\n"
                     "  end\n"
                     "endprogram\n"),
            "3 5a 5b\n");
}

TEST(ReadmemAnyTime, ACallInAModuleTaskLoads) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "task", "1 10\n",
                     "module t;\n"
                     "  reg [7:0] mem [0:1];\n"
                     "  task load(); #2 $readmemb(\"<F>\", mem); endtask\n"
                     "  initial begin\n"
                     "    load();\n"
                     "    $display(\"%0t %h %h\", $time, mem[0], mem[1]);\n"
                     "  end\n"
                     "endmodule\n"),
            "2 01 02\n");
}

TEST(ReadmemAnyTime, ACallInAModuleTaskLoadsHexadecimal) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "taskh", "6a 6b\n",
                     "module t;\n"
                     "  reg [7:0] mem [0:1];\n"
                     "  task load(); #2 $readmemh(\"<F>\", mem); endtask\n"
                     "  initial begin\n"
                     "    load();\n"
                     "    $display(\"%0t %h %h\", $time, mem[0], mem[1]);\n"
                     "  end\n"
                     "endmodule\n"),
            "2 6a 6b\n");
}

TEST(ReadmemAnyTime, APackageFunctionLoadsTheCallersArrayThroughARef) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "pkgref", "7a 7b\n",
                     "package p;\n"
                     "  function automatic void load(ref reg [7:0] m [0:1]);\n"
                     "    $readmemh(\"<F>\", m);\n"
                     "  endfunction\n"
                     "endpackage\n"
                     "module t;\n"
                     "  reg [7:0] mem [0:1];\n"
                     "  initial begin\n"
                     "    p::load(mem);\n"
                     "    $display(\"%h %h\", mem[0], mem[1]);\n"
                     "  end\n"
                     "endmodule\n"),
            "7a 7b\n");
}

std::string LoadFour(SimFixture& f, const std::string& tag,
                     const std::string& task, const std::string& text) {
  return LoadWith(f, tag, text,
                  ModuleCall("  reg [7:0] mem [0:3];", task + "(\"<F>\", mem)",
                             "\"%h %h %h %h\", mem[0], mem[1], mem[2], "
                             "mem[3]"));
}

TEST(ReadmemFileText, AFormfeedSeparatesNumbers) {
  SimFixture f;
  EXPECT_EQ(LoadFour(f, "ff", "$readmemh", "11\f22\f33\n"), "11 22 33 xx\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ReadmemFileText, ASemicolonIsReported) {
  SimFixture f;
  LoadFour(f, "semi", "$readmemh", "11;\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 4, "21.4"));
}

TEST(ReadmemFileText, AnUppercaseZLoadsAsHighImpedance) {
  SimFixture f;
  EXPECT_EQ(LoadFour(f, "bigz", "$readmemh", "Z5 X1\n"), "z5 x1 xx xx\n");
}

TEST(ReadmemFileText, ASizedBasedNumberUnderReadmembIsReported) {
  SimFixture f;
  LoadFour(f, "sized_b", "$readmemb", "4'b1010\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized binary number", 4, "21.4"));
}

TEST(ReadmemFileText, ABasedNumberWithoutASizeIsReported) {
  SimFixture fh;
  LoadFour(fh, "based_h", "$readmemh", "'hff\n");
  EXPECT_TRUE(ReportedError(fh.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 4, "21.4"));
  SimFixture fb;
  LoadFour(fb, "based_b", "$readmemb", "'b101\n");
  EXPECT_TRUE(ReportedError(fb.diag.Diagnostics(),
                            "is not an unsized binary number", 4, "21.4"));
}

TEST(ReadmemFileText, AnAddressUnderReadmembIsHexadecimal) {
  SimFixture f;
  EXPECT_EQ(
      LoadWith(f, "b_addr", "@a 1\n@10 11\n",
               ModuleCall("  reg [7:0] mem [0:31];", "$readmemb(\"<F>\", mem)",
                          "\"%0d %0d %0d\", mem[10], mem[16], mem[2]")),
      "1 3 x\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ReadmemFileText, ABlockCommentAloneSeparatesNumbers) {
  SimFixture f;
  EXPECT_EQ(LoadFour(f, "blk_h", "$readmemh", "aa/*c*/bb\n"), "aa bb xx xx\n");
  SimFixture g;
  EXPECT_EQ(LoadFour(g, "blk_b", "$readmemb", "1/*c*/10\n"), "01 02 xx xx\n");
}

TEST(ReadmemFileText, ALineCommentAloneSeparatesNumbers) {
  SimFixture f;
  EXPECT_EQ(LoadFour(f, "line_h", "$readmemh", "aa//c\nbb\n"), "aa bb xx xx\n");
  SimFixture g;
  EXPECT_EQ(LoadFour(g, "line_b", "$readmemb", "1//c\n10\n"), "01 02 xx xx\n");
}

TEST(ReadmemDirection, ADescendingMemoryLoadsFromItsLowestAddress) {
  SimFixture f;
  EXPECT_EQ(
      LoadWith(f, "desc", "a0 a1\n",
               ModuleCall("  reg [7:0] mem [7:0];", "$readmemh(\"<F>\", mem)",
                          "\"%h %h %h\", mem[0], mem[1], mem[7]")),
      "a0 a1 xx\n");
}

TEST(ReadmemDirection, ALongFileStopsAtTheHighestAddress) {
  SimFixture f;
  EXPECT_EQ(LoadFour(f, "long", "$readmemh", "1 2 3 4 5 6\n"), "01 02 03 04\n");
}

TEST(ReadmemDirection, StartAboveFinishLoadsDownwardUnderReadmemb) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "down_b", "1 10 11 100\n",
                     ModuleCall("  reg [7:0] mem [0:7];",
                                "$readmemb(\"<F>\", mem, 5, 2)",
                                "\"%0d %0d %0d %0d\", mem[5], mem[4], mem[3], "
                                "mem[2]")),
            "1 2 3 4\n");
}

TEST(ReadmemDirection, DISABLED_ExtraWordsStopAtFinishUnderEitherTask) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "over_h", "1 2 3 4\n",
                     ModuleCall("  reg [7:0] mem [0:7];",
                                "$readmemh(\"<F>\", mem, 1, 2)",
                                "\"%h %h %h %h\", mem[0], mem[1], mem[2], "
                                "mem[3]")),
            "xx 01 02 xx\n");
  SimFixture g;
  EXPECT_EQ(LoadWith(g, "over_b", "1 10 11 100\n",
                     ModuleCall("  reg [7:0] mem [0:7];",
                                "$readmemb(\"<F>\", mem, 1, 2)",
                                "\"%h %h %h %h\", mem[0], mem[1], mem[2], "
                                "mem[3]")),
            "xx 01 02 xx\n");
}

TEST(ReadmemDirection, DISABLED_WordsAfterAnAddressStopAtFinish) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "over_at", "@3 1 2 3 4\n",
                     ModuleCall("  reg [7:0] mem [0:7];",
                                "$readmemh(\"<F>\", mem, 1, 4)",
                                "\"%h %h %h\", mem[3], mem[4], mem[5]")),
            "01 02 xx\n");
}

TEST(ReadmemDirection,
     DISABLED_AnAssociativeArrayLoadedDownwardCreatesNoKeyPastFinish) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "assoc_down", "1 2 3 4\n",
                     ModuleCall("  reg [7:0] aa [int];",
                                "$readmemh(\"<F>\", aa, 5, 4)",
                                "\"%0d %h %h %0d\", aa.num(), aa[5], aa[4], "
                                "aa.exists(3)")),
            "2 01 02 0\n");
}

constexpr const char* kOutsideRange =
    "file address outside the range given by the task";

TEST(ReadmemFileAddresses, AnAddressOutsideADescendingWindowIsReported) {
  SimFixture f;
  LoadWith(f, "win_down", "@7 1\n",
           ModuleCall("  reg [7:0] mem [0:7];", "$readmemh(\"<F>\", mem, 5, 2)",
                      "\"done\""));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideRange, 4, "21.4"));
}

TEST(ReadmemFileAddresses, AnAddressBelowAStartAloneIsReported) {
  SimFixture f;
  LoadWith(f, "win_start", "@1 1\n",
           ModuleCall("  reg [7:0] mem [0:7];", "$readmemh(\"<F>\", mem, 3)",
                      "\"done\""));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOutsideRange, 4, "21.4"));
}

TEST(ReadmemFileAddresses, AnAddressInsideTheWindowLoadsWithoutAReport) {
  SimFixture f;
  EXPECT_EQ(LoadWith(f, "win_ok", "@3 c3 c4\n",
                     ModuleCall("  reg [7:0] mem [0:7];",
                                "$readmemh(\"<F>\", mem, 2, 5)",
                                "\"%h %h %h\", mem[2], mem[3], mem[4]")),
            "xx c3 c4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ReadmemWordCount, MoreWordsThanTheRangeWarns) {
  SimFixture f;
  LoadWith(f, "count_more", "1 2 3 4 5\n",
           ModuleCall("  reg [7:0] mem [0:7];", "$readmemh(\"<F>\", mem, 1, 2)",
                      "\"done\""));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "number of data words differs from the address "
                              "range",
                              4, "21.4"));
}

TEST(ReadmemWordCount, AFileWithAddressesDrawsNoCountWarning) {
  SimFixture f;
  LoadWith(f, "count_at", "@1 1\n",
           ModuleCall("  reg [7:0] mem [0:7];", "$readmemh(\"<F>\", mem, 1, 4)",
                      "\"done\""));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
