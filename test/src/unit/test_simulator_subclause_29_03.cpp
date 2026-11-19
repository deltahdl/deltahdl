#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>

#include "driver/cli_options.h"
#include "driver/protect_license_libraries.h"
#include "driver/source_units.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;

namespace {

constexpr const char* kAnd2Definition =
    "primitive and2 (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "    1 1 : 1 ;\n"
    "    0 ? : 0 ;\n"
    "    ? 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kAnd2User =
    "module top;\n"
    "  reg a, b;\n"
    "  wire y;\n"
    "  and2 u(y, a, b);\n"
    "  initial begin\n"
    "    a = 1; b = 1; #1 $display(\"%b\", y);\n"
    "    b = 0; #1 $display(\"%b\", y);\n"
    "  end\n"
    "endmodule\n";

TEST(ExternUdpDeclarationRun,
     ExternPrototypeBeforeTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string("extern primitive and2 (y, a, b);\n") +
                           kAnd2User + kAnd2Definition,
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ExternUdpDeclarationRun, ExternPrototypeAfterTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAnd2Definition) + kAnd2User +
                           "extern primitive and2 (y, a, b);\n",
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(UdpInputCountRun, TenInputCombinationalAndNineInputSequentialRun) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "primitive c10(output y, input a0, a1, a2, a3, a4, a5, a6, a7, a8,"
          " a9);\n"
          "  table\n"
          "    1 1 1 1 1 1 1 1 1 1 : 1;\n"
          "    1 1 1 1 1 1 1 1 1 0 : 0;\n"
          "    0 ? ? ? ? ? ? ? ? ? : 0;\n"
          "  endtable\n"
          "endprimitive\n"
          "primitive s9(output reg q, input c, d1, d2, d3, d4, d5, d6, d7,"
          " d8);\n"
          "  table\n"
          "    r 1 1 1 1 1 1 1 1 : ? : 1;\n"
          "    r 1 1 1 1 1 1 1 0 : ? : 0;\n"
          "    f ? ? ? ? ? ? ? ? : ? : -;\n"
          "    ? * ? ? ? ? ? ? ? : ? : -;\n"
          "    ? ? * ? ? ? ? ? ? : ? : -;\n"
          "    ? ? ? * ? ? ? ? ? : ? : -;\n"
          "    ? ? ? ? * ? ? ? ? : ? : -;\n"
          "    ? ? ? ? ? * ? ? ? : ? : -;\n"
          "    ? ? ? ? ? ? * ? ? : ? : -;\n"
          "    ? ? ? ? ? ? ? * ? : ? : -;\n"
          "    ? ? ? ? ? ? ? ? * : ? : -;\n"
          "  endtable\n"
          "endprimitive\n"
          "module m;\n"
          "  reg [9:0] a;\n"
          "  reg c;\n"
          "  reg [7:0] d;\n"
          "  wire y, q;\n"
          "  c10 u1(y, a[9], a[8], a[7], a[6], a[5], a[4], a[3], a[2], a[1],"
          " a[0]);\n"
          "  s9 u2(q, c, d[7], d[6], d[5], d[4], d[3], d[2], d[1], d[0]);\n"
          "  initial begin\n"
          "    a = 10'b1111111111; c = 0; d = 8'hff;\n"
          "    #1 $write(\"%b\", y); a = 10'b1111111110;\n"
          "    #1 $write(\"%b\", y); a = 10'b1111111100;\n"
          "    #1 $write(\"%b \", y);\n"
          "    c = 1; #1 $write(\"%b\", q); d = 8'hfe; #1 $write(\"%b\", q);\n"
          "    c = 0; #1 c = 1; #1 $write(\"%b\", q);\n"
          "    d = 8'hff; #1 $write(\"%b\", q);\n"
          "    c = 0; #1 c = 1; #1 $display(\"%b\", q);\n"
          "  end\n"
          "endmodule\n",
          f),
      "10x 11001\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(UdpPortOrderRun, TableColumnsFollowThePortListNotTheDeclarationOrder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive p(y, a, b, c);\n"
                       "  output y;\n"
                       "  input c;\n"
                       "  input b;\n"
                       "  input a;\n"
                       "  table\n"
                       "    1 0 0 : 1;\n"
                       "    0 1 0 : 0;\n"
                       "    0 0 1 : 0;\n"
                       "    0 0 0 : 0;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module m;\n"
                       "  reg a, b, c;\n"
                       "  wire y;\n"
                       "  p u(y, a, b, c);\n"
                       "  initial begin\n"
                       "    a = 1; b = 0; c = 0; #1 $write(\"%b\", y);\n"
                       "    a = 0; b = 0; c = 1; #1 $write(\"%b\", y);\n"
                       "    a = 0; b = 1; c = 0; #1 $display(\"%b\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "100\n");
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kLaterFileTop =
    "module top;\n"
    "  reg d, c;\n"
    "  wire q1, q2, q3, q4;\n"
    "  myudp (q1, d, c);\n"
    "  myudp u2 (q2, d, c);\n"
    "  myudp #5 u3 (q3, d, c);\n"
    "  myudp (strong1, weak0) u4 (q4, d, c);\n"
    "  initial begin\n"
    "    d = 1; c = 1;\n"
    "    #10 $display(\"%b%b%b%b %v\", q1, q2, q3, q4, q4);\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kLaterFilePrimitive =
    "primitive myudp(output q, input d, c);\n"
    "  table\n"
    "    1 1 : 1;\n"
    "    0 ? : 0;\n"
    "    ? 0 : 0;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kLaterFileOutput = "1111 St1\n";

std::string RunElaborated(RtlirDesign* design, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(UdpDefinedInALaterFile, EveryInstanceFormRunsThroughTheDriver) {
  ScratchDir tmp;
  CliOptions opts;
  opts.source_files.push_back(tmp.Write("top.sv", kLaterFileTop).string());
  opts.source_files.push_back(
      tmp.Write("prim.sv", kLaterFilePrimitive).string());
  SimFixture f;
  ProtectLicenseLibraries licenses;
  auto pp = PreprocessSources(opts, f.mgr, f.diag, licenses);
  auto* cu = ParseSource(pp, f.mgr, f.diag, f.arena);
  ASSERT_NE(cu, nullptr);
  ApplyPreprocMetadata(cu, pp);
  Elaborator elab(f.arena, f.diag, cu);
  EXPECT_EQ(RunElaborated(elab.Elaborate("top"), f), kLaterFileOutput);
  EXPECT_FALSE(f.has_errors);
}

TEST(UdpDefinedInALaterFile, EveryInstanceFormRunsThroughTheCommandLine) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.sv;\n");
  auto top = tmp.Write("src/top.sv", kLaterFileTop);
  auto prim = tmp.Write("src/prim.sv", kLaterFilePrimitive);
  SimFixture f;
  LibraryMap libs;
  ASSERT_TRUE(libs.LoadMapFile(tmp.dir / "lib.map"));
  CompilationUnit unit;
  SinglePassCompiler compiler(libs, f.mgr, f.arena, f.diag);
  ASSERT_TRUE(compiler.CompileCommandLine({top, prim}, unit));
  Elaborator elab(f.arena, f.diag, &unit);
  EXPECT_EQ(RunElaborated(elab.Elaborate("top"), f), kLaterFileOutput);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
