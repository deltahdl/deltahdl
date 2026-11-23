#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_memload.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

struct SreadmemCall {
  const char* task;
  const char* mem;
  int start;
  int finish;
  std::vector<const char*> strings;
};

void Sreadmem(SimFixture& f, const SreadmemCall& call) {
  std::vector<Expr*> args = {
      MakeId(f.arena, call.mem),
      MakeInt(f.arena, static_cast<uint64_t>(call.start)),
      MakeInt(f.arena, static_cast<uint64_t>(call.finish))};
  for (const char* s : call.strings) args.push_back(MkStr(f.arena, s));
  EvalExpr(MakeSysCall(f.arena, call.task, args), f.ctx, f.arena);
}

TEST(OptionalSreadmemSim, SreadmemhLoadsHexFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14 1E 28"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

TEST(OptionalSreadmemSim, SreadmembParsesBinaryFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemb", "mem", 0, 1, {"1010 0110"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b0110u);
}

TEST(OptionalSreadmemSim, MultipleStringArgumentsAreConcatenated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14", "1E 28"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

TEST(OptionalSreadmemSim, StartFinishBoundTheStoredRange) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 1, 2, {"AA BB"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
}

TEST(OptionalSreadmemSim, StartGreaterThanFinishLoadsDescending) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 2, 0, {"01 02 03"}});

  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x03u);
}

TEST(OptionalSreadmemSim, AtAddressInStringRepositionsCursor) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"@2 FF"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xFFu);
}

TEST(OptionalSreadmemSim, AdjacentStringsAreTokenSeparated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {"0A", "14"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
}

TEST(OptionalSreadmemSim, MissingDataStringLeavesMemoryUnchanged) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$sreadmemh takes a memory name, a start address, a finish "
                    "address, and one or more strings, and this call has fewer",
                    0, "D.14"));
}

TEST(OptionalSreadmemSim, LoadsADeclaredMemoryFromTheSource) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3, \"0A 14 1E 28\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0a 14 1e 28\n");
}

TEST(OptionalSreadmemSim, TheAddressesBoundWhereTheSourceDataIsStored) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemb(mem, 1, 2, \"1010 0110\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx 0a 06 xx\n");
}

TEST(OptionalSreadmemSim, AStringCarriesACommentAndAnAddressAsAFileDoes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3, \"// header\\n@2 7F\", \"/* skip */ 01\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx 7f 01\n");
}

TEST(OptionalSreadmemSim, ACallWithoutAStringIsReportedUnderD14) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3);\n"
      "    $display(\"%h %h\", mem[0], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$sreadmemh takes a memory name, a start address, "
                            "a finish address, and one or more strings, and "
                            "this call has fewer",
                            4, "D.14"));
}

TEST(OptionalSreadmemSim, AShortSreadmembCallIsReportedUnderItsOwnName) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemb(mem, 1);\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$sreadmemb takes a memory name, a start address, "
                            "a finish address, and one or more strings, and "
                            "this call has fewer",
                            4, "D.14"));
}

constexpr const char* kFourWords = "reg [7:0] mem [0:3];";
constexpr const char* kShowFour =
    "\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]";

std::string LoadSource(const std::string& call,
                       const std::string& decl = kFourWords,
                       const std::string& display = kShowFour) {
  std::string src = "module t;\n  ";
  src += decl;
  src += "\n  initial begin\n    ";
  src += call;
  src += ";\n    $display(";
  src += display;
  src += ");\n  end\nendmodule\n";
  return src;
}

TEST(OptionalSreadmemSim, SeveralSreadmembStringsSplitAtEachBoundary) {
  SimFixture f;
  EXPECT_EQ(RunCapture(LoadSource("$sreadmemb(mem, 0, 1, \"1\", \"10\")"), f),
            "01 02 xx xx\n");
}

TEST(OptionalSreadmemSim, ACallLoadsWhereverItRuns) {
  const char* const kPlaces[] = {
      "module t;\n  reg [7:0] mem [0:3];\n  task automatic ld;\n    CALL;\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n  endtask\n"
      "  initial ld();\nendmodule\n",
      "module t;\n  reg [7:0] mem [0:3];\n  function void ld;\n    CALL;\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n  endfunction\n"
      "  initial ld();\nendmodule\n",
      "class c;\n  bit [7:0] mem [0:3];\n  function void ld();\n    CALL;\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n  endfunction\nendclass\n"
      "module t;\n  c o;\n  initial begin\n    o = new;\n    o.ld();\n"
      "  end\n"
      "endmodule\n",
      "program t;\n  reg [7:0] mem [0:3];\n  initial begin\n    CALL;\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n"
      "  end\nendprogram\n",
  };
  struct PlacedCall {
    const char* call;
    const char* shown;
  };
  const PlacedCall kCalls[] = {
      {"$sreadmemh(mem, 0, 1, \"5A\", \"C3\")", "5a c3\n"},
      {"$sreadmemb(mem, 0, 1, \"101\", \"11\")", "05 03\n"},
  };
  for (const char* place : kPlaces) {
    for (const auto& c : kCalls) {
      std::string src = place;
      src.replace(src.find("CALL"), 4, c.call);
      SimFixture f;
      EXPECT_EQ(RunCapture(src, f), c.shown) << src;
      EXPECT_FALSE(f.diag.HasErrors()) << src;
    }
  }
}

TEST(OptionalSreadmemSim, EveryShortCallIsReportedUnderD14) {
  struct ShortCall {
    const char* call;
    const char* task;
  };
  const ShortCall kCalls[] = {
      {"$sreadmemb(mem, 0, 3)", "$sreadmemb"},
      {"$sreadmemh(mem, 1)", "$sreadmemh"},
      {"$sreadmemh(mem)", "$sreadmemh"},
      {"$sreadmemb(mem)", "$sreadmemb"},
      {"$sreadmemh()", "$sreadmemh"},
      {"$sreadmemb()", "$sreadmemb"},
  };
  for (const auto& c : kCalls) {
    SimFixture f;
    RunCapture(LoadSource(c.call), f);
    std::string message = c.task;
    message +=
        " takes a memory name, a start address, a finish address, and one or "
        "more strings, and this call has fewer";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 4, "D.14"))
        << c.call;
  }
}

TEST(OptionalSreadmemSim, UnknownDigitsAndUnderscoresReadAsInAFile) {
  SimFixture hex;
  EXPECT_EQ(RunCapture(LoadSource("$sreadmemh(mem, 0, 2, \"1_1 2x 3z\")"), hex),
            "11 2x 3z xx\n");
  SimFixture bin;
  EXPECT_EQ(RunCapture(LoadSource("$sreadmemb(mem, 0, 0, \"1x_0z\")",
                                  kFourWords, "\"%b\", mem[0]"),
                       bin),
            "00001x0z\n");
}

TEST(OptionalSreadmemSim,
     ASreadmembAddressIsHexadecimalAndCommentsLoadNothing) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          LoadSource("$sreadmemb(mem, 0, 16, \"@10 1 // 11\\n /* 11 */\")",
                     "reg [7:0] mem [0:16];",
                     "\"%h %h %h\", mem[2], mem[16], mem[3]"),
          f),
      "xx 01 xx\n");
}

TEST(OptionalSreadmemSim, ASreadmembStartAboveFinishLoadsDownward) {
  SimFixture f;
  EXPECT_EQ(RunCapture(LoadSource("$sreadmemb(mem, 3, 2, \"11 101\")"), f),
            "xx xx 05 03\n");
}

TEST(OptionalSreadmemSim, DISABLED_StoringStopsAtTheFinishAddress) {
  struct ExcessCall {
    const char* call;
    const char* shown;
    const char* warning;
  };
  const ExcessCall kCalls[] = {
      {"$sreadmemh(mem, 0, 1, \"01 02 03\")", "01 02 xx xx\n",
       "$sreadmemh: number of data words differs from the address range"},
      {"$sreadmemb(mem, 0, 1, \"1 1 1\")", "01 01 xx xx\n",
       "$sreadmemb: number of data words differs from the address range"},
  };
  for (const auto& c : kCalls) {
    SimFixture f;
    EXPECT_EQ(RunCapture(LoadSource(c.call), f), c.shown) << c.call;
    EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), c.warning, 4, "21.4"))
        << c.call;
  }
}

TEST(OptionalSreadmemSim, DISABLED_AnAddressOutsideTheWindowIsReported) {
  SimFixture f;
  EXPECT_EQ(RunCapture(LoadSource("$sreadmemh(mem, 0, 1, \"@3 7F\")"), f),
            "xx xx xx xx\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$sreadmemh: file address outside the range given by the task", 4,
      "21.4"));
}

TEST(OptionalSreadmemSim, DISABLED_ADigitOutsideTheRadixIsReportedByItsTask) {
  SimFixture bin;
  RunCapture(LoadSource("$sreadmemb(mem, 0, 1, \"10 1a\")"), bin);
  EXPECT_TRUE(ReportedError(bin.diag.Diagnostics(),
                            "$sreadmemb: '1a' is not an unsized binary number",
                            4, "21.4"));
  SimFixture hex;
  RunCapture(LoadSource("$sreadmemh(mem, 0, 1, \"10 1g\")"), hex);
  EXPECT_TRUE(ReportedError(
      hex.diag.Diagnostics(),
      "$sreadmemh: '1g' is not an unsized hexadecimal number", 4, "21.4"));
}

TEST(OptionalSreadmemSim, DISABLED_DataThatIsNoStringLiteralIsReported) {
  struct NonLiteralCall {
    const char* call;
    const char* task;
  };
  const NonLiteralCall kCalls[] = {
      {"$sreadmemh(mem, 0, 1, s)", "$sreadmemh"},
      {"$sreadmemb(mem, 0, 1, s)", "$sreadmemb"},
      {"$sreadmemh(mem, 0, 1, \"AA\", 5)", "$sreadmemh"},
      {"$sreadmemb(mem, 0, 1, 5)", "$sreadmemb"},
  };
  for (const auto& c : kCalls) {
    std::string src = LoadSource(
        c.call, "reg [7:0] mem [0:3];\n  string s = \"AA BB\";", kShowFour);
    SimFixture f;
    RunCapture(src, f);
    std::string message = c.task;
    message +=
        " takes each data argument as a string literal, and this one is not";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, c.call), "D.14"))
        << c.call;
  }
}

}  // namespace
